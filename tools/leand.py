#!/usr/bin/env python3
"""A small daemon keeping a Lean language server alive, so that Mathlib is loaded once.

Usage:
  leand.py serve SOCKET            # start the daemon (run in background, from the project root)
  leand.py check SOCKET FILE [TIMEOUT]   # (re)check FILE, print errors (and warnings with -w)

The daemon opens each requested file as an LSP document; subsequent checks of the same file send
the new full content as a change, so only the changed part is re-elaborated (the imports stay
loaded as long as the header is unchanged).
"""
import json, os, socket, subprocess, sys, threading, time

LEAN_BIN = "/home/perobinson/.local/opt/lean/lean-4.35.0-linux_aarch64/bin"


class LSP:
    def __init__(self, root):
        env = dict(os.environ)
        env["PATH"] = LEAN_BIN + ":" + env.get("PATH", "")
        self.p = subprocess.Popen(["lake", "serve"], cwd=root, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
        self.lock = threading.Lock()
        self.id = 0
        self.diags = {}      # uri -> list
        self.dver = {}       # uri -> version of the diagnostics
        self.version = {}    # uri -> version
        self.done = {}       # uri -> (version, bool) processing finished
        self.cv = threading.Condition()
        threading.Thread(target=self.reader, daemon=True).start()
        self.request("initialize", {"processId": os.getpid(), "rootUri": "file://" + root,
                                    "capabilities": {}})
        self.notify("initialized", {})

    def send(self, msg):
        data = json.dumps(msg).encode()
        with self.lock:
            self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
            self.p.stdin.flush()

    def request(self, method, params):
        self.id += 1
        self.send({"jsonrpc": "2.0", "id": self.id, "method": method, "params": params})

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def reader(self):
        f = self.p.stdout
        while True:
            line = f.readline()
            if not line:
                return
            if line.startswith(b"Content-Length:"):
                n = int(line.split(b":")[1])
                while f.readline() not in (b"\r\n", b"\n"):
                    pass
                msg = json.loads(f.read(n))
                m = msg.get("method")
                with self.cv:
                    if m == "textDocument/publishDiagnostics":
                        uri = msg["params"]["uri"]
                        self.diags[uri] = msg["params"]["diagnostics"]
                        self.dver[uri] = msg["params"].get("version")
                        self.cv.notify_all()
                    elif m == "$/lean/fileProgress":
                        uri = msg["params"]["textDocument"]["uri"]
                        ver = msg["params"]["textDocument"].get("version")
                        if not msg["params"]["processing"]:
                            self.done[uri] = ver
                        self.cv.notify_all()

    def check(self, path, timeout):
        uri = "file://" + os.path.abspath(path)
        text = open(path).read()
        with self.cv:
            if uri not in self.version:
                self.version[uri] = 1
                self.done.pop(uri, None)
                self.notify("textDocument/didOpen", {"textDocument": {
                    "uri": uri, "languageId": "lean4", "version": 1, "text": text}})
            else:
                self.version[uri] += 1
                self.done.pop(uri, None)
                self.notify("textDocument/didChange", {
                    "textDocument": {"uri": uri, "version": self.version[uri]},
                    "contentChanges": [{"text": text}]})
            ver = self.version[uri]
            t0 = time.time()
            while self.done.get(uri) != ver:
                if time.time() - t0 > timeout:
                    return None
                self.cv.wait(5)
            t1 = time.time()
            while self.dver.get(uri) != ver and time.time() - t1 < 20:
                self.cv.wait(1)
            return self.diags.get(uri, [])

    def close(self, path):
        uri = "file://" + os.path.abspath(path)
        with self.cv:
            if uri in self.version:
                self.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
                del self.version[uri]


def fmt(diags, warnings):
    out = []
    for d in diags:
        sev = d.get("severity", 1)
        if sev == 1 or (warnings and sev == 2):
            r = d["range"]["start"]
            kind = "error" if sev == 1 else "warning"
            out.append(f"{r['line']+1}:{r['character']}: {kind}: {d['message']}")
    return "\n".join(out)


def serve(qdir):
    root = os.getcwd()
    lsp = LSP(root)
    os.makedirs(qdir, exist_ok=True)
    seen = set()

    def handle(name):
        rp = os.path.join(qdir, name)
        try:
            req = json.load(open(rp))
            out = os.path.join(qdir, name[:-4] + ".out")
            if req.get("cmd") == "close":
                lsp.close(req["file"])
                txt = "closed\n"
            else:
                diags = lsp.check(req["file"], req.get("timeout", 3600))
                if diags is None:
                    txt = "TIMEOUT\n"
                else:
                    errs = [d for d in diags if d.get("severity", 1) == 1]
                    t = fmt(diags, req.get("warnings", False))
                    txt = ((t + "\n") if t else "") + ("OK (no errors)\n" if not errs else "FAILED\n")
        except Exception as e:
            txt = f"daemon error: {e}\n"
        open(out + ".tmp", "w").write(txt)
        os.rename(out + ".tmp", out)

    while True:
        for name in sorted(os.listdir(qdir)):
            if name.endswith(".req") and name not in seen:
                seen.add(name)
                threading.Thread(target=handle, args=(name,), daemon=True).start()
        time.sleep(0.3)


def check(qdir, path, timeout, warnings, close=False):
    import uuid
    rid = uuid.uuid4().hex
    req = {"cmd": "close" if close else "check", "file": os.path.abspath(path),
           "timeout": timeout, "warnings": warnings}
    tmp = os.path.join(qdir, rid + ".tmpreq")
    json.dump(req, open(tmp, "w"))
    os.rename(tmp, os.path.join(qdir, rid + ".req"))
    out = os.path.join(qdir, rid + ".out")
    t0 = time.time()
    while not os.path.exists(out):
        if time.time() - t0 > timeout + 60:
            print("client timeout"); return
        time.sleep(0.5)
    sys.stdout.write(open(out).read())
    os.unlink(out)
    os.unlink(os.path.join(qdir, rid + ".req"))


if __name__ == "__main__":
    if sys.argv[1] == "serve":
        serve(sys.argv[2])
    elif sys.argv[1] in ("check", "checkw", "close"):
        timeout = int(sys.argv[4]) if len(sys.argv) > 4 else 3600
        check(sys.argv[2], sys.argv[3], timeout, sys.argv[1] == "checkw", sys.argv[1] == "close")
