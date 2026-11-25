import re,sys
s=open('ApspStoc/Toolkit.lean').read()
start=s.index('structure Toolkit where')
body=s[start:s.index('end APSP.Stoc',start)]
lines=body.split('\n')[1:]
fields=[]; cur=[]
for ln in lines:
    if (ln.startswith('  /--') or ln.startswith('  -- ###')) and cur and any(re.match(r'^  [A-Za-z0-9]+ :',l) for l in cur):
        fields.append(cur); cur=[]
    cur.append(ln)
if cur: fields.append(cur)
def name(f):
    for l in f:
        m=re.match(r'^  ([A-Za-z0-9]+) :',l)
        if m: return m.group(1)
def sub(t):
    t=re.sub(r'\bImpl\b','CImplT',t); t=re.sub(r'\bAlg\b','CAlg',t); return t
assumed=['sched','mstAlg','approxAlg','eoAlg','expDecomp','routeG0','ghs','mstRed','approxRed','eoVirt','schedule']
names=[name(f) for f in fields]
missing=[a for a in assumed if a not in names]
if missing: print("MISSING",missing); sys.exit(1)
out=[]
for f in fields:
    n=name(f)
    if n in assumed:
        txt='\n'.join(l for l in f if not l.startswith('  -- ###')).rstrip()+'\n'
        out.append(sub(txt))
hdr=open('ApspStoc/Congest/Assume.lean').read()
hdr=hdr[:hdr.index('structure CAssume where')+len('structure CAssume where\n')]
open('ApspStoc/Congest/Assume.lean','w').write(hdr+'\n'.join(out)+'\nend APSP.Stoc.Congest\n')
def stmt(n):
    for f in fields:
        if name(f)==n:
            txt='\n'.join(l for l in f if not l.startswith('  -- ###'))
            i=txt.index('  '+n+' :')
            return sub(txt[i+len('  '+n+' :'):].rstrip())
defs={'notify':'NotifyC','treeCast':'TreeCastC','clusterSetup':'SetupC'}
out=''
for n,d in defs.items():
    out+=f'/-- the toolkit field `{n}` for the CONGEST semantics -/\ndef {d} : Prop :={stmt(n)}\n\n'
m=open('ApspStoc/Congest/Model.lean').read()
a=m.index('/-- the toolkit field `notify`')
b=m.index('/-- The toolkit of the CONGEST semantics')
m=m[:a]+out+m[b:]
open('ApspStoc/Congest/Model.lean','w').write(m)
print("ok")
