import ApspStoc.Congest.Tasks

/-!
# The generic [STD] rules in the CONGEST semantics

The algorithm constructors of the toolkit (`seq`, `skip`, `loc`, `call`, `dstart`, `dstep`) as
concrete protocols, and proofs of the generic rules (`mono`, `weaken`, `weakenIO`, `bind`,
`callR`, `locR`, `embThen`, `embWeaken`, `decompThen`, `decompStart`, `decompBase`,
`decompStep`, `g0Then`, `routeViaWeaken`, `routeWeaken`) for the concrete judgement `CImplT`.
-/

namespace APSP.Stoc.Congest

open APSP Finset

/-! ## Algorithm constructors -/

/-- sequential composition -/
def cseq (A B : CAlg) : CAlg := fun V _ _ => seqP (A V) (B V)

/-- the empty algorithm -/
def cskip : CAlg := fun _ _ _ => skipP

/-- a local computation -/
noncomputable def cloc (F : LocFn) : CAlg := fun _ _ _ => locP F

/-- a local call -/
noncomputable def ccall (F : LocFn) (A : CAlg) : CAlg := fun V _ _ => callP F (A V)

/-- initialisation of the decomposition: the residual edges are the incident edges (those with a
non-zero weight in the local view), no clusters yet -/
def initD : LocFn :=
  ⟨fun _ => Unit, DState, fun _ _ _ _ vw _ => (univ.filter (fun e => vw e ≠ 0), ∅)⟩

/-- update of the decomposition state by newly found cluster slices -/
def updD : LocFn :=
  ⟨fun V => DState V × Finset (Finset (Sym2 V)), DState,
    fun _ _ _ _ _ p => (p.1.1 \ p.2.biUnion id, p.1.2 ∪ p.2)⟩

/-- start of the iterative decomposition -/
noncomputable def cdstart (A : CAlg) : CAlg := ccall initD A

/-- one step of the iterative decomposition -/
noncomputable def cdstep (A B : CAlg) : CAlg := cseq A (ccall updD B)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Typed sequencing -/

lemma postOf_mono {I : Inst V} {β : Type} {R R' : (Agent V → β) → Prop} (h : ∀ z, R z → R' z)
    (y : Agent V → Mem) : postOf I R y → postOf I R' y := fun ⟨z, hz, hR⟩ => ⟨z, hz, h z hR⟩

/-- Sequencing with typed data: the second protocol starts from the pairs (input, output). -/
theorem bindT {A B : Proto V} {I : Inst V} {α β : Type} {x : Agent V → α}
    {R : (Agent V → β) → Prop} {Q : (Agent V → Mem) → Prop} {p q : Prof V} {δ δ' : ℝ}
    (hA : ImplI A I (inOf x) (postOf I R) p δ)
    (hB : ∀ z, R z → ImplI B I (inOf (fun g => (x g, z g))) Q q δ') (hδ' : 0 ≤ δ') :
    ImplI (seqP A B) I (inOf x) Q (p + q) (δ + δ') := by
  refine bindI hA (fun y ⟨z, hz, hR⟩ => ?_) hδ'
  refine (ImplI.congr B I (fun g hg => ?_)).1 (hB z hR)
  show (⟨α × β, (x g, z g)⟩ : Mem) = pairMem ⟨α, x g⟩ (y g)
  rw [hz g hg]; rfl

/-- `ImplI` for typed inputs only depends on the inputs of hosted agents. -/
lemma implI_inOf_congr {P : Proto V} {I : Inst V} {α : Type} {x x' : Agent V → α}
    (hx : ∀ g, (I.host g).isSome → x g = x' g) {Q : (Agent V → Mem) → Prop} {p : Prof V}
    {δ : ℝ} : ImplI P I (inOf x) Q p δ ↔ ImplI P I (inOf x') Q p δ :=
  ImplI.congr P I (fun g hg => by simp only [inOf, hx g hg])

/-! ## Hosts -/

lemma baseInst_host {N : WNet V} {g : Agent V} (h : ((baseInst N).host g).isSome) :
    ∃ v, g = .inl v := by
  cases g with
  | inl v => exact ⟨v, rfl⟩
  | inr _ => simp [baseInst, physHost] at h

lemma clInst_host {N : WNet V} {C : Finset (Sym2 V)} {g : Agent V}
    (h : ((clInst N C).host g).isSome) : ∃ v ∈ nodes C, g = .inl v := by
  cases g with
  | inl v =>
    refine ⟨v, ?_, rfl⟩
    by_contra hv
    simp [clInst, clInstP, clHost, hv] at h
  | inr _ => simp [clInst, clInstP, clHost] at h

/-- `locOut` on an agent holding data of the right type. -/
lemma locOut_some (F : LocFn) (c : NCtx V) (inp : Agent V → Option Mem) (g : Agent V)
    (a : F.α V) (vw : Sym2 V → ℕ) (h1 : inp g = some ⟨F.α V, a⟩) (h2 : c.view g = some vw) :
    locOut F c inp g = some ⟨F.β V, F.f V g vw a⟩ := by
  unfold locOut; rw [h1, h2]; simp

lemma filter_lview (N : WNet V) (v : V) :
    univ.filter (fun e => lview N (.inl v) e ≠ 0) = resLoc N.G.edgeFinset v := by
  ext e
  rw [Finset.mem_filter, resLoc, Finset.mem_filter]
  simp only [mem_univ, true_and, lview]
  by_cases h : e ∈ N.G.edgeFinset ∧ v ∈ e
  · have := N.wpos e (SimpleGraph.mem_edgeFinset.1 h.1)
    rw [if_pos h]
    exact ⟨fun _ => h, fun _ => by omega⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

/-! ## The generic rules -/

theorem c_mono {A : CAlg} {N : WNet V} {t : Task V} {p p' : Prof V} {δ δ' : ℝ}
    (h : CImplT A N t p δ) (hp : p ≤ p') (hδ : δ ≤ δ') : CImplT A N t p' δ' := by
  cases t with
  | compute ctx β spec =>
    cases ctx with
    | none => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
    | some E => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | io E j sz α β x R => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | mst E j sz S => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | embedOverlays Good => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | decompose Good => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | decompRest F acc Good => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | expDecompOnce F φinv Good => exact fun a => ImplI.mono _ _ (h a) hp hδ (fun _ h => h)
  | embedFrom cl Good => exact fun r => ImplI.mono _ _ (h r) hp hδ (fun _ h => h)
  | clusterSetup C => exact ImplI.mono _ _ h hp hδ (fun _ h => h)
  | buildG0 C P Good => exact fun pl lam => ImplI.mono _ _ (h pl lam) hp hδ (fun _ h => h)
  | routeViaG0 C P g D lam pw Good =>
    exact fun R ℓ ω hω pl hpl hok => ImplI.mono _ _ (h R ℓ ω hω pl hpl hok) hp hδ (fun _ h => h)
  | route C P D lam pw Good =>
    exact fun pl hpl hok => ImplI.mono _ _ (h pl hpl hok) hp hδ (fun _ h => h)

theorem c_weaken {A : CAlg} {N : WNet V} {ctx : Option (Overlays V)} {β : Type}
    {spec spec' : (V → β) → Prop} {p : Prof V} {δ : ℝ} (hs : ∀ o, spec o → spec' o)
    (h : CImplT A N (.compute ctx β spec) p δ) : CImplT A N (.compute ctx β spec') p δ := by
  cases ctx with
  | none => exact ImplI.mono _ _ h le_rfl le_rfl (postOf_mono (fun z hz => hs _ hz))
  | some E => exact ImplI.mono _ _ h le_rfl le_rfl (postOf_mono (fun z hz => hs _ hz))

theorem c_weakenIO {A : CAlg} {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V}
    {α β : Type} {x : Agent V → α} {R R' : (Agent V → β) → Prop} {p : Prof V} {δ : ℝ}
    (hR : ∀ y, R y → R' y) (h : CImplT A N (.io E j sz Pt α β x R) p δ) :
    CImplT A N (.io E j sz Pt α β x R') p δ :=
  ImplI.mono _ _ h le_rfl le_rfl (postOf_mono hR)

theorem c_bind {A B : CAlg} {N : WNet V} {E : Overlays V} {j sz : ℕ} {Pt : Finset V}
    {α β γ : Type} {x : Agent V → α} {R : (Agent V → β) → Prop} {R' : (Agent V → γ) → Prop}
    {p q : Prof V} {δ δ' : ℝ} (hA : CImplT A N (.io E j sz Pt α β x R) p δ)
    (hB : ∀ y, R y → CImplT B N (.io E j sz Pt (α × β) γ (fun g => (x g, y g)) R') q δ')
    (hδ' : 0 ≤ δ') : CImplT (cseq A B) N (.io E j sz Pt α γ x R') (p + q) (δ + δ') :=
  bindT hA hB hδ'

theorem c_callR (F : LocFn) {B : CAlg} {N : WNet V} {E : Overlays V} {j sz : ℕ}
    {Pt : Finset V} {β : Type}
    (x : Agent V → F.α V) {R : (Agent V → β) → Prop} {p : Prof V} {δ : ℝ}
    (h : CImplT B N (.io E j sz Pt (F.β V) β (fun g => F.f V g (lview N g) (x g)) R) p δ) :
    CImplT (ccall F B) N (.io E j sz Pt (F.α V) β x R) p δ := by
  refine callI F (fun v => ?_) h
  funext g
  by_cases hg : ioHost E j Pt g = some v
  · have h1 : inpAt (ioInst N E j sz Pt) (inOf x) v g = some ⟨F.α V, x g⟩ := by
      unfold inpAt; exact if_pos hg
    have h2 : ((ioInst N E j sz Pt).ctx v).view g = some (lview N g) := by
      show ioView N E j Pt v g = _; unfold ioView; exact if_pos hg
    have h3 : inpAt (ioInst N E j sz Pt) (inOf (fun g => F.f V g (lview N g) (x g))) v g =
        some ⟨F.β V, F.f V g (lview N g) (x g)⟩ := by
      unfold inpAt; exact if_pos hg
    rw [h3]; unfold locOut; rw [h1, h2]; simp
  · have h1 : inpAt (ioInst N E j sz Pt) (inOf x) v g = none := by
      unfold inpAt; exact if_neg hg
    have h3 : inpAt (ioInst N E j sz Pt) (inOf (fun g => F.f V g (lview N g) (x g))) v g = none := by
      unfold inpAt; exact if_neg hg
    rw [h3]; unfold locOut; rw [h1]

theorem c_locR (F : LocFn) (N : WNet V) (E : Overlays V) (j sz : ℕ) (Pt : Finset V)
    (x : Agent V → F.α V) :
    CImplT (cloc F) N (.io E j sz Pt (F.α V) (F.β V) x
      (fun y => ∀ g, y g = F.f V g (lview N g) (x g))) 0 0 := by
  refine locI F le_rfl (inOf (fun g => F.f V g (lview N g) (x g))) (fun g v hv => ?_)
    ⟨fun g => F.f V g (lview N g) (x g), fun _ _ => rfl, fun _ => rfl⟩
  have h1 : inpAt (ioInst N E j sz Pt) (inOf x) v g = some ⟨F.α V, x g⟩ := by
    unfold inpAt; exact if_pos hv
  have h2 : ((ioInst N E j sz Pt).ctx v).view g = some (lview N g) := by
    show ioView N E j Pt v g = _; unfold ioView; exact if_pos hv
  unfold locOut; rw [h1, h2]; simp [inOf]

theorem c_embThen {A B : CAlg} {N : WNet V} {Good : Overlays V → Prop} {β : Type}
    {spec : (V → β) → Prop} {p q : Prof V} {δ δ' : ℝ} (hA : CImplT A N (.embedOverlays Good) p δ)
    (hB : ∀ E, Good E → CImplT B N (.compute (some E) β spec) q δ') (hδ' : 0 ≤ δ') :
    CImplT (cseq A B) N (.compute none β spec) (p + q) (δ + δ') := by
  refine bindT hA (fun z ⟨E, hE, hz⟩ => ?_) hδ'
  refine (implI_inOf_congr (fun g hg => ?_)).1 (hB E hE)
  obtain ⟨v, rfl⟩ := baseInst_host hg
  simp [hz v]

theorem c_embWeaken {A : CAlg} {N : WNet V} {Good Good' : Overlays V → Prop} {p : Prof V}
    {δ : ℝ} (hG : ∀ E, Good E → Good' E) (h : CImplT A N (.embedOverlays Good) p δ) :
    CImplT A N (.embedOverlays Good') p δ :=
  ImplI.mono _ _ h le_rfl le_rfl (postOf_mono (fun _ ⟨E, hE, hz⟩ => ⟨E, hG E hE, hz⟩))

theorem c_decompThen {A B : CAlg} {N : WNet V} {GoodD : Finset (Finset (Sym2 V)) → Prop}
    {Good : Overlays V → Prop} {p q : Prof V} {δ δ' : ℝ} (hA : CImplT A N (.decompose GoodD) p δ)
    (hB : ∀ cl, GoodD cl → CImplT B N (.embedFrom cl Good) q δ') (hδ' : 0 ≤ δ') :
    CImplT (cseq A B) N (.embedOverlays Good) (p + q) (δ + δ') := by
  refine bindT hA (fun z ⟨cl, hcl, hz⟩ => ?_) hδ'
  refine (implI_inOf_congr (fun g hg => ?_)).1 (hB cl hcl (fun v => (z (.inl v)).1))
  obtain ⟨v, rfl⟩ := baseInst_host hg
  simp only [← hz v]

theorem c_decompStart {A : CAlg} {N : WNet V} {Good : Finset (Finset (Sym2 V)) → Prop}
    {p : Prof V} {δ : ℝ} (h : CImplT A N (.decompRest N.G.edgeFinset ∅ Good) p δ) :
    CImplT (cdstart A) N (.decompose Good) p δ := by
  refine callI initD (fun v => ?_) h
  funext g
  by_cases hg : g = .inl v
  · subst hg
    have h1 : inpAt (baseInst N) (inOf (fun _ => ())) v (.inl v) = some ⟨Unit, ()⟩ := by
      unfold inpAt; exact if_pos rfl
    have h2 : ((baseInst N).ctx v).view (.inl v) = some (lview N (.inl v)) := by
      show (if (Sum.inl v : Agent V) = .inl v then _ else _) = _; exact if_pos rfl
    have h3 : inpAt (baseInst N) (inOf (dAt N.G.edgeFinset ∅)) v (.inl v) =
        some ⟨DState V, (resLoc N.G.edgeFinset v, clLoc ∅ v)⟩ := by
      unfold inpAt; exact if_pos rfl
    rw [h3, locOut_some initD _ _ _ () _ h1 h2]
    show some (⟨DState V, (univ.filter (fun e => lview N (.inl v) e ≠ 0), ∅)⟩ : Mem) = _
    rw [filter_lview]
    simp [clLoc]
  · have hh : (baseInst N).host g ≠ some v := by
      cases g with
      | inl u => simp only [baseInst, physHost, ne_eq, Option.some.injEq]; rintro rfl; exact hg rfl
      | inr _ => simp [baseInst, physHost]
    have h1 : inpAt (baseInst N) (inOf (fun _ => ())) v g = none := by
      unfold inpAt; exact if_neg hh
    have h3 : inpAt (baseInst N) (inOf (dAt N.G.edgeFinset ∅)) v g = none := by
      unfold inpAt; exact if_neg hh
    rw [h3]; unfold locOut; rw [h1]

theorem c_decompBase {N : WNet V} {Good : Finset (Finset (Sym2 V)) → Prop}
    {acc : Finset (Finset (Sym2 V))} (h : Good acc) :
    CImplT cskip N (.decompRest ∅ acc Good) 0 0 :=
  skipI le_rfl ⟨dAt ∅ acc, fun _ _ => rfl, acc, h, fun _ => rfl⟩

lemma clLoc_biUnion (P : Finset (Finset (Sym2 V))) (v : V) :
    (clLoc P v).biUnion id = (P.biUnion id).filter (fun e => v ∈ e) := by
  ext e
  simp only [clLoc, mem_biUnion, mem_filter, mem_image, id]
  constructor
  · rintro ⟨s, ⟨⟨C, hC, rfl⟩, -⟩, he⟩
    exact ⟨⟨C, hC, (mem_filter.1 he).1⟩, (mem_filter.1 he).2⟩
  · rintro ⟨⟨C, hC, heC⟩, hv⟩
    exact ⟨C.filter (fun e => v ∈ e), ⟨⟨C, hC, rfl⟩, ⟨e, mem_filter.2 ⟨heC, hv⟩⟩⟩,
      mem_filter.2 ⟨heC, hv⟩⟩

lemma resLoc_sdiff (F : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) (v : V) :
    resLoc F v \ (clLoc P v).biUnion id = resLoc (F \ P.biUnion id) v := by
  rw [clLoc_biUnion]
  ext e
  simp only [resLoc, mem_sdiff, mem_filter]
  tauto

lemma clLoc_union (A B : Finset (Finset (Sym2 V))) (v : V) :
    clLoc A v ∪ clLoc B v = clLoc (A ∪ B) v := by
  simp only [clLoc, image_union, filter_union]

theorem c_decompStep {A B : CAlg} {N : WNet V} {Good : Finset (Finset (Sym2 V)) → Prop}
    {GP : Finset (Finset (Sym2 V)) → Prop} {F : Finset (Sym2 V)} {acc : Finset (Finset (Sym2 V))}
    {φinv : ℕ} {p q : Prof V} {δ δ' : ℝ} (hA : CImplT A N (.expDecompOnce F φinv GP) p δ)
    (hB : ∀ P, GP P → CImplT B N (.decompRest (F \ P.biUnion id) (acc ∪ P) Good) q δ')
    (hδ' : 0 ≤ δ') : CImplT (cdstep A B) N (.decompRest F acc Good) (p + q) (δ + δ') := by
  have hA' : ImplI (A V) (baseInst N) (inOf (dAt F acc))
      (postOf (baseInst N) (fun z : Agent V → Finset (Finset (Sym2 V)) =>
        ∃ P, GP P ∧ ∀ v, z (.inl v) = clLoc P v)) p δ := by
    refine (implI_inOf_congr (fun g hg => ?_)).1 (hA (clLoc acc))
    obtain ⟨v, rfl⟩ := baseInst_host hg
    rfl
  refine bindT hA' (fun z ⟨P, hP, hz⟩ => ?_) hδ'
  refine callI updD (fun v => ?_) (hB P hP)
  funext g
  by_cases hg : g = .inl v
  · subst hg
    have h1 : inpAt (baseInst N) (inOf (fun g => (dAt F acc g, z g))) v (.inl v) =
        some ⟨DState V × Finset (Finset (Sym2 V)), (dAt F acc (.inl v), z (.inl v))⟩ := by
      unfold inpAt; exact if_pos rfl
    have h2 : ((baseInst N).ctx v).view (.inl v) = some (lview N (.inl v)) := by
      show (if (Sum.inl v : Agent V) = .inl v then _ else _) = _; exact if_pos rfl
    have h3 : inpAt (baseInst N) (inOf (dAt (F \ P.biUnion id) (acc ∪ P))) v (.inl v) =
        some ⟨DState V, (resLoc (F \ P.biUnion id) v, clLoc (acc ∪ P) v)⟩ := by
      unfold inpAt; exact if_pos rfl
    rw [h3, locOut_some updD _ _ _ (dAt F acc (.inl v), z (.inl v)) _ h1 h2]
    show some (⟨DState V, ((dAt F acc (.inl v)).1 \ (z (.inl v)).biUnion id,
      (dAt F acc (.inl v)).2 ∪ z (.inl v))⟩ : Mem) = _
    simp only [dAt, hz v, resLoc_sdiff, clLoc_union]
  · have hh : (baseInst N).host g ≠ some v := by
      cases g with
      | inl u => simp only [baseInst, physHost, ne_eq, Option.some.injEq]; rintro rfl; exact hg rfl
      | inr _ => simp [baseInst, physHost]
    have h1 : inpAt (baseInst N) (inOf (fun g => (dAt F acc g, z g))) v g = none := by
      unfold inpAt; exact if_neg hh
    have h3 : inpAt (baseInst N) (inOf (dAt (F \ P.biUnion id) (acc ∪ P))) v g = none := by
      unfold inpAt; exact if_neg hh
    rw [h3]; unfold locOut; rw [h1]

theorem c_g0Then {A B : CAlg} {N : WNet V} {C : Finset (Sym2 V)} {P : Finset (Port V)}
    {D : Demand V} {lam pw : ℕ} {GG : G0Data → Prop} {GR : Routes V → Prop} {p q : Prof V}
    {δ δ' : ℝ} (hA : CImplT A N (.buildG0 C P GG) p δ)
    (hB : ∀ g, GG g → CImplT B N (.routeViaG0 C P g D lam pw GR) q δ') (hδ' : 0 ≤ δ') :
    CImplT (cseq A B) N (.route C P D lam pw GR) (p + q) (δ + δ') := by
  intro pl hpl hok
  refine bindT (hA pl lam) (fun z ⟨R, ℓ, ω, g, hT, hg, hz⟩ => ?_) hδ'
  refine (implI_inOf_congr (fun a ha => ?_)).1 (hB g hg R ℓ ω hT pl hpl hok)
  obtain ⟨v, hv, rfl⟩ := clInst_host ha
  simp [hz v hv]

theorem c_routeViaWeaken {A : CAlg} {N : WNet V} {C : Finset (Sym2 V)} {P : Finset (Port V)}
    {g : G0Data} {D : Demand V} {lam pw : ℕ} {GR GR' : Routes V → Prop} {p : Prof V} {δ : ℝ}
    (hG : ∀ r, GR r → GR' r) (h : CImplT A N (.routeViaG0 C P g D lam pw GR) p δ) :
    CImplT A N (.routeViaG0 C P g D lam pw GR') p δ := fun R ℓ ω hω pl hpl hok =>
  ImplI.mono _ _ (h R ℓ ω hω pl hpl hok) le_rfl le_rfl
    (postOf_mono (fun _ ⟨r, hr, hz⟩ => ⟨r, hG r hr, hz⟩))

theorem c_routeWeaken {A : CAlg} {N : WNet V} {C : Finset (Sym2 V)} {P : Finset (Port V)}
    {D : Demand V} {lam pw : ℕ} {GR GR' : Routes V → Prop} {p : Prof V} {δ : ℝ}
    (hG : ∀ r, GR r → GR' r) (h : CImplT A N (.route C P D lam pw GR) p δ) :
    CImplT A N (.route C P D lam pw GR') p δ := fun pl hpl hok =>
  ImplI.mono _ _ (h pl hpl hok) le_rfl le_rfl
    (postOf_mono (fun _ ⟨r, hr, hz⟩ => ⟨r, hG r hr, hz⟩))

end APSP.Stoc.Congest
