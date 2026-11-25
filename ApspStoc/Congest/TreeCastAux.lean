import ApspStoc.Congest.Tasks

/-!
# Auxiliary material for the tree convergecast/broadcast (`TreeCast.lean`)

* **Encoding.** A value (a list of at most `b` words with numbers `≤ n^Bw`) is sent as a stream of
  exactly `encLen Bw b = (b + 1) * (Bw + 2)` words with numbers `≤ n + 3`: one block of `Bw + 2`
  words per position (a tag, then the word itself or the base-`(n + 4)` digits of the number).
  `dec_enc`: decoding inverts encoding.
* **Forests.** For parent pointers `par` on `S` with a rank function `rk`, the children, height,
  depth and the aggregate of a subtree (`kidsOf`, `hgt`, `dep`, `agg`), with their recursive
  equations, the bounds `hgt u < |S|` and `dep u < |S|`, and `agg_spec`: the aggregate of a root is
  an `AggOf` of the values of its tree.
* **Full-information protocols** (`histP`): a node keeps its context, input and the history of all
  messages received; it sends a function of these and halts at a public round. `succ_histP`: if
  the protocol, fed with the histories of an explicit schedule `M`, sends exactly the messages of
  `M` (at every participant, to every node), and `M` sends only along edges of the instance, then
  the run follows `M` and its sends are proper, so its costs and outputs can be read off `M`.
-/

namespace APSP.Stoc.Congest

open APSP Finset Relation

set_option linter.unusedSectionVars false

section Enc

variable {V : Type}

/-! ## Encoding values as streams of small words -/

/-- the number in a word (`0` for IDs and edges) -/
def wnum : Word V → ℕ
  | .num k => k
  | _ => 0

/-- the value of `D` little-endian base-`β` digits, given positionally -/
def digVal (β : ℕ) (g : ℕ → Word V) : ℕ → ℕ
  | 0 => 0
  | D + 1 => wnum (g 0) + β * digVal β (fun r => g (r + 1)) D

/-- position `r` of the block encoding the (optional) word `o`: a tag (`0` ID or edge, `1` number,
`2` absent) followed by the payload (the word itself, or the base-`β` digits of the number) -/
def blockAt (β : ℕ) : Option (Word V) → ℕ → Word V
  | none, 0 => .num 2
  | none, _ + 1 => .num 0
  | some (.num _), 0 => .num 1
  | some (.num k), r + 1 => .num (k / β ^ r % β)
  | some (.id _), 0 => .num 0
  | some (.id v), 1 => .id v
  | some (.id _), _ + 2 => .num 0
  | some (.edge _), 0 => .num 0
  | some (.edge e), 1 => .edge e
  | some (.edge _), _ + 2 => .num 0

/-- decoding of a block (tag and `D + 1` digits) given positionally -/
def decBlock (β D : ℕ) (f : ℕ → Word V) : Option (Word V) :=
  match f 0 with
  | .num 0 => some (f 1)
  | .num 1 => some (.num (digVal β (fun r => f (r + 1)) (D + 1)))
  | _ => none

/-- position `j` of the encoding of a value: block `j / (Bw + 2)` at position `j % (Bw + 2)`;
digits in base `n + 4` -/
def encAt (n Bw : ℕ) (m : Msg V) (j : ℕ) : Word V := blockAt (n + 4) m[j / (Bw + 2)]? (j % (Bw + 2))

/-- the length of an encoded value with at most `b` words -/
def encLen (Bw b : ℕ) : ℕ := (b + 1) * (Bw + 2)

/-- the encoding of a value with at most `b` words -/
def enc (n Bw b : ℕ) (m : Msg V) : List (Word V) := (List.range (encLen Bw b)).map (encAt n Bw m)

/-- decoding -/
def dec (n Bw b : ℕ) (l : List (Word V)) : Msg V :=
  (List.range (b + 1)).filterMap
    (fun i => decBlock (n + 4) Bw (fun r => l.getD (i * (Bw + 2) + r) (.num 0)))

lemma digVal_digits (β : ℕ) (D : ℕ) : ∀ k : ℕ,
    digVal (V := V) β (fun r => .num (k / β ^ r % β)) D = k % β ^ D := by
  induction D with
  | zero => intro k; simp [digVal, Nat.mod_one]
  | succ D ih =>
    intro k
    simp only [digVal, wnum, pow_zero, Nat.div_one]
    have h1 : (fun r => (Word.num (k / β ^ (r + 1) % β) : Word V)) =
        (fun r => Word.num (k / β / β ^ r % β)) := by
      funext r; rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [h1, ih, pow_succ', Nat.mod_mul]

lemma digVal_congr (β : ℕ) (D : ℕ) : ∀ g g' : ℕ → Word V, (∀ r < D, g r = g' r) →
    digVal β g D = digVal β g' D := by
  induction D with
  | zero => intros; rfl
  | succ D ih =>
    intro g g' h
    simp only [digVal]
    rw [h 0 (by omega), ih (fun r => g (r + 1)) (fun r => g' (r + 1)) (fun r hr => h _ (by omega))]

lemma decBlock_congr (β D : ℕ) (f f' : ℕ → Word V) (h : ∀ r < D + 2, f r = f' r) :
    decBlock β D f = decBlock β D f' := by
  unfold decBlock
  rw [h 0 (by omega), h 1 (by omega),
    digVal_congr β (D + 1) (fun r => f (r + 1)) (fun r => f' (r + 1)) (fun r hr => h _ (by omega))]

lemma decBlock_blockAt (β D : ℕ) (o : Option (Word V))
    (ho : ∀ k, o = some (.num k) → k < β ^ (D + 1)) :
    decBlock β D (blockAt β o) = o := by
  rcases o with _ | (v | k | e)
  · rfl
  · rfl
  · have hk := ho k rfl
    simp only [decBlock, blockAt]
    rw [digVal_digits, Nat.mod_eq_of_lt hk]
  · rfl

lemma filterMap_getElem?_range : ∀ (l : List (Word V)) (N : ℕ), l.length ≤ N →
    (List.range N).filterMap (fun i => l[i]?) = l := by
  intro l
  induction l with
  | nil => intro N _; simp
  | cons a l ih =>
    intro N hN
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Function.comp_def]
    rw [ih N (by simp at hN; omega)]

lemma length_enc (n Bw b : ℕ) (m : Msg V) : (enc n Bw b m).length = encLen Bw b := by
  simp [enc]

lemma dec_enc (n Bw b : ℕ) (m : Msg V) (hl : m.length ≤ b)
    (hm : ∀ k, Word.num k ∈ m → k < (n + 4) ^ (Bw + 1)) : dec n Bw b (enc n Bw b m) = m := by
  unfold dec
  have h1 : ∀ i ∈ List.range (b + 1), decBlock (n + 4) Bw
      (fun r => (enc n Bw b m).getD (i * (Bw + 2) + r) (.num 0)) = m[i]? := by
    intro i hi
    rw [List.mem_range] at hi
    rw [decBlock_congr (n + 4) Bw _ (blockAt (n + 4) m[i]?)]
    · apply decBlock_blockAt
      intro k hk
      exact hm k (List.mem_of_getElem? hk)
    · intro r hr
      have hlt : i * (Bw + 2) + r < encLen Bw b := by
        unfold encLen
        nlinarith
      simp only [enc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        Option.map_some, Option.getD_some, encAt]
      have hd : (i * (Bw + 2) + r) / (Bw + 2) = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]
      have hmod : (i * (Bw + 2) + r) % (Bw + 2) = r := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      rw [hd, hmod]
  rw [List.filterMap_congr h1]
  exact filterMap_getElem?_range m (b + 1) (by omega)

lemma encAt_ok (n Bw : ℕ) (m : Msg V) (j : ℕ) : WordOK n (encAt n Bw m j) := by
  unfold encAt
  generalize m[j / (Bw + 2)]? = o
  generalize j % (Bw + 2) = r
  rcases o with _ | (v | k | e) <;> rcases r with _ | _ | r <;>
    simp only [blockAt, WordOK] <;> try omega
  all_goals exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))

end Enc

section TreeSec

variable {V : Type}

section Tree
variable [Fintype V] [DecidableEq V] (S : Finset V) (par : V → Option V) (rk : V → ℕ)

/-- the children of `u` in the forest -/
def kidsOf (u : V) : Finset V := S.filter (fun c => par c = some u)

/-- a measure decreasing from parents to children -/
def mu (u : V) : ℕ := S.sup rk + 1 - rk u

/-- the height of `u` in the forest -/
noncomputable def hgt (u : V) : ℕ :=
  (kidsOf S par u).sup (fun c => if h : mu S rk c < mu S rk u then hgt c + 1 else 0)
termination_by mu S rk u

/-- the depth of `u` in the forest -/
noncomputable def dep (u : V) : ℕ :=
  match par u with
  | none => 0
  | some p => if h : rk p < rk u then dep p + 1 else 0
termination_by rk u

/-- the aggregate of the subtree of `u`, folding the children in the order of `toList` -/
noncomputable def agg (val : V → Msg V) (op : Msg V → Msg V → Msg V) (u : V) : Msg V :=
  (kidsOf S par u).toList.foldl
    (fun a c => if _h : mu S rk c < mu S rk u then op a (agg val op c) else a) (val u)
termination_by mu S rk u

/-- one step towards the root -/
def PR (x y : V) : Prop := par x = some y

/-- the ancestors of `u` (including `u`) -/
noncomputable def ancS (u : V) : Finset V := by
  classical exact univ.filter (fun a => ReflTransGen (PR par) u a)

/-- the subtree of `u` -/
noncomputable def desc (u : V) : Finset V := by
  classical exact S.filter (fun w => ReflTransGen (PR par) w u)

variable {S par rk}

lemma mem_kidsOf {u c : V} : c ∈ kidsOf S par u ↔ c ∈ S ∧ par c = some u := by
  simp [kidsOf]

lemma mem_desc {u w : V} : w ∈ desc S par u ↔ w ∈ S ∧ ReflTransGen (PR par) w u := by
  classical simp [desc]

lemma mem_ancS {u a : V} : a ∈ ancS par u ↔ ReflTransGen (PR par) u a := by
  classical simp [ancS]

variable (hS : ∀ v ∈ S, ∀ u, par v = some u → u ∈ S)
  (hrk : ∀ v ∈ S, ∀ u, par v = some u → rk u < rk v)
include hrk

lemma mu_lt {u c : V} (hc : c ∈ kidsOf S par u) : mu S rk c < mu S rk u := by
  rw [mem_kidsOf] at hc
  have h1 := hrk c hc.1 u hc.2
  have h2 : rk c ≤ S.sup rk := le_sup hc.1
  unfold mu; omega

lemma kid_induction {P : V → Prop} (h : ∀ u, (∀ c ∈ kidsOf S par u, P c) → P u) (u : V) : P u := by
  induction hn : mu S rk u using Nat.strong_induction_on generalizing u with
  | _ n ih => exact h u (fun c hc => ih _ (hn ▸ mu_lt hrk hc) c rfl)

lemma hgt_eq (u : V) : hgt S par rk u = (kidsOf S par u).sup (fun c => hgt S par rk c + 1) := by
  rw [hgt]
  exact Finset.sup_congr rfl (fun c hc => dite_eq_left (mu_lt hrk hc))

lemma agg_eq (val : V → Msg V) (op : Msg V → Msg V → Msg V) (u : V) :
    agg S par rk val op u =
      (kidsOf S par u).toList.foldl (fun a c => op a (agg S par rk val op c)) (val u) := by
  rw [agg]
  exact List.foldl_ext _ _ _ (fun a c hc => dite_eq_left (mu_lt hrk (Finset.mem_toList.1 hc)))

omit hrk in
lemma dep_none {u : V} (h : par u = none) : dep par rk u = 0 := by
  rw [dep]; split <;> simp_all

lemma dep_some {u p : V} (hu : u ∈ S) (h : par u = some p) : dep par rk u = dep par rk p + 1 := by
  rw [dep]; split
  · simp_all
  · rename_i p' hp'
    rw [h] at hp'; cases hp'
    exact dite_eq_left (hrk u hu p h)

lemma dep_kid {u c : V} (hc : c ∈ kidsOf S par u) : dep par rk c = dep par rk u + 1 := by
  rw [mem_kidsOf] at hc; exact dep_some hrk hc.1 hc.2

/-! ### Ancestors -/

omit hrk in
include hS in
lemma anc_mem {w a : V} (hw : w ∈ S) (h : ReflTransGen (PR par) w a) : a ∈ S := by
  induction h with
  | refl => exact hw
  | tail _ hxy ih => exact hS _ ih _ hxy

include hS in
lemma anc_rk {w a : V} (hw : w ∈ S) (h : ReflTransGen (PR par) w a) : a = w ∨ rk a < rk w := by
  induction h with
  | refl => left; rfl
  | tail hwb hbc ih =>
    right
    have hb := anc_mem hS hw hwb
    have := hrk _ hb _ hbc
    rcases ih with rfl | ih
    · exact this
    · omega

include hS in
lemma card_ancS (u : V) (hu : u ∈ S) : (ancS par u).card = dep par rk u + 1 := by
  induction hn : rk u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    cases hp : par u with
    | none =>
      have : ancS par u = {u} := by
        ext a
        rw [mem_ancS, ReflTransGen.cases_head_iff, mem_singleton]
        constructor
        · rintro (h | ⟨c, hc, _⟩)
          · exact h.symm
          · simp [PR, hp] at hc
        · rintro rfl; left; rfl
      rw [this, dep_none hp]; rfl
    | some p =>
      have hpS := hS u hu p hp
      have hlt := hrk u hu p hp
      have : ancS par u = insert u (ancS par p) := by
        ext a
        rw [mem_ancS, ReflTransGen.cases_head_iff, mem_insert, mem_ancS]
        constructor
        · rintro (h | ⟨c, hc, h⟩)
          · exact Or.inl h.symm
          · simp only [PR, hp, Option.some.injEq] at hc
            subst hc; exact Or.inr h
        · rintro (rfl | h)
          · left; rfl
          · exact Or.inr ⟨p, hp, h⟩
      have hnot : u ∉ ancS par p := by
        rw [mem_ancS]
        intro h
        rcases anc_rk hS hrk hpS h with h' | h'
        · subst h'; omega
        · omega
      rw [this, card_insert_of_notMem hnot, ih (rk p) (hn ▸ hlt) p hpS rfl, dep_some hrk hu hp]

omit hrk in
include hS in
lemma ancS_sub {u : V} (hu : u ∈ S) : ancS par u ⊆ S := fun _ ha =>
  anc_mem hS hu (mem_ancS.1 ha)

include hS in
lemma dep_lt {u : V} (hu : u ∈ S) : dep par rk u < S.card := by
  have h1 := card_ancS hS hrk u hu
  have h2 := card_le_card (ancS_sub hS hu)
  omega

lemma exists_deep (u : V) : u ∈ S → ∃ w ∈ S, dep par rk w = dep par rk u + hgt S par rk u := by
  induction u using kid_induction hrk with
  | _ u ih =>
    intro hu
    rcases (kidsOf S par u).eq_empty_or_nonempty with he | hne
    · refine ⟨u, hu, ?_⟩
      rw [hgt_eq hrk, he, sup_empty]; rfl
    · obtain ⟨c, hc, hcs⟩ := exists_mem_eq_sup _ hne (fun c => hgt S par rk c + 1)
      have hcS := (mem_kidsOf.1 hc).1
      obtain ⟨w, hw, hdw⟩ := ih c hc hcS
      refine ⟨w, hw, ?_⟩
      rw [hgt_eq hrk, hcs, hdw, dep_kid hrk hc]
      ring

include hS in
lemma hgt_lt {u : V} (hu : u ∈ S) : hgt S par rk u < S.card := by
  obtain ⟨w, hw, h⟩ := exists_deep hrk u hu
  have := dep_lt hS hrk hw
  omega

lemma hgt_kid {u c : V} (hc : c ∈ kidsOf S par u) : hgt S par rk c < hgt S par rk u := by
  rw [hgt_eq hrk u]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_sup (f := fun c => hgt S par rk c + 1) hc)

/-! ### Subtrees -/

include hS in
lemma not_mem_desc_kid {u c : V} (hc : c ∈ kidsOf S par u) : u ∉ desc S par c := by
  rw [mem_desc]
  rintro ⟨hu, h⟩
  rw [mem_kidsOf] at hc
  have := hrk c hc.1 u hc.2
  rcases anc_rk hS hrk hu h with h' | h'
  · subst h'; omega
  · omega

include hS in
lemma desc_disj (u : V) : (↑(kidsOf S par u) : Set V).PairwiseDisjoint (desc S par) := by
  intro c hc c' hc' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  rw [mem_desc] at hw hw'
  rw [mem_coe, mem_kidsOf] at hc hc'
  have hU : Relator.RightUnique (PR par) := fun a b b' h1 h2 => by
    simp only [PR] at h1 h2; rw [h1] at h2; exact Option.some.inj h2
  have key : ∀ x y, x ∈ S → y ∈ S → par x = some u → par y = some u → x ≠ y →
      ¬ ReflTransGen (PR par) x y := by
    intro x y hx hy hxu hyu hxy h
    rcases ReflTransGen.cases_head_iff.1 h with h1 | ⟨z, hz, h2⟩
    · exact hxy h1
    · simp only [PR, hxu, Option.some.injEq] at hz
      subst hz
      have := hrk y hy u hyu
      rcases anc_rk hS hrk (hS x hx u hxu) h2 with h3 | h3
      · subst h3; omega
      · omega
  rcases ReflTransGen.total_of_right_unique hU hw.2 hw'.2 with h | h
  · exact key c c' hc.1 hc'.1 hc.2 hc'.2 hne h
  · exact key c' c hc'.1 hc.1 hc'.2 hc.2 (Ne.symm hne) h

include hS in
lemma desc_eq {u : V} (hu : u ∈ S) :
    desc S par u = insert u ((kidsOf S par u).biUnion (desc S par)) := by
  ext w
  rw [mem_insert, mem_biUnion, mem_desc]
  constructor
  · rintro ⟨hw, h⟩
    rcases ReflTransGen.cases_tail_iff _ _ _ |>.1 h with h1 | ⟨c, hc, hcu⟩
    · exact Or.inl h1.symm
    · right
      exact ⟨c, mem_kidsOf.2 ⟨anc_mem hS hw hc, hcu⟩, mem_desc.2 ⟨hw, hc⟩⟩
  · rintro (rfl | ⟨c, hc, hw⟩)
    · exact ⟨hu, ReflTransGen.refl⟩
    · rw [mem_desc] at hw
      exact ⟨hw.1, hw.2.tail (mem_kidsOf.1 hc).2⟩

/-! ### Aggregates of subtrees -/

omit hrk in
lemma map_val_eq_sum {M : Type} (s : Finset V) (f : V → M) :
    s.val.map f = ∑ x ∈ s, ({f x} : Multiset M) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [insert_val_of_notMem ha, Multiset.map_cons, sum_insert ha, ih, Multiset.singleton_add]

omit hrk in
lemma aggOf_foldl {M : Type} (op : M → M → M) (g : V → M) (Mc : V → Multiset M) :
    ∀ (l : List V) (s : Multiset M) (a : M), AggOf op s a → (∀ c ∈ l, AggOf op (Mc c) (g c)) →
      AggOf op (s + (l.map Mc).sum) (l.foldl (fun a c => op a (g c)) a) := by
  intro l
  induction l with
  | nil => intro s a h _; simpa using h
  | cons c l ih =>
    intro s a h hl
    rw [List.map_cons, List.sum_cons, List.foldl_cons, ← add_assoc]
    exact ih _ _ (AggOf.comb h (hl c List.mem_cons_self))
      (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))

omit hrk in
lemma foldl_pres {M : Type} (op : M → M → M) (g : V → M) (P : M → Prop)
    (hop : ∀ m m', P m → P m' → P (op m m')) :
    ∀ (l : List V) (a : M), P a → (∀ c ∈ l, P (g c)) → P (l.foldl (fun a c => op a (g c)) a) := by
  intro l
  induction l with
  | nil => intro a h _; exact h
  | cons c l ih =>
    intro a h hl
    rw [List.foldl_cons]
    exact ih _ (hop _ _ h (hl c List.mem_cons_self)) (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))

include hS in
lemma agg_spec (val : V → Msg V) (op : Msg V → Msg V → Msg V) (u : V) :
    u ∈ S → AggOf op ((desc S par u).val.map val) (agg S par rk val op u) := by
  induction u using kid_induction hrk with
  | _ u ih =>
    intro hu
    have hnot : u ∉ (kidsOf S par u).biUnion (desc S par) := fun h => by
      obtain ⟨c, hc, hu'⟩ := mem_biUnion.1 h
      exact not_mem_desc_kid hS hrk hc hu'
    have hsum : (desc S par u).val.map val = {val u} +
        ((kidsOf S par u).toList.map (fun c => (desc S par c).val.map val)).sum := by
      rw [map_val_eq_sum, desc_eq hS hrk hu, sum_insert hnot, sum_biUnion (desc_disj hS hrk u),
        sum_map_toList]
      congr 1
      exact sum_congr rfl (fun c _ => (map_val_eq_sum _ _).symm)
    rw [hsum, agg_eq hrk]
    exact aggOf_foldl op _ _ _ _ _ (AggOf.single _)
      (fun c hc => ih c (mem_toList.1 hc) (mem_kidsOf.1 (mem_toList.1 hc)).1)

lemma agg_pres (val : V → Msg V) (op : Msg V → Msg V → Msg V) (P : Msg V → Prop)
    (hval : ∀ v ∈ S, P (val v)) (hop : ∀ m m', P m → P m' → P (op m m')) (u : V) :
    u ∈ S → P (agg S par rk val op u) := by
  induction u using kid_induction hrk with
  | _ u ih =>
    intro hu
    rw [agg_eq hrk]
    exact foldl_pres op _ P hop _ _ (hval u hu)
      (fun c hc => ih c (mem_toList.1 hc) (mem_kidsOf.1 (mem_toList.1 hc)).1)

/-! ### Roots -/

include hS in
lemma exists_top (w : V) (hw : w ∈ S) : ∃ t, ReflTransGen (PR par) w t ∧ par t = none := by
  induction hn : rk w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    cases hp : par w with
    | none => exact ⟨w, ReflTransGen.refl, hp⟩
    | some p =>
      obtain ⟨t, ht, htn⟩ := ih (rk p) (hn ▸ hrk w hw p hp) p (hS w hw p hp) rfl
      exact ⟨t, ReflTransGen.head hp ht, htn⟩

variable {root : V → V} (hroot : ∀ v ∈ S, ∀ u, par v = some u → root u = root v)
  (hself : ∀ v ∈ S, par v = none → root v = v)

omit hrk in
include hS hroot in
lemma root_anc {w a : V} (hw : w ∈ S) (h : ReflTransGen (PR par) w a) : root a = root w := by
  induction h with
  | refl => rfl
  | tail hwb hbc ih => rw [hroot _ (anc_mem hS hw hwb) _ hbc, ih]

include hS hroot hself in
lemma root_spec {v : V} (hv : v ∈ S) :
    root v ∈ S ∧ par (root v) = none ∧ ReflTransGen (PR par) v (root v) := by
  obtain ⟨t, ht, htn⟩ := exists_top hS hrk v hv
  have htS := anc_mem hS hv ht
  have h1 : root t = root v := root_anc hS hroot hv ht
  have h2 : root t = t := hself t htS htn
  rw [← h1, h2]
  exact ⟨htS, htn, ht⟩

include hS hroot hself in
lemma desc_root {r : V} (hr : r ∈ S) (hpr : par r = none) :
    desc S par r = S.filter (fun w => root w = r) := by
  ext w
  rw [mem_desc, mem_filter]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, by rw [← root_anc hS hroot hw h, hself r hr hpr]⟩
  · rintro ⟨hw, h⟩
    obtain ⟨_, _, h3⟩ := root_spec hS hrk hroot hself hw
    rw [h] at h3
    exact ⟨hw, h3⟩

end Tree

end TreeSec

section HistSec

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Full-information protocols -/

/-- A history: the messages received in each round so far. -/
abbrev Hist (V : Type) := List (V → Option (Word V))

/-- the messages of round `i` in a history (`none` beyond its end) -/
def hget (h : Hist V) (i : ℕ) : V → Option (Word V) := h.getD i (fun _ => none)

/-- A full-information protocol: a node keeps its context, its input and the history of the
messages it received. What it sends is a function `F` of these, and it halts with outputs `O` once
the history has length `Tf c` (a function of the public context). -/
@[reducible] def histP
    (F : NCtx V → (Agent V → Option Mem) → Hist V → V → Option (Word V)) (Tf : NCtx V → ℕ)
    (O : NCtx V → (Agent V → Option Mem) → Hist V → Agent V → Option Mem) : Proto V where
  S := NCtx V × (Agent V → Option Mem) × Hist V
  Ω := Unit
  init c inp _ := (c, inp, [])
  send c s v := F c s.2.1 s.2.2 v
  recv _ s m := (s.1, s.2.1, s.2.2 ++ [m])
  out s := if Tf s.1 ≤ s.2.2.length then some (O s.1 s.2.1 s.2.2) else none

section HistRun

variable {F : NCtx V → (Agent V → Option Mem) → Hist V → V → Option (Word V)} {Tf : NCtx V → ℕ}
  {O : NCtx V → (Agent V → Option Mem) → Hist V → Agent V → Option Mem}
  {I : Inst V} {x : Agent V → Mem} {ω : V → Unit} {T : ℕ}

/-- the history of `v` after `t` rounds of a run -/
noncomputable def histOf (P : Proto V) (I : Inst V) (x : Agent V → Mem) (ω : V → P.Ω) (v : V)
    (t : ℕ) : Hist V :=
  (List.range t).map (fun i u => msg P I (st P I x ω i) u v)

/-- the history of `v` after `s` rounds of a schedule `M` (`M u v i`: message from `u` to `v` in
round `i`) -/
def schedHist (M : V → V → ℕ → Option (Word V)) (v : V) (s : ℕ) : Hist V :=
  (List.range s).map (fun i w => M w v i)

lemma length_schedHist (M : V → V → ℕ → Option (Word V)) (v : V) (s : ℕ) :
    (schedHist M v s).length = s := by simp [schedHist]

lemma hget_schedHist (M : V → V → ℕ → Option (Word V)) (v : V) {s i : ℕ} (hi : i < s) (w : V) :
    hget (schedHist M v s) i w = M w v i := by
  simp [hget, schedHist, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- Before halting, the state of a node is its context, input and history. -/
lemma st_histP (hT : ∀ v, Tf (I.ctx v) = T) : ∀ t ≤ T, ∀ v,
    st (histP F Tf O) I x ω t v = (I.ctx v, inpAt I x v, histOf (histP F Tf O) I x ω v t) := by
  intro t
  induction t with
  | zero => intro _ v; rfl
  | succ t ih =>
    intro ht v
    rw [st_succ]
    unfold step
    rw [ih (by omega) v]
    have hout : (histP F Tf O).out (I.ctx v, inpAt I x v, histOf (histP F Tf O) I x ω v t) = none := by
      simp only [histP, histOf, List.length_map, List.length_range, hT]
      rw [ite_eq_right (by omega)]
    rw [hout]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, histP, histOf, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]

/-- **Runs of full-information protocols.** If the protocol, fed with the histories of a schedule
`M`, sends exactly the messages of `M` at every participant and to every node (and `M` only uses
edges and valid words), then the run follows `M`. -/
theorem msg_histP (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w) :
    ∀ s < T, ∀ u v, msg (histP F Tf O) I (st (histP F Tf O) I x ω s) u v = M u v s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs u v
    have hh : histOf (histP F Tf O) I x ω u s = schedHist M u s := by
      unfold histOf schedHist
      apply List.map_congr_left
      intro i hi
      funext w
      exact ih i (List.mem_range.1 hi) (by have := List.mem_range.1 hi; omega) w u
    have hst := st_histP (F := F) (O := O) (x := x) (ω := ω) hT s hs.le u
    obtain ⟨h1, h2, h3⟩ := hM s hs u v
    unfold msg
    by_cases hadj : I.G.Adj u v
    · have hout : (histP F Tf O).out (st (histP F Tf O) I x ω s u) = none := by
        rw [hst]
        simp only [histP, histOf, List.length_map, List.length_range, hT]
        rw [ite_eq_right (by omega)]
      rw [ite_eq_left ⟨hadj, hout⟩, hst]
      simp only [histP]
      rw [hh, h1 (I.adj_part u v hadj)]
      cases hm : M u v s with
      | none => rfl
      | some w => simp [h3 w hm]
    · rw [ite_eq_right (fun h => hadj h.1), h2 hadj]

lemma histOf_histP_sched (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w)
    {s : ℕ} (hs : s ≤ T) (v : V) :
    histOf (histP F Tf O) I x ω v s = schedHist M v s := by
  unfold histOf schedHist
  apply List.map_congr_left
  intro i hi
  funext w
  exact msg_histP hT M hM i (lt_of_lt_of_le (List.mem_range.1 hi) hs) w v

/-- **Proper sends**: a full-information protocol following a schedule that only uses edges sends
only along edges. -/
lemma properUpTo_histP (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w) :
    ProperUpTo (histP F Tf O) I x ω T := by
  intro s hs u hu _ v hv
  rw [st_histP hT s hs.le u] at hv
  have hv' : (F (I.ctx u) (inpAt I x u) (schedHist M u s) v).isSome := by
    rw [← histOf_histP_sched hT M hM hs.le u]; exact hv
  rw [(hM s hs u v).1 hu] at hv'
  by_contra hadj
  rw [(hM s hs u v).2.1 hadj] at hv'
  exact absurd hv' (by simp)

lemma st_histP_sched (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w)
    (v : V) : st (histP F Tf O) I x ω T v = (I.ctx v, inpAt I x v, schedHist M v T) := by
  rw [st_histP hT T le_rfl v]
  congr 2
  unfold histOf schedHist
  apply List.map_congr_left
  intro i hi
  funext w
  exact msg_histP hT M hM i (List.mem_range.1 hi) w v

lemma sentSet_histP (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w)
    {s : ℕ} (hs : s < T) :
    sentSet (histP F Tf O) I (st (histP F Tf O) I x ω s) =
      univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome) := by
  unfold sentSet
  ext uv
  simp only [mem_filter, mem_univ, true_and]
  rw [msg_histP hT M hM s hs]

/-- **Success of full-information protocols** following a schedule `M`: every participant `u`,
fed with the history of `M`, sends `M u v s` to every node `v`, and `M` is `none` off the graph
(so the sends are proper) and uses valid words. -/
theorem succ_histP (hT : ∀ v, Tf (I.ctx v) = T) (M : V → V → ℕ → Option (Word V))
    (hM : ∀ s < T, ∀ u v, (I.part u → F (I.ctx u) (inpAt I x u) (schedHist M u s) v = M u v s) ∧
      (¬ I.G.Adj u v → M u v s = none) ∧ ∀ w, M u v s = some w → WordOK (Fintype.card V) w)
    {Q : (Agent V → Mem) → Prop} {p : Prof V} (hr : T ≤ p.rounds)
    (hm : ∑ s ∈ range T, (univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).card ≤ p.msgs)
    (hl : ∀ e, ∑ s ∈ range T, ((univ.filter (fun uv : V × V => (M uv.1 uv.2 s).isSome)).filter
      (fun uv => s(uv.1, uv.2) = e)).card ≤ p.load e)
    (y : Agent V → Mem)
    (hy : ∀ g v, I.host g = some v → O (I.ctx v) (inpAt I x v) (schedHist M v T) g = some (y g))
    (hQ : Q y) : Succ (histP F Tf O) I x Q p ω := by
  classical
  refine ⟨T, ⟨fun v _ => ?_, fun s hs v _ => ?_⟩, properUpTo_histP hT M hM, hr, ?_, fun e => ?_,
    y, fun g hg => ?_, hQ⟩
  · rw [st_histP_sched hT M hM v]
    simp [length_schedHist, hT]
  · rw [st_histP hT s hs.le v]
    simp only [histP, histOf, List.length_map, List.length_range, hT]
    rw [ite_eq_right (by omega)]
  · unfold msgsUpTo
    refine le_trans (le_of_eq ?_) hm
    exact sum_congr rfl (fun s hs => by rw [sentSet_histP hT M hM (mem_range.1 hs)])
  · unfold loadUpTo
    refine le_trans (le_of_eq ?_) (hl e)
    refine sum_congr rfl (fun s hs => ?_)
    rw [sentSet_histP hT M hM (mem_range.1 hs)]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hg
    unfold outAt
    rw [hv]
    dsimp only
    rw [st_histP_sched hT M hM v]
    simp only [length_schedHist, hT, le_refl, ite_true, Option.bind_some]
    exact hy g v hv

end HistRun

end HistSec

/-! ## Streams in schedules -/

/-- The words of a value sent in slot `h` (slots of length `L`), collected over the first `k`
slots: all of them if `h < k`, none otherwise. -/
lemma filterMap_slot {α : Type} (L h : ℕ) (hL : 0 < L) (f : ℕ → α) (k : ℕ) :
    (List.range (k * L)).filterMap (fun j => if j / L = h then some (f (j % L)) else none) =
      if h < k then (List.range L).map f else [] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, List.range_add, List.filterMap_append, ih, List.filterMap_map]
    have h2 : (List.range L).filterMap
        ((fun j => if j / L = h then some (f (j % L)) else none) ∘ (fun x => k * L + x)) =
        if h = k then (List.range L).map f else [] := by
      have hd : ∀ i ∈ List.range L, (k * L + i) / L = k ∧ (k * L + i) % L = i := by
        intro i hi
        rw [List.mem_range] at hi
        rw [mul_comm, Nat.mul_add_div hL, Nat.mul_add_mod, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
        simp
      split_ifs with hk
      · rw [← List.filterMap_eq_map]
        apply List.filterMap_congr
        intro i hi
        simp only [Function.comp_apply, (hd i hi).1, (hd i hi).2, hk, ite_true]
      · apply List.filterMap_eq_nil_iff.2
        intro i hi
        simp only [Function.comp_apply, (hd i hi).1]
        rw [ite_eq_right (fun h' => hk h'.symm)]
    rw [h2]
    by_cases h1 : h < k
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega), List.append_nil]
    · by_cases h3 : h = k
      · rw [ite_eq_right h1, ite_eq_left h3, ite_eq_left (by omega), List.nil_append]
      · rw [ite_eq_right h1, ite_eq_right h3, ite_eq_right (by omega), List.nil_append]

/-- The words of a value sent in rounds `a, …, a + L - 1`, collected over the first `N ≥ a + L`
rounds. -/
lemma filterMap_window {α : Type} (a L N : ℕ) (f : ℕ → α) (h : a + L ≤ N) :
    (List.range N).filterMap (fun j => if a ≤ j ∧ j < a + L then some (f (j - a)) else none) =
      (List.range L).map f := by
  obtain ⟨r, rfl⟩ : ∃ r, N = a + L + r := ⟨N - a - L, by omega⟩
  rw [List.range_add, List.range_add, List.filterMap_append, List.filterMap_append,
    List.filterMap_map, List.filterMap_map]
  have h1 : (List.range a).filterMap
      (fun j => if a ≤ j ∧ j < a + L then some (f (j - a)) else none) = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro j hj
    rw [List.mem_range] at hj
    rw [ite_eq_right (by omega)]
  have h2 : (List.range L).filterMap
      ((fun j => if a ≤ j ∧ j < a + L then some (f (j - a)) else none) ∘ (fun x => a + x)) =
      (List.range L).map f := by
    rw [← List.filterMap_eq_map]
    apply List.filterMap_congr
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ite_eq_left (by omega), Nat.add_sub_cancel_left]
  have h3 : (List.range r).filterMap
      ((fun j => if a ≤ j ∧ j < a + L then some (f (j - a)) else none) ∘ (fun x => a + L + x)) =
      [] := by
    apply List.filterMap_eq_nil_iff.2
    intro j _
    simp only [Function.comp_apply]
    rw [ite_eq_right (by omega)]
  rw [h1, h2, h3, List.nil_append, List.append_nil]

/-! ## Counting messages -/

lemma sum_card_filter_swap {α : Type} [Fintype α] (T : ℕ) (P : ℕ → α → Prop)
    [∀ s a, Decidable (P s a)] :
    ∑ s ∈ range T, (univ.filter (P s)).card = ∑ a, ((range T).filter (fun s => P s a)).card := by
  simp only [card_filter]
  exact sum_comm

lemma sum_le_mul_card {α : Type} [Fintype α] (g : α → ℕ) (Q : α → Prop) [DecidablePred Q]
    (c : ℕ) (h : ∀ a, g a ≤ if Q a then c else 0) : ∑ a, g a ≤ c * (univ.filter Q).card := by
  calc ∑ a, g a ≤ ∑ a, (if Q a then c else 0) := sum_le_sum (fun a _ => h a)
    _ = c * (univ.filter Q).card := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_comm]

section Counting
variable {V : Type} [Fintype V] [DecidableEq V]

lemma card_sym2_fiber (e : Sym2 V) :
    (univ.filter (fun uv : V × V => s(uv.1, uv.2) = e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    calc _ ≤ ({(a, b), (b, a)} : Finset (V × V)).card := card_le_card (fun uv huv => by
            simp only [mem_filter, mem_univ, true_and, Sym2.eq_iff] at huv
            rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [Prod.ext_iff, h1, h2])
      _ ≤ 2 := (card_insert_le _ _).trans (by simp)

lemma card_treePairs (S : Finset V) (par : V → Option V) :
    (univ.filter (fun uv : V × V => (uv.1 ∈ S ∧ par uv.1 = some uv.2) ∨
      (uv.2 ∈ S ∧ par uv.2 = some uv.1))).card ≤ 2 * S.card := by
  rw [filter_or]
  refine (card_union_le _ _).trans ?_
  have h1 : (univ.filter (fun uv : V × V => uv.1 ∈ S ∧ par uv.1 = some uv.2)).card ≤ S.card := by
    refine card_le_card_of_injOn Prod.fst (fun uv huv => ?_) (fun uv huv uv' huv' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv
      exact huv.1
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv huv'
      have h2 := huv.2
      rw [h, huv'.2] at h2
      exact Prod.ext h (Option.some.inj h2).symm
  have h2 : (univ.filter (fun uv : V × V => uv.2 ∈ S ∧ par uv.2 = some uv.1)).card ≤ S.card := by
    refine card_le_card_of_injOn Prod.snd (fun uv huv => ?_) (fun uv huv uv' huv' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv
      exact huv.1
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at huv huv'
      have h2 := huv.2
      rw [h, huv'.2] at h2
      exact Prod.ext (Option.some.inj h2).symm h
  omega

end Counting

end APSP.Stoc.Congest
