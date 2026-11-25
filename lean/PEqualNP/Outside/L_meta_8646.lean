import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8646
namespace PQ1425Lower
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]
theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false
theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj
theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card
theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega
theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)
def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]
theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false
theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩
theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]
theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)
theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]
theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false
theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp
theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]
def shift (K a : ℕ) : ℕ := if a < K then a else a - 1
def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩
def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false
theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs
open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))
theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]
theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range
abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x
theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩
open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)
theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)
def diff (k w : Nat) : Nat := w ^^^ (w >>> k)
def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t
theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k
theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]
def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p
def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat
def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat
def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))
theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]
theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])
theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _
theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp
theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i
def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)
theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]
theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]
theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl
theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl
theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])
def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)
def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t
theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]
theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]
def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k
theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]
theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih
def search (k : Nat) : Nat → List Nat → Bool
  | 0, ws => ws == [goal k]
  | s+1, ws => covers k (s+1) ws &&
      next (mask k) (s+2-ws.length) ws (fun _ zs => search k s zs)
theorem search_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : search k s ws = true := by
  induction s generalizing ws with
  | zero => simp [search,zero_done h rfl]
  | succ s ih =>
    rw [search, covers_ok h, Bool.true_and]
    exact next_complete h s rfl _ (List.Perm.refl _) _ (fun _ _ hh => ih hh)
def fn (T : Nat) : BFn 5 := fun x =>
  T.testBit (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def bound (T n : Nat) :=
  ∀ (gs : List Gate) (o : Nat), (∀ g ∈ gs, Ok g) →
    (∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) →
    (∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = fn T x) →
    (∃ g ∈ gs, g.op = GateOp.not) → n ≤ gs.length
theorem mkBound (T cap k : Nat) (rows : List Nat) (xs : List Nat)
    (hnc : fn T (fun _ => false) ≠ fn T (fun _ => true))
    (hm : mask k = 2^rows.length-1)
    (hi : (List.ofFn fun i : Fin 5 => fun x : Fin 5 → Bool => x i).map (fun a => encL a rows) = xs)
    (hy : encL (fn T) rows = goal k)
    (hp : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hn : ∀ s ≤ cap, ¬ NatRun (mask k) (goal k) s xs) : bound T (cap+1) := by
  intro gs o hok _ hev _
  by_contra! hn'
  have hc : HasCircuitSize 5 (fn T) cap :=
    ⟨⟨gs,o⟩, hok, (show gs.length ≤ cap by omega), hev⟩
  obtain ⟨s,hs,ws,hsub,h⟩ := exists_run (fn T) ⟨_,_,hnc⟩ cap hc
  have hr : NatRun (mask k) (encL (fn T) rows) s (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn 5 => encL a rows) (fun a => by rw [hm]; exact encL_inv a rows) (fun a b => encL_and a b rows)
      (fun a b => encL_or a b rows) h
  rw [hy] at hr
  have hsub' := hsub.map (fun a => encL a rows)
  rw [hi] at hsub'
  by_cases e : ws.map (fun a => encL a rows) = xs
  · rw [e] at hr; exact hn s hs hr
  · exact hp _ (List.mem_sublists.2 hsub') e (required hr)
def spr : List (Nat × Nat) → Nat → Nat
  | [],_ => 0
  | (i,m)::qs,v => (if v.testBit i then m else 0) ||| spr qs v
def used : List (Nat × Nat) → Nat
  | [] => 0
  | (_,m)::qs => m ||| used qs
def cleanMasks : List (Nat × Nat) → Bool
  | [] => true
  | (_,m)::qs => (m &&& used qs == 0) && cleanMasks qs
theorem spr_sub (p : List (Nat × Nat)) (v j : Nat) :
    (spr p v).testBit j = true → (used p).testBit j = true := by
  induction p with
  | nil => simp [spr]
  | cons a qs ih =>
    rcases a with ⟨i,m⟩
    simp only [spr,used,Nat.testBit_or,Bool.or_eq_true]
    split <;> grind [Nat.zero_testBit]
theorem spr_hom (p : List (Nat × Nat)) (h : cleanMasks p = true) (a b : Nat) :
    spr p (a &&& b) = spr p a &&& spr p b ∧
    spr p (a ||| b) = spr p a ||| spr p b ∧
    spr p (a ^^^ b) = spr p a ^^^ spr p b := by
  induction p with
  | nil => simp [spr]
  | cons v qs ih =>
    rcases v with ⟨i,m⟩
    simp only [cleanMasks,Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨ha,ho,hx⟩ := ih h.2
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      have hm := congrArg (fun x : Nat => x.testBit j) h.1 <;>
      simp only [Nat.testBit_and,Nat.zero_testBit] at hm <;>
      have hs := spr_sub qs a j <;> have ht := spr_sub qs b j <;>
      simp only [spr,ha,ho,hx,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> simp_all <;> grind
def sprOK (p : List (Nat × Nat)) (m y : Nat) : Bool :=
  cleanMasks p && (spr p m == m) && (spr p y == y)
theorem sprRun {m y s ws p} (h : NatRun m y s ws) (hp : sprOK p m y = true) :
    NatRun m y s (ws.map (spr p)) := by
  simp only [sprOK,Bool.and_eq_true,beq_iff_eq] at hp
  rw [←hp.2]
  exact Run.map _ (fun a => (spr_hom p hp.1.1 a m).2.2.trans (by rw [hp.1.2]))
    (fun a b => (spr_hom p hp.1.1 a b).1) (fun a b => (spr_hom p hp.1.1 a b).2.1) h
def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)
def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩
def barrier (k gf : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          !(v/gf < N s && (rot (v % gf) zs).isPerm (S s (v/gf)))))
theorem barrier_sound {k gf S N act rot} {s i} (hb : barrier k gf S N act rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      !(v/gf < N s && (rot (v % gf) zs).isPerm (S s (v/gf))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction
theorem barrier_all {k gf S N act rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k gf S N act rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h
def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel
theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'
def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)
theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]
def scorebarrier (k gf : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/(2*gf) < N s && (rot (v/2 % gf) zs).isPerm (S s (v/(2*gf))))))
theorem scorebarrier_sound {k gf S N act wits rot} {s i} (hb : scorebarrier k gf S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [scorebarrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/(2*gf) < N s && (rot (v/2 % gf) zs).isPerm (S s (v/(2*gf)))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction
theorem scorebarrier_all {k gf S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, scorebarrier k gf S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := scorebarrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h
namespace ce8a8a8a8
def rs : List Nat := [14, 14, 14, 22, 22, 22, 25, 25, 25, 26, 26, 26, 28, 28, 28, 1, 1, 2, 4, 6, 9, 9, 10, 12, 14, 17, 17, 18, 20, 22, 25, 25, 26, 28, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 3, 5, 7, 11, 13, 11, 13, 15, 19, 21, 19, 21, 23, 27, 29, 27, 29]
def xs : List Nat := [0xffffedb6cc63181c0,0x5ad6b6db5294a0e3f,0xad6b5b6da318c703f,0xf07c12493c1f07fc7,0xff8012493fe007ff8]
theorem no : search 34 5 xs = false := by decide +kernel
end ce8a8a8a8
open ce8a8a8a8 in
theorem lower_e8a8a8a8 : bound 0xe8a8a8a8 6 := by
  apply mkBound 0xe8a8a8a8 5 34 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 34) (goal 34) 5 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction
namespace ce8a8e888
def rs : List Nat := [5, 5, 5, 5, 22, 22, 22, 22, 25, 25, 25, 25, 26, 26, 26, 26, 28, 28, 28, 28, 1, 2, 5, 6, 6, 9, 9, 10, 10, 12, 12, 17, 17, 18, 20, 22, 22, 25, 25, 26, 26, 28, 28, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 3, 7, 7, 14, 11, 13, 11, 14, 13, 14, 19, 21, 19, 21, 23, 30, 27, 29, 27, 30, 29, 30]
def xs : List Nat := [0x177d77ddddd86186500f0f,0x2dd6dfaaaaa99a19a0f0f0,0x3aebae7777761c61cf00ff,0x3f83f8333337e07e0fff00,0x3ffc00444447ff800ffff0]
theorem no : search 43 6 xs = false := by decide +kernel
end ce8a8e888
open ce8a8e888 in
theorem lower_e8a8e888 : bound 0xe8a8e888 7 := by
  apply mkBound 0xe8a8e888 6 43 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 43) (goal 43) 6 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction
namespace ce8e8e880
def wdA (i : Nat) := (if i<2 then (if i<1 then 0x492492244891224cf3cff80fe03f8014514993264c99300000000000007f1451491224489123cf3c07ffe0007f03f038f1e3c78f103f0000001fffff000fc78f1e3c78f000fc00001fffff000fc70e1c3870e000fc00000000000000008102040810000000001fffff000000000000000000000000000000 else 0xb6db6d5ab56ad5a30c3007f0000000a28a24c993264c90000000001fc0005d75dbb76eddbb70c30c000fe03fff5d75dbb76eddbb70c30c000fe0007f5d75dbb76eddbb7000000000003fff5d75db366cd9b360c30c000fe000005c05c3060c183060c00c000fe00000492492a54a952a5000000000003f80) else (if i<3 then 0xfc0fc78f1e3c78ffc0fffffffffffffc0fc70e1c3870efc0ffffffe00000fc0fc70e1c3870e3c03c07ffe00000fc0000000000000fc003ffffe00000ebaeb6eddbb76edc30c3f8001fff80ebaeb6eddbb76ed0000000001fff80b6db6ddbb76eddb30c3007f01fc07fb6db6ddbb76eddb30c3007f000007f else 0xffffffffffffffffffffffffe03ffffffffffffffffff3cf3c07ffffffffffffff7efdfbf7efffffffffe00000ffffff7efdfbf7efcfffffffe00000ffffff7efdfbf7e3cf3c07ffe00000fff5fb76eddbb76fff0fffffe00000fff03870e1c3870fff03ffffe00000fd7fdfbf7efdfbffc3ffffffe03fff))
def wd (i : Nat) := (wdA (i/8) >>> (120*(i % 8))) &&& 0xffffffffffffffffffffffffffffff
def stA (i : Nat) := (if i<1 then 0x66cd3941d9c5a305a7168c168b4a304e2d20c199c5a204e2d1881d9c5a105a71684009c5a1003b38b400e4e2d003738b400ece2c003f38a8138bdaa003b38ac00f7666003369181d9c5460767141819b3906003b169400eb4e500271684008b4a1000138280006e660001d918009bd46003ae4180000000000000000000000 else (if i<2 then 0x66d38b738b4e2dcdad38b736a4e2df66d38b7369c5adcda716a7369c5a6066d1697369c5a5cda7168c169c5a307fb38b41dece2d003b38b41dc4e2d076d38b41ab4e2d066d38b417b4e2d076938b41eece2d066b38b41d9c5ad076716a81d9c5a9066d38ac1ecda660767169b369c506003b16941db45a5066d16941d9c5a5 else 0x66d38b400ece2d076d38b7b9b4e2d))
def st (i : Nat) := (stA (i/34) >>> (30*(i % 34))) &&& 0x3fffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 8 else 24) else (if i<7 then 56 else 71)))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 5)) else (if i<6 then (if i<5 then 16 else 32) else (if i<7 then 15 else 1)))
def state (s i : Nat) := unpackWords wd 5 8 (st (off s+i))
def oaA (i : Nat) := 0xe3d5cbc0b5adaaa49f9c97948d8b8985817e7a73716d6c696864605d5c57534f4a45403e3d3c3a393635343332312e2d2b2a29262421201c1916130f0c0b0a09080706050403020100
def oa (i : Nat) := (oaA (i/128) >>> (8*(i % 128))) &&& 0xff
def ovA (i : Nat) := 0x3bfe5378d1317bb2d1aeea3a02699322e87a097cde672dba6718a5e96d5916354d3a4c51e410f2394d62f0b72b8aa2989625487218852107b1e86c1ac621846016452114400e02b0901f0641404c120441003c0e0340800c0200400
def ov (i : Nat) := (ovA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def aValA (i : Nat) := (if i<1 then 0x10e0051000410003130190c20010c00836c008811b04e0000c00001850002090800000022950033060040000023800010000000810093c000100004004c0000802002c10020400811930010800000001c00000070030010000000030010070000030800c0003040002040003042000000000000000000000000000000000000 else 0xc6e049f3d91426c03973c20cc14e5c04900dc990846b824ab5c03cd4c35c51c050004f9940c08c710a080)
def aVal (i : Nat) := (aValA (i/170) >>> (6*(i % 170))) &&& 0x3f
def vValA (i : Nat) := (if i<5 then (if i<2 then (if i<1 then 0x40207802000401180010040105c030040322003000030e403210800fc000003b0ec3b0ec410ec3b0ec00080010fc450c4071400000c0300c031804011c000000300c0300c4900c0300c000003d10c400f43d080030ec03000000000000c0001c0701c000f40000400004000ec490f4000003b12c490000001c070f40000000 else 0xb5e00b5e0004003200000c2d0d42d3002d2800101c800000328001000601006012060780600000b0006000001000600040100401004000040700403000030000100001100000000000c0001c000040101c010040100c010002000401000000040178000004010000000003000070000100407004010040302c010002001020) else (if i<3 then 0x40000001005e000001005e0000010002f00000000010b40178001780c40000700000300070040358001004000000000003511400042b004010000b02c010000b02c0b02c0b02407001e0000010140348000074073c0000c40000c0300c0300ce00dc0300000074034000000c000000300c03000002a0000d42d01d0000c17 else (if i<4 then 0x4000000100001004010bc01004010b40102c0b024070140302c010000b001e00040b02c0b02c0b005e002c010140002c0b0000902c0002c01780010000100001004000000901c0500c01005e000401004010040100017004010bc0100c0100401401a00052c001e0001e00000000c0100401004010000b005c20040000400 else 0x40100401004000000701c00004e0380e0380e018300004a0300c434320005e06302f0b40000401005e00002b00000000010000058001004000040100188005e0780010040701c0300c01004000040100401000000000000c0000c000bde000c0101c0001c000cc0001c70004640b401780010046000420005e00042b005e0))) else (if i<7 then (if i<6 then 0x240100401003200040100000c800102c00002400040101c0900401d00010340d00011064150001104c0580003701c80032000c0d05c07c800d0000d004010000d035e000400601a0001823016030960481604a160c816002d400000300403000010000100001004010040101c0100401004010040300c80000010040040001 else 0x400c8009d8003004010040000001004050040700003004000000000401c8000004000140000001c8000b800100401026c000401002a00040f0000000401a8b2000403000010040bc8001004008b20000c00004010041700000004000000fa00010040b0040d0000100720c8000000010000100401004000040102c0301405) else (if i<8 then 0x2c01d88010040102c070940b0042100c050000100001004000040100001000000000038964381605c0010a41500400024050076209c0fe800d004030040700c010040700c01d80030040700720c8320c800100401007200000f0340002c0100720004000000100400e00000040100400004010000000401c8007000010000b else (if i<9 then 0x488509a000fb000e83e8b11f0e81b050280102889b144f8260792d0b01e0691a0e828cf0150e801b0000bd801d0740b64388f000002c2102f8007c2002f600000b085809024c0776002c00064004080b02f60087600778c02e4802c0b02d84000210076002f60000000032000403d800100c1db800000407c800900423f0001 else 0xae000a20014870084539802b0403314020000581a011022301a2528002a0603c0025807040120508aa2814c39090190e0080c8))))
def vVal (i : Nat) := (vValA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<6 then (if i<3 then (if i<1 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(43,0xc0000000000),(45,0x300000000000),(47,0xc00000000000),(49,0x3000000000000),(51,0xc000000000000),(53,0x30000000000000),(55,0xc000000fe00000),(57,0x3000007f0000000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x141020408102000000000000000),(106,0x482040810204000000000000000),(107,0xa04081020408000000000000000),(110,0x5008102040810000000000000000),(112,0x12010204081020000000000000000),(113,0x28020408102040000000000000000),(116,0x140000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else (if i<2 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(43,0x3000000000000),(45,0xc000000000000),(47,0x30000000000000),(49,0xc0000000000),(51,0x300000000000),(53,0xc00000000000),(55,0xc000000fe00000),(57,0x3000007f0000000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x5008102040810000000000000000),(106,0x12010204081020000000000000000),(107,0x28020408102040000000000000000),(110,0x141020408102000000000000000),(112,0x482040810204000000000000000),(113,0xa04081020408000000000000000),(116,0x140000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x3f80),(13,0x7f),(20,0x1fc000),(43,0xc0000000000),(45,0xc00000000000),(47,0x300000000000),(49,0x3000000000000),(51,0x30000000000000),(53,0xc000000000000),(55,0xc000000fe00000),(57,0xc0003f800000000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x482040810204000000000000000),(106,0x141020408102000000000000000),(107,0xa04081020408000000000000000),(110,0x12010204081020000000000000000),(112,0x5008102040810000000000000000),(113,0x28020408102040000000000000000),(116,0x480000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)))) else (if i<4 then ([(6,0x3f80),(13,0x7f),(20,0x1fc000),(43,0x3000000000000),(45,0x30000000000000),(47,0xc000000000000),(49,0xc0000000000),(51,0xc00000000000),(53,0x300000000000),(55,0xc000000fe00000),(57,0xc0003f800000000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x12010204081020000000000000000),(106,0x5008102040810000000000000000),(107,0x28020408102040000000000000000),(110,0x482040810204000000000000000),(112,0x141020408102000000000000000),(113,0xa04081020408000000000000000),(116,0x480000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else (if i<5 then ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(43,0x300000000000),(45,0xc0000000000),(47,0xc00000000000),(49,0xc000000000000),(51,0x3000000000000),(53,0x30000000000000),(55,0x3000007f0000000),(57,0xc000000fe00000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x141020408102000000000000000),(106,0xa04081020408000000000000000),(107,0x482040810204000000000000000),(110,0x5008102040810000000000000000),(112,0x28020408102040000000000000000),(113,0x12010204081020000000000000000),(116,0x140000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(43,0xc000000000000),(45,0x3000000000000),(47,0x30000000000000),(49,0x300000000000),(51,0xc0000000000),(53,0xc00000000000),(55,0x3000007f0000000),(57,0xc000000fe00000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x5008102040810000000000000000),(106,0x28020408102040000000000000000),(107,0x12010204081020000000000000000),(110,0x141020408102000000000000000),(112,0xa04081020408000000000000000),(113,0x482040810204000000000000000),(116,0x140000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat))))) else (if i<9 then (if i<7 then ([(6,0x1fc000),(13,0x7f),(20,0x3f80),(43,0x300000000000),(45,0xc00000000000),(47,0xc0000000000),(49,0xc000000000000),(51,0x30000000000000),(53,0x3000000000000),(55,0x3000007f0000000),(57,0xc0003f800000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0xa04081020408000000000000000),(106,0x141020408102000000000000000),(107,0x482040810204000000000000000),(110,0x28020408102040000000000000000),(112,0x5008102040810000000000000000),(113,0x12010204081020000000000000000),(116,0xa00000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else (if i<8 then ([(6,0x1fc000),(13,0x7f),(20,0x3f80),(43,0xc000000000000),(45,0x30000000000000),(47,0x3000000000000),(49,0x300000000000),(51,0xc00000000000),(53,0xc0000000000),(55,0x3000007f0000000),(57,0xc0003f800000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0x28020408102040000000000000000),(106,0x5008102040810000000000000000),(107,0x12010204081020000000000000000),(110,0xa04081020408000000000000000),(112,0x141020408102000000000000000),(113,0x482040810204000000000000000),(116,0xa00000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x3f80),(13,0x1fc000),(20,0x7f),(43,0xc00000000000),(45,0xc0000000000),(47,0x300000000000),(49,0x30000000000000),(51,0x3000000000000),(53,0xc000000000000),(55,0xc0003f800000000),(57,0xc000000fe00000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x482040810204000000000000000),(106,0xa04081020408000000000000000),(107,0x141020408102000000000000000),(110,0x12010204081020000000000000000),(112,0x28020408102040000000000000000),(113,0x5008102040810000000000000000),(116,0x480000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)))) else (if i<10 then ([(6,0x3f80),(13,0x1fc000),(20,0x7f),(43,0x30000000000000),(45,0x3000000000000),(47,0xc000000000000),(49,0xc00000000000),(51,0xc0000000000),(53,0x300000000000),(55,0xc0003f800000000),(57,0xc000000fe00000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x12010204081020000000000000000),(106,0x28020408102040000000000000000),(107,0x5008102040810000000000000000),(110,0x482040810204000000000000000),(112,0xa04081020408000000000000000),(113,0x141020408102000000000000000),(116,0x480000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)) else (if i<11 then ([(6,0x1fc000),(13,0x3f80),(20,0x7f),(43,0xc00000000000),(45,0x300000000000),(47,0xc0000000000),(49,0x30000000000000),(51,0xc000000000000),(53,0x3000000000000),(55,0xc0003f800000000),(57,0x3000007f0000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0xa04081020408000000000000000),(106,0x482040810204000000000000000),(107,0x141020408102000000000000000),(110,0x28020408102040000000000000000),(112,0x12010204081020000000000000000),(113,0x5008102040810000000000000000),(116,0xa00000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x1fc000),(13,0x3f80),(20,0x7f),(43,0x30000000000000),(45,0xc000000000000),(47,0x3000000000000),(49,0xc00000000000),(51,0x300000000000),(53,0xc0000000000),(55,0xc0003f800000000),(57,0x3000007f0000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0x28020408102040000000000000000),(106,0x12010204081020000000000000000),(107,0x5008102040810000000000000000),(110,0xa04081020408000000000000000),(112,0x482040810204000000000000000),(113,0x141020408102000000000000000),(116,0xa00000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat))))))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 12)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 60) (goal 60) s ws) :
    NatRun (mask 60) (goal 60) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 12, sprOK (opTab j) (mask 60) (goal 60) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<1 then 0x180d0dc701a05f34140ec711c05f18330507117c6e18140e4711b85f18310347017c6e34310186e17c70180d0dc771d05f180d0dc761a05fdc390ec771d868ac2d0ec771d868182b0346a17c68342b0186817c6a180d0dc701b85f180d0dc701d05f34140ec771d85f180d0dc761b85f18140e4771d05f180d0dc761d05f else (if i<2 then 0x183b0507717c74e40d0dc761d07718140ec711b85fdc140ec771d874dc140e4771d07618140ec771d05fe43b0dc761d077dc3b0e4771d05f182f0506b17c68dc390ec771d87418390507717c7418140e4771d85f18370347617c7434370187417c76e43b0dc761d05f180d0dc6a1d05f182d0506b17c68180d0dc6a1b85f else 0xdc3b0e4771d076183b0e4771d05f))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 60 16 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 5 0 = true := by decide +kernel
theorem z3 : span (Z 3) 5 0 = true := h3_0
theorem h4_0 : span (Z 4) 12 0 = true := by decide +kernel
theorem h4_12 : span (Z 4) 4 12 = true := by decide +kernel
theorem z4 : span (Z 4) 16 0 = true := (@span_join (Z 4) 12 0 4 h4_0 h4_12)
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 8 24 = true := by decide +kernel
theorem z5 : span (Z 5) 32 0 = true := (@span_join (Z 5) 24 0 8 (@span_join (Z 5) 12 0 12 h5_0 h5_12) h5_24)
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 3 12 = true := by decide +kernel
theorem z6 : span (Z 6) 15 0 = true := (@span_join (Z 6) 12 0 3 h6_0 h6_12)
theorem h7_0 : span (Z 7) 1 0 = true := by decide +kernel
theorem z7 : span (Z 7) 1 0 = true := h7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
def rs : List Nat := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 9, 9, 10, 10, 12, 12, 17, 17, 18, 18, 20, 20, 25, 25, 26, 26, 28, 28, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 11, 13, 11, 14, 13, 14, 19, 21, 19, 22, 21, 22, 27, 29, 27, 30, 29, 30]
def xs : List Nat := [0x5d75dbb76eddbb70c30c000fe03fff,0xb6db6ddbb76eddb30c3007f01fc07f,0xebaeb6eddbb76edc30c3f8001fff80,0xfc0fc70e1c3870efc0ffffffe00000,0xfff03870e1c3870fff03ffffe00000]
end ce8e8e880
open ce8e8e880 in
theorem lower_e8e8e880 : bound 0xe8e8e880 8 := by
  apply mkBound 0xe8e8e880 7 60 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have hh : NatRun (mask 60) (goal 60) 7 xs := extend_run h hs
  have hp : xs.Perm (state 7 0) := by decide +kernel
  exact scorebarrier_all rokok checked 7 (by decide) 0 (by decide) (Run.perm hp hh)
namespace ceaa8a888
def wdA (i : Nat) := (if i<6 then (if i<3 then (if i<1 then 0x8021084210807f800007fff008021084210802a8000003ff001e10842108400780000001f0001084210843f757fff07c0000010842108426647c1f07c00000108421084155503ff07c000000000000002a207c00000000000000000000075000007c0000000000000000000000000000000000000000000000000000 else (if i<2 then 0x1fe318c6318ea7ffc0007fff01fe318c6318c77f801f07fff01fe318c6318c07f800007fff01fe318c6318c06e800007fff01fe318c6318c05f800007fff01fe318c6318c00a8000003ff01f821084210807e000007fff0198210842108066000007c1f017e108421084055000007c000101084210840040000007c00 else 0x577e108421084000000000000560108421084150003ff00000517908421084145403ff07c001ffe739ce739c7ff801ffffff1fe06318c63187f8001ffffe01e1e5294a5294787801ff801f1119084210840444001f07c00111800000000000000000000007fe318c6318c1ff8000fffff01ff39ce739cff7fffff07fff)) else (if i<4 then 0x666694a5294a599983e0f83e057ff39ce739cd57f83ff07fff57fe318c6318c07f800007fff577f18c6318c7f757fff07c00577f18c6318c557503ff07c00577f18c6318c555503ff07c00577f18c6318c550003ff00000577f18c6318c545403ff07c00577f18c6318c4444001f07c00577f18c6318c4040000007c00 else (if i<5 then 0x99816b5ad6b5a0607c0007c0098014a5294a526007c1f000009199294a5294a4647c1f07c0089816b5ad6b5a2627c0007c1f88816b5ad6b5a6667c1f07c1f88806318c631a2227c000001f878739ce739ce1e1fc00ffc008181294a5294a0607c0007c00818021084210800000000000080010842108420007c0000000 else 0x99996b5ad6b5a6647c1f07c0099996b5ad6b5a6627c1f07c1f99996b5ad6b5a6027c1f0001f99996b5ad6b5a4667c1f07c1f99996b5ad6b5a0627c0007c1f99996b5ad6b5a0027c000001f99996b5ad6b58446001f07c1f99996b5ad6b58042000007c1f99986318c631800200000001f99816b5ad6b5a6607c1f07c00))) else (if i<9 then (if i<7 then 0xb999ef7bdef7aeeefc1ffffffa9fef7bdef7beafffc00fffffa881ef7bdef7bffffffffffffa880e739ce73aafffc00fffffa880e739ce73aaaafc00f83ffa880e739ce73a2aafc00f83ffa880e739ce73808a8000f83ff99ff7bdef7bde67ffc1f07fff99996b5ad6b5bf777fff07c1f99996b5ad6b5a6667c1f07c1f else (if i<8 then 0xe1e1ad6b5ad6a0687c0007fe0e1e1ad6b5ad6905803e007fe0e0018c6318c638007fe000000dfff7bdef7bdf7777fff07c1fdfff7bdef7bde6667c1f07c1fdfff7bdef7bdd55703ff07c1fdffe739ce739c00200000001fd9f96b5ad6b5b6767fff07c1fd7ff39ce739cf5757fff07c00d7ff39ce739cd55503ff07c00 else 0xf9f9ef7bdef7be7e7fff07ffff9f9ef7bdef7a66e7c1f07ffff9f8e739ce73800a0000003fff999ef7bdef7be667fff07c1ff801ce739ce73e007fff00000f801ce739ce726007c1f00000f7ffbdef7bdefd7d7fff07fe0f7ffbdef7bdef8787fe007fe0e1ffbdef7bdef87d7fe007fe0e1e1ad6b5ad6b8787fe007fe0)) else (if i<10 then 0xff7fdef7bdef7f807ffff8000ff19ce739ce73f807ffff8000fe1fdef7bdef7f857ffff8000fe07def7bdef7f81fffff8000fe01ce739ce73fa07ffff8000fe01ce739ce73f857ffff8000fe01ce739ce73f807ffff8000fe01ce739ce73f007fff00000fe01ce739ce738807fe0f8000fe00c6318c6300800000f8000 else (if i<11 then 0xffffffffffffc4ce801fffffffffef7bdef7beaaafc00f83fffffef7bdef7bc0ff8000ffffffffef7bdef7bc08a8000f83fffffef7bdef7bc00a0000003fffff9ef7bdef7bffe7ffffffffffe1ef7bdef7bff87ffffffe0ff99ef7bdef7bfe67fffffc1fff81ef7bdef7bf807ffff8000ff7fdef7bdef7fd57fffffc00 else 0xfffffffffffffffffffffffffffffffffffffff8afffff83ffffffffffffffff7f7fff07ffffffffffffffffefeffffffffffffffffffffff8faffe0ffffffffffffffffff7fffffffffffffffffffffffe6eefc1ffffffffffffffffffe0eafc00fffffffffffffffffd5df83fffffff))))
def wd (i : Nat) := (wdA (i/10) >>> (100*(i % 10))) &&& 0xfffffffffffffffffffffffff
def stA (i : Nat) := (if i<7 then (if i<3 then (if i<1 then 0x35507c8860001aa83c443c000d541e26160006ba0f110e0003550788848001aa6bc441c00001aaeab4400000d571522000006aaaa91000003554548800001a6eaa4400000aaa9106000006aab055000003532446800001a9e223200000d4a91150000000000000000000000000000000000000000000000000 else (if i<2 then 0x35507888a8001aa93c4444000d545e22220006aa0f11110003550648888001aa8394444000d541ba2220006ab2a911100035506a8888001aa83c4244000d541e1f22000507888886000355082f088001420bc2218000d4f1118220003c44608860003541786088001a93a23044000d541e221a0006aa0f1110 else 0x2ed9548830001768354418000bb41e1f0c0005da0f51050002ed0789020001aaed084f0000d58e841780006abb420bc000355da10590001aaed082dc000d5768415c0006abb660aa000355da105a8001768417818000d576840780006abb422ac000365da0fde0001aa83c444c000d59de22340006aa0f1112)) else (if i<5 then (if i<4 then 0x355d9cd510001aaed06888000d57683c400006abb4261f000355da12cf8001aaed0787c000d5767bc3e0006abb41e1e00034dda0f110001aaed75488000db76833440006abb3d9a2000355da0ccf8001aa83c4a88000d5768353a0006abb416a200031d07888300017683c4418000bb419220c0005da0dd106 else 0x355da0ed10001aaed07488000d576832440006abb41c22000355da6dd10001aaed06e88000d56e837440006abb418a2000355da0d910001aaed05c88000e9aaeaa440006abb65522000355daca910001aaed55488000d566aaa4400000d555522000355db0a910001aaabc5488000d53582a440006abb41aa2) else (if i<6 then 0x1aaed07888700d541e22223806abb41e22040355da0f110801aaed07888380d57683c440405da0f1106020355da105e0101aa83c444408001aaed08cf0000d57683c460006ac749e220003565a0f110001ab1d07888000d58a83c440006abf41e220003561a0f110001aaf507888000d58283c440006abb41e22 else 0x1aa83c4470880d541e222e4406bd541e22220356aa0f111101aad507888880d541e33444406aa0f111d2202ed07888886000283c4444300d541e22221806abb420bc220006aa105e1101aa8417888880d541e223044000d4f11182203550788889101aaed07888600d541e22223006abb41e221603550788888b))) else (if i<11 then (if i<9 then (if i<8 then 0x1aaed07ef1100d5768417ef006abb41e22060355da0f111a01db5507888880d59a83c444406ac941e222203aeaa0f111101aaed07888880d56683c4444000d541e22220355098f111101c35507888880d541f3c444406aa0f1e22220355078c111101aa83c5488880ddaa83c444406aa0f132222035507889111 else 0x355da105e00d576cd082f006abb42641780386abb420bc01aaed08b05e00d57684178f006abb420bc540376abb420bc01aaed082f1100d576841785c06cd576841780356abb420bc01aaed082f1980d5768417874000bb420bc0c02ed082f110601aaed082f0300d57684182f006abb41e2c440355da105e2c) else (if i<10 then 0x176cd07888300bb4263c4418070bb41e220c02ed07af1106017683c7888300bb41e2a441806ebb41e220c02ed07891106017683c4488300bb41e222e1806abb41e220c02ed078cd106017683c4474300bb41e220c1806abb41e220a02ed0788830501aaed07888200bb41e220c1006abb4223c4403b6abb420bc else 0x1af55da0f1100d5aaed0788806abb5e83c440355da125e2201c2ed078cd100e1aaed0668806abb41e33440355da0cd52201aaed06688b80d57683c528806ebb41e223a0376abb41e1d01ab1d07888e80d57683c447406abb41e1d2e0355da0f111601aaed086f1100d57683c4450076bb41e220c0005da0f1106)) else (if i<13 then (if i<12 then 0x1aaed078a1100ddaaed0788806abb4253c44036eabb41e22000355da0d5100d57683c6a8806ed576835440355da0f122201aaed07899100d57683c448806abb41e22360006abb41e1f01c355da0f0f80d57683c447c06abb4263c2e0355da13111701aaed07888beabb426bc445c06abb41e22140366abb41e22 else 0x1c355da0f1100d576c50788806fd57683c440355da12de2201aaed07af1100d576845788806abb41f3c440355da0f1e2201ab3dda0c910001aaed0648806abb41e32440355da0f17a2000355da0dd100e5aaed06e8806abb41e37440006abb6552201aaed978a9100d5769bc548806abb41e2a440355da0c1522) else (if i<14 then 0x1aaed07888e80017683c441806abb41e220c0006abb420bc01aaed082f1100d57683c4444000d541e222203aeac941e220003563a0f1100edaaed0788806ad17683c440006abb41e2201d355da0f1100e7aaed0788806abb6683c440355dad41e2201c755da0f1100d57684c788806abb4243c440355da11de22 else 0x355da0f110001aaed0788806abb6683c440355da131e2201c355da0f1100d57683c788806abb41e2a440376abb41e2201aaed07889100d57683c445c06ad57683c440355da0f19a2))))
def st (i : Nat) := (stA (i/20) >>> (49*(i % 20))) &&& 0x1ffffffffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 4 else 14) else (if i<7 then 111 else (if i<8 then 273 else 291))))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 1)) else (if i<6 then (if i<5 then 10 else 97) else (if i<7 then 162 else (if i<8 then 18 else 1))))
def state (s i : Nat) := unpackWords wd 7 9 (st (off s+i))
def oaA (i : Nat) := (if i<1 then 0x23c8e22c8a21c862148420c811fc7e1f0781d4701b4651845e16c5a1645815c561545414c511384a1244610c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400 else (if i<2 then 0x5494d5314a51d46515425053f4f93d4f13b4e1374d1334c12c4a52648d224851e4751a45d164551243d0e4310b4290741905411033f8fb3d4f33c4ee3b4ec3acea39ce4388e1380dd370db364d835cd6354d4344d033cce32cca324c831cc6314c430cc2304bd2e4b62ccaf2b4a828ca027c9e2749a264972549424c9224490 else 0x39fe4f87ddb64d634ecf72fc8f17c3f00bcae6b5acaaeaaaa7a9ca5290a3a86a067c9de719b6679925d962539324590a3d8de348c62988a1d8561082dff7e5f47bdea795e1769d5739c6709be6f1ba6ddaf6a9a5691a267d9c6659664d8f629816017b5d5705b56a5a5665855c56957))
def oa (i : Nat) := (oaA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def ovA (i : Nat) := (if i<2 then (if i<1 then 0x14c09d04a023010807a03801940c805c02a014c0a4051028013c09804b024011c08c045022010c08404101f00f407803901c00dc06c03501a00cc05c02d01480a004e0260128090046022010808003e01e00e807003601a00c806002e01600a8050026012008803801a00c0058028012008003801800a0040018008002000 else 0x64031d18c8c506042fd1790bb85ce2e216f0b6c5aa2ce1648b145822bd15c0ad05602ad1530a9453429914c0a3451828b14009f44d0263124890845a22910807fc3d41cf0e407083761b30d906a43421a00cf867833a19c0cd86683241910c486202fc1760b705882b01500a004d024e11408003901b00c705902c41600a7) else (if i<3 then 0xeb27423969c60e066d935e1a60d2e6833349978c8062b30b1804bd45cd2e616d8b365812b61538a9a53528b13dc9c44c7257927892e48c243920c8fc47923a91bc8d446523091748984492221104854425208102c7f03f01f18f747b43d31e60f207863be1d68ea87483a11cf0e6471c38d1c60e246e236c1ac0d48672327 else 0x431e13f0778173f91f2cf5d787bb05d12e41703b6f9adad4567cb34590ec3c60a2fed7a4bb75cf2dd96aeb3b590ac055ccacb55a2a6d4fca61520a87d4109ef4ec270d35097b4aca50522e8f846b229d11487242a20d502e7fb3ef1efcf28775))
def ov (i : Nat) := (ovA (i/78) >>> (13*(i % 78))) &&& 0x1fff
def aValA (i : Nat) := (if i<3 then (if i<1 then 0x1830000183000000000140070000100000c28000000830e003040a0c00a32141001e101000614009001020010000000000000000400302000091400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i<2 then 0x300000400000042000004000000c200002800000000000208000000000f200c300000800100140020000004000400100000001400080040048000000800000000000000000000000000000000000000000000000000000008000001801804000002018000000040014080000420300000800a30000000400000000010000000 else 0x120e2800217286468c06006070018400000050020003061400b8d000c30016000000e002821e10d80120c28000080001800104002c18200082832c00404080008600300020018280102400a002048f04000051814506220018100001001200081000000100000000000000000000100001000018001000400014001000000009)) else (if i<5 then (if i<4 then 0x40200149800c0c08000100020a001131200c82003939b4a01117061420424008042610002023508a08012140800182182048d0c0c00a36690914c0d0803e5d087082420100100800a0821900586880e040191a1018100009990064102240000c2e14889006c38d088c480000001a005c1010044280000000d001c4001400110 else 0x2922bc50f0808ba6480801b3208dc570089bd58084bf58080394408dc15a1083f501034574a40351ea450f0808ba6480801b32081001a906030084a0300280800a00725000c0222a0c49e260c00f16044000200681240028c0010180140401406100020a143000a04409220018a2230180180078100340181e080043810586) else (if i<6 then 0xf0d0114aae561072c487cdb57ae003152e0024445d08628087357f24d1d2a313035a1243d72d402a509e4417675b80623dc8b3e5d41d66c0b035c4cf80545120e74a9e9886dc1008c9de0b4a3d48040b14aa886dc37687988048401986a35cb526513b7426cc4b00c45c3143c2022e99202006cc823911f8a24c9b8a10b55af else 0x28784045d3240400d990428784045d3240400d9904c21c070a93c108e5223305039b1801802410ddbd6860497)))
def aVal (i : Nat) := (aValA (i/146) >>> (7*(i % 146))) &&& 0x7f
def vValA (i : Nat) := (if i<25 then (if i<12 then (if i<6 then (if i<3 then (if i<1 then 0x2b0c70330bd06f00306b00004801500300004003301300000000306f00303800006b0150bb03000000303300000300000003300000000302001001500006500000008708700306b00301500303300301300000000000000000000006f01300000300000006f0030000980000e706f0b708706f06f06f00006f000000000000 else (if i<2 then 0x3300003301507b07b03300007b07b00000007b07b07b03300007b07b00000007b00000002b01300007b00001300000002b01300007b00001309300f08900f09500f00000f07500f09b0500000070070070000070610070000390000150e103d03703703703703700002d02d02d02d03302d02d02d02b02b02b02b03302b02b else 0x400260dd0b50d900006f0d30000d50000300b70db0d706f06f0d30000d50df06f0d307007006f06f0130e708705d0000370600130130130130130eb07005d0ed05d05d05d06f05d0b500005d05d06f00005d00006f0a90000720700f106f0f306f0f30f507806f0d306f06f06f00000006f000033033033033000083033033)) else (if i<4 then 0x870000bb0370500000870e70800000870000870870870000870870870030630870650000370700030030030030030700e30e500000000000006300000006306305d06f0d30630000000e10ef06f07006306306f0630870630630630d30000650650d10700370d300000006500006f06506500000006507006f06f065000 else (if i<5 then 0x7d01100001107f01100001106f00300306f01506f0030630000090090000ab08800900306300006b06b0000ab07806b0030830870870870000870000870000870000000430150000870000150000000cd0150000cb0000150ab0680000a10ad0a10770a10e70a10870a10b30130cb0130cf0130000130cd0130000000e90bb else 0x1507b01303300357800003303300000000300000001301301301301300300000300300000300300000056056000356056000000300000356000003300300303300300300300300330000000030000030000000300026000026000316000000016000016007f00001101101107d0110110030330000330330330c90330c9033))) else (if i<9 then (if i<7 then 0x330000030090005980030000335600301601741600331700000000150005600000330330330030130030330000330330190030330330330030001600330200035820000000030000030030000030000330035880030030030330030000035f0003003003000003000003003033003000000000000003033003003003009003 else (if i<8 then 0x330150c00000e00a03000e00e00a41600e00e00030151600000d00c00940d00d00902600d00d00030030900000b00a01600b00b00801620b00b001516016000300300000300301d00300300300300356000300300000300300300303300316000000305000000304100000003300000303f033033033033033033000592 else 0x150e01600b01600b41600d01605601600000050001601600f0060000013160134160160000015050000003000160003160000000120000160003160110160040000033160114160000033160030000033000160000033000160000033000160020160160000033000033000160000019000160011160000184160340180160)) else (if i<10 then 0x35a20000000030000030030000035a00330035a80030030030330030000030000030330030000031b0003000000000000000003003003003033003033003000160160160000003160160003160154000009000160160140003144100003015000015033015000003000003003015015000000033015000070120160160003 else (if i<11 then 0x2602602600332600112602782702722600333000002000c00c82002000c22602002000030032602600030000030030bd0030110035600030330bf0030000030030000330030030030050bb0000032602600001e00030030000000330000110030330335600330000000030190170330330330330332600001d0000000 else 0x150000030000030002600000000000002600000d20002600035602002602600d80d02600002562600032200000002600052462601f00000130002441e02600002340032362600000030002602200000002600032162600332102140000030000330330030330030000030030030030030030000032600330000001d0033)))) else (if i<18 then (if i<15 then (if i<13 then 0x330030030330113000003183103123000330033003000000030330000110030030000000000030000130030030030330030690005600030003000000032a0000033033033000033000033000033003033000000560033033003003033033033300300033290000015015000000015033033003015003000003015003015 else (if i<14 then 0x30000000030030330193003003000000033003000030e03000e23000e83002003005603002d02f63000033000000050003002e63000132e42b03003000000032a00000030003000002d00003000033002c62c00332c4300300000033300290000033000300000033000300003003000000000000003000003003003003 else 0x335600330330330330000000330000000000330330330330333c00330330330000330000330000030030000030030000005605b20035b05600000030000035600000330030030330030030030030000033200030030330bd3243260000030000030030c50030000c7003003000033033003000003000000033003003000000)) else (if i<16 then 0x1101103300000008303303333033633408508100003303303300003300003303303300003303303306f06f5e00310335c000006f5e40335c003300003300000001d00003303303300006f0330330330330335c00330330000035c20410035c00330035c8033560033033000000033045000033033033000003000033000009 else (if i<17 then 0x1101100301103301156001100002d02d02d45400050002d01507101507302d01b03302d02b07502d00007707902d02d02d00000003303303300003337003300000000003300000003303303342002303303303301101101100307d60000007f0030000010000030115d0003000011033560003011000011011560000560 else 0x2f00000300302101906702f00002f01702f01100301f02f03302300056002f03304702304901100903300004101b01101104500002301f0005c802303300302302302302b36202b02b02b01102d36035002b02b03302b00000002b00002b02b00003302b02b00001100000000002d01100303300001100302b56001f000003))) else (if i<21 then (if i<19 then 0x3303303300000300000000300303303300000303303300003303301300003300300000000000300056003300303303303301503300303300000001556003301900003303301500303300303303303301100003301703303301900301701501101303303303303303303356056000300000000000000301b03300002f560380 else (if i<20 then 0x3300003303301303303300000003300900308f00003303300000003300003500003303303300003300003300003303303300000300000000003303303303303300356000003300000303303300300303303300056003300001d00300300303300303300000001d055000560033033560003033000000033033000560033083 else 0x3500130130330000130330130333c03c03c005100f01303301301301304d3d001304b0000452b00f228800001301301300000000001307b0130133b00000130133c00130330133b20130130130130003c001301301300002b03301303303303300000000004b00004d0330333e00000450453c00410335600330335c8033033)) else (if i<23 then (if i<22 then 0x903300000000000056000300703303300000000300003356003300003303103300303300003303300303300003300901d0000000000000330000070330000330330090330000335600335600050030330330330330000330000330000330030030000005600330330030030330330330000000000000f010805304f02b033 else 0x3342001f03342003342001f03311203303311003342001f00001f01f01f03303302301108101f00301f01d01f00300b00100356001f03300003300042000001f01f01f00300003300003342003341203341000042000042000000003303303303303d03301f033033033033033033033003005033033033033033033033003) else (if i<24 then 0x3342001f00901d0c300300107100703300000501f03302302700002956000003301f01f01f00000308337000003303300003301f0033c003300040603301503303303340403301303303503342003303300056003301f00000000001f42003d2100350000000330000330331c800003302303300003303d33000003d00b2c0 else 0x49403106b06f0000a906b06b0000770000000005300ad06b0ab06b07d0a506b00006343000356007b06f00000008700300302b00300000356003300000304301900000003301100000300356000300300300000000000356000042603342403342008356003303303300303d00301f00303303303303303303303300001f081))))) else (if i<38 then (if i<31 then (if i<28 then (if i<26 then 0x4a00030610030030030050034a005f0000110670000130030030030030000030650030874b000006106100107306108d00000003308900008706108b0610000610000610610005600110030030035600034a00000030000c100300300006100303302d00004f00300000100f00306b00306300306b06b06b49608706b000 else (if i<27 then 0x6100300301503300000050000503f00300301500303300356000000300002d04f00000300300f0030110030130030030030000000000004600000002d01b64b04704804a04a01202204a003700f00600303100303100301103d00300300300338003b01901503900300300900300703b037003000015003003063440003000 else 0x50110630030030000030030030090000000002e01422400001301aa05b04302d03336401501503300001503301503305901500f03300001501505701501504100003f5005005005100150130150000430000000000000000000330004f00000150150000150875000150150155000150150153b4015033000000015003)) else (if i<29 then 0x5302f01522500a50a307d03900006b06b03103706b03100003b00006b0a109f03d09b06b06b06b00006b09d44803b46853053053006b06b06b00000301101156000303b06505100300348806b06b00300000353000306903306b00006d00003b003063003003000003000000000003000000003003560003001011000033013 else (if i<30 then 0x309900300303309700301500300000309b00356003301501500001502307b01502b01500301501501500301556000303301300000000300000000300356000000501100300300300300300306b53053006b06b00006b06b06b53003703106b06b06b00000047800006b07b00006b06b00000006b00000000044a150198530 else 0xf01350400f03300f00308900f4d607b01300004500303302307b00000900007b0050030a70415c807b0450450335600450450000000030000453c00450330000450330030030030000110030000000130000030030150030030055600030330330030030034c45600000030000330030000000050000130110030000004c6))) else (if i<34 then (if i<32 then 0x300100100100007b0030005040000130135600000030133c000303301350601301501300300056001300301300002b00001345000000002f5040030035600000070130030000000030030030050000130110000330030034e605d00300300f00356000f00300350000f0950000000750000150003a000f000000033000093 else (if i<33 then 0x330030030030030030030030090000000030000000c156003300300556000300000500703300002300507b0050030050000050690000000150030000110030000000130000030030030030030055600030330330030030af0010a90090a90010010030075600010030050330030010010010a90b1 else 0x150150150030035603f00030030150150000000150005600030035600000070034a000000300300001500000300300003353606500300300000302f06300353606500006500000349200356003353400349000500006300000000001d01300000300000301300300300302f033003560003526003524003560003560003)) else (if i<36 then (if i<35 then 0x30001601683001622600190170110330000030030330000030330030330000030150130330150030030090000030070000050005605605600030030030000000030070004b000300356000706100039009b00900700002f033556007007007003007560007007007000007560000003015000003033560546015015015015 else 0x2700330b90b503300006f06f0333d606f03306f03306f0b70b303300006f06f06f00006f03100001d0005c05c05c006f06f06f033003560003560003560003560003560003000000000000000000000033003003003003003003003560003000003560003000033000009000000000000003091003033003003003560003000) else (if i<37 then 0x1503300001501501501503f2802100000150151401101901d01701f00002700b40000b00e09d02240d01301002441601a02002540002500e41e01742400700f41b42341b02300902202602600f028006f5c000006f06551800006f05d51200006f0333e606f00006f00006f03306f00006f06f06f000000000010188310182 else 0x50170110330030330030330030000150130030030090030070030003c03c00150032141c02b42a01501200000000300f20c40f82b02c00000330331800000800d08d62900006c00c00a00000000158e078028028001503302d0330150330000330000150330000330130330150339f00418e4015033043033015015015015)))) else (if i<44 then (if i<41 then (if i<39 then 0x4383e20003e01101183f63f03403c04162f04103e84060004041124003864143801223164323144303103f44404401201280300000000001023203003709f03501088f07700103b01003300036d03d03263b63243b40004504200000330038f64268f4424019033033003003033003000003033033003003000003000003 else (if i<40 then 0x5901524e00000000300000000000001324a04809f00000035665605a09007904d44c00030005645204a61384a44e04e04b03400330331306b00190110030030330000330000030330030130030030099060079040030330170330030030030030030330150334e00030030030030054d64d00200150333609d03903303843a0 else 0x330390330330215d600d0330215d00335f00390330336200330000215f03705e40330336b00395e61680330395e00007700350000330330339160215d40339100336000000330331403605465005325760005804940004901429d05444b01503505884f65565305740005701485105385824961584f45544f0550470540590)) else (if i<42 then 0x6524d00116700000110230000111729d002f0116b066001101165093601101166001b5d066002d01138063002302393400002502d6600110116606800230006326400116608d01700110000235b86089d00000001605f06020000009d00330001625f00330000339140215f0000a02a000394c05f0a085f00236105f05c0033 else (if i<43 then 0x337007007000330336b06666646605f06b09469449407f00000330350336b06b06b00000001901980006b04e019239003303303502303300003702f03300001b03303303303303302303702f03303302f0350000236b00000009d00330330330007e00000000119d002366002901101102b660000027000023188660023011 else 0x3303303301d03303101d03300003303103301d0000330009760330331b24685d01b03b09d09d07106e07007007004f01c86400330335e07d09660006e20007209647708d070003301d00003503303300001d03300001d03300003302303300003b03303300103500001d0000330330330330336f001d03300003303503301d))) else (if i<47 then (if i<45 then 0x1f7b601f7f003d1f07f00330337a601f0000330007f03d003303d0337f003303303303303302303d03d00000b03301f0337a403303303361003d9867c00000330000000330330000000005001d877003301d1d07700330231d23c00319d00330017707709d07f05f0770706033033974704970700770770770031033035 else (if i<46 then 0x82000300b0139966540010030008208502000010038200112188100000038308d00170078200030098402129d00010006308200030008440000016e092000f0036508200030059509d00030030030000153e00330000350006b07f09809849d07b40000000336207f07c47700001f25207f02e07f07c67b00337a07f01f8033 else 0x130130008d00198d00159400210000039a201d0000039a09d09700038d001122000000300300366001f0018d082200901d0038d028800300300301700001302300301d0039d00008200077002228d00055408d03f00150000038340000030032d600d6f68000110038140190008205300030008d401b820015000)) else (if i<49 then (if i<48 then 0x598000589601d9c02509700059700050058760007400009d08869d07508669b07306b09b28d0980033013940864940940940680560298000874240410a1867088406824201301303300004f01301301303300003394094001301301303305102b03301301300001300004503301301301305300f03300001304d01304b033 else 0x1f02f9a001901d8408b600301327001d0150039e09a00037608440036a00030039a09d00008d05709700212520059d00019700239700050050050450050050470050059c297083400597042000003f01d03fa1800583600500000500001d72000502501d00597000571000505897002300504969001f77001d8940012a801d) else (if i<50 then 0x9400009a87060007042604408d67704e02889466607f08289a20009a02629706669445f02828229768209747008d49d09d02803c00000039d00070150030112b20468d00039c00050030009a000301d8d402f8500000000099a00039b001d0030319a09d00070030000000032b80218c60030170038a60154309a0580003000 else 0x500080800d00740e00001080960000940000300d60a00400180e60700b00c81020001000020f00760e40600120c20f60c00f40900d41101100100205902686b08d0664))))))
def vVal (i : Nat) := (vValA (i/85) >>> (12*(i % 85))) &&& 0xfff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<3 then (if i<1 then ([(35,0x800000000),(36,0x1000000000),(37,0x200000001f),(38,0x4000000000),(39,0x80000003e0),(40,0x10000000000),(41,0x20000000000),(42,0x40000007c00),(43,0x800000f8000),(44,0x100000000000),(45,0x200000000000),(46,0x400001f00000),(47,0x800000000000),(48,0x100003e000000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x18000000000000000000000),(90,0x60000000000000000000000),(91,0x80210842108000000000000),(92,0x100000000000000000000000),(94,0x600000000000000000000000),(95,0x800421084210000000000000),(96,0x1000000000000000000000000),(97,0x2000842108420000000000000),(98,0x4000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else (if i<2 then ([(35,0x800000000),(36,0x1000000000),(37,0x200000001f),(38,0x4000000000),(39,0x800000f8000),(40,0x100000000000),(41,0x200000000000),(42,0x400001f00000),(43,0x80000003e0),(44,0x10000000000),(45,0x20000000000),(46,0x40000007c00),(47,0x800000000000),(48,0x100003e000000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x18000000000000000000000),(90,0x600000000000000000000000),(91,0x800421084210000000000000),(92,0x1000000000000000000000000),(94,0x60000000000000000000000),(95,0x80210842108000000000000),(96,0x100000000000000000000000),(97,0x2000842108420000000000000),(98,0x4000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else ([(35,0x800000000),(36,0x1000000000),(37,0x80000003e0),(38,0x10000000000),(39,0x200000001f),(40,0x4000000000),(41,0x20000000000),(42,0x40000007c00),(43,0x800000f8000),(44,0x100000000000),(45,0x800000000000),(46,0x100003e000000),(47,0x200000000000),(48,0x400001f00000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x60000000000000000000000),(90,0x18000000000000000000000),(91,0x80210842108000000000000),(92,0x100000000000000000000000),(94,0x600000000000000000000000),(95,0x2000842108420000000000000),(96,0x4000000000000000000000000),(97,0x800421084210000000000000),(98,0x1000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)))) else (if i<4 then ([(35,0x800000000),(36,0x1000000000),(37,0x80000003e0),(38,0x10000000000),(39,0x800000f8000),(40,0x100000000000),(41,0x800000000000),(42,0x100003e000000),(43,0x200000001f),(44,0x4000000000),(45,0x20000000000),(46,0x40000007c00),(47,0x200000000000),(48,0x400001f00000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x60000000000000000000000),(90,0x600000000000000000000000),(91,0x2000842108420000000000000),(92,0x4000000000000000000000000),(94,0x18000000000000000000000),(95,0x80210842108000000000000),(96,0x100000000000000000000000),(97,0x800421084210000000000000),(98,0x1000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else (if i<5 then ([(35,0x800000000),(36,0x1000000000),(37,0x800000f8000),(38,0x100000000000),(39,0x200000001f),(40,0x4000000000),(41,0x200000000000),(42,0x400001f00000),(43,0x80000003e0),(44,0x10000000000),(45,0x800000000000),(46,0x100003e000000),(47,0x20000000000),(48,0x40000007c00),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x600000000000000000000000),(90,0x18000000000000000000000),(91,0x800421084210000000000000),(92,0x1000000000000000000000000),(94,0x60000000000000000000000),(95,0x2000842108420000000000000),(96,0x4000000000000000000000000),(97,0x80210842108000000000000),(98,0x100000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else ([(35,0x800000000),(36,0x1000000000),(37,0x800000f8000),(38,0x100000000000),(39,0x80000003e0),(40,0x10000000000),(41,0x800000000000),(42,0x100003e000000),(43,0x200000001f),(44,0x4000000000),(45,0x200000000000),(46,0x400001f00000),(47,0x20000000000),(48,0x40000007c00),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x600000000000000000000000),(90,0x60000000000000000000000),(91,0x2000842108420000000000000),(92,0x4000000000000000000000000),(94,0x18000000000000000000000),(95,0x800421084210000000000000),(96,0x1000000000000000000000000),(97,0x80210842108000000000000),(98,0x100000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)))))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 6)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 50) (goal 50) s ws) :
    NatRun (mask 50) (goal 50) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 6, sprOK (opTab j) (mask 50) (goal 50) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<3 then (if i<1 then 0x9c2b0945f16c6194290b85417c5b942a0b8541805b94290b8541805ba8310945f160548c2c0c45416c568c2c0c45417c568c280c45418c568c260c45418c568c2c0c454184568c2a0c45418c56942d0a85416c5f942e0a8541705fac2c0c45418c569c2c0c45418c56942c0c45418c568c2c0c45418c56942d0a8541705f else (if i<2 then 0x942c0c45417c5694260c45418c568c280c45417c569c280c45418c5694280c45418c569c2a0c0541885b9c2f0a854170619c290c0541845bc03109c5b16854942b09c6116c5f94270ac6117c5b9c290c0541885bb8310945b160548c280c454184568c260c45418456ac2c0c454184569c2c0c45418456942c0c45418456 else 0xac2c0c45418c58942c0c45418c58b8310945b16854ac280c45418c5eac2c0c45418c5a9c260c45418c5a9c290b8541885bac260c45418c5e8c280c45416c568c300c45418c56ac280c45418c56ac2f0b854180618c260c45416c568c2e0c45418c568c260c45417c56ac260c45418c569c260c45418c56942c0c45416c56)) else (if i<5 then (if i<4 then 0x94270ac611785ba83109c6116854ac260c45418c5a9c2a0c45418c5a9c280c45418c5a9c2a0c0541845b9c250ac5f1845b942a0b85417c5bac2c0c4541845aac2c0c4541845894260c45418c58ac280c4541845aac280c454184588c2a0c454184569c280c4541845a94300a8541705fac2c0c45418c5eac260c45418c58 else 0xac2e0c45418c5eac2d0c0541845f942e0a8541685fac280c45417c589c280c45418c5eac2d0c0541885f94260c45418456ac2c0c45416c58ac2c0c45417c58ac280c45418c58ac2e0c45418c589c2c0c45418c589c280c45418c588c260c45418c5e8c260c45418c5a8c2a0c45417c56942a0c45418c588c240c45418c56) else (if i<6 then 0xac2a0c0541885bac2f0a85417061ac290c0541885b9c2c0c45418c5e8c2e0c45416c568c300c45417c569c300c45418c5a9c2b0945f16c628c2c0c45418c5e8c2c0c45418c5a94300b8541805b94280c45418c588c260c45418c588c2c0c45418c588c280c45418c58ac2c0c45417c5eac300c45418c5eac2c0c4541845e else 0xac300c45417c5eac300c4541845eac290b8541805bac2c0c45416c5aac290b8541885b942c0c45418c5e8c280c45417c58ac280c45418c5ac0310945b1605494280c45418c5aac280c45416c5ac0310ac5b17854ac2c0c45416c5eac2a0c45418c5eac290c0541845b)))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 50 8 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3_0
theorem h4_0 : span (Z 4) 10 0 = true := by decide +kernel
theorem z4 : span (Z 4) 10 0 = true := h4_0
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 12 24 = true := by decide +kernel
theorem h5_36 : span (Z 5) 12 36 = true := by decide +kernel
theorem h5_48 : span (Z 5) 12 48 = true := by decide +kernel
theorem h5_60 : span (Z 5) 12 60 = true := by decide +kernel
theorem h5_72 : span (Z 5) 12 72 = true := by decide +kernel
theorem h5_84 : span (Z 5) 12 84 = true := by decide +kernel
theorem h5_96 : span (Z 5) 1 96 = true := by decide +kernel
theorem z5 : span (Z 5) 97 0 = true := (@span_join (Z 5) 96 0 1 (@span_join (Z 5) 48 0 48 (@span_join (Z 5) 24 0 24 (@span_join (Z 5) 12 0 12 h5_0 h5_12) (@span_join (Z 5) 12 24 12 h5_24 h5_36)) (@span_join (Z 5) 24 48 24 (@span_join (Z 5) 12 48 12 h5_48 h5_60) (@span_join (Z 5) 12 72 12 h5_72 h5_84))) h5_96)
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 12 12 = true := by decide +kernel
theorem h6_24 : span (Z 6) 12 24 = true := by decide +kernel
theorem h6_36 : span (Z 6) 12 36 = true := by decide +kernel
theorem h6_48 : span (Z 6) 12 48 = true := by decide +kernel
theorem h6_60 : span (Z 6) 12 60 = true := by decide +kernel
theorem h6_72 : span (Z 6) 12 72 = true := by decide +kernel
theorem h6_84 : span (Z 6) 12 84 = true := by decide +kernel
theorem h6_96 : span (Z 6) 12 96 = true := by decide +kernel
theorem h6_108 : span (Z 6) 12 108 = true := by decide +kernel
theorem h6_120 : span (Z 6) 12 120 = true := by decide +kernel
theorem h6_132 : span (Z 6) 12 132 = true := by decide +kernel
theorem h6_144 : span (Z 6) 12 144 = true := by decide +kernel
theorem h6_156 : span (Z 6) 6 156 = true := by decide +kernel
theorem z6 : span (Z 6) 162 0 = true := (@span_join (Z 6) 96 0 66 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 h6_0 h6_12) (@span_join (Z 6) 12 24 12 h6_24 h6_36)) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 h6_48 h6_60) (@span_join (Z 6) 12 72 12 h6_72 h6_84))) (@span_join (Z 6) 48 96 18 (@span_join (Z 6) 24 96 24 (@span_join (Z 6) 12 96 12 h6_96 h6_108) (@span_join (Z 6) 12 120 12 h6_120 h6_132)) (@span_join (Z 6) 12 144 6 h6_144 h6_156)))
theorem h7_0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7_12 : span (Z 7) 6 12 = true := by decide +kernel
theorem z7 : span (Z 7) 18 0 = true := (@span_join (Z 7) 12 0 6 h7_0 h7_12)
theorem h8_0 : span (Z 8) 1 0 = true := by decide +kernel
theorem z8 : span (Z 8) 1 0 = true := h8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
def rs : List Nat := [5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 14, 14, 14, 14, 14, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 1, 2, 5, 6, 9, 10, 12, 14, 17, 18, 20, 22, 24, 26, 28, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 3, 7, 7, 11, 11, 13, 15, 19, 19, 21, 23, 25, 27, 29]
def xs : List Nat := [0xfffef7bdef7bc08a8000f83ff,0x577f18c6318c555503ff07c00,0x99996b5ad6b5a6667c1f07c1f,0xe1e1ad6b5ad6b8787fe007fe0,0xfe01ce739ce73f807ffff8000]
end ceaa8a888

open ceaa8a888 in
theorem no_run_eaa8a888 : ∀ s ≤ 8, ¬ NatRun (mask 50) (goal 50) s xs := by
  intro s hs h
  have hh : NatRun (mask 50) (goal 50) 8 xs := extend_run h hs
  have hp : xs.Perm (state 8 0) := by decide +kernel
  exact scorebarrier_all rokok checked 8 (by decide) 0 (by decide) (Run.perm hp hh)

open ceaa8a888 in
theorem lower_eaa8a888_all (gs : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gs, Ok g)
    (hev : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = fn 0xeaa8a888 x) :
    9 ≤ gs.length := by
  by_contra! hn'
  have hc : HasCircuitSize 5 (fn 0xeaa8a888) 8 :=
    ⟨⟨gs, o⟩, hok, (show gs.length ≤ 8 by omega), hev⟩
  obtain ⟨s, hs, ws, hsub, h⟩ :=
    exists_run (fn 0xeaa8a888)
      ⟨(fun _ => false), (fun _ => true), by decide +kernel⟩ 8 hc
  have hh : NatRun (mask 50) (encL (fn 0xeaa8a888) rs) s
      (ws.map fun a => encL a rs) :=
    Run.map (fun a : BFn 5 => encL a rs)
      (fun a => by rw [show mask 50 = 2 ^ rs.length - 1 by decide +kernel]; exact encL_inv a rs)
      (fun a b => encL_and a b rs) (fun a b => encL_or a b rs) h
  rw [show encL (fn 0xeaa8a888) rs = goal 50 by decide +kernel] at hh
  have hsub' := hsub.map (fun a => encL a rs)
  rw [show (List.ofFn fun i : Fin 5 => fun x : Fin 5 → Bool => x i).map
      (fun a => encL a rs) = xs by decide +kernel] at hsub'
  by_cases e : ws.map (fun a => encL a rs) = xs
  · rw [e] at hh
    exact no_run_eaa8a888 s hs hh
  · exact (by decide +kernel : ∀ zs ∈ xs.sublists, zs ≠ xs →
      (cov 50 zs &&& lo 50) ≠ lo 50) _ (List.mem_sublists.2 hsub') e (required hh)

end PQ1425Lower
namespace PQ1425Upper
open PEqualNP.CircuitLowerBounds
abbrev FanIn (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
abbrev OneNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j
abbrev HasNot (gs : List Gate) : Prop :=
  ∃ g ∈ gs, g.op = GateOp.not
abbrev Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
abbrev Evaluates (T : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∀ x : Fin 5 → Bool,
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
abbrev LowerBound (T m : ℕ) : Prop :=
  ∀ (gs : List Gate) (o : ℕ), FanIn gs → OneNot gs → Evaluates T gs o →
    HasNot gs → m ≤ gs.length
abbrev Witness (T m : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), Mono gs ∧ gs.length ≤ m ∧ Evaluates T gs o
private theorem allRows (P : (Fin 5 → Bool) → Prop)
    (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) : ∀ x, P x := by
  intro x
  have E : ![x 0, x 1, x 2, x 3, x 4] = x := by
    funext i
    fin_cases i <;> rfl
  exact E ▸ h (x 0) (x 1) (x 2) (x 3) (x 4)
private theorem finish {T m : ℕ} (lb : LowerBound T m) (w : Witness T m)
    (gs : List Gate) (o : ℕ) (hOk : FanIn gs)
    (hOne : OneNot gs) (hEval : Evaluates T gs o) : Witness T gs.length := by
  classical
  by_cases hn : HasNot gs
  · obtain ⟨us, p, hu, hlen, hev⟩ := w
    exact ⟨us, p, hu, hlen.trans (lb gs o hOk hOne hEval hn), hev⟩
  · refine ⟨gs, o, ?_, Nat.le_refl _, hEval⟩
    intro g hg
    obtain ⟨hop, harity⟩ := hOk g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun hn' => hn ⟨g, hg, hn'⟩)),
      harity⟩
private def gates_e8a8a8a8 : List Gate :=
  [⟨.and, [0, 1]⟩,
   ⟨.and, [3, 4]⟩,
   ⟨.and, [1, 6]⟩,
   ⟨.or, [0, 7]⟩,
   ⟨.and, [2, 8]⟩,
   ⟨.or, [5, 9]⟩]
theorem upper_e8a8a8a8 : Witness 0xe8a8a8a8 6 := by
  refine ⟨gates_e8a8a8a8, 10, ?_, by decide, ?_⟩
  · simp [gates_e8a8a8a8, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private def gates_e8a8e888 : List Gate :=
  [⟨.and, [0, 1]⟩,
   ⟨.or, [0, 1]⟩,
   ⟨.and, [0, 4]⟩,
   ⟨.or, [3, 7]⟩,
   ⟨.and, [6, 8]⟩,
   ⟨.and, [2, 9]⟩,
   ⟨.or, [5, 10]⟩]
theorem upper_e8a8e888 : Witness 0xe8a8e888 7 := by
  refine ⟨gates_e8a8e888, 11, ?_, by decide, ?_⟩
  · simp [gates_e8a8e888, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private def gates_e8e8e880 : List Gate :=
  [⟨.or, [0, 1]⟩,
   ⟨.and, [0, 1]⟩,
   ⟨.and, [2, 6]⟩,
   ⟨.or, [2, 6]⟩,
   ⟨.or, [3, 4]⟩,
   ⟨.and, [8, 9]⟩,
   ⟨.or, [7, 10]⟩,
   ⟨.and, [5, 11]⟩]
theorem upper_e8e8e880 : Witness 0xe8e8e880 8 := by
  refine ⟨gates_e8e8e880, 12, ?_, by decide, ?_⟩
  · simp [gates_e8e8e880, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private def gates_eaa8a888 : List Gate :=
  [⟨.and, [1, 2]⟩,
   ⟨.or, [0, 5]⟩,
   ⟨.and, [3, 4]⟩,
   ⟨.or, [3, 4]⟩,
   ⟨.and, [2, 8]⟩,
   ⟨.or, [1, 9]⟩,
   ⟨.and, [0, 10]⟩,
   ⟨.or, [7, 11]⟩,
   ⟨.and, [6, 12]⟩]
theorem upper_eaa8a888 : Witness 0xeaa8a888 9 := by
  refine ⟨gates_eaa8a888, 13, ?_, by decide, ?_⟩
  · simp [gates_eaa8a888, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

end PQ1425Upper
end PEqualNP.Outside.L_meta_8646

theorem PEqualNP.Outside.L_meta_8646 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8a888
        (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a888
          (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, hmono, hsz, hev⟩ := hs
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_8646.PQ1425Lower.Ok g := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    simpa [PEqualNP.Outside.L_meta_8646.PQ1425Lower.Ok] using (hmono g hg).1
  have hlow := PEqualNP.Outside.L_meta_8646.PQ1425Lower.lower_eaa8a888_all
    C.gates C.output hok hev
  obtain ⟨gs, o, hu, hlen, hev9⟩ :=
    PEqualNP.Outside.L_meta_8646.PQ1425Upper.upper_eaa8a888
  refine ⟨⟨gs, o⟩, ?_, ?_, ?_⟩
  · intro g hg
    simpa [PEqualNP.MetaComplexity.Monotone2] using hu g hg
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hlen.trans (hlow.trans hsz)
  · exact hev9
