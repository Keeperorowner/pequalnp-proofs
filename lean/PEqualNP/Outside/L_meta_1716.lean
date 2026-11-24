import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1716

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp

lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [ite_eq_left htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [ite_eq_right htt] at ht ⊢
    exact h x y hxy t ht

lemma mono_all {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact mono_nil
  | append_singleton l a ih =>
    intro h
    exact mono_step l a (h a (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true :=
  mono_all gs h x y hxy o hx

lemma circuitFun_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true := by
  exact eval_mono C.gates C.output hC x y hxy hx

lemma append_mono {n m : ℕ} {A A' : Finset (Fin n)} {B B' : Finset (Fin m)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    ∀ i : Fin (n + m),
      Fin.append (fun a => decide (a ∈ A)) (fun b => decide (b ∈ B)) i = true →
      Fin.append (fun a => decide (a ∈ A')) (fun b => decide (b ∈ B')) i = true := by
  intro i hi
  have hfun : ∀ i : Fin (n + m),
      Fin.append (fun a => decide (a ∈ A)) (fun b => decide (b ∈ B)) i = true →
      Fin.append (fun a => decide (a ∈ A')) (fun b => decide (b ∈ B')) i = true := by
    intro i
    induction i using Fin.addCases with
    | left a =>
      intro hi
      rw [Fin.append_left] at hi ⊢
      simpa only [decide_eq_true_eq] using
        hA (by simpa only [decide_eq_true_eq] using hi)
    | right b =>
      intro hi
      rw [Fin.append_right] at hi ⊢
      simpa only [decide_eq_true_eq] using
        hB (by simpa only [decide_eq_true_eq] using hi)
  exact hfun i hi

end PEqualNP.Outside.L_meta_1716

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1716 : ∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false) := by
  intro N8 K8 I8 _ Ca8 Cb8 S8 W8 hCa _hRBca hCb _hRBcb hboth
  have hCaop : ∀ g ∈ Ca8.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hCa g hg).1
  have hCbop : ∀ g ∈ Cb8.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hCb g hg).1
  constructor
  · intro pz8 hpz8 T8 hTsub hTind hTcard hCbT X8 Y8 hXsub hYsub hcard hind
    by_contra hCaNot
    have hCaXY : circuitFun (N8 + N8) Ca8
        (Fin.append (fun a => decide (a ∈ X8))
          (fun b => decide (b ∈ Y8 ∪ T8))) = true := by
      simpa using hCaNot
    have hXsubS : X8 ⊆ S8 := fun u hu => (Finset.mem_filter.mp (hXsub hu)).1
    have hYsubW : Y8 ⊆ W8 := fun l hl => (Finset.mem_filter.mp (hYsub hl)).1
    have hYno : ∀ l ∈ Y8, ¬ I8 pz8 l :=
      fun l hl => (Finset.mem_filter.mp (hYsub hl)).2.1
    have hXno : ∀ u ∈ X8, ∀ l ∈ T8, ¬ I8 u l :=
      fun u hu l hl => (Finset.mem_filter.mp (hXsub hu)).2.2 l hl
    have hX'in : insert pz8 X8 ⊆ S8 := Finset.insert_subset hpz8 hXsubS
    have hY'in : Y8 ∪ T8 ⊆ W8 := Finset.union_subset hYsubW hTsub
    have hY'card : (Y8 ∪ T8).card ≤ K8 := (Finset.card_union_le Y8 T8).trans hcard
    have hind' : ∀ p ∈ insert pz8 X8, ∀ l ∈ Y8 ∪ T8, ¬ I8 p l := by
      intro p hp l hl
      rcases Finset.mem_insert.mp hp with hp | hp
      · subst p
        rcases Finset.mem_union.mp hl with hl | hl
        · exact hYno l hl
        · exact hTind l hl
      · rcases Finset.mem_union.mp hl with hl | hl
        · exact hind p hp l hl
        · exact hXno p hp l hl
    have hCa' : circuitFun (N8 + N8) Ca8
        (Fin.append (fun a => decide (a ∈ insert pz8 X8))
          (fun b => decide (b ∈ Y8 ∪ T8))) = true :=
      PEqualNP.Outside.L_meta_1716.circuitFun_mono Ca8 hCaop
        (Fin.append (fun a => decide (a ∈ X8))
          (fun b => decide (b ∈ Y8 ∪ T8)))
        (Fin.append (fun a => decide (a ∈ insert pz8 X8))
          (fun b => decide (b ∈ Y8 ∪ T8)))
        (PEqualNP.Outside.L_meta_1716.append_mono
          (Finset.subset_insert pz8 X8) (Finset.Subset.refl (Y8 ∪ T8)))
        hCaXY
    have hCb' : circuitFun (N8 + N8) Cb8
        (Fin.append (fun a => decide (a ∈ insert pz8 X8))
          (fun b => decide (b ∈ Y8 ∪ T8))) = true :=
      PEqualNP.Outside.L_meta_1716.circuitFun_mono Cb8 hCbop
        (Fin.append (fun a => decide (a ∈ ({pz8} : Finset (Fin N8))))
          (fun b => decide (b ∈ T8)))
        (Fin.append (fun a => decide (a ∈ insert pz8 X8))
          (fun b => decide (b ∈ Y8 ∪ T8)))
        (PEqualNP.Outside.L_meta_1716.append_mono
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self pz8 X8)) Finset.subset_union_right)
        hCbT
    have hbad := hboth (insert pz8 X8) (Y8 ∪ T8) hX'in hY'in hY'card hind'
    rw [hCa', hCb'] at hbad
    simp at hbad
  · intro wz8 hwz8 Q8 hQsub hQind hCbQw X8b Y8b hXbsub hYbsub hcardb hindb
    by_contra hCaNot
    have hCaXb : circuitFun (N8 + N8) Ca8
        (Fin.append (fun a => decide (a ∈ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b))) = true := by
      simpa using hCaNot
    have hXbS : X8b ⊆ S8 := fun u hu => (Finset.mem_filter.mp (hXbsub hu)).1
    have hYbW : Y8b ⊆ W8 := fun l hl => (Finset.mem_filter.mp (hYbsub hl)).1
    have hYbno : ∀ l ∈ Y8b, l ≠ wz8 ∧ ∀ p ∈ Q8, ¬ I8 p l :=
      fun l hl => (Finset.mem_filter.mp (hYbsub hl)).2
    have hXbno : ∀ u ∈ X8b, ¬ I8 u wz8 ∧ u ∉ Q8 :=
      fun u hu => (Finset.mem_filter.mp (hXbsub hu)).2
    have hX'in : Q8 ∪ X8b ⊆ S8 := Finset.union_subset hQsub hXbS
    have hY'in : insert wz8 Y8b ⊆ W8 := Finset.insert_subset hwz8 hYbW
    have hY'card : (insert wz8 Y8b).card ≤ K8 := by
      have hle := Finset.card_insert_le wz8 Y8b
      omega
    have hind' : ∀ p ∈ Q8 ∪ X8b, ∀ l ∈ insert wz8 Y8b, ¬ I8 p l := by
      intro p hp l hl
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          exact hQind p hp
        · exact (hYbno l hl).2 p hp
      · rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          exact (hXbno p hp).1
        · exact hindb p hp l hl
    have hCa' : circuitFun (N8 + N8) Ca8
        (Fin.append (fun a => decide (a ∈ Q8 ∪ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b))) = true :=
      PEqualNP.Outside.L_meta_1716.circuitFun_mono Ca8 hCaop
        (Fin.append (fun a => decide (a ∈ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b)))
        (Fin.append (fun a => decide (a ∈ Q8 ∪ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b)))
        (PEqualNP.Outside.L_meta_1716.append_mono Finset.subset_union_right
          (Finset.Subset.refl (insert wz8 Y8b)))
        hCaXb
    have hCb' : circuitFun (N8 + N8) Cb8
        (Fin.append (fun a => decide (a ∈ Q8 ∪ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b))) = true :=
      PEqualNP.Outside.L_meta_1716.circuitFun_mono Cb8 hCbop
        (Fin.append (fun a => decide (a ∈ Q8))
          (fun b => decide (b ∈ ({wz8} : Finset (Fin N8)))))
        (Fin.append (fun a => decide (a ∈ Q8 ∪ X8b))
          (fun b => decide (b ∈ insert wz8 Y8b)))
        (PEqualNP.Outside.L_meta_1716.append_mono Finset.subset_union_left
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
        hCbQw
    have hbad := hboth (Q8 ∪ X8b) (insert wz8 Y8b) hX'in hY'in hY'card hind'
    rw [hCa', hCb'] at hbad
    simp at hbad
