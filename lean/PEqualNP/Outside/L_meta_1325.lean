import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1325_aux.Dual

open PEqualNP.CircuitLowerBounds

private def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

-- Invalid reads are false before complementation. Constants are the empty AND and OR.
private def dualGate (m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if ∀ i ∈ g.inputs, i < m then ⟨.or, g.inputs⟩ else ⟨.and, []⟩
  | .or => ⟨.and, g.inputs.filter fun i => decide (i < m)⟩
  | .not =>
      match g.inputs with
      | [] => ⟨.or, []⟩
      | i :: _ => if i < m then ⟨.not, [i]⟩ else ⟨.or, []⟩
  | _ => ⟨.or, []⟩

private def dualList (m : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate m g :: dualList (m + 1) gs

private theorem dualGate_allowed (m : ℕ) (g : Gate) (hg : Allowed g) :
    Allowed (dualGate m g) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
      have hf : inputs.length ≤ 2 := hg.2
      by_cases h : ∀ i ∈ inputs, i < m
      · simp only [dualGate, ite_eq_left h]; simp [Allowed, hf]
      · simp only [dualGate, ite_eq_right h]; simp [Allowed]
  | or =>
      have h : (inputs.filter fun i => decide (i < m)).length ≤ 2 :=
        (List.length_filter_le _ _).trans hg.2
      simp [dualGate, Allowed, h]
  | not =>
      cases inputs with
      | nil => simp [dualGate, Allowed]
      | cons i is =>
          by_cases hi : i < m <;> simp [dualGate, hi, Allowed]
  | mod r => simp [dualGate, Allowed]
  | maj => simp [dualGate, Allowed]

private theorem dualGate_not (m : ℕ) (g : Gate) (h : (dualGate m g).op = .not) :
    g.op = .not := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
      by_cases h' : ∀ i ∈ inputs, i < m
      · simp only [dualGate, ite_eq_left h'] at h
        cases h
      · simp only [dualGate, ite_eq_right h'] at h
        cases h
  | or => simp [dualGate] at h
  | not => rfl
  | mod r => simp [dualGate] at h
  | maj => simp [dualGate] at h

private theorem dualList_length (m : ℕ) (gs : List Gate) :
    (dualList m gs).length = gs.length := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih => simp [dualList, ih]

private theorem dualList_allowed (m : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ dualList m gs, Allowed g := by
  induction gs generalizing m with
  | nil => simp [dualList]
  | cons g gs ih =>
      intro g' hg'
      simp only [dualList, List.mem_cons] at hg'
      obtain rfl | hg' := hg'
      · exact dualGate_allowed m g (h _ (by simp))
      · exact ih (m + 1) (fun g₀ hg₀ => h g₀ (by simp [hg₀])) g' hg'

private theorem dualList_not (m : ℕ) (gs : List Gate) (i : ℕ) (g' : Gate)
    (hGet : (dualList m gs)[i]? = some g') (hNot : g'.op = .not) :
    ∃ g, gs[i]? = some g ∧ g.op = .not := by
  induction gs generalizing m i with
  | nil => simp [dualList] at hGet
  | cons g gs ih =>
      cases i with
      | zero =>
          have hEq : dualGate m g = g' := Option.some.inj hGet
          exact ⟨g, rfl, dualGate_not m g (hEq.symm ▸ hNot)⟩
      | succ i =>
          exact ih (m + 1) i hGet

private theorem dualRead (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map (!·)).getD i false = !(w.getD i false) := by
  have hi' : i < (w.map (!·)).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi, List.getElem_map]

private theorem dualOr (w : List Bool) (is : List ℕ) :
    ((is.filter fun i => decide (i < w.length)).map fun i =>
      (w.map (!·)).getD i false).all id =
      !((is.map fun i => w.getD i false).any id) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      by_cases hi : i < w.length
      · simp only [List.filter_cons, hi, decide_true, ite_true, List.map_cons, List.all_cons,
          List.any_cons, id_eq, Bool.not_or, dualRead w i hi, ih]
      · have h0 := List.getD_eq_default w false (Nat.le_of_not_lt hi)
        simp only [List.filter_cons, hi, decide_false, List.map_cons, List.any_cons,
          id_eq, h0, Bool.false_or]
        exact ih

private theorem dualAndValid (w : List Bool) (is : List ℕ)
    (hv : ∀ i ∈ is, i < w.length) :
    (is.map fun i => (w.map (!·)).getD i false).any id =
      !((is.map fun i => w.getD i false).all id) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hi : i < w.length := hv i (by simp)
      have ht : ∀ j ∈ is, j < w.length := fun j hj => hv j (by simp [hj])
      simp only [List.map_cons, List.any_cons, List.all_cons, id_eq, dualRead w i hi,
        ih ht, Bool.not_and]

private theorem origAndInvalid (w : List Bool) (is : List ℕ)
    (hv : ¬ ∀ i ∈ is, i < w.length) :
    (is.map fun i => w.getD i false).all id = false := by
  push Not at hv
  obtain ⟨i, hi, hInvalid⟩ := hv
  apply List.all_eq_false.mpr
  refine ⟨w.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
  rw [List.getD_eq_default w false hInvalid]
  decide

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem dualValue (w : List Bool) (g : Gate) (hg : Allowed g) :
    gateValue (w.map (!·)) (dualGate w.length g) = !(gateValue w g) := by
  obtain ⟨op, is⟩ := g
  cases op with
  | and =>
      by_cases hv : ∀ i ∈ is, i < w.length
      · simp only [dualGate, ite_eq_left hv, gateValue, GateOp.eval]
        exact dualAndValid w is hv
      · simp only [dualGate, ite_eq_right hv, gateValue, GateOp.eval, origAndInvalid w is hv]
        rfl
  | or => simpa [dualGate, gateValue, GateOp.eval] using dualOr w is
  | not =>
      cases is with
      | nil => rfl
      | cons i is =>
          by_cases hi : i < w.length
          · simp [dualGate, hi, gateValue, GateOp.eval]
          · simp [dualGate, hi, gateValue, GateOp.eval]
  | mod r => simp [Allowed] at hg
  | maj => simp [Allowed] at hg

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

private theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp [ih, step_length, Nat.add_comm, Nat.add_left_comm]

private theorem fold_dual (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    (dualList w.length gs).foldl step (w.map (!·)) = (gs.foldl step w).map (!·) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      have hStep : step (w.map (!·)) (dualGate w.length g) = (step w g).map (!·) := by
        simp [step, dualValue w g (h g (by simp))]
      simp only [dualList, List.foldl_cons, hStep, ← step_length w g]
      exact ih (step w g) (fun g₀ hg₀ => h g₀ (by simp [hg₀]))

end PEqualNP.Outside.L_meta_1325_aux.Dual

namespace PEqualNP.Outside.L_meta_1325_aux

open PEqualNP.CircuitLowerBounds Dual in
theorem dualForGates : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates h
  refine ⟨dualList n gates, dualList_length n gates, dualList_allowed n gates h,
    dualList_not n gates, ?_⟩
  intro i x hi
  let w := List.ofFn fun p : Fin n => !x p
  have hw : w.length = n := List.length_ofFn
  have hmap : w.map (!·) = List.ofFn x := by
    simp [w, List.map_ofFn, Function.comp_def]
  change ((dualList n gates).foldl step (List.ofFn x)).getD i false =
    !((gates.foldl step w).getD i false)
  rw [← hmap, ← hw, fold_dual gates w h]
  apply dualRead
  simpa [fold_length, hw] using hi

end PEqualNP.Outside.L_meta_1325_aux

namespace PEqualNP.Outside.L_meta_1325_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Ladder.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end Ladder.Helpers

namespace Ladder.Helpers

open PEqualNP.CircuitLowerBounds

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

end Ladder.Helpers

namespace Ladder.OneNot

open PEqualNP.CircuitLowerBounds Ladder.Helpers

theorem on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

theorem on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

theorem on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

theorem on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

theorem on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

theorem on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

theorem on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

end Ladder.OneNot

namespace Ladder.OneNot

open PEqualNP.CircuitLowerBounds Ladder.Helpers

def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

theorem on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

theorem on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

theorem on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem on1_restrict_down : ∀ (n : ℕ) (a : Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨gates.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => x i && decide (i ∈ a))) := by
  intro n a gates
  refine ⟨fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else n + gates.length)
    else i, ?_⟩
  intro o x
  set r : ℕ → ℕ := fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else
    n + gates.length) else i with hr
  show (wiresFrom (gates.map (on1_relabel r)) (List.ofFn x)).getD (r o) false
    = (wiresFrom gates (List.ofFn (fun i => x i && decide (i ∈ a)))).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [on1_getD_ofFn _ _ hi]
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · simp [hr, hi, ha]
    · simp only [hr, hi, ha, dite_true, ite_false]
      rw [List.getD_eq_default _ _ (by simp)]; simp
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · left; simp [hr, hi, ha]
    · right; simp [hr, hi, ha]
  · intro k _
    simp [hr]
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    simp [hr, show ¬ i < n by omega]; omega

theorem on1_restrict_up : ∀ (n : ℕ) (b : Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
              PEqualNP.CircuitLowerBounds.Gate) ::
            gates.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
              PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => x i || decide (i ∈ b))) := by
  intro n b gates
  refine ⟨fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ b then n else i) else i + 1, ?_⟩
  intro o x
  set r : ℕ → ℕ := fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ b then n else i)
    else i + 1 with hr
  have e : (List.ofFn x).getD n false = false := List.getD_eq_default _ _ (by simp)
  show (wiresFrom (gates.map (on1_relabel r)) (List.ofFn x ++ [true])).getD (r o) false
    = (wiresFrom gates (List.ofFn (fun i => x i || decide (i ∈ b)))).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [on1_getD_ofFn _ _ hi]
    by_cases hb : (⟨i, hi⟩ : Fin n) ∈ b
    · simp only [hr, hi, hb, dite_true, ite_true]
      have := getD_snoc_eq (List.ofFn x) true false
      simp only [List.length_ofFn] at this
      rw [this]; simp
    · simp only [hr, hi, hb, dite_true, ite_false]
      rw [on1_getD_append_left _ _ _ (by simpa using hi), on1_getD_ofFn _ _ hi]; simp
  · intro i hi
    simp only [List.length_ofFn] at hi
    left
    by_cases hb : (⟨i, hi⟩ : Fin n) ∈ b
    · simp [hr, hi, hb]
    · simp [hr, hi, hb]; omega
  · intro k _
    simp [hr]; omega
  · intro i hi
    simp only [List.length_ofFn] at hi
    simp [hr, show ¬ i < n by omega]; omega

end Ladder.OneNot

namespace Ladder.OneNot

open PEqualNP.CircuitLowerBounds Ladder.Helpers

def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

theorem on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

theorem on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

theorem on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

theorem on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

theorem on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

theorem on1_piece_u : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ post.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
            PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins
  set p := pre.length
  refine ⟨fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1, ?_⟩
  intro o x h
  set r : ℕ → ℕ := fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1 with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = n + p := by rw [hv, length_wiresFrom]; simp [p]
  set nv := GateOp.not.eval (ins.map fun i => v.getD i false) with hnv
  have hnv0 : nv = false := by
    rw [hnv]; simp only [GateOp.eval]; rw [show v = Circuit.wires ⟨pre, 0⟩ (List.ofFn x) from rfl,
      h]; rfl
  unfold Circuit.eval
  rw [List.append_cons, on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0,
    on1_wires_append _ _ _ 0]
  show (wiresFrom (post.map (on1_relabel r)) v).getD (r o) false
    = (wiresFrom post (v ++ [nv])).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi
    by_cases hlt : i < n + p
    · simp only [hr, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hi' : i = n + p := by omega
      subst hi'
      simp only [hr, lt_irrefl, ite_false, ite_true]
      rw [List.getD_eq_default _ _ (by omega), ← hvl, getD_snoc_eq, hnv0]
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < n + p
    · left; simp [hr, hlt]
    · right; have hi' : i = n + p := by omega
      subst hi'; simp [hr]
  · intro k _
    simp only [List.length_append, List.length_singleton, hvl, hr]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr]
    split_ifs <;> omega

end Ladder.OneNot

namespace Ladder.OneNot

open PEqualNP.CircuitLowerBounds

theorem on1_split : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) := by
  intro gates hops huniq
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.not
  · right
    obtain ⟨g, hg, hop⟩ := hex
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hg

    have hslot : ((s ++ g :: t).get ⟨s.length, by simp⟩).op = GateOp.not := by
      simp [hop]
    have nf : ∀ g' ∈ s ++ g :: t, g'.op ≠ GateOp.not → (g'.op = GateOp.and ∨
        g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg' hne
      obtain ⟨h1 | h1 | h1, h2⟩ := hops g' hg'
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 hne
    refine ⟨s, t, g.inputs, ?_, ?_, ?_⟩
    · cases g with
      | mk op ins => simp only at hop; subst hop; rfl
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by simp [List.getElem_append_left hi, hn]) hslot
      simp only [Fin.mk.injEq] at this; omega
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨s.length + 1 + i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp only [show s.length + 1 + i - s.length = i + 1 by omega,
            List.getElem_cons_succ]
          exact hn) hslot
      simp only [Fin.mk.injEq] at this; omega
  · left
    intro g hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops g hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨g, hg, h1⟩ hex

end Ladder.OneNot

namespace Ladder.FewNot

def fewNotBound (m q s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (if b' = 0 then m else m - (b' * q + 1)) * min K' q)
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (min K' (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fn_G_zero (m q b K : ℕ) :
    fewNotBound m q 0 b K = (if b = 0 then m else m - (b * q + 1)) * min K q := rfl

theorem fn_G_succ (m q s b K : ℕ) :
    fewNotBound m q (s + 1) b K =
      (List.range (min K (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (fewNotBound m q s (b + j) (K - j))
          (fewNotBound m q s b j))) 0 := rfl

theorem fn_le_foldr_max {f : ℕ → ℕ} {r j : ℕ} (hj : j ∈ List.range r) :
    f j ≤ (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 := by
  suffices H : ∀ l : List ℕ, j ∈ l → f j ≤ l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 from
    H _ hj
  intro l hl
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hl with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih h) (le_max_left _ _)

theorem fn_foldr_max_le {f : ℕ → ℕ} {r c : ℕ} (h : ∀ j ∈ List.range r, f j ≤ c) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c := by
  suffices H : ∀ l : List ℕ, (∀ j ∈ l, f j ≤ c) →
      l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c from H _ h
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (ih fun j hj => hl j (List.mem_cons_of_mem a hj)) (hl a List.mem_cons_self)

theorem fn_val_one : fewNotBound 73 8 1 0 73 = 292 := by decide

theorem fn_val_two : fewNotBound 73 8 2 0 73 = 112 := by decide

end Ladder.FewNot

namespace Ladder.FewNot

open PEqualNP.CircuitLowerBounds

def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

def PSub : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1)

def PSplit : Prop :=
  ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), s = s' + 1 ∧ gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post ∧ ins.length ≤ 2 ∧ (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ g' : PEqualNP.CircuitLowerBounds.Gate, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g'.inputs.length ≤ 2 → (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length, ∀ i : Fin (pre ++ g' :: post).length, ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s', ι' j = i

def H713 : Prop :=
  ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r

def Fam (n m q : ℕ) (S : Fin m → Finset (Fin n)) : Prop :=
  (∀ i : Fin m, (S i).card = q + 1) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) ∧
  (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1)

def OpsOK (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

def AndOr2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def NotAtMost (s : ℕ) (gates : List Gate) : Prop :=
  ∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin s, ι j = i

def Win {n : ℕ} (y : Finset (Fin n)) (K : ℕ) (x : Fin n → Bool) : Prop :=
  (∀ p ∈ y, x p = true) ∧ (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K

def Right {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) →
    (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K →
    Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)

theorem fnp_right_iff_win {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates : List Gate) (out : Fin m → ℕ) :
    Right S y K gates out ↔ ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → Win y K x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) :=
  ⟨fun h w x hd hw => h w x hd hw.1 hw.2, fun h w x hd h1 h2 => h w x hd ⟨h1, h2⟩⟩

def Claim (n m q : ℕ) (S : Fin m → Finset (Fin n)) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotBound m q s b K ≤ gates.length

def BoundPlane : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) →
    (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1) →
    ∀ s : ℕ, Claim n m q S s

def TargetPlane : Prop := H270 → H669 → BoundPlane

def PCount : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), Fam n m q S → ∀ (b : ℕ) (y : Finset (Fin n)),
    y.card ≤ b → (if b = 0 then m else m - (b * q + 1)) ≤
      (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card

def fewNotGenG (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (m - kappa b') * min K' (d - 1))
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (K' + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fnp_genG_zero (m d : ℕ) (kappa : ℕ → ℕ) (b K : ℕ) :
    fewNotGenG m d kappa 0 b K = (m - kappa b) * min K (d - 1) := rfl

theorem fnp_genG_succ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) :
    fewNotGenG m d kappa (s + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (fewNotGenG m d kappa s (b + j) (K - j))
        (fewNotGenG m d kappa s b j))) 0 := rfl

def FamG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) : Prop :=
  (∀ i : Fin m, (S i).card = d) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
    (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ kappa b)

def ClaimG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotGenG m d kappa s b K ≤ gates.length

def BoundG : Prop :=
  ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ), FamG n m d S kappa →
    ∀ s : ℕ, ClaimG n m d S kappa s

def PSplitS : Prop :=
  ∀ (gates : List Gate) (s : ℕ), OpsOK gates → NotAtMost (s + 1) gates →
    NotAtMost s gates ∨
    ∃ (pre post : List Gate) (ins : List ℕ),
      gates = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧ AndOr2 pre ∧
      OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post)

theorem fnp_splitS (h : PSplit) : PSplitS := by
  intro gates s hops hnot
  rcases h (s + 1) gates hops hnot with hno | ⟨s', pre, post, ins, hs, heq, _, hpre, hvar⟩
  · left
    obtain ⟨ι, _⟩ := hnot
    refine ⟨fun _ => ι 0, fun i hi => ?_⟩
    rcases (hno _ (List.get_mem gates i)).1 with h' | h' <;> rw [h'] at hi <;> cases hi
  · obtain rfl : s' = s := by omega
    right
    have ha := hvar { op := GateOp.and, inputs := [] } (Or.inl rfl) (by simp)
    have ho := hvar { op := GateOp.or, inputs := [] } (Or.inr rfl) (by simp)
    exact ⟨pre, post, ins, heq, hpre, ha.1, ho.1, ha.2, ho.2⟩

def H669at : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (y : Finset (Fin n)), AndOr2 gates →
    ∃ (gates' : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      gates'.length ≤ gates.length ∧ ∀ o : ℕ,
      (∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i)) ≠
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x' i))) →
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i))

theorem fnp_669_at (h : H669) : H669at := fun n gates y hg => h n gates y ∅ hg

def PBaseG : Prop :=
  H270 → H669at → PSub → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ClaimG n m d S kappa 0

def PStepG : Prop :=
  PSplitS → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ∀ s : ℕ, ClaimG n m d S kappa s → ClaimG n m d S kappa (s + 1)

def PMono : Prop :=
  ∀ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ),
    fewNotGenG m d kappa s b K ≤ fewNotGenG m d kappa s b (K + 1) ∧
    fewNotGenG m d kappa (s + 1) b K ≤ fewNotGenG m d kappa s b K ∧
    ((∀ b', kappa b' ≤ kappa (b' + 1)) → fewNotGenG m d kappa s (b + 1) K ≤ fewNotGenG m d kappa s b K)

theorem fnp_assemblyG (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG) :
    H270 → H669 → BoundG := by
  intro h270 h669 n m d S kappa hF s
  induction s with
  | zero => exact hB h270 (fnp_669_at h669) hS n m d S kappa hF
  | succ s ih => exact hSt (fnp_splitS hSp) n m d S kappa hF s ih

theorem fnp_variant_length (pre post : List Gate) (g g' : Gate) :
    (pre ++ g :: post).length = (pre ++ g' :: post).length := by simp

def kappaPlane (q : ℕ) : ℕ → ℕ := fun b => if b = 0 then 0 else b * q + 1

end Ladder.FewNot

namespace Ladder.FewNot

open PEqualNP.CircuitLowerBounds

theorem fnb_andOr2_of_not0 (gates : List Gate) (hops : OpsOK gates)
    (hn : NotAtMost 0 gates) : AndOr2 gates := by
  intro g hg
  obtain ⟨ι, hι⟩ := hn
  refine ⟨?_, (hops g hg).2⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  rcases (hops _ hg).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨j, _⟩ := hι i h
    exact j.elim0

theorem fnb_card_disj {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ)
    (hF : FamG n m d S kappa) (b : ℕ) (y : Finset (Fin n)) (hy : y.card ≤ b) :
    m - kappa b ≤ (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card := by
  have hk := hF.2.2 b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

def fnb_force {n : ℕ} (y : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i

theorem fnb_right_force {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) (hr : Right S y K gates out) (w : Fin m)
    (hw : Disjoint (S w) y) (x : Fin n → Bool)
    (hx : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K) :
    Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) =
      decide (∃ v ∈ S w, x v = true) := by
  have hv : ∀ v ∈ S w, fnb_force y x v = x v := fun v hv => by
    have : v ∉ y := Finset.disjoint_left.mp hw hv
    simp [fnb_force, this]
  rw [hr w (fnb_force y x) hw (fun p hp => by simp [fnb_force, hp]) ?_]
  · simp only [decide_eq_decide]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [← hv v h1]; exact h2⟩,
      fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [hv v h1]; exact h2⟩⟩
  · refine le_trans (Finset.card_le_card ?_) hx
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    simpa [fnb_force, h2] using h1

theorem fnb_card_single {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hc
  rw [ha, hc]

theorem fnb_main : PBaseG := by
  intro h270 h669 hsub n m d S kappa hF b K y gates out hy hops hnot hright
  rw [fnp_genG_zero]
  rcases Nat.eq_zero_or_pos (min K (d - 1)) with h0 | hpos
  · rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  obtain ⟨hK, hd⟩ := Nat.lt_min.mp hpos
  obtain ⟨gates', r, hg', hlen, hcomp⟩ := h669 n gates y (fnb_andOr2_of_not0 gates hops hnot)
  obtain ⟨m', e, hm', _, hiff, hcard', hpair'⟩ :=
    hsub n m (d - 1) S y (fun i => by rw [hF.1 i]; omega) hF.2.1
  have hc : ∀ w : Fin m, Disjoint (S w) y → ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K →
      Circuit.eval ⟨gates', r (out w)⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w hw x hx
    have hne : ∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) ≠
          Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x')) := by
      obtain ⟨p, hp⟩ : (S w).Nonempty := by
        rw [← Finset.card_pos, hF.1 w]
        omega
      refine ⟨fun _ => false, fun q => decide (q = p), ?_⟩
      rw [fnb_right_force S y K gates out hright w hw _ (by simp),
        fnb_right_force S y K gates out hright w hw _ ((fnb_card_single p).trans hK)]
      have h2 : ∃ v ∈ S w, decide (v = p) = true := ⟨p, hp, by simp⟩
      rw [decide_eq_true h2]
      simp
    have h1 := hcomp (out w) hne x
    exact h1.trans (fnb_right_force S y K gates out hright w hw x hx)
  have hdisj : ∀ i : Fin m', Disjoint (S (e i)) y := fun i => (hiff (e i)).mpr ⟨i, rfl⟩
  have key := h270 n m' K (fun i => S (e i)) ⟨gates', 0⟩ (fun i => r (out (e i)))
    (fun _ => min K (d - 1)) hpair' (fun i => by rw [hcard' i]; omega) hg'
    (fun i p => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = true ↔ _
      rw [hc (e i) (hdisj i) _ ((fnb_card_single p).trans hK)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = false
      rw [hc (e i) (hdisj i) x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv
      simp [hz v hv])
    (fun _ => min_le_left _ _) (fun i => by rw [hcard' i]; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at key
  have hm : m - kappa b ≤ m' := hm' ▸ fnb_card_disj S kappa hF b y hy
  calc (m - kappa b) * min K (d - 1) ≤ m' * min K (d - 1) := Nat.mul_le_mul_right _ hm
    _ ≤ gates'.length := key
    _ ≤ gates.length := hlen

end Ladder.FewNot

namespace Ladder.FewNot

open PEqualNP.CircuitLowerBounds

def fns_hv {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false

theorem fns_right_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    {j K : ℕ} (hj : j ≤ K) (gates : List Gate) (out : Fin m → ℕ)
    (h : Right S y K gates out) : Right S y j gates out :=
  fun w x hd h1 h2 => h w x hd h1 (le_trans h2 hj)

theorem fns_right_congr {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ)
    (hag : ∀ x : Fin n → Bool, Win y K x → ∀ o : ℕ,
      Circuit.eval ⟨gates', o⟩ (List.ofFn x) = Circuit.eval ⟨gates, o⟩ (List.ofFn x))
    (h : Right S y K gates out) : Right S y K gates' out := by
  intro w x hd h1 h2
  rw [hag x ⟨h1, h2⟩ (out w)]
  exact h w x hd h1 h2

theorem fns_card_true {n : ℕ} (y : Finset (Fin n)) (b j : ℕ) (hy : y.card ≤ b)
    (x : Fin n → Bool) (hx : Win y j x) :
    (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ b + j := by
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true) ⊆
      y ∪ Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hpy : p ∈ y
    · exact Finset.mem_union_left _ hpy
    · exact Finset.mem_union_right _ (by simp [hp, hpy])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ b + j := Nat.add_le_add hy hx.2

theorem fns_win_above {n : ℕ} (y : Finset (Fin n)) {j K : ℕ} (hj : j ≤ K)
    (x0 : Fin n → Bool) (hx0 : Win y j x0) (x : Fin n → Bool)
    (hx : Win (Finset.univ.filter (fun p : Fin n => x0 p = true)) (K - j) x) :
    Win y K x := by
  refine ⟨fun p hp => hx.1 p (by simp [hx0.1 p hp]), ?_⟩
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) ⊆
      Finset.univ.filter (fun p : Fin n => x0 p = true ∧ p ∉ y) ∪
      Finset.univ.filter (fun p : Fin n => x p = true ∧
        p ∉ Finset.univ.filter (fun p : Fin n => x0 p = true)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : x0 p = true
    · exact Finset.mem_union_left _ (by simp [h0, hp.2])
    · exact Finset.mem_union_right _ (by simp [h0, hp.1])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ j + (K - j) := Nat.add_le_add hx0.2 hx.2
    _ = K := by omega

theorem fns_right_base {n m : ℕ} (S : Fin m → Finset (Fin n)) (y y' : Finset (Fin n))
    (hyy : y ⊆ y') (K K' : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (hwin : ∀ x : Fin n → Bool, Win y' K' x → Win y K x)
    (h : Right S y K gates out) : Right S y' K' gates out := by
  intro w x hd h1 h2
  have hw := hwin x ⟨h1, h2⟩
  exact h w x (Finset.disjoint_of_subset_right hyy hd) hw.1 hw.2

theorem fns_term_split {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ)
    (ih : ClaimG n m d S kappa s) (b K : ℕ) (y : Finset (Fin n)) (out : Fin m → ℕ)
    (hy : y.card ≤ b) (pre post : List Gate) (ins : List ℕ)
    (hpre : AndOr2 pre)
    (hopsA : OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hopsO : OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hnA : NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hnO : NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hR : Right S y K (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post) out)
    (j : ℕ) (hj : j ≤ K) :
    min (fewNotGenG m d kappa s (b + j) (K - j)) (fewNotGenG m d kappa s b j) ≤
      (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post).length := by
  classical
  by_cases hex : ∃ x0 : Fin n → Bool, Win y j x0 ∧ fns_hv pre ins x0 = true
  · obtain ⟨x0, hx0, hv⟩ := hex
    set y' := Finset.univ.filter (fun p : Fin n => x0 p = true) with hy'
    have hyy : y ⊆ y' := fun p hp => by simp [hy', hx0.1 p hp]
    have hRy := fns_right_base S y y' hyy K (K - j) _ out
      (fun x hx => fns_win_above y hj x0 hx0 x hx) hR
    have hRO : Right S y' (K - j)
        (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y' (K - j) _ _ out ?_ hRy
      intro x hx o
      apply OneNot.on1_piece_u_cheap
      exact OneNot.on1_piece_h n pre ins hpre x0 x
        (fun i hi => hx.1 i (by simp [hy', hi])) hv
    have := ih (b + j) (K - j) y' _ out (fns_card_true y b j hy x0 hx0) hopsO hnO hRO
    rw [fnp_variant_length pre post _ ({ op := GateOp.or, inputs := [] } : Gate)]
    exact le_trans (min_le_left _ _) this
  · have hRA : Right S y j
        (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y j _ _ out ?_ (fns_right_mono S y hj _ out hR)
      intro x hx o
      apply OneNot.on1_piece_d
      have hf : ¬ fns_hv pre ins x = true := fun ht => hex ⟨x, hx, ht⟩
      simpa [fns_hv] using hf
    have := ih b j y _ out hy hopsA hnA hRA
    rw [fnp_variant_length pre post _ ({ op := GateOp.and, inputs := [] } : Gate)]
    exact le_trans (min_le_right _ _) this

theorem fns_main : PStepG := by
  intro hsplit n m d S kappa _hF s ih b K y gates out hy hops hnot hR
  rw [fnp_genG_succ]
  apply fn_foldr_max_le
  intro j hjr
  have hj : j ≤ K := by
    have := List.mem_range.mp hjr
    omega
  rcases hsplit gates s hops hnot with hle | ⟨pre, post, ins, heq, hpre, hopsA, hopsO, hnA, hnO⟩
  · exact le_trans (min_le_right _ _) (ih b j y gates out hy hops hle (fns_right_mono S y hj _ out hR))
  · subst heq
    exact fns_term_split S kappa s ih b K y out hy pre post ins hpre hopsA hopsO hnA hnO hR j hj

end Ladder.FewNot

namespace Ladder.FewNot

theorem fn_family_reindex (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ (m' : ℕ) (e : Fin m' → Fin m),
      m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧
      Function.Injective e ∧
      (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧
      (∀ i : Fin m', (S (e i)).card = q + 1) ∧
      (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  classical
  set F := Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) with hF
  let f := F.orderEmbOfFin (rfl : F.card = F.card)
  refine ⟨F.card, fun i => f i, rfl, f.injective, ?_, fun i => hcard _, ?_⟩
  · intro w
    have hr : Set.range f = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    constructor
    · intro hw
      have : w ∈ (F : Set (Fin m)) := by simp [hF, hw]
      rw [← hr] at this
      exact this
    · rintro ⟨i, rfl⟩
      have : f i ∈ (F : Set (Fin m)) := hr ▸ Set.mem_range_self i
      simpa [hF] using this
  · intro i j hij
    exact hmeet _ _ (fun h => hij (f.injective h))

end Ladder.FewNot

namespace Ladder.FewNot

open PEqualNP.CircuitLowerBounds

theorem fn_split_getElem?_ne (pre post : List Gate) (a b : Gate) (i : ℕ)
    (hi : i ≠ pre.length) : (pre ++ b :: post)[i]? = (pre ++ a :: post)[i]? := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem fn_split_count (t : ℕ) (pre post : List Gate) (a b : Gate)
    (hb : b.op ≠ GateOp.not)
    (ι : Fin (t + 1) → Fin (pre ++ a :: post).length)
    (hι : ∀ i : Fin (pre ++ a :: post).length, ((pre ++ a :: post).get i).op = GateOp.not →
      ∃ j : Fin (t + 1), ι j = i)
    (j0 : Fin (t + 1)) (hj0 : (ι j0).val = pre.length) :
    ∃ ι' : Fin t → Fin (pre ++ b :: post).length,
      ∀ i : Fin (pre ++ b :: post).length, ((pre ++ b :: post).get i).op = GateOp.not →
        ∃ j : Fin t, ι' j = i := by
  have hlen : (pre ++ b :: post).length = (pre ++ a :: post).length := by simp
  refine ⟨fun j => ⟨(ι (j0.succAbove j)).val, by have := (ι (j0.succAbove j)).isLt; omega⟩, ?_⟩
  intro i hi
  have hne : i.val ≠ pre.length := by
    intro h
    apply hb
    have : (pre ++ b :: post).get i = b := by
      simp only [List.get_eq_getElem, h, List.getElem_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem_cons_zero]
    rw [← this]; exact hi
  have hget : (pre ++ a :: post).get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ b :: post).get i := by
    have := fn_split_getElem?_ne pre post a b i.val hne
    simp only [List.get_eq_getElem]
    rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem (by have := i.isLt; omega)] at this
    exact (Option.some.inj this).symm
  obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
  have hjne : j ≠ j0 := by
    rintro rfl
    apply hne
    rw [← hj0, hj]
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjne
  refine ⟨j', ?_⟩
  apply Fin.ext
  simp only [hj]

theorem fn_split_first : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      1 ≤ s ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ∨
          g' = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }) →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin (s - 1) → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin (s - 1), ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    have hs : 1 ≤ s := by
      rcases s with _ | t
      · exact j0.elim0
      · omega
    refine ⟨pre, post, (gates[k]).inputs, hsplit', ?_, hs, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg'
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with rfl | rfl <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h; rcases hg' with rfl | rfl <;> simp
          · exact hops g (by rw [hsplit]; simp [h])
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

theorem fn_split_general : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      s = s' + 1 ∧
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      ins.length ≤ 2 ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        g'.inputs.length ≤ 2 →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin s', ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
      rcases s with _ | t
      · exact j0.elim0
      · exact ⟨t, rfl⟩
    refine ⟨t, pre, post, (gates[k]).inputs, rfl, hsplit',
      (hops gates[k] (List.getElem_mem hk)).2, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg' hg'len
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with h | h <;> rw [h] <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h
            rcases hg' with h | h
            · exact ⟨Or.inl h, hg'len⟩
            · exact ⟨Or.inr (Or.inl h), hg'len⟩
          · exact hops g (by rw [hsplit]; simp [h])
      · have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ =
              (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

end Ladder.FewNot

theorem Ladder.L708 : ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) :=
  fun n m q S y hcard hmeet =>
    Ladder.FewNot.fn_family_reindex n m q S y hcard hmeet

theorem Ladder.L709 : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), s = s' + 1 ∧ gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post ∧ ins.length ≤ 2 ∧ (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ g' : PEqualNP.CircuitLowerBounds.Gate, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g'.inputs.length ≤ 2 → (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length, ∀ i : Fin (pre ++ g' :: post).length, ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s', ι' j = i :=
  Ladder.FewNot.fn_split_general

open PEqualNP.CircuitLowerBounds

namespace Ladder.L270

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := by
    cases h : g.inputs with
    | nil => simp [h] at hlen
    | cons a rest =>
      cases rest with
      | nil => simp [h] at hlen
      | cons b tail =>
        have : tail = [] := by simpa [h] using hlen
        exact ⟨a, b, by simp [this]⟩
  let P := ({a, b} : Finset ℕ).filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ?_, ?_, ?_⟩
  · by_cases h : a = b <;> simp [h, Finset.card_insert_of_notMem]
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ ({a, b} : Finset ℕ)) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨hr, h⟩)
      · simp [h]
    have ha := hr a (by simp)
    have hb := hr b (by simp)
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          [if a < w then value C z a else false, if b < w then value C z b else false] := by
      simpa [g, hab] using gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        Bool.and_eq_true] at hx ⊢
      exact ⟨ha hx.1, hb hx.2⟩
    · simp only [hop, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        Bool.or_eq_true] at hx ⊢
      exact hx.imp ha hb

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

private lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

private def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

private lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

private lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

private def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

private lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ T.card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue

end Ladder.L270

open Ladder.L270 in
theorem Ladder.L270 :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n),
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hG ho hsparse hk hc
  let G (i : Fin m) := assigned C (S i)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
    have hle := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      card_assigned C (S i) (o i) hG (ho i) (hsparse i) (hk i) (hc i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

namespace Ladder.L669

open PEqualNP.CircuitLowerBounds

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
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ gates.length ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hg
  have hρ : ∀ i : Fin n,
      (∃ c : Bool, ∀ x : Fin n → Bool,
        (if i ∈ T then true else if i ∈ Z then false else x i) = c) ∨
      (∀ x : Fin n → Bool, (if i ∈ T then true else if i ∈ Z then false else x i) = x i) := by
    intro i
    by_cases h1 : i ∈ T
    · exact Or.inl ⟨true, fun x => by rw [if_pos h1]⟩
    · by_cases h2 : i ∈ Z
      · exact Or.inl ⟨false, fun x => by rw [if_neg h1, if_pos h2]⟩
      · exact Or.inr (fun x => by rw [if_neg h1, if_neg h2])
  exact inv_final (fun (x : Fin n → Bool) (i : Fin n) =>
    if i ∈ T then true else if i ∈ Z then false else x i) gates
    (inv_all _ hρ gates hg)

end Ladder.L669

theorem Ladder.L669 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) :=
  Ladder.L669.main_aux

namespace Ladder.L686
end Ladder.L686

open Ladder.L686 in
theorem Ladder.L686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  intro m n r S hp hr B
  classical
  let T := fun A : Finset (Fin n) => Finset.univ.filter (fun i : Fin m => ∃ x ∈ A, x ∈ S i)
  change (T B).card + B.card ≤ B.card * r + 1
  induction B using Finset.induction_on with
  | empty => simp [T]
  | @insert a B ha ih =>
    let U := Finset.univ.filter (fun i : Fin m => a ∈ S i)
    have he : T (insert a B) = U ∪ T B := by
      ext i
      simp [T, U]
    rw [he, Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
    have hu : U.card = r := hr a
    by_cases hB : B.Nonempty
    · obtain ⟨b, hb⟩ := hB
      have hab : a ≠ b := fun e => ha (e ▸ hb)
      obtain ⟨i, hi, hj⟩ := hp a b hab
      have hI : 0 < (U ∩ T B).card := Finset.card_pos.mpr ⟨i,
        Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, hj⟩⟩⟩
      have hc := Finset.card_union_add_card_inter U (T B)
      omega
    · have hE := Finset.not_nonempty_iff_eq_empty.mp hB
      subst B
      simp [T, hu]

def through {n : ℕ} (S : Fin n → Finset (Fin n)) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i)

theorem through_card {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hn : n = q*q + q + 1) (hq : 0 < q)
    (hS : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (p : Fin n) : (through S p).card = q + 1 := by
  let T := through S p
  have hdis : (T : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hpi : p ∈ S i := by simpa [T, through] using hi
    have hpj : p ∈ S j := by simpa [T, through] using hj
    have hp : p ∈ S i ∩ S j := Finset.mem_inter.mpr ⟨hpi, hpj⟩
    have ha' : a ∈ S i ∩ S j := Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase ha, Finset.mem_of_mem_erase hb⟩
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcross i j hij)
    have hpv : p = v := by simpa [hv] using hp
    have hav : a = v := by simpa [hv] using ha'
    exact (Finset.mem_erase.mp ha).1 (hav.trans hpv.symm)
  have hcover : T.biUnion (fun i => (S i).erase p) =
      (Finset.univ : Finset (Fin n)).erase p := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hmem⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hmem).1, Finset.mem_univ _⟩
    · intro ha
      have hpa : p ≠ a := Ne.symm (Finset.mem_erase.mp ha).1
      obtain ⟨i, hpi, hai⟩ := hjoin p a hpa
      exact Finset.mem_biUnion.mpr ⟨i, by simpa [T, through] using hpi,
        Finset.mem_erase.mpr ⟨Ne.symm hpa, hai⟩⟩
  have hf (i : Fin n) (hi : i ∈ T) : ((S i).erase p).card = q := by
    have hpi : p ∈ S i := by simpa [T, through] using hi
    rw [Finset.card_erase_of_mem hpi, hS]
    omega
  have hcount := Finset.card_biUnion hdis
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  calc
    (through S p).card = T.card := rfl
    _ = q + 1 := by
      have hsum : (∑ i ∈ T, ((S i).erase p).card) = T.card * q := by
        rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hsum] at hcount
      have hmul : q * T.card = q * (q+1) := by
        rw [Nat.mul_comm q T.card, ← hcount, hn]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.eq_of_mul_eq_mul_left hq hmul


open Ladder.FewNot in
lemma firstConjunct (q s : ℕ) (L : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)))
    (hq : 2 ≤ q) (hcard : ∀ i, (L i).card = q + 1)
    (hpair : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hjoin : ∀ p p', p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i)
    (gates : List Gate) (out : Fin (q^2 + q + 1) → ℕ)
    (hops : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hnot : ∃ ι : Fin s → Fin gates.length,
      ∀ i : Fin gates.length, (gates.get i).op = .not → ∃ j : Fin s, ι j = i)
    (hright : ∀ w (x : Fin (q^2 + q + 1) → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true))
    (G : ℕ → ℕ → ℕ → ℕ)
    (hzero : ∀ b K, G 0 b K =
      ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (hsucc : ∀ t b K, G (t + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) :
    G s 0 (q^2 + q + 1) ≤ gates.length := by
  classical
  let n := q^2 + q + 1
  let kappa := kappaPlane q
  have hreg (p : Fin n) : (through L p).card = q + 1 :=
    through_card L (by simp [pow_two]) (by omega) hcard hpair hjoin p
  have hF : FamG n n (q + 1) L kappa := by
    refine ⟨hcard, fun i j hij => le_of_eq (hpair i j hij), ?_⟩
    intro b y hy
    by_cases hb : b = 0
    · have hy' : y = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [hy', kappa, kappaPlane, hb]
    · have hlines := Ladder.L686 n n (q + 1) L hjoin hreg y
      have he :
          (Finset.univ.filter (fun w : Fin n => ¬ Disjoint (L w) y)) =
            Finset.univ.filter (fun w : Fin n => ∃ x ∈ y, x ∈ L w) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff]
        exact ⟨fun ⟨x, h₁, h₂⟩ => ⟨x, h₂, h₁⟩, fun ⟨x, h₁, h₂⟩ => ⟨x, h₂, h₁⟩⟩
      rw [he]
      change _ ≤ (if b = 0 then 0 else b * q + 1)
      rw [ite_eq_right hb]
      rw [Nat.mul_add, Nat.mul_one] at hlines
      have hmul := Nat.mul_le_mul_right q hy
      omega
  have hg_eq : ∀ t b K, G t b K = fewNotGenG n (q + 1) kappa t b K := by
    intro t
    induction t with
    | zero =>
        intro b K
        rw [hzero, fnp_genG_zero]
        have hmin (a b : ℕ) : a - min a b = a - b := by omega
        by_cases hb : b = 0 <;> simp [n, kappa, kappaPlane, hb, hmin]
    | succ t ih =>
        intro b K
        rw [hsucc, fnp_genG_succ]
        simp_rw [ih]
  rw [hg_eq]
  exact fnp_assemblyG Ladder.L708 Ladder.L709 fnb_main fns_main Ladder.L270 Ladder.L669
    n n (q + 1) L kappa hF s 0 n ∅ gates out (by simp) hops hnot
    (fun w x _ _ _ => hright w x)


end PEqualNP.Outside.L_meta_1325_aux

namespace PEqualNP.Outside.L_meta_1325_aux

lemma minFormFromStable {α β : Type} [DecidableEq α]
    (trace : Finset α → β) (F delta T budget : ℕ)
    (hcount : ∀ r (z : ℕ → Finset α),
      (∀ i : ℕ, i < r → z i ⊆ z (i + 1)) →
      (∀ i : ℕ, i < r → trace (z i) ≠ trace (z (i + 1))) → r ≤ F)
    (hsparse : ∀ r : ℕ, r < F → ∀ z : Finset α, z.card ≤ r * delta →
      (∀ y : Finset α, z ⊆ y → (y \ z).card ≤ delta → trace z = trace y) → T ≤ budget)
    (hfull : ∀ z : Finset α, z.card ≤ F * delta →
      (∀ y : Finset α, z ⊆ y → trace z = trace y) → T ≤ budget) :
    T ≤ budget := by
  classical
  let Valid (r : ℕ) := ∃ z : ℕ → Finset α, z 0 = ∅ ∧
    ∀ i : ℕ, i < r → z i ⊆ z (i + 1) ∧ (z (i + 1) \ z i).card ≤ delta ∧
      trace (z i) ≠ trace (z (i + 1))
  have h0 : Valid 0 := ⟨fun _ => ∅, rfl, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  let r := Nat.findGreatest Valid F
  have hr : r ≤ F := Nat.findGreatest_le _
  obtain ⟨z, hz0, hz⟩ : Valid r := Nat.findGreatest_spec (Nat.zero_le F) h0
  have hzcard : ∀ i : ℕ, i ≤ r → (z i).card ≤ i * delta := by
    intro i
    induction i with
    | zero => simp [hz0]
    | succ i ih =>
        intro hi
        obtain ⟨hsub, hdiff, _⟩ := hz i (by omega)
        rw [← Finset.card_sdiff_add_card_eq_card hsub, Nat.succ_mul]
        have hprev : (z i).card ≤ i * delta := ih (by omega)
        omega
  let extend (y : Finset α) (i : ℕ) := if i = r + 1 then y else z i
  have ext_old (y : Finset α) (i : ℕ) (hi : i ≤ r) : extend y i = z i := by
    simp [extend, show i ≠ r + 1 by omega]
  have ext_end (y : Finset α) : extend y (r + 1) = y := by simp [extend]
  have hstep (y : Finset α) (hy : z r ⊆ y) (hne : trace (z r) ≠ trace y)
      (i : ℕ) (hi : i < r + 1) :
      extend y i ⊆ extend y (i + 1) ∧ trace (extend y i) ≠ trace (extend y (i + 1)) := by
    by_cases hir : i < r
    · rw [ext_old _ _ (by omega : i ≤ r), ext_old _ _ (by omega : i + 1 ≤ r)]
      exact ⟨(hz i hir).1, (hz i hir).2.2⟩
    · have e : i = r := by omega
      subst i
      rw [ext_old _ _ le_rfl, ext_end]
      exact ⟨hy, hne⟩
  by_cases hlt : r < F
  · refine hsparse r hlt (z r) (hzcard r le_rfl) ?_
    intro y hy hd
    by_contra hne
    have hvalid : Valid (r + 1) := by
      refine ⟨extend y, (ext_old _ _ (Nat.zero_le r)).trans hz0, ?_⟩
      intro i hi
      have ht := hstep y hy hne i hi
      refine ⟨ht.1, ?_, ht.2⟩
      by_cases hir : i < r
      · rw [ext_old _ _ (by omega : i ≤ r), ext_old _ _ (by omega : i + 1 ≤ r)]
        exact (hz i hir).2.1
      · have e : i = r := by omega
        subst i
        rw [ext_old _ _ le_rfl, ext_end]
        exact hd
    exact (Nat.findGreatest_is_greatest (P := Valid) (show r < r + 1 by omega)
      (show r + 1 ≤ F by omega)) hvalid
  · have heq : r = F := by omega
    refine hfull (z r) ?_ ?_
    · simpa only [heq] using hzcard r le_rfl
    · intro y hy
      by_contra hne
      have hbad := hcount (r + 1) (extend y)
        (fun i hi => (hstep y hy hne i hi).1)
        (fun i hi => (hstep y hy hne i hi).2)
      omega

end PEqualNP.Outside.L_meta_1325_aux

namespace PEqualNP.Outside.L_meta_1325_aux.Frontier

private def spent (A : Finset ℕ) (b : ℕ) : ℕ := (A.filter (· < b)).card

private lemma spent_succ (A : Finset ℕ) (b : ℕ) :
    spent A (b + 1) = spent A b + if b ∈ A then 1 else 0 := by
  classical
  by_cases hb : b ∈ A
  · have he : A.filter (· < b + 1) = insert b (A.filter (· < b)) := by
      ext w
      by_cases h : w = b
      · subst w
        simp [hb]
      · by_cases hw : w ∈ A <;> simp [h, hw] <;> omega
    simp only [spent, he, hb, ite_true]
    exact Finset.card_insert_of_notMem (by simp)
  · have he : A.filter (· < b + 1) = A.filter (· < b) := by
      ext w
      by_cases h : w = b
      · subst w
        simp [hb]
      · by_cases hw : w ∈ A <;> simp [hw] <;> omega
    simp only [spent, he, ite_eq_right hb, Nat.add_zero]

theorem shrink {X : Type*} (V : X → ℕ → Prop) (r : X) (terminal : ℕ → Prop)
    (A : Finset ℕ)
    (expand : ∀ w, V r w → ¬terminal w →
      ∃ K : Finset ℕ, K ⊆ Finset.range w ∧ (∀ v ∈ K, V r v) ∧
        (∀ x, (∀ v ∈ K, V x v) → V x w) ∧ K.card ≤ 1 + (if w ∈ A then 1 else 0)) :
    ∀ (b : ℕ) (W : Finset ℕ), W ⊆ Finset.range b → (∀ w ∈ W, V r w) →
      ∃ T : Finset ℕ, T ⊆ Finset.range b ∧ T.card ≤ W.card + spent A b ∧
        (∀ w ∈ T, terminal w ∧ V r w) ∧
        ∀ x, (∀ w ∈ T, V x w) → ∀ w ∈ W, V x w := by
  classical
  intro b
  induction b with
  | zero =>
    intro W hW _
    have h : W = ∅ := by simpa using hW
    subst W
    exact ⟨∅, Finset.empty_subset _, by simp, by simp, by simp⟩
  | succ b ih =>
    intro W hW hval
    have rise : Finset.range b ⊆ Finset.range (b + 1) := Finset.range_mono (by omega)
    by_cases hb : b ∈ W
    · let U := W.erase b
      have hu : U ⊆ Finset.range b := by
        intro w hw
        obtain ⟨hne, hw'⟩ := Finset.mem_erase.mp hw
        have hlt := Finset.mem_range.mp (hW hw')
        exact Finset.mem_range.mpr (by omega)
      have huv (w : ℕ) (hw : w ∈ U) : V r w := hval w (Finset.mem_erase.mp hw).2
      have hcc : U.card + 1 = W.card := Finset.card_erase_add_one hb
      by_cases hterm : terminal b
      · obtain ⟨T, ht, hc, hTV, hForce⟩ := ih U hu huv
        refine ⟨insert b T, ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (Finset.mem_range.mpr (by omega)) (ht.trans rise)
        · have hi := Finset.card_insert_le b T
          rw [spent_succ]
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact ⟨hterm, hval _ hb⟩
          · exact hTV w hw
        · intro x hx w hw
          by_cases hwb : w = b
          · subst w
            exact hx _ (Finset.mem_insert_self ..)
          · exact hForce x (fun v hv => hx v (Finset.mem_insert_of_mem hv)) w
              (Finset.mem_erase.mpr ⟨hwb, hw⟩)
      · obtain ⟨K, hk, hkv, hForceK, hkc⟩ := expand b (hval b hb) hterm
        obtain ⟨T, ht, hc, hTV, hForce⟩ := ih (U ∪ K) (Finset.union_subset hu hk)
          (fun w hw => (Finset.mem_union.mp hw).elim (huv w) (hkv w))
        refine ⟨T, ht.trans rise, ?_, hTV, ?_⟩
        · have hU := Finset.card_union_le U K
          rw [spent_succ]
          omega
        · intro x hx w hw
          have hv := hForce x hx
          by_cases hwb : w = b
          · subst w
            exact hForceK x (fun v hk' => hv v (Finset.mem_union_right U hk'))
          · exact hv w (Finset.mem_union_left K (Finset.mem_erase.mpr ⟨hwb, hw⟩))
    · have hsub : W ⊆ Finset.range b := by
        intro w hw
        have hlt := Finset.mem_range.mp (hW hw)
        have hne : w ≠ b := fun h => hb (h ▸ hw)
        exact Finset.mem_range.mpr (by omega)
      obtain ⟨T, ht, hc, hTV, hForce⟩ := ih W hsub hval
      refine ⟨T, ht.trans rise, ?_, hTV, hForce⟩
      rw [spent_succ]
      omega

theorem root {X : Type*} (V : X → ℕ → Prop) (r : X) (terminal : ℕ → Prop)
    (A : Finset ℕ)
    (expand : ∀ w, V r w → ¬terminal w →
      ∃ K : Finset ℕ, K ⊆ Finset.range w ∧ (∀ v ∈ K, V r v) ∧
        (∀ x, (∀ v ∈ K, V x v) → V x w) ∧ K.card ≤ 1 + (if w ∈ A then 1 else 0))
    (w : ℕ) (hw : V r w) :
    ∃ T : Finset ℕ, T.card ≤ A.card + 1 ∧
      (∀ w ∈ T, terminal w ∧ V r w) ∧
      ∀ x, (∀ w ∈ T, V x w) → V x w := by
  have hsub : ({w} : Finset ℕ) ⊆ Finset.range (w + 1) := by simp
  obtain ⟨T, _, hc, ht, hforce⟩ :=
    shrink V r terminal A expand (w + 1) {w} hsub (by simpa using hw)
  have hcost : spent A (w + 1) ≤ A.card := Finset.card_filter_le _ _
  refine ⟨T, ?_, ht, fun x hx => hforce x hx _ (Finset.mem_singleton_self _)⟩
  simp only [Finset.card_singleton] at hc
  omega

end PEqualNP.Outside.L_meta_1325_aux.Frontier

namespace PEqualNP.Outside.L_meta_1325_aux.CC

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

def booleanGate : Bool → Gate
  | true => ⟨.and, []⟩
  | false => ⟨.or, []⟩

theorem booleanGate_pos (b : Bool) : Positive (booleanGate b) := by
  cases b <;> simp [Positive, booleanGate]

theorem booleanGate_runs (b : Bool) (x : List Bool) :
    gateValue x (booleanGate b) = b := by
  cases b <;> rfl

noncomputable def freezeGate (a : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then booleanGate (gateValue a g) else g

noncomputable def freeze (a : List Bool) : List Gate → List Gate
  | [] => []
  | g :: gs => freezeGate a g :: freeze (appendGate a g) gs

theorem freeze_length (gs : List Gate) (a : List Bool) : (freeze a gs).length = gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [freeze, ih]

theorem freeze_pos (gs : List Gate) (a : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ freeze a gs, Positive g := by
  induction gs generalizing a with
  | nil => simp [freeze]
  | cons g gs ih =>
    intro q hq
    rw [freeze, List.mem_cons] at hq
    rcases hq with rfl | hq
    · classical
      unfold freezeGate
      split
      · exact booleanGate_pos _
      · rename_i hn
        obtain ⟨ha | ho | hh, hf⟩ := h g (List.mem_cons_self ..)
        · exact ⟨Or.inl ha, hf⟩
        · exact ⟨Or.inr ho, hf⟩
        · exact (hn hh).elim
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ hq

theorem freeze_run (gs : List Gate) (a b z : List Bool)
    (haz : Below a z) (hzb : Below z b) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : AgreesNot gs a b) : run (freeze a gs) z = run gs z := by
  induction gs generalizing a b z with
  | nil => rfl
  | cons g gs ih =>
    rw [freeze, run_cons, run_cons]
    have hA : g ∈ g :: gs := List.mem_cons_self
    have hop := (hops g hA).1
    rcases hop with h | h | h
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inl h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inl h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inr h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inr h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have he : gateValue a g = gateValue b g := hnot.first h
      have hze : gateValue z g = gateValue a g := by
        apply Bool.eq_iff_iff.mpr
        refine ⟨gateValue_neg g h a z haz, ?_⟩
        rw [he]
        exact gateValue_neg g h z b hzb
      have hf : appendGate z (freezeGate a g) = appendGate z g := by
        classical
        unfold appendGate
        simp [freezeGate, h, booleanGate_runs, hze]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (by rw [hze]; exact id))
        (appendGate_below hzb g (by rw [hze, he]; exact id))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail


theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

noncomputable def notIndices (gs : List Gate) : Finset (Fin gs.length) := by
  classical
  exact Finset.univ.filter (fun i => (gs.get i).op = .not)

theorem mem_notIndices (gs : List Gate) (j : Fin gs.length) :
    j ∈ notIndices gs ↔ (gs.get j).op = .not := by
  classical
  simp [notIndices]

noncomputable def notEmbedding (gs : List Gate) :
    Fin (notIndices gs).card ↪o Fin gs.length :=
  (notIndices gs).orderEmbOfFin rfl

theorem notEmbedding_mem (gs : List Gate) (j : Fin (notIndices gs).card) :
    notEmbedding gs j ∈ notIndices gs :=
  (notIndices gs).orderEmbOfFin_mem rfl j

theorem exists_notEmbedding (gs : List Gate) (j : Fin gs.length)
    (hj : j ∈ notIndices gs) : ∃ i, notEmbedding gs i = j := by
  have h := (notIndices gs).range_orderEmbOfFin rfl
  change Set.range (notEmbedding gs) = _ at h
  change j ∈ Set.range (notEmbedding gs)
  rw [h]
  exact hj

theorem card_notIndices (gs : List Gate) (t : ℕ)
    (h : ∃ f : Fin t → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i) :
    (notIndices gs).card ≤ t := by
  classical
  obtain ⟨f, h⟩ := h
  have hsub : notIndices gs ⊆ Finset.univ.image f := by
    intro j hj
    obtain ⟨i, hi⟩ := h j ((mem_notIndices gs j).1 hj)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

def trace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) : Bool :=
  (run gs (List.ofFn x)).getD (n + i.val) false

theorem trace_after {n m : ℕ} (gs : List Gate) (x : Fin m → Fin n → Bool)
    (hx : ∀ a b : Fin m, a ≤ b → ∀ w, x a w = true → x b w = true)
    (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card) (a b : Fin m) (hab : a ≤ b)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs (x a) (notEmbedding gs j) = trace gs (x b) (notEmbedding gs j)) :
    trace gs (x b) (notEmbedding gs i) = true →
      trace gs (x a) (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn (x a)) (List.ofFn (x b))
    (initial_below _ _ (hx a b hab)) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn (x a))).getD ((List.ofFn (x a)).length + k) false =
      (run gs (List.ofFn (x b))).getD ((List.ofFn (x b)).length + k) false := by
    have hkl : k < gs.length := by
      apply lt_trans hk
      exact j.isLt
    let k' : Fin gs.length := ⟨k, hkl⟩
    have hget : gs.get k' = q := by simpa [k', List.getElem?_eq_getElem hkl] using hq
    obtain ⟨p, hp⟩ := exists_notEmbedding gs k'
      ((mem_notIndices gs k').2 (hget ▸ hqn))
    have hpi : p < i := by
      have hlt : notEmbedding gs p < notEmbedding gs i := by
        rw [hp]
        exact hk
      exact (notEmbedding gs).lt_iff_lt.mp hlt
    have h := hprev p hpi
    rw [hp] at h
    simpa only [trace, List.length_ofFn, k'] using h
  simpa only [trace, List.length_ofFn, j] using got earlier

theorem trace_agrees {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (h : ∀ i : Fin (notIndices gs).card,
      trace gs a (notEmbedding gs i) = trace gs b (notEmbedding gs i)) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  intro j g hj hg
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).choose
  let i : Fin gs.length := ⟨j, hlt⟩
  have he : gs.get i = g := by simpa [i, List.getElem?_eq_getElem hlt] using hj
  obtain ⟨p, hp⟩ := exists_notEmbedding gs i
    ((mem_notIndices gs i).2 (he ▸ hg))
  have hh := h p
  rw [hp] at hh
  simpa only [trace, List.length_ofFn, i] using hh

end PEqualNP.Outside.L_meta_1325_aux.CC


namespace PEqualNP.Outside.L_meta_1325_aux.CC

lemma existsCuts {t m : ℕ} (p : Fin t → Fin m → Bool)
    (h : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
      (∀ j : Fin t, j < i → p j a = p j b) → (p i b = true → p i a = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.range m ∧ P.card + 1 ≤ 2 ^ t ∧
      ∀ a b : Fin m, a ≤ b → (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) →
        ∀ i : Fin t, p i a = p i b := by
  induction t with
  | zero =>
      refine ⟨∅, by simp, by simp, ?_⟩
      intro _ _ _ _ i
      exact Fin.elim0 i
  | succ t ih =>
      let p₀ (i : Fin t) := p i.castSucc
      have h₀ : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
          (∀ j : Fin t, j < i → p₀ j a = p₀ j b) →
          (p₀ i b = true → p₀ i a = true) := by
        intro i a b hab hearlier htrue
        apply h i.castSucc a b hab ?_ htrue
        intro j hj
        have hjt : j.val < t := lt_of_lt_of_le hj i.isLt.le
        exact hearlier ⟨j.val, hjt⟩ (by exact hj)
      obtain ⟨P, hP, hp, stable⟩ := ih p₀ h₀
      have hlast {a b : Fin m} (hab : a ≤ b)
          (hgood : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) :
          p (Fin.last t) b = true → p (Fin.last t) a = true := by
        apply h (Fin.last t) a b hab
        intro j hj
        exact stable a b hab hgood ⟨j.val, hj⟩
      let value (w : ℕ) : Bool := if hw : w < m then p (Fin.last t) ⟨w, hw⟩ else false
      have value_eq (w : ℕ) (hw : w < m) : value w = p (Fin.last t) ⟨w, hw⟩ := dite_eq_left hw
      let N := (Finset.range m).filter (fun w =>
        0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false)
      have hN {w : ℕ} (hw : w ∈ N) :
          w < m ∧ 0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false := by
        have he := Finset.mem_filter.mp hw
        exact ⟨Finset.mem_range.mp he.1, he.2⟩
      let before (w : ℕ) := P.filter (fun k => k ≤ w)
      have hsep {u v : ℕ} (hu : u ∈ N) (hv : v ∈ N) (hlt : u < v) :
          (before u).card ≠ (before v).card := by
        intro he
        have hsub : before u ⊆ before v := by
          intro k hk
          obtain ⟨hkP, hku⟩ := Finset.mem_filter.mp hk
          exact Finset.mem_filter.mpr ⟨hkP, le_trans hku hlt.le⟩
        have heq : before u = before v :=
          Finset.eq_of_subset_of_card_le hsub he.ge
        have hnocut : ∀ w ∈ P, ¬ (u < w ∧ w ≤ v - 1) := by
          intro w hw hinterval
          have hwv : w ∈ before v :=
            Finset.mem_filter.mpr ⟨hw, hinterval.2.trans (Nat.sub_le ..)⟩
          rw [← heq] at hwv
          exact (not_le_of_gt hinterval.1) (Finset.mem_filter.mp hwv).2
        have huu := hN hu
        have hvv := hN hv
        have hvlt : v - 1 < m := lt_of_le_of_lt (Nat.sub_le ..) hvv.1
        have htrans := hlast
          (a := ⟨u, huu.1⟩) (b := ⟨v - 1, hvlt⟩)
          (by show u ≤ v - 1; omega) hnocut
        have htrue : value u = true := by
          rw [value_eq _ huu.1]
          apply htrans
          rw [← value_eq _ hvlt]
          exact hvv.2.2.2.1
        rw [huu.2.2.2.2] at htrue
        contradiction
      have hcount : N.card ≤ P.card + 1 := by
        simpa only [Finset.card_range] using
          (Finset.card_le_card_of_injOn
            (s := N) (t := Finset.range (P.card + 1))
            (fun w => (before w).card)
            (fun w _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
              (Finset.card_filter_le _ _)))
            (by
              intro u hu v hv he
              rcases lt_trichotomy u v with hlt | heq | hgt
              · exact False.elim (hsep hu hv hlt he)
              · exact heq
              · exact False.elim (hsep hv hu hgt he.symm)))
      refine ⟨P ∪ N, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hP hw
        · exact Finset.mem_range.mpr (hN hw).1
      · have hU := Finset.card_union_le P N
        rw [Nat.pow_succ]
        omega
      · intro a b hab hgood i
        have hprev : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val) :=
          fun w hw => hgood w (Finset.mem_union_left _ hw)
        by_cases hi : i.val < t
        · exact stable a b hab hprev ⟨i.val, hi⟩
        · have hie : i = Fin.last t := by
            apply Fin.ext
            have hi' := i.isLt
            change i.val = t
            omega
          subst i
          have hadj (w : ℕ) (haw : a.val < w) (hwb : w ≤ b.val) :
              value (w - 1) = value w := by
            have hw : w < m := hwb.trans_lt b.isLt
            have hw' : w - 1 < m := (Nat.sub_le ..).trans_lt hw
            have hpos : 0 < w := by omega
            have hpw : w ∉ P := fun hmem => hprev w hmem ⟨haw, hwb⟩
            have hnW : w ∉ N :=
              fun hmem => hgood w (Finset.mem_union_right _ hmem) ⟨haw, hwb⟩
            have hstep := hlast
              (a := ⟨w - 1, hw'⟩) (b := ⟨w, hw⟩)
              (Nat.sub_le ..)
              (by
                rintro k hk ⟨hkw, hwk⟩
                change w - 1 < k at hkw
                change k ≤ w at hwk
                have he : k = w := by omega
                exact hpw (he ▸ hk))
            have himp : value w = true → value (w - 1) = true := by
              rw [value_eq _ hw, value_eq _ hw']
              exact hstep
            cases hr : value w <;> cases hl : value (w - 1)
            · rfl
            · exact False.elim (hnW (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hw, hpos, hpw, hl, hr⟩))
            · exact False.elim (Bool.false_ne_true (hl.symm.trans (himp hr)))
            · rfl
          have hdist : ∀ d : ℕ, a.val + d ≤ b.val → value (a.val + d) = value a.val := by
            intro d
            induction d with
            | zero => simp
            | succ d ih =>
                intro hd
                have hprev' := ih (by omega)
                have hs := hadj (a.val + (d + 1)) (by omega) hd
                have he : a.val + (d + 1) - 1 = a.val + d := by omega
                rw [he] at hs
                exact hs.symm.trans hprev'
          have hab' : a.val ≤ b.val := hab
          have hdist' := hdist (b.val - a.val) (by omega)
          have he : a.val + (b.val - a.val) = b.val := by omega
          rw [he, value_eq _ b.isLt, value_eq _ a.isLt] at hdist'
          exact hdist'.symm

end PEqualNP.Outside.L_meta_1325_aux.CC

namespace PEqualNP.Outside.L_meta_1325_aux.CC

open PEqualNP.CircuitLowerBounds

def assign {n : ℕ} (Z : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∈ Z)

noncomputable def signature {n : ℕ} (gs : List Gate) (Z : Finset (Fin n)) :
    Fin (notIndices gs).card → Bool :=
  fun j => trace gs (assign Z) (notEmbedding gs j)

theorem assign_mono {n : ℕ} {Z Y : Finset (Fin n)} (h : Z ⊆ Y)
    (v : Fin n) (hv : assign Z v = true) : assign Y v = true :=
  decide_eq_true (h (of_decide_eq_true hv))

theorem distinctChain {n s r : ℕ} (gs : List Gate) (Z : ℕ → Finset (Fin n))
    (hg : ∀ g ∈ gs, Allowed g)
    (hn : ∃ f : Fin s → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i)
    (hstep : ∀ a < r, Z a ⊆ Z (a + 1))
    (hchange : ∀ a < r, signature gs (Z a) ≠ signature gs (Z (a + 1))) :
    r + 1 ≤ 2 ^ s := by
  classical
  have hz (b : ℕ) (hb : b ≤ r) : ∀ a ≤ b, Z a ⊆ Z b := by
    induction b with
    | zero =>
      intro a ha
      have h0 : a = 0 := by omega
      subst a
      exact Finset.Subset.rfl
    | succ b ih =>
      intro a ha
      by_cases h : a = b + 1
      · subst a
        exact Finset.Subset.rfl
      · exact (ih (by omega) a (by omega)).trans (hstep b (by omega))
  let x (a : Fin (r + 1)) : Fin n → Bool := assign (Z a.val)
  have hmono (a b : Fin (r + 1)) (hab : a ≤ b) : ∀ v, x a v = true → x b v = true :=
    assign_mono (hz b.val (by have := b.isLt; omega) a.val hab)
  obtain ⟨P, _, hP, hclosed⟩ :=
    existsCuts (fun j (a : Fin (r + 1)) => trace gs (x a) (notEmbedding gs j))
      (fun i a b hab h => trace_after gs x hmono hg i a b hab h)
  have hsub : (Finset.range r).image Nat.succ ⊆ P := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hir := Finset.mem_range.mp hi
    by_contra hp
    let a : Fin (r + 1) := ⟨i, by omega⟩
    let b : Fin (r + 1) := ⟨i + 1, by omega⟩
    apply hchange i hir
    funext k
    have hnocut (w : ℕ) (hw : w ∈ P) : ¬(a.val < w ∧ w ≤ b.val) := by
      intro hw'
      apply hp
      have he : w = i + 1 := by
        change i < w ∧ w ≤ i + 1 at hw'
        omega
      change i + 1 ∈ P
      rwa [← he]
    exact hclosed a b (show i ≤ i + 1 by omega) hnocut k
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Nat.succ_injective, Finset.card_range] at hc
  have hnot := card_notIndices gs s hn
  calc
    r + 1 ≤ P.card + 1 := by omega
    _ ≤ 2 ^ (notIndices gs).card := hP
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hnot

theorem freeze_assign {n : ℕ} (gs : List Gate) (Z Y : Finset (Fin n))
    (hg : ∀ g ∈ gs, Allowed g) (hsub : Z ⊆ Y)
    (htrace : signature gs Z = signature gs Y) :
    run (freeze (List.ofFn (assign Z)) gs) (List.ofFn (assign Y)) =
      run gs (List.ofFn (assign Y)) := by
  apply freeze_run
  · exact initial_below _ _ (assign_mono hsub)
  · exact initial_below _ _ (fun _ h => h)
  · exact hg
  · apply trace_agrees
    intro i
    exact congrFun htrace i

end PEqualNP.Outside.L_meta_1325_aux.CC

namespace PEqualNP.Outside.L_meta_1325_aux.Expand

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def terminal {ι : Type*} {n : ℕ} (C : Circuit) (refs : ι → Fin n → Bool)
    (i : ι) (w : ℕ) : Prop :=
  w < n ∨ ∃ j, j ≠ i ∧ value C (refs j) w = true

open Classical in
noncomputable def charges {ι : Type*} {n : ℕ} (C : Circuit)
    (refs : ι → Fin n → Bool) (i : ι) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    (∃ g, C.gates[w - n]? = some g ∧ g.op = .and) ∧
    value C (refs i) w = true ∧ ∀ j, j ≠ i → value C (refs j) w = false

lemma mem_charges {ι : Type*} {n : ℕ} (C : Circuit)
    (refs : ι → Fin n → Bool) (i : ι) (w : ℕ) :
    w ∈ charges C refs i ↔
      (n ≤ w ∧ w < n + C.size) ∧
      (∃ g, C.gates[w - n]? = some g ∧ g.op = .and) ∧
      value C (refs i) w = true ∧ ∀ j, j ≠ i → value C (refs j) w = false := by
  classical
  simp only [charges, Finset.mem_filter, Finset.mem_Ico]

lemma charges_subset {ι : Type*} {n : ℕ} (C : Circuit)
    (refs : ι → Fin n → Bool) (i : ι) :
    charges C refs i ⊆ Finset.Ico n (n + C.size) :=
  fun w hw => Finset.mem_Ico.mpr ((mem_charges C refs i w).mp hw).1

lemma charges_disjoint {ι : Type*} {n : ℕ} (C : Circuit)
    (refs : ι → Fin n → Bool) {i j : ι} (hij : i ≠ j) :
    Disjoint (charges C refs i) (charges C refs j) := by
  rw [Finset.disjoint_left]
  intro w hi hj
  have hzero := ((mem_charges C refs i w).mp hi).2.2.2 j hij.symm
  have hone := ((mem_charges C refs j w).mp hj).2.2.1
  rw [hzero] at hone
  contradiction

lemma nonterminal_expand {ι : Type*} {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (refs : ι → Fin n → Bool) (i : ι) (w : ℕ)
    (hprivate : ¬ terminal C refs i w) (htrue : value C (refs i) w = true) :
    ∃ K : Finset ℕ, K ⊆ Finset.range w ∧
      K.card ≤ 1 + (if w ∈ charges C refs i then 1 else 0) ∧
      (∀ r ∈ K, value C (refs i) r = true) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ K, value C y r = true) → value C y w = true := by
  have hn : n ≤ w := Nat.le_of_not_gt fun h => hprivate (Or.inl h)
  have hw : w < n + C.size := by
    by_contra hw
    rw [missing_value C (refs i) w (Nat.le_of_not_lt hw)] at htrue
    contradiction
  have hIndex : w - n < C.gates.length := by simpa [Circuit.size] using (show w - n < C.size by omega)
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  have hform (z : Fin n → Bool) :
      value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
    gate_value C z w hn hw
  rcases hop with hand | hor
  · have hzero (j : ι) (hj : j ≠ i) : value C (refs j) w = false := by
      cases h : value C (refs j) w
      · rfl
      · exact False.elim (hprivate (Or.inr ⟨j, hj, h⟩))
    have hcharge : w ∈ charges C refs i :=
      (mem_charges C refs i w).mpr
        ⟨⟨hn, hw⟩, ⟨g, List.getElem?_eq_getElem hIndex, hand⟩, htrue, hzero⟩
    have hAll := htrue
    rw [hform (refs i), hand, GateOp.eval, List.all_eq_true] at hAll
    have hChild (r : ℕ) (hr : r ∈ g.inputs) : r < w ∧ value C (refs i) r = true := by
      have hv := hAll _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      by_cases hl : r < w
      · exact ⟨hl, by simpa only [id_eq, ite_eq_left hl] using hv⟩
      · simp only [id_eq, ite_eq_right hl, Bool.false_eq_true] at hv
    refine ⟨g.inputs.toFinset, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact Finset.mem_range.mpr (hChild r (List.mem_toFinset.mp hr)).1
    · rw [ite_eq_left hcharge]
      exact (List.toFinset_card_le g.inputs).trans hlen
    · intro r hr
      exact (hChild r (List.mem_toFinset.mp hr)).2
    · intro y hy
      rw [hform y, hand, GateOp.eval, List.all_eq_true]
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      simpa only [id_eq, ite_eq_left (hChild r hr).1] using hy r (List.mem_toFinset.mpr hr)
  · rw [hform (refs i), hor, GateOp.eval, List.any_eq_true] at htrue
    obtain ⟨b, hb, hbit⟩ := htrue
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    have hrw : r < w := by
      by_contra hh
      simp only [id_eq, ite_eq_right hh, Bool.false_eq_true] at hbit
    have hchild : value C (refs i) r = true := by
      simpa only [id_eq, ite_eq_left hrw] using hbit
    refine ⟨{r}, ?_, ?_, ?_, ?_⟩
    · simpa using hrw
    · simp
    · simpa using hchild
    · intro y hy
      rw [hform y, hor, GateOp.eval, List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩,
        by simpa only [id_eq, ite_eq_left hrw] using hy r (by simp)⟩

end PEqualNP.Outside.L_meta_1325_aux.Expand

namespace PEqualNP.Outside.L_meta_1325_aux

lemma lineUnion_card {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (q : ℕ) (F : Finset ι)
    (hline : ∀ l, (S l).card = q + 1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) :
    (F.biUnion S).card ≤ F.card * q + 1 := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert i F hi ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hi, Nat.add_mul]
    by_cases hF : F.Nonempty
    · obtain ⟨j, hj⟩ := hF
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hsub : S i ∩ S j ⊆ S i ∩ F.biUnion S := by
        intro x hx
        obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hxi, Finset.mem_biUnion.mpr ⟨j, hj, hxj⟩⟩
      have hover : 1 ≤ (S i ∩ F.biUnion S).card := by
        rw [← hcross i j hij]
        exact Finset.card_le_card hsub
      have hcard := Finset.card_union_add_card_inter (S i) (F.biUnion S)
      rw [hline] at hcard
      simp only [Nat.one_mul]
      omega
    · have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simp [hempty, hline]

lemma lineUnion_points_card {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (q : ℕ) (F : Finset ι) (T : Finset α) (d : ℕ)
    (hline : ∀ l, (S l).card = q + 1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (hd : T.card ≤ d) :
    (F.biUnion S ∪ T).card ≤ F.card * q + 1 + d :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (lineUnion_card S q F hline hcross) hd)

lemma lineUnion_meet_residual {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (F : Finset ι) (T R : Finset α) (l : ι) (d : ℕ)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hnot : l ∉ F) (hR : R ⊆ S l) (hd : T.card ≤ d) :
    (R ∩ (F.biUnion S ∪ T)).card ≤ F.card + d := by
  have he : R ∩ (F.biUnion S ∪ T) =
      F.biUnion (fun j => R ∩ S j) ∪ (R ∩ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx, ⟨j, hj, hs⟩ | ht⟩
      · exact Or.inl ⟨j, hj, hx, hs⟩
      · exact Or.inr ⟨hx, ht⟩
    · rintro (⟨j, hj, hx, hs⟩ | ⟨hx, ht⟩)
      · exact ⟨hx, Or.inl ⟨j, hj, hs⟩⟩
      · exact ⟨hx, Or.inr ht⟩
  have hunion : (F.biUnion (fun j => R ∩ S j)).card ≤ F.card := by
    have hh : ∀ j ∈ F, (R ∩ S j).card ≤ 1 := by
      intro j hj
      have hne : l ≠ j := fun h => hnot (h ▸ hj)
      rw [← hcross l j hne]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxr, hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hR hxr, hxj⟩
    simpa using Finset.card_biUnion_le_card_mul F (fun j => R ∩ S j) 1 hh
  have hT : (R ∩ T).card ≤ d :=
    (Finset.card_le_card Finset.inter_subset_right).trans hd
  rw [he]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hunion hT)

end PEqualNP.Outside.L_meta_1325_aux

namespace PEqualNP.Outside.L_meta_1325_aux

lemma pack_terminals {n : ℕ} {ι : Type*} [DecidableEq ι]
    (T : Finset ℕ) (i : ι) (W : ι → ℕ → Prop)
    (hshared : ∀ w ∈ T, n ≤ w → ∃ j, j ≠ i ∧ W j w) :
    ∃ (F : Finset ι) (P : Finset (Fin n)),
      i ∉ F ∧ F.card + P.card ≤ T.card ∧
      (∀ w ∈ T, ∀ h : w < n, (⟨w, h⟩ : Fin n) ∈ P) ∧
      (∀ w ∈ T, n ≤ w → ∃ j ∈ F, W j w) := by
  classical
  let ins := T.filter (fun w => w < n)
  let ext := T.filter (fun w => ¬ w < n)
  have hfor (w : ext) : ∃ j, j ≠ i ∧ W j w :=
    hshared w (Finset.mem_filter.mp w.2).1 (Nat.le_of_not_gt (Finset.mem_filter.mp w.2).2)
  let point (w : ins) : Fin n := ⟨w, (Finset.mem_filter.mp w.2).2⟩
  let line (w : ext) : ι := Classical.choose (hfor w)
  have hline (w : ext) : line w ≠ i ∧ W (line w) w :=
    Classical.choose_spec (hfor w)
  let F := ext.attach.image line
  let P := ins.attach.image point
  refine ⟨F, P, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨w, _, he⟩ := Finset.mem_image.mp h
    exact (hline w).1 he
  · have hF : F.card ≤ ext.card := by
      simpa [F] using (Finset.card_image_le (s := ext.attach) (f := line))
    have hP : P.card ≤ ins.card := by
      simpa [P] using (Finset.card_image_le (s := ins.attach) (f := point))
    have hc : ins.card + ext.card = T.card :=
      Finset.card_filter_add_card_filter_not (s := T) (fun w => w < n)
    omega
  · intro w hw h
    let wm : ins := ⟨w, Finset.mem_filter.mpr ⟨hw, h⟩⟩
    exact Finset.mem_image.mpr ⟨wm, Finset.mem_attach _ _, rfl⟩
  · intro w hw h
    let wm : ext := ⟨w, Finset.mem_filter.mpr ⟨hw, Nat.not_lt.mpr h⟩⟩
    exact ⟨line wm, Finset.mem_image.mpr ⟨wm, Finset.mem_attach _ _, rfl⟩, (hline wm).2⟩

lemma packed_terminal_union_bounds {n : ℕ} {ι : Type*} [DecidableEq ι]
    (L : ι → Finset (Fin n)) (q k : ℕ) (F : Finset ι)
    (P Z : Finset (Fin n)) (i : ι)
    (hq : 1 ≤ q) (hline : ∀ j, (L j).card = q + 1)
    (hcross : ∀ j l, j ≠ l → (L j ∩ L l).card = 1)
    (hi : i ∉ F) (hk : F.card + P.card ≤ k) :
    ((Z ∪ (F.biUnion L ∪ P)) \ Z).card ≤ k*q+1 ∧
      ((L i \ Z) ∩ (Z ∪ (F.biUnion L ∪ P))).card ≤ k := by
  have hU := lineUnion_points_card L q F P P.card hline hcross le_rfl
  have hM := lineUnion_meet_residual L F P (L i \ Z) i P.card hcross hi
    (fun _ hx => (Finset.mem_sdiff.mp hx).1) le_rfl
  constructor
  · have hsub : (Z ∪ (F.biUnion L ∪ P)) \ Z ⊆ F.biUnion L ∪ P := by
      intro p hp
      obtain ⟨hm, hZ⟩ := Finset.mem_sdiff.mp hp
      exact (Finset.mem_union.mp hm).resolve_left hZ
    have hP : P.card ≤ P.card * q := by
      simpa using Nat.mul_le_mul_left P.card hq
    calc
      _ ≤ (F.biUnion L ∪ P).card := Finset.card_le_card hsub
      _ ≤ F.card * q + 1 + P.card := hU
      _ ≤ (F.card + P.card) * q + 1 := by rw [Nat.add_mul]; omega
      _ ≤ k*q+1 := Nat.add_le_add_right (Nat.mul_le_mul_right q hk) 1
  · have hsub : (L i \ Z) ∩ (Z ∪ (F.biUnion L ∪ P)) ⊆
        (L i \ Z) ∩ (F.biUnion L ∪ P) := by
      intro p hp
      obtain ⟨hpi, hpm⟩ := Finset.mem_inter.mp hp
      exact Finset.mem_inter.mpr ⟨hpi, (Finset.mem_union.mp hpm).resolve_left
        (Finset.mem_sdiff.mp hpi).2⟩
    exact (Finset.card_le_card hsub).trans (hM.trans hk)

end PEqualNP.Outside.L_meta_1325_aux

namespace PEqualNP.Outside.L_meta_1325_aux

open PEqualNP.CircuitLowerBounds

private theorem wire_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    Expand.value C x w = true → Expand.value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
      intro hw
      by_cases hn : w < n
      · let p : Fin n := ⟨w, hn⟩
        change Expand.value C x p = true at hw
        change Expand.value C y p = true
        rw [Expand.input_value] at hw ⊢
        exact hxy p hw
      · have hpriv : ¬ Expand.terminal C (fun _ : Unit => x) () w := by
          rintro (h | ⟨j, hj, _⟩)
          · exact hn h
          · exact hj (Subsingleton.elim _ _)
        obtain ⟨K, hK, _, hKtrue, hForce⟩ :=
          Expand.nonterminal_expand C hG (fun _ : Unit => x) () w hpriv hw
        exact hForce y fun r hr => ih r (Finset.mem_range.mp (hK hr)) (hKtrue r hr)

private def bits {n : ℕ} (U : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ U)

private theorem bits_mono {n : ℕ} (A B : Finset (Fin n)) (h : A ⊆ B) (v : Fin n) :
    bits A v = true → bits B v = true := by
  simpa only [bits, decide_eq_true_eq] using (@h v)

theorem price {n m : ℕ} (C : Circuit) (out : Fin m → ℕ) (L : Fin m → Finset (Fin n))
    (q j : ℕ) (Z : Finset (Fin n)) (hq : 1 ≤ q) (hj : 1 ≤ j)
    (hline : ∀ i, (L i).card = q + 1)
    (hcross : ∀ i i', i ≠ i' → (L i ∩ L i').card = 1)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hOut : ∀ i (U : Finset (Fin n)), Z ⊆ U → (U \ Z).card ≤ j * q + 1 →
      Expand.value C (fun v => decide (v ∈ U)) (out i) = decide (L i ⊆ U)) :
    ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => (L i ∩ Z).card + 1 ≤ q),
        min j (q - (L i ∩ Z).card) ≤ C.size := by
  classical
  let refs : Fin m → Fin n → Bool := fun i => bits (Z ∪ L i)
  let A := Expand.charges C refs
  let I := (Finset.univ : Finset (Fin m)).filter (fun i => (L i ∩ Z).card + 1 ≤ q)
  have hCharge (i : Fin m) (hi : i ∈ I) : min j (q - (L i ∩ Z).card) ≤ (A i).card := by
    by_contra hcost
    have href : Expand.value C (refs i) (out i) = true := by
      have hsub : (Z ∪ L i) \ Z ⊆ L i := by
        intro v hv
        obtain ⟨hv, hz⟩ := Finset.mem_sdiff.mp hv
        exact (Finset.mem_union.mp hv).resolve_left hz
      have hsize := Finset.card_le_card hsub
      have hmul : q ≤ j*q := by simpa using Nat.mul_le_mul_right q hj
      rw [hline] at hsize
      have he := hOut i (Z ∪ L i) Finset.subset_union_left (by omega)
      change Expand.value C (refs i) (out i) = decide (L i ⊆ Z ∪ L i) at he
      rw [he, decide_eq_true_eq]
      exact Finset.subset_union_right
    have hExpansion (w : ℕ) (hw : Expand.value C (refs i) w = true)
        (hTerm : ¬ Expand.terminal C refs i w) :
        ∃ K : Finset ℕ, K ⊆ Finset.range w ∧
          (∀ v ∈ K, Expand.value C (refs i) v = true) ∧
          (∀ y : Fin n → Bool, (∀ v ∈ K, Expand.value C y v = true) →
            Expand.value C y w = true) ∧
          K.card ≤ 1 + (if w ∈ A i then 1 else 0) := by
      obtain ⟨K, hr, hc, hv, hf⟩ := Expand.nonterminal_expand C hG refs i w hTerm hw
      exact ⟨K, hr, hv, hf, hc⟩
    obtain ⟨T, htcard, hT, hForce⟩ :=
      Frontier.root (fun (x : Fin n → Bool) w => Expand.value C x w = true)
        (refs i) (Expand.terminal C refs i) (A i) hExpansion (out i) href
    have htmin : T.card ≤ min j (q - (L i ∩ Z).card) := by omega
    have htj : T.card ≤ j := htmin.trans (min_le_left _ _)
    have htd : T.card ≤ q - (L i ∩ Z).card := htmin.trans (min_le_right _ _)
    have hShared (w : ℕ) (hw : w ∈ T) (hn : n ≤ w) :
        ∃ i', i' ≠ i ∧ Expand.value C (refs i') w = true :=
      ((hT w hw).1).resolve_left (Nat.not_lt.mpr hn)
    obtain ⟨F, P, hFi, hFP, hPin, hFout⟩ :=
      pack_terminals T i (fun i' w => Expand.value C (refs i') w = true) hShared
    let U := Z ∪ (F.biUnion L ∪ P)
    have ⟨hUCard, hUCross⟩ :=
      packed_terminal_union_bounds L q T.card F P Z i hq hline hcross hFi hFP
    have hForceTrue : Expand.value C (bits U) (out i) = true := by
      apply hForce
      intro w hw
      by_cases hiw : w < n
      · let v : Fin n := ⟨w, hiw⟩
        change Expand.value C (bits U) v = true
        rw [Expand.input_value, bits, decide_eq_true_eq]
        exact Finset.mem_union_right _ (Finset.mem_union_right _ (hPin w hw hiw))
      · obtain ⟨a, ha, hav⟩ := hFout w hw (Nat.le_of_not_gt hiw)
        have hsub : Z ∪ L a ⊆ U := by
          intro v hv
          rcases Finset.mem_union.mp hv with hv | hv
          · exact Finset.mem_union_left _ hv
          · exact Finset.mem_union_right _
              (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a, ha, hv⟩))
        exact wire_mono C hG (refs a) (bits U) (bits_mono _ _ hsub) w hav
    have hUle : (U \ Z).card ≤ j*q+1 :=
      hUCard.trans (Nat.add_le_add_right (Nat.mul_le_mul_right q htj) 1)
    have houtU := hOut i U Finset.subset_union_left hUle
    change Expand.value C (bits U) (out i) = decide (L i ⊆ U) at houtU
    have hLiU : L i ⊆ U := by
      rw [houtU, decide_eq_true_eq] at hForceTrue
      exact hForceTrue
    have hres : L i \ Z ⊆ (L i \ Z) ∩ U :=
      fun v hv => Finset.mem_inter.mpr ⟨hv, hLiU (Finset.mem_sdiff.mp hv).1⟩
    have hlt : (L i \ Z).card ≤ T.card := (Finset.card_le_card hres).trans hUCross
    have hc := Finset.card_sdiff_add_card_inter (L i) Z
    rw [hline] at hc
    have hi' : (L i ∩ Z).card + 1 ≤ q := (Finset.mem_filter.mp hi).2
    omega
  have hpair : (I : Set (Fin m)).PairwiseDisjoint A := by
    intro a _ b _ hab
    exact Expand.charges_disjoint C refs hab
  calc
    _ ≤ ∑ i ∈ I, (A i).card := Finset.sum_le_sum hCharge
    _ = (I.biUnion A).card := (Finset.card_biUnion hpair).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact Expand.charges_subset C refs i hi
    _ = C.size := by simp

end PEqualNP.Outside.L_meta_1325_aux

open PEqualNP.CircuitLowerBounds in
open PEqualNP.Outside.L_meta_1325_aux in
theorem PEqualNP.Outside.L_meta_1325 : ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → (∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → G s 0 (q ^ 2 + q + 1) ≤ gates.length) ∧ (∀ j F T : ℕ, 1 ≤ j → j ≤ q → F + 1 = 2 ^ s → (∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ i * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), min j (q - (L l ∩ z).card)) → (∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ F * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), (q - (L l ∩ z).card)) → T ≤ gates.length) := by
  classical
  intro q s L hq hline hcross hjoin gs out hops hnot hout
  constructor
  · exact firstConjunct q s L hq hline hcross hjoin gs out hops hnot hout
  · intro j F T hj hjq hF hsparse hfull
    let n := q^2 + q + 1
    have hb (w : Fin n) : out w < n + gs.length := by
      by_contra! ho
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (L w).card by rw [hline]; omega)
      have he : Expand.value ⟨gs, 0⟩ (fun (_ : Fin n) => true) (out w) = true := by
        change Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun _ : Fin n => true)) = true
        rw [hout]
        exact decide_eq_true ⟨v, hv, rfl⟩
      have hh := Expand.missing_value (⟨gs, 0⟩ : Circuit)
        (fun (_ : Fin n) => true) (out w) ho
      rw [hh] at he
      cases he
    obtain ⟨dual, hlen, hdual, hkeep, hneg⟩ := dualForGates n gs hops
    have hdn : ∃ ι : Fin s → Fin dual.length,
        ∀ i : Fin dual.length, (dual.get i).op = .not → ∃ j, ι j = i := by
      obtain ⟨old, hOld⟩ := hnot
      let ι (j : Fin s) : Fin dual.length := ⟨(old j).val, by rw [hlen]; exact (old j).isLt⟩
      refine ⟨ι, ?_⟩
      intro i hi
      obtain ⟨g, hg, hgn⟩ := hkeep i.val (dual.get i) (List.getElem?_eq_getElem i.isLt) hi
      let i' : Fin gs.length := ⟨i.val, hlen ▸ i.isLt⟩
      have he : gs.get i' = g := by
        simpa [i', List.getElem?_eq_getElem i'.isLt] using hg
      obtain ⟨k, hk⟩ := hOld i' (by rw [he]; exact hgn)
      refine ⟨k, Fin.ext ?_⟩
      change (old k).val = i'.val
      exact congrArg Fin.val hk
    have dualRight (w : Fin n) (Y : Finset (Fin n)) :
        Expand.value ⟨dual, 0⟩ (CC.assign Y) (out w) = decide (L w ⊆ Y) := by
      change (Circuit.wires ⟨dual, 0⟩ (List.ofFn (CC.assign Y))).getD (out w) false = _
      rw [hneg (out w) (CC.assign Y) (hb w)]
      change Bool.not (Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun p => !(CC.assign Y p)))) = _
      rw [hout, ← decide_not, decide_eq_decide]
      constructor
      · intro h p hp
        by_contra hn
        exact h ⟨p, hp, by simp [CC.assign, hn]⟩
      · intro h
        rintro ⟨p, hp, hval⟩
        simp [CC.assign, h hp] at hval
    let frozen (Z : Finset (Fin n)) : List Gate := CC.freeze (List.ofFn (CC.assign Z)) dual
    have hfrozen (Z : Finset (Fin n)) : (frozen Z).length = gs.length :=
      (CC.freeze_length dual _).trans hlen
    have hmono (Z : Finset (Fin n)) :
        ∀ g ∈ frozen Z, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
      CC.freeze_pos dual _ hdual
    have freezeRight (Z Y : Finset (Fin n)) (hsub : Z ⊆ Y)
        (hsig : CC.signature dual Z = CC.signature dual Y) (w : Fin n) :
        Expand.value ⟨frozen Z, 0⟩ (CC.assign Y) (out w) = decide (L w ⊆ Y) := by
      change (CC.run (frozen Z) (List.ofFn (CC.assign Y))).getD (out w) false = _
      rw [show CC.run (frozen Z) (List.ofFn (CC.assign Y)) =
          CC.run dual (List.ofFn (CC.assign Y)) from CC.freeze_assign dual Z Y hdual hsub hsig]
      exact dualRight w Y
    refine minFormFromStable (CC.signature (n := n) dual) F (j * q + 1) T gs.length ?_ ?_ ?_
    · intro r z hstep hchange
      have hbnd := CC.distinctChain dual z hdual hdn hstep hchange
      omega
    · intro r hr Z hZ hstable
      have hcost := price ⟨frozen Z, 0⟩ out L q j Z (by omega) hj hline hcross (hmono Z)
        (fun w Y hsub hY => freezeRight Z Y hsub (hstable Y hsub hY) w)
      have ht := hsparse r (by omega) Z hZ
      exact ht.trans (hcost.trans_eq (hfrozen Z))
    · intro Z hZ hstable
      have hcost := price ⟨frozen Z, 0⟩ out L q q Z (by omega) (by omega) hline hcross (hmono Z)
        (fun w Y hsub _ => freezeRight Z Y hsub (hstable Y hsub) w)
      simp only [min_eq_right (Nat.sub_le q _)] at hcost
      exact (hfull Z hZ).trans (hcost.trans_eq (hfrozen Z))
