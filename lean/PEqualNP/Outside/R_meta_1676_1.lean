import Mathlib
import PEqualNP.Defs

/-- A cut of L-meta-1676 by the operation of the second gate. Size 0 and 1 are
discharged here: the first-gate constraint already rules them out. -/
theorem PEqualNP.Outside.R_meta_1676_1
    (hAnd : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.and → 16 ≤ C.size)
    (hOr : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.or → 16 ≤ C.size)
    (hNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → C.gates[1]?.map (fun g => g.op) = some PEqualNP.CircuitLowerBounds.GateOp.not → 16 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hFan hFirst hFun
  let edge : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have hEval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x := by
    intro x
    simpa [PEqualNP.MetaComplexity.circuitFun, edge] using congrFun hFun x
  have wlen : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).length = 9 + C.size := by
    intro x
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires PEqualNP.CircuitLowerBounds.Circuit.size
    have h : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
          = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih =>
        intro w
        have ih' := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        simp [List.foldl_cons, List.length_append] at ih' ⊢
        omega
    exact h C.gates (List.ofFn x)
  have hprefix : ∀ (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9),
      (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ)
        (hj : j < w.length),
        (gs.foldl (fun w g =>
          w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w).getD j false
          = w.getD j false := by
      intro gs
      induction gs with
      | nil => intro w j hj; simp
      | cons g gs ih =>
        intro w j hj
        have hj' : j < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
          simp; omega
        rw [List.foldl_cons, ih (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) j hj',
          List.getD_append w _ false j hj]
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    have hi' : i < (List.ofFn x).length := hi
    rw [hpre C.gates (List.ofFn x) i hi', List.getD_eq_getElem (List.ofFn x) false hi']
    exact List.getElem_ofFn hi'
  by_cases hsz : 2 ≤ C.size
  · have hlen : 1 < C.gates.length := by
      change 1 < C.size at hsz ⊢
      omega
    have hop : C.gates[1].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        C.gates[1].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        C.gates[1].op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
        (hFan C.gates[1] (List.getElem_mem hlen)).1
    have hsome : C.gates[1]?.map (fun g => g.op) = some C.gates[1].op := by
      simp [List.getElem?_eq_getElem hlen]
    rcases hop with hand | hor | hnot
    · exact hAnd C hFan hFirst hFun (hsome.trans (congrArg some hand))
    · exact hOr C hFan hFirst hFun (hsome.trans (congrArg some hor))
    · exact hNot C hFan hFirst hFun (hsome.trans (congrArg some hnot))
  · have hsmall : C.size ≤ 1 := by omega
    let y0 : Fin 9 → Bool := fun i => decide (i.val = 0)
    let y1 : Fin 9 → Bool := fun i => decide (i.val = 1)
    let y01 : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 1)
    have edge0 : edge y0 = false := by simp [edge, y0]
    have edge1 : edge y1 = false := by simp [edge, y1]
    have edge01 : edge y01 = true := by simp [edge, y01]
    have first0 : (C.wires (List.ofFn y0)).getD 9 false = true := by
      have : (y0 0 || y0 4) = true := by simp [y0]
      simpa using (hFirst y0).trans this
    have ev0 : C.eval (List.ofFn y0) = false := (hEval y0).trans edge0
    have ev1 : C.eval (List.ofFn y1) = false := (hEval y1).trans edge1
    have ev01 : C.eval (List.ofFn y01) = true := (hEval y01).trans edge01
    cases hsz0 : C.size
    · have : (C.wires (List.ofFn y0)).getD 9 false = false :=
        List.getD_eq_default _ _ (by rw [wlen y0, hsz0])
      exact (Bool.false_ne_true (this.symm.trans first0)).elim
    · rename_i n
      have hn : n = 0 := by omega
      subst hn
      have hout_ne_nine : C.output ≠ 9 := by
        intro heq
        have : C.eval (List.ofFn y0) = true := by
          unfold PEqualNP.CircuitLowerBounds.Circuit.eval
          rw [heq, first0]
        exact Bool.false_ne_true (ev0.symm.trans this)
      have hout_lt : C.output < 10 := by
        by_contra hge
        have : C.eval (List.ofFn y01) = false := by
          unfold PEqualNP.CircuitLowerBounds.Circuit.eval
          exact List.getD_eq_default _ _ (by rw [wlen y01, hsz0]; omega)
        exact Bool.false_ne_true (this.symm.trans ev01)
      have hout_lt9 : C.output < 9 := by omega
      have ev_out : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = x ⟨C.output, hout_lt9⟩ := by
        intro x
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        exact hprefix x C.output hout_lt9
      have hout_ne0 : C.output ≠ 0 := by
        intro heq
        have h := ev_out y0
        have hy : y0 ⟨C.output, hout_lt9⟩ = decide (C.output = 0) := by simp [y0]
        rw [hy, heq] at h
        simp at h
        exact Bool.false_ne_true (ev0.symm.trans h)
      have hout_ne1 : C.output ≠ 1 := by
        intro heq
        have h := ev_out y1
        have hy : y1 ⟨C.output, hout_lt9⟩ = decide (C.output = 1) := by simp [y1]
        rw [hy, heq] at h
        simp at h
        exact Bool.false_ne_true (ev1.symm.trans h)
      have hout_01 : C.output = 0 ∨ C.output = 1 := by
        have h := ev_out y01
        have : y01 ⟨C.output, hout_lt9⟩ = true := by
          exact h.symm.trans ev01
        simp [y01, decide_eq_true_eq] at this
        exact this
      cases hout_01 with
      | inl h => exact (hout_ne0 h).elim
      | inr h => exact (hout_ne1 h).elim
