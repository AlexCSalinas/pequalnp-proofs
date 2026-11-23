import Mathlib
import PEqualNP.Defs

/-!
L-meta-200: a NOT gate at the top of a circuit can be replaced by an AND gate with an input
bit followed by a NOT gate, which ORs the negation of that input onto the circuit's function
at the cost of one gate.
-/

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Evaluating one more gate appends its value to the wires. -/
theorem L_meta_200_wires_append (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires x =
      (Circuit.mk gs o').wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o').wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

/-- The wires are the inputs followed by one value per gate. -/
theorem L_meta_200_wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    ((Circuit.mk gs o).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [L_meta_200_wires_append gs g o o]
    simp only [List.length_append, List.length_singleton, ih]
    omega

/-- Reading the wire just appended. -/
theorem L_meta_200_getD_last (l : List Bool) (a : Bool) (k : ℕ) (hk : l.length = k) :
    (l ++ [a]).getD k false = a := by
  subst hk
  simp [List.getD_eq_getElem?_getD]

/-- An input wire keeps its value through the gates. -/
theorem L_meta_200_wires_getD_input (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length) :
    ((Circuit.mk gs o).wires x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [L_meta_200_wires_append gs g o o,
      List.getD_append _ _ _ _ (by rw [L_meta_200_wires_length]; omega)]
    exact ih

/-- Reading an input wire. -/
theorem L_meta_200_getD_ofFn {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD, p.isLt]

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_200 :
    ∀ (n : ℕ) (p : Fin n) (w : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit), C = { gates := gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [w]⟩], output := n + gs.length } → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.HasCircuitSize n (fun x => !x p || PEqualNP.MetaComplexity.circuitFun n C x) (C.size + 1) := by
  intro n p w gs C hC hF
  subst hC
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk
    (gs ++ [⟨.and, [p.val, w]⟩, ⟨.not, [n + gs.length]⟩]) (n + gs.length + 1), ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hF g (by simp [hg])
    · simp
    · simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval]
    have e : gs ++ [(⟨.and, [p.val, w]⟩ : PEqualNP.CircuitLowerBounds.Gate),
        ⟨.not, [n + gs.length]⟩] =
        (gs ++ [⟨.and, [p.val, w]⟩]) ++ [⟨.not, [n + gs.length]⟩] := by simp
    rw [e, L_meta_200_wires_append _ _ _ 0, L_meta_200_wires_append _ _ 0 0,
      L_meta_200_wires_append _ _ _ 0]
    have hl : ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (List.ofFn x)).length
        = n + gs.length := by
      rw [L_meta_200_wires_length]; simp
    set W := (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (List.ofFn x) with hW
    rw [L_meta_200_getD_last _ _ _ (by simp [hl])]
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons]
    rw [L_meta_200_getD_last _ _ _ hl, L_meta_200_getD_last _ _ _ hl]
    have hp : W.getD p.val false = x p := by
      rw [hW, L_meta_200_wires_getD_input _ _ _ _ (by simp), L_meta_200_getD_ofFn]
    have hp' : W[p.val]?.getD false = x p := by
      rw [← List.getD_eq_getElem?_getD]; exact hp
    simp [hp']
