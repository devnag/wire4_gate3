import Proof.Quartic.Statement.Joint

/-!
# Reading checks for the joint statement

`JointStatement4` implies each half with its own constants: `FinalStatement4` (`thm:main`) and `GateStatement4`
(`thm:gates`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Statement

theorem jointStatement4_wires (h : JointStatement4) : FinalStatement4 := by
  obtain ⟨γ, h0, h1, hj⟩ := h
  refine ⟨γ, h0, h1, fun d hd hdγ => ?_⟩
  obtain ⟨K, hK, F, hF, n₀, hn₀, hboth⟩ := hj d hd hdγ
  exact ⟨K, hK, F, hF, n₀, hn₀, fun n hn => (hboth n hn).1⟩

theorem jointStatement4_gates (h : JointStatement4) : GateStatement4 := by
  obtain ⟨γ, h0, h1, hj⟩ := h
  refine ⟨γ, h0, h1, fun d hd hdγ => ?_⟩
  obtain ⟨K, hK, F, hF, n₀, hn₀, hboth⟩ := hj d hd hdγ
  exact ⟨K, hK, F, hF, n₀, hn₀, fun n hn => (hboth n hn).2⟩

theorem jointStatement4_halves (h : JointStatement4) : FinalStatement4 ∧ GateStatement4 :=
  ⟨jointStatement4_wires h, jointStatement4_gates h⟩

end NearQuarticWires.Statement
