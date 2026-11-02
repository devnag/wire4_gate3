import Proof.Quartic.GateCorollary.Replication
import Proof.Quartic.GateCorollary.Caps

set_option autoImplicit false

namespace NearQuarticWires.GateCorollary

open NearCubicWires NearCubicGates.Target
open NearCubicGates.Close.Transfer NearQuarticWires.Statement

/-- `cor:gates`, paper/paper.tex: the ordinary
SYM-over-threshold gate count follows from the wire theorem with
the identical constant, language, gap and input-length cutoff. -/
theorem symGatesAt_of_wiresAt {K : ℕ} {F : Language} {d : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (h : WiresAt K F d n) : SymGatesAt K F d n := by
  intro C hC
  exact h C ((occurrence_wires C).trans
    ((Nat.mul_le_mul_left (n + 1) hC).trans (gateCap_wires_le K n hn)))

/-- `cor:gates`, paper/paper.tex: the exact gate
cap follows from the wire cap for the same K, language and error gap,
by signed integral replication with support-preserving complements. -/
theorem gatesAt_of_wiresAt {K : ℕ} {F : Language} {d : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (h : WiresAt K F d n) : GatesAt K F d n := by
  intro C hC
  have hw : wires (toSymmetric C) ≤ wireCap K n :=
    (replication_wires C).trans
      ((Nat.mul_le_mul_left (n + 1) hC).trans (gateCap_wires_le K n hn))
  rw [← replication_agreement C F]
  exact h (toSymmetric C) hw

/-- `thm:main` and `cor:gates`, paper/paper.tex: the same rational gap and the same K, language and
input-length cutoff satisfy both conclusions of the joint statement. -/
theorem jointStatement4_of_final : FinalStatement4 → JointStatement4 := by
  rintro ⟨gamma, hgamma, hgamma1, hmain⟩
  refine ⟨gamma, hgamma, hgamma1, ?_⟩
  intro d hd hdgamma
  obtain ⟨K, hK, F, hF, n₀, hn₀, hlength⟩ := hmain d hd hdgamma
  refine ⟨K, hK, F, hF, n₀, hn₀, ?_⟩
  intro n hn
  have hw : WiresAt K F d n := hlength n hn
  exact ⟨hw, symGatesAt_of_wiresAt (by omega) hw, gatesAt_of_wiresAt (by omega) hw⟩

end NearQuarticWires.GateCorollary
