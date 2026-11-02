import Proof.Quartic.StageCertNative.PriceOriginal
import Proof.Quartic.Cells.ParametersRecoveryReserve

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open StageCertificateControl

/-- `sec:params` and `prop:time`, paper/paper.tex: the original unchanged degree test
pays every fixed occurrence exponent at most fifty. -/
theorem job_degree_reserve {B1 B2 : ℕ} (r : TermJob B1 B2)
    (d : ℕ) (hd : d≤50) :
    r.moment.selected.1.Uocc^(d*r.moment.packet.degree)≤
      2^(r.moment.call.n-r.moment.selected.1.k) := by
  have hU:=job_occurrence_pos r
  have hh:=r.moment.rules.recovery_compiler_reserve (r.moment.selected.1.Uocc-1)
    r.moment.packet.degree (by omega) r.moment.source_degree_guard
  rw [Nat.sub_add_cancel hU] at hh
  have hp : r.moment.selected.1.Uocc^(d*r.moment.packet.degree)≤
      r.moment.selected.1.Uocc^(50*r.moment.packet.degree) :=
    Nat.pow_le_pow_right hU (Nat.mul_le_mul_right _ hd)
  exact hp.trans ((Nat.le_mul_of_pos_left _ Nat.one_le_two_pow).trans hh)

theorem OriginalPrice.of_job_reserve {B1 B2 : ℕ}
    {f : IndexedRequest B1 B2→ℕ} {d : ℕ}
    (h : JobPrice (fun r=>f r.base) d) (hd : d≤50) : OriginalPrice f := by
  obtain ⟨C,E,h⟩:=h
  refine ⟨C,E,fun r=>?_⟩
  exact (h (firstJob r)).trans (Nat.mul_le_mul_left _ (job_degree_reserve (firstJob r) d hd))

end NearQuarticWires.StageCertNative
