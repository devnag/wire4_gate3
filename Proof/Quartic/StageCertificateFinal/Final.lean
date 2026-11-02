import Proof.Quartic.StageCertificateFinal.ActualTables
import Proof.Quartic.StageCertNative.Final

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires

/-- `thm:counter`, `sec:algorithm` and `prop:time`,
paper/paper.tex:
the complete actual certificate stage uses the original source's
generated native tables, exact signed tests and original-column
prefixes, the actual all-tests bitmap/default/retention program and
its proved same-budget original-call ledger. The existing published
counting input is the only external algorithmic argument. -/
noncomputable def certField
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ)
    (_h1 : 0<B1) (_h2 : 0<B2) : Program.CertField B1 B2 :=
  certFieldOfBudgetBound (actualTables B1 B2)
    (StageCertNative.baseNativeWordFunction h B1 B2)
    (StageCertNative.baseNativeBudget_bound h B1 B2)

end NearQuarticWires.StageCertificateFinal
