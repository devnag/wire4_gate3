import Proof.Quartic.StageCertNative.Table
import Proof.Quartic.StageNativeWidth.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl StageCert.Tokens

/-- `lem:print`, paper/paper.tex: one fixed
coefficient controls the actual selected degree and coefficient bits. -/
def widthBaseCoefficient (B1 : ℕ) : ℕ :=
  100*(Cells.ParameterArithmetic.preparationCoefficient B1+1)^2+3

def widthBaseDegree (B1 : ℕ) : ℕ := 2*(B1+12)

def nativeWidthCoefficient (B1 : ℕ) : ℕ := 2000*(widthBaseCoefficient B1+1)^2

def nativeWidthDegree (B1 : ℕ) : ℕ := 2*widthBaseDegree B1+6

/-- `lem:print` and `prop:time`, paper/paper.tex: actual native q depends only polynomially on original
arity, using expansion coefficient bits rather than Formula weight,
including all bad witnesses and padded native table positions. -/
theorem actualTable_width {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (actualTable r).q+3≤nativeWidthCoefficient B1*(r.prepared.call.n+1)^nativeWidthDegree B1 := by
  let m:=zeroMoment r
  let n:=r.prepared.call.n
  let C:=widthBaseCoefficient B1
  let E:=widthBaseDegree B1
  have hs:=m.rules
  have hC : 1≤C := by dsimp only [C,widthBaseCoefficient];omega
  have hE : 1≤E := by dsimp only [E,widthBaseDegree];omega
  have hpow : 1≤(n+1)^E := Nat.one_le_pow _ _ (by omega)
  have hdegree : 16*m.selected.1.Xmax+8*m.selected.1.k≤n := by
    have hh:=hs.moment_degree
    rw [hs.m_eq] at hh
    have hd : m.selected.1.Dmax≤n := by rw [hs.Dmax_eq];exact Nat.findGreatest_le (P:=Cells.ParameterArithmetic.DegreePass
      (Builder.callInput m.call).n m.selected.1.m m.selected.1.k m.selected.1.Uocc) (n:=(Builder.callInput m.call).n)
    exact hh.trans hd
  have hD : m.packet.degree≤C*(m.call.n+1)^E := by
    have hn : n≤(n+1)^E := (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
    exact hdegree.trans (hn.trans (Nat.le_mul_of_pos_left _ hC))
  have hbits : Cells.nativeCertificateBits B1 m.call.n≤C*(m.call.n+1)^E := by
    change 100*(Cells.ParameterArithmetic.preparationCoefficient B1+1)^2*(n+1)^E+2≤C*(n+1)^E
    dsimp only [C,widthBaseCoefficient]
    nlinarith only [hpow]
  have hq:=(StageNativeWidth.native_widths_polynomial m.nativeContext m.packet.degree
    (Cells.nativeCertificateBits B1 m.call.n) C E hD hbits).2.2
  have hactual : (actualTable r).q≤1000*(C+1)^2*(n+1)^(2*E+6) := hq
  have hmin : 3≤1000*(C+1)^2*(n+1)^(2*E+6) := by
    have hp : 1≤(n+1)^(2*E+6) := Nat.one_le_pow _ _ (by omega)
    have hc : 1≤(C+1)^2 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hp,hc]
  change (actualTable r).q+3≤2000*(C+1)^2*(n+1)^(2*E+6)
  nlinarith only [hactual,hmin]

end NearQuarticWires.StageCertNative
