import Proof.Quartic.StageCert.MomentBitBounds

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: one explicit binary workspace scale covers the actual
source, original occurrence census and selected mask/chain parameters. -/
noncomputable def MomentRequest.bodyScale {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  r.word.length+(Builder.allGates r.call).length+r.selected.1.Xmax+r.selected.1.k+
    r.selected.1.J+r.selected.1.tau+r.atomBits+r.coefficientBits+r.call.n+2

/-- `prop:time`, paper/paper.tex: the explicit
workspace is quadratic in the displayed original source quantities. -/
noncomputable def MomentRequest.bodyCapacity {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  100*r.bodyScale^2

/-- `lem:print` and `prop:time`, paper/paper.tex: these are exactly the concrete numeric ranges used by
the complete physical population and signed walk-moment emitters. -/
structure MomentCapacity {B1 B2 : ℕ} (r : MomentRequest B1 B2) (width : ℕ) : Prop where
  source : r.word.length+2≤width
  minWidth : 6≤width
  degree : 16*r.selected.1.Xmax+8*r.selected.1.k<2^width
  atoms : 17*(Builder.allGates r.call).length<2^width
  address : r.selected.1.k+(r.selected.1.J+1)*(Builder.allGates r.call).length≤2^width
  tupleCount : 2*(Builder.allGates r.call).length^r.selected.1.Xmax≤2^width
  newtonArithmetic : 2*r.selected.1.Xmax+2≤width
  atomWord : r.atomBits+2<2^width
  coefficientWord : r.coefficientBits+2<2^width
  newtonWord : r.selected.1.Xmax+1+2<2^width
  chain : r.selected.1.J≤2^width
  rate : r.call.n+1<2^width
  scale : r.selected.1.M1<2^width
  exponent : 8*r.selected.1.k<2^width
  exponentWord : natBitLength (8*r.selected.1.k)+2<2^width

/-- `lem:print` and `prop:time`, paper/paper.tex: the displayed workspace suffices for every actual
source and every proposed witness, including all failed columns. -/
theorem MomentRequest.body_capacity {B1 B2 : ℕ} (r : MomentRequest B1 B2) (width : ℕ)
    (hwidth : r.bodyCapacity≤width) : MomentCapacity r width := by
  let S := r.bodyScale
  have hS : 2≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hword : r.word.length≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hG : (Builder.allGates r.call).length≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hX : r.selected.1.Xmax≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hk : r.selected.1.k≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hJ : r.selected.1.J≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hA : r.atomBits≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hC : r.coefficientBits≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hn : r.call.n≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hsq : S≤S^2 := by nlinarith
  have hbig : 100*S^2≤width := hwidth
  have hlinear : 100*S≤width := by nlinarith
  have hpow : width<2^width := Nat.lt_two_pow_self
  have hGX : (Builder.allGates r.call).length*r.selected.1.Xmax≤S^2 := by nlinarith
  have hJG : r.selected.1.J*(Builder.allGates r.call).length≤S^2 := by nlinarith
  have hbase : (Builder.allGates r.call).length≤2^(Builder.allGates r.call).length :=
    Nat.lt_two_pow_self.le
  have htuple : (Builder.allGates r.call).length^r.selected.1.Xmax≤
      2^((Builder.allGates r.call).length*r.selected.1.Xmax) := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hbase r.selected.1.Xmax
  have htupleBound : 2*((Builder.allGates r.call).length^r.selected.1.Xmax)≤2^width := by
    have hp : 2^((Builder.allGates r.call).length*r.selected.1.Xmax+1)≤2^width :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    rw [pow_succ] at hp
    omega
  have hM : r.selected.1.M1<2^r.coefficientBits := by
    have hh := lt_natBitLength (1+r.call.n+r.selected.1.M1+r.selected.1.A)
    change _<2^natBitLength (1+r.call.n+r.selected.1.M1+r.selected.1.A)
    omega
  have hexpBits : natBitLength (8*r.selected.1.k)≤8*r.selected.1.k+1 := by
    unfold natBitLength
    have hh := Nat.log_le_self 2 (8*r.selected.1.k)
    omega
  refine ⟨by omega,by omega,by omega,by omega,?_,htupleBound,by omega,
    by omega,by omega,by omega,by omega,by omega,?_,by omega,by omega⟩
  · have hh : r.selected.1.k+(r.selected.1.J+1)*(Builder.allGates r.call).length≤width := by
      nlinarith
    exact hh.trans hpow.le
  · exact hM.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end NearQuarticWires.StageCert.Tokens
