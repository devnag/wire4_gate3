import Proof.Quartic.StageCertNative.CountSource
import Proof.Quartic.StageCert.MomentCapacity
import Proof.Quartic.StageLift.RawHeader

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertificateControl StageCert.Tokens

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the actual BASE count is no
larger than the eight-vertex census at the selected binary radix. -/
theorem termCount_le_eighth {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    termCount r≤r.prepared.selected.1.N^8 := by
  have hs := Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  have hN : 1≤r.prepared.selected.1.N :=
    (Cells.ParameterRules.N_ge_two hs).trans' (by decide)
  rw [termCount_eq_tag]
  unfold countByTag
  split
  · exact Nat.pow_le_pow_right hN (by decide : 2≤8)
  · exact le_rfl

/-- `prop:time`, paper/paper.tex: the existing
actual source workspace also pays the entire binary term census;
no unary count is added to the original BASE input. -/
theorem count_capacity {B1 B2 : ℕ} (r : IndexedRequest B1 B2) (width : ℕ)
    (hw : (zeroMoment r).bodyCapacity≤width) :
    r.prepared.selected.1.N^8<2^width ∧
      4*r.prepared.selected.1.k+3<2^width ∧ 2≤width := by
  let S := (zeroMoment r).bodyScale
  have hS : 2≤S := by dsimp only [S,MomentRequest.bodyScale]; omega
  have hk : r.prepared.selected.1.k≤S := by
    dsimp only [S,MomentRequest.bodyScale,zeroMoment,actualMoment]
    omega
  have hs : 100*S^2≤width := hw
  have hsq : S≤S^2 := by nlinarith
  have hl : 4*r.prepared.selected.1.k+3<width := by nlinarith
  have hN : r.prepared.selected.1.N^8≤2^(4*r.prepared.selected.1.k) := by
    have he := (zeroMoment r).rules.N_eq
    change r.prepared.selected.1.N=2^(r.prepared.selected.1.k/2) at he
    rw [he,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨hN.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)),
    hl.trans Nat.lt_two_pow_self,by omega⟩

/-- `prop:time`, paper/paper.tex: exact binary
count serialization uses at most four selected dimension bits per
inner coordinate, for both population and full-moment branches. -/
theorem count_bits {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    natBitLength (termCount r)≤4*r.prepared.selected.1.k+1 := by
  have hN : r.prepared.selected.1.N^8≤2^(4*r.prepared.selected.1.k) := by
    have he := (zeroMoment r).rules.N_eq
    change r.prepared.selected.1.N=2^(r.prepared.selected.1.k/2) at he
    rw [he,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h := StageLift.codec_nbl_mono ((termCount_le_eighth r).trans hN)
  have hp : natBitLength (2^(4*r.prepared.selected.1.k))=4*r.prepared.selected.1.k+1 := by
    unfold natBitLength
    rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  rw [hp] at h
  exact h

/-- `lem:print` and `prop:time`, paper/paper.tex: the counted whole-test loop is initialized from
the actual original prep and five metadata fields, decoded by the
closed exact source reader rather than supplied count data. -/
def countBody : St VV MM :=
  .seq readMomentSource (.seq computeTermCount (StageLift.emitNaturalFields [termRemaining]))

noncomputable def countBodySteps {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  (zeroMoment r).readSteps+40*(4*r.prepared.selected.1.k+1)+100

theorem countBody_run {B1 B2 : ℕ} (C : Ctx) (r : IndexedRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=(zeroMoment r).word)
    (hw : (zeroMoment r).bodyCapacity≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C countBody a (countBodySteps r) (fun z=>z.out=a.out++natWord (termCount r)) := by
  have hcap := (zeroMoment r).body_capacity C.Wd hw
  have hcnt := count_capacity r C.Wd hw
  have hh := (zeroMoment r).rules
  have hN : 1≤r.prepared.selected.1.N := (Cells.ParameterRules.N_ge_two hh).trans' (by decide)
  unfold countBody
  apply Hx.hs
  refine Hs.then (readMomentSource_run C (zeroMoment r) [] a hc
    (by simpa only [List.append_nil] using hin) hcap.source hempty)
    (fun b ⟨bd,_,bs,bc⟩ n1 hn1=>?_)
  have bt : b.env sourceTestTag=r.metadata.tag := by
    have h := bd.fields ⟨0,by decide⟩
    change b.env sourceTestTag=((actualOrdinal r).metadata r.prepared.selected.1).tag at h
    rw [actualOrdinal_metadata] at h
    exact h
  refine Hs.then (computeTermCount_run C r.prepared.selected.1.N r.metadata.tag b bc hN bd.base bt hcnt.1)
    (fun d ⟨dv,ds,dc,_⟩ n2 hn2=>?_)
  have dv' : d.env termRemaining=termCount r := dv.trans (termCount_eq_tag r).symm
  refine Hs.last (StageLift.emitNaturalFields_spec C [termRemaining] d dc
    (4*r.prepared.selected.1.k+1) (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      decide)
    (by intro x hx; simp only [List.mem_singleton] at hx; subst x; rw [dv']; exact count_bits r)
    hcnt.2.2 hcnt.2.1)
    (fun z ⟨zo,_,_,_⟩ n3 hn3=>?_)
  have doo : d.out=a.out := (congrArg (fun q=>q.2.1) ds).trans (congrArg Prod.fst bs)
  refine ⟨?_,?_⟩
  · rw [zo,doo]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,dv']
  · change n3≤1*(40*(4*r.prepared.selected.1.k+1)+43)+1 at hn3
    unfold countBodySteps
    omega

end NearQuarticWires.StageCertNative
