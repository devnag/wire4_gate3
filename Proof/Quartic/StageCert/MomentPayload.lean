import Proof.Quartic.StageCert.MomentCapacity
import Proof.Quartic.StageCert.MomentFlagSource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `eq:testX` and `prop:time`, paper/paper.tex: the literal complete population source clock. -/
def MomentRequest.populationSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  (Builder.allGates r.call).length*(r.retainedWitness.length+
    5*(r.selected.1.k+(Builder.allGates r.call).length)+160*r.atomBits+540)+
      40*natBitLength (2*r.selected.1.k)+540

/-- `eq:testE` and `prop:time`, paper/paper.tex: the literal complete signed digit source clock. -/
def MomentRequest.digitSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  completeMaskSourceCost (Builder.allGates r.call).length r.selected.1.k r.selected.1.Xmax
    r.atomBits (r.selected.1.Xmax+1) r.retainedWitness.length+
  (Builder.allGates r.call).length*(12*r.retainedWitness.length+6*r.selected.1.factors.length+
    8*(40*r.coefficientBits+160*r.atomBits+640)+160)+40*natBitLength (8*r.selected.1.k)+1510

/-- `eq:testPhi` and `prop:time`, paper/paper.tex: the literal complete signed final-error source clock. -/
def MomentRequest.finalSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  completeMaskSourceCost (Builder.allGates r.call).length r.selected.1.k r.selected.1.Xmax
    r.atomBits (r.selected.1.Xmax+1) r.retainedWitness.length+
  (Builder.allGates r.call).length*(6*r.retainedWitness.length+
    8*(40*r.coefficientBits+160*r.atomBits+640)+100)+40*natBitLength (8*r.selected.1.k)+1510

/-- `prop:time`, paper/paper.tex: one fixed
source program includes all three whole-test branches and their tests. -/
def MomentRequest.payloadSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  r.populationSteps+r.digitSteps+r.finalSteps+2

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: actual parsed tags choose the full
original population, signed digit or signed final-error source body. -/
def emitMomentPayload : St VV MM :=
  .ite (.eq sourceTestTag vZ) (emitPopulationMoment 0)
    (.ite (.eq sourceTestTag v1) emitDigitMoment emitFinalMoment)

/-- `lem:print` and `prop:time`, paper/paper.tex: each original test produces its exact signed integer
Formula tokens from the actual source records and computed flag suffix,
on every proposed witness and every failed column. -/
theorem emitMomentPayload_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hcap : MomentCapacity r C.Wd)
    (hparams : a.ram StageLift.parameterStore=StageLift.parameterScalars r.selected.1)
    (hwitness : a.ram StageLift.witnessStore=r.retainedWitness.map Bool.toNat)
    (hfactors : a.ram StageLift.factorStore=r.selected.1.factors)
    (hfields : ∀i : Fin 6,a.env momentSourceFields[i]=r.sourceValues[i])
    (hG : a.env atomCount=(Builder.allGates r.call).length)
    (hG1 : a.env firstGateCount=r.call.first.gates.length)
    (hRC : ∀m,a.rc m≤(a.ram m).length) (hKC : a.kc≤a.kout.length)
    (hin : C.inp.drop a.ip=structuralFlagList r (momentFlagEdges r.test)++rest) :
    Hs C emitMomentPayload a r.payloadSteps (fun z=>
      z.out=a.out++(toks r.formula).flatMap tokWord ∧
      z.ip=a.ip+(momentFlagEdges r.test).length ∧
      (z.ram,z.kin,z.kout,z.kc)=(a.ram,a.kin,a.kout,a.kc) ∧ Cst z) := by
  have hpos : 1≤(Builder.allGates r.call).length := r.pool_pos
  have hJ : 1≤r.selected.1.J := r.rules.J_pos
  have hbits : r.selected.1.k+(r.selected.1.J+1)*(Builder.allGates r.call).length≤
      r.retainedWitness.length := r.retainedWitness_length.ge
  have hspan : (Builder.allGates r.call).length≤
      (r.selected.1.J+1)*(Builder.allGates r.call).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  have htag : a.env sourceTestTag=(r.test.metadata r.selected.1).tag := hfields ⟨0,by decide⟩
  have hj : a.env selectedCircuit=(r.test.metadata r.selected.1).circuit := hfields ⟨1,by decide⟩
  have hcode : a.env sourceSignOrdinal=(r.test.metadata r.selected.1).signOrdinal := hfields ⟨2,by decide⟩
  have hrow : a.env requestedChainRow=(r.test.metadata r.selected.1).digitOrdinal := hfields ⟨3,by decide⟩
  unfold emitMomentPayload
  cases htest : r.test with
  | population =>
    have htag0 : a.env sourceTestTag=0 := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using htag
    have hi : C.inp.drop a.ip=StagePrint.callStructural r.call r.rules r.walk 0::rest := by
      simpa only [htest,momentFlagEdges,structuralFlagList,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using hin
    have hp := emitPopulationMoment_run C r.selected.1 0 (Builder.allGates r.call).length r.atomBits
      r.retainedWitness (StagePrint.callStructural r.call r.rules r.walk 0) rest a hc hpos hG hi hparams
      hwitness hRC hKC (by omega)
      (by have hh := hcap.address; omega)
      (by have hh := hcap.minWidth; omega)
      (by have hh := hcap.newtonArithmetic; have hp := Nat.lt_two_pow_self (n := C.Wd); omega)
      hcap.atoms (fun g hg j=>r.atom_bits_bound g hg 0 j) hcap.atomWord
      (by have hh := hcap.exponent; omega)
      (lt_of_le_of_lt (Nat.add_le_add_right (StageLift.codec_nbl_mono (by omega :
        2*r.selected.1.k≤8*r.selected.1.k)) 2) hcap.exponentWord)
    refine (Hs.iteT (c := .eq sourceTestTag vZ) (show sourceTestTag≠vZ by decide)
      (by simp only [Cnd.eval,htag0,hc.z,decide_true]) hp).mono
        (by change r.populationSteps+1≤r.populationSteps+r.digitSteps+r.finalSteps+2; omega) ?_
    rintro z ⟨zo,zi,zs,_,zc,_⟩
    exact ⟨by simpa only [MomentRequest.formula,htest] using zo,
      by simpa only [htest,momentFlagEdges,List.length_cons,List.length_nil] using zi,zs,zc⟩
  | digit j code row =>
    have htag1 : a.env sourceTestTag=1 := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using htag
    have hj' : a.env selectedCircuit=j.val := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using hj
    have hc' : a.env sourceSignOrdinal=code.val := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using hcode
    have hr' : a.env requestedChainRow=row.val := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using hrow
    have hi : C.inp.drop a.ip=List.ofFn (StagePrint.callStructural r.call r.rules r.walk)++rest := by
      simpa only [htest,momentFlagEdges,structuralFlagList,List.map_ofFn,Function.comp_def] using hin
    have hp := emitDigitMoment_run C r.selected.1 (Builder.allGates r.call).length row.val j.val
      r.call.first.gates.length code.val r.coefficientBits r.atomBits (r.selected.1.Xmax+1)
      r.retainedWitness (StagePrint.callStructural r.call r.rules r.walk) rest a hc hpos hG hr' hj' hG1 hc'
      htag1 (by have hh := row.isLt; omega) hJ hi hparams hwitness hfactors
      (retainedFactors_length r.call r.rules) hRC hKC hbits hcap.address hcap.tupleCount
      hcap.newtonArithmetic hcap.minWidth hcap.atoms r.atom_bits_bound hcap.atomWord
      r.newton_bits_bound hcap.newtonWord hcap.chain
      (lt_of_le_of_lt (source_digit_rate_le r.call r.rules row) hcap.rate)
      (fun g hg=>r.digit_coefficient_bits j row ⟨g,hg⟩) hcap.coefficientWord
      hcap.exponent hcap.exponentWord
    refine (Hs.iteF (c := .eq sourceTestTag vZ) (show sourceTestTag≠vZ by decide)
      (by simp only [Cnd.eval,htag1,hc.z]; decide)
      (Hs.iteT (c := .eq sourceTestTag v1) (show sourceTestTag≠v1 by decide)
        (by simp only [Cnd.eval,htag1,hc.one,decide_true]) hp)).mono
      (by change r.digitSteps+1+1≤r.populationSteps+r.digitSteps+r.finalSteps+2; omega) ?_
    rintro z ⟨zo,zi,zs,_,_,zc,_⟩
    exact ⟨by simpa only [MomentRequest.formula,htest] using zo,
      by simpa only [htest,momentFlagEdges,List.length_ofFn] using zi,zs,zc⟩
  | finalError j code =>
    have htag2 : a.env sourceTestTag=2 := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using htag
    have hj' : a.env selectedCircuit=j.val := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using hj
    have hc' : a.env sourceSignOrdinal=code.val := by simpa only [htest,StageCertTests.TestOrdinal.metadata] using hcode
    have hi : C.inp.drop a.ip=List.ofFn (StagePrint.callStructural r.call r.rules r.walk)++rest := by
      simpa only [htest,momentFlagEdges,structuralFlagList,List.map_ofFn,Function.comp_def] using hin
    have hp := emitFinalMoment_run C r.selected.1 (Builder.allGates r.call).length j.val
      r.call.first.gates.length code.val r.coefficientBits r.atomBits (r.selected.1.Xmax+1)
      r.retainedWitness (StagePrint.callStructural r.call r.rules r.walk) rest a hc hpos hG hj' hG1 hc'
      htag2 hJ hi hparams hwitness hRC hKC hbits hcap.address hcap.tupleCount hcap.newtonArithmetic
      hcap.minWidth hcap.atoms r.atom_bits_bound hcap.atomWord r.newton_bits_bound hcap.newtonWord
      hcap.scale (fun g hg=>r.final_coefficient_bits j ⟨g,hg⟩) hcap.coefficientWord
      hcap.exponent hcap.exponentWord
    refine (Hs.iteF (c := .eq sourceTestTag vZ) (show sourceTestTag≠vZ by decide)
      (by simp only [Cnd.eval,htag2,hc.z]; decide)
      (Hs.iteF (c := .eq sourceTestTag v1) (show sourceTestTag≠v1 by decide)
        (by simp only [Cnd.eval,htag2,hc.one]; decide) hp)).mono
      (by change r.finalSteps+1+1≤r.populationSteps+r.digitSteps+r.finalSteps+2; omega) ?_
    rintro z ⟨zo,zi,zs,_,zc,_⟩
    exact ⟨by simpa only [MomentRequest.formula,htest] using zo,
      by simpa only [htest,momentFlagEdges,List.length_ofFn] using zi,zs,zc⟩

end NearQuarticWires.StageCert.Tokens
