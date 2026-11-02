import Proof.Quartic.StageCertificateControl.Censuses
import Proof.Quartic.StageLift.CallSource
import Proof.Quartic.StageLift.ParameterRun
import Proof.Quartic.StageLift.PrintFrames
import Proof.Quartic.StageLift.StoreFrame
import Proof.Quartic.StageLift.MemoryVariable

/-!
# Locate actual tests after the original preparation prefix

Paper: the witness prefix `sec:algorithm`, paper/paper.tex, Step 2, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageRecovery (widthVar)

/-- The first complete conjunction array of `sec:algorithm`,
paper/paper.tex, has a store disjoint from the original data. -/
def firstFlagStore : Fin MM := 8

/-- The second complete conjunction array of `sec:algorithm`,
paper/paper.tex, alternates with the first array. -/
def secondFlagStore : Fin MM := 9

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
read the real call, public parameters and bounded witness frame,
then recover the original arity by a paid retained-call head return. -/
def readPreparedInput : St VV MM :=
  .seq StageLift.readCallSource (.seq StageLift.readParameters
    (.seq (StageLift.readFrame StageLift.witnessStore)
      (.seq (.op (.rwM StageLift.callStore))
        (StageLift.readMemoryVariable StageLift.callStore widthVar))))

/-- The prefix work of `prop:time`, paper/paper.tex, pays the exact original-call and parameter readers,
the retained witness frame, and the original-arity decoder. -/
def preparedInputCost (c : Call) (p : Cells.Parameters) (B : ℕ) (witness : List Bool) : ℕ :=
  (3000*((callWord c).length+1)^3+12*(callWord c).length+16)+
    (StageLift.parameterReadCost p B+
      ((8*witness.length+4)+
        (((callWord c).length+1)+(30*natBitLength c.n+32)+1)+1)+1)+1

/-- The actual preparation-prefix reader of `sec:algorithm` and
`prop:time`, paper/paper.tex, leaves the complete test suffix unread. It recovers arity
from original encoded bits and leaves both flag stores empty. -/
theorem readPreparedInput_spec (C : Ctx) (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=true::(callWord c++Program.parametersWord p++frame witness++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hwidth : ∀ value∈StageLift.parameterHeadFields p++p.primes.sort (·≤·)++
      StageLift.parameterTailFields p++p.factors,natBitLength value≤B)
    (hB : B+2≤C.Wd) (hcounts : p.primes.card<2^C.Wd ∧ p.factors.length<2^C.Wd)
    (hempty : ∀ store,a.ram store=[] ∧ a.rc store=0) :
    Hs C readPreparedInput a (preparedInputCost c p B witness) (fun b =>
      b.env widthVar=c.n ∧
      b.ram StageLift.parameterStore=StageLift.parameterScalars p ∧
      b.rc StageLift.parameterStore=46 ∧
      b.ram firstFlagStore=[] ∧ b.rc firstFlagStore=0 ∧
      b.ram secondFlagStore=[] ∧ b.rc secondFlagStore=0 ∧
      b.ip=a.ip+1+(callWord c).length+(Program.parametersWord p).length+(frame witness).length ∧
      C.inp.drop b.ip=rest ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b) := by
  have hnword : (natWord c.n).length≤(callWord c).length := by simp [callWord]
  have hnwidth : natBitLength c.n+2≤C.Wd := by rw [natWord_length] at hnword;omega
  unfold readPreparedInput preparedInputCost
  refine Hs.seq
    (StageLift.readCallSource_spec C c (Program.parametersWord p++frame witness++rest) a hc
      (by simpa only [List.append_assoc] using hin) hcall (hempty _))
    fun b ⟨hbi,_,hbcall,hbrcall,hbother,hbs,hbc,_⟩ => ?_
  have hbin : C.inp.drop b.ip=Program.parametersWord p++(frame witness++rest) := by
    rw [hbi,Nat.add_assoc,←List.drop_drop,hin,Nat.add_comm 1 (callWord c).length]
    simp only [List.drop_succ_cons,List.append_assoc,List.drop_left]
  have he : ∀ store∈[StageLift.parameterStore,StageLift.primeStore,StageLift.factorStore],
      b.ram store=[] ∧ b.rc store=0 := by
    intro store hs
    have hne : store≠StageLift.callStore := by
      rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hs) with
        rfl|rfl|rfl <;> decide
    rw [(hbother store hne).1,(hbother store hne).2]
    exact hempty store
  obtain ⟨d,td,ed,hd,⟨⟨hdi,hdp,_,_,_,_,hds,hdc,_⟩,hdpc,_,_⟩⟩ :=
    StageLift.readParameters_cursor_spec C p B (frame witness++rest) b hbc hbin hwidth hB hcounts he
  have hdother (store : Fin MM) (hs : store∉[StageLift.parameterStore,StageLift.primeStore,StageLift.factorStore]) :
      d.ram store=b.ram store ∧ d.rc store=b.rc store :=
    StageLift.avoidsStore_spec ed (StageLift.readParameters_avoids store hs)
  refine Hs.seq (show Hs C StageLift.readParameters b (StageLift.parameterReadCost p B)
    (·=d) from ⟨d,td,ed,hd,rfl⟩) fun e hed => ?_
  subst e
  have hdin : C.inp.drop d.ip=frame witness++rest := by
    rw [hdi,←List.drop_drop,hbin,List.drop_left]
  have hdw : d.ram StageLift.witnessStore=[] ∧ d.rc StageLift.witnessStore=0 := by
    rw [(hdother _ (by decide)).1,(hdother _ (by decide)).2,
      (hbother _ (by decide)).1,(hbother _ (by decide)).2]
    exact hempty _
  refine Hs.seq
    (StageLift.readFrame_spec C StageLift.witnessStore witness rest d hdc hdin
      (by rw [hdw.1,hdw.2];rfl))
    fun e ⟨hei,her,herc,heother,hes,hec,_⟩ => ?_
  have hecall : e.ram StageLift.callStore=(callWord c).map Bool.toNat := by
    rw [(heother _ (by decide)).1,(hdother _ (by decide)).1,hbcall]
  have hecallc : e.rc StageLift.callStore=(callWord c).length := by
    rw [(heother _ (by decide)).2,(hdother _ (by decide)).2,hbrcall]
  have hr : Hs C (.op (.rwM StageLift.callStore)) e ((callWord c).length+1)
      (·=e.rew StageLift.callStore) := by simpa only [hecallc] using hs_rwM C StageLift.callStore e
  refine Hs.seq hr fun f hf => ?_
  subst f
  have hninput : (callWord c).drop ((e.rew StageLift.callStore).rc StageLift.callStore)=
      natWord c.n++(natWord (kindTag c.kind)++circuitWord c.first++circuitWord c.second++
        listWord natWord c.parity++ratWord c.radius) := by
    simp only [DS.rew,Function.update_self,List.drop_zero,callWord,List.append_assoc]
  refine (StageLift.readMemoryVariable_spec C StageLift.callStore (callWord c)
    (e.rew StageLift.callStore) ⟨hec.z,hec.one,hec.two⟩ hecall widthVar (by decide) (by decide)
    c.n _ hninput hnwidth).mono le_rfl ?_
  rintro g ⟨hgn,_,hgs,hgc,_⟩
  have hgip : g.ip=e.ip := congrArg Prod.fst hgs
  have hgram : g.ram=e.ram := congrArg (fun q => q.2.2.1) hgs
  have hgrc (store : Fin MM) (hne : store≠StageLift.callStore) : g.rc store=e.rc store := by
    have hh := congrArg (fun q => q.2.2.2.1 store) hgs
    simpa only [StageLift.memorySourceRest,Function.update_of_ne hne,DS.rew] using hh
  refine ⟨hgn,?_,?_,?_,?_,?_,?_,?_,?_,?_,hgc⟩
  · rw [hgram,(heother _ (by decide)).1,hdp]
  · rw [hgrc _ (by decide),(heother _ (by decide)).2,hdpc]
  · rw [hgram,(heother _ (by decide)).1,(hdother _ (by decide)).1,(hbother _ (by decide)).1]
    exact (hempty _).1
  · rw [hgrc _ (by decide),(heother _ (by decide)).2,(hdother _ (by decide)).2,(hbother _ (by decide)).2]
    exact (hempty _).2
  · rw [hgram,(heother _ (by decide)).1,(hdother _ (by decide)).1,(hbother _ (by decide)).1]
    exact (hempty _).1
  · rw [hgrc _ (by decide),(heother _ (by decide)).2,(hdother _ (by decide)).2,(hbother _ (by decide)).2]
    exact (hempty _).2
  · rw [hgip,hei,hdi,hbi]
  · rw [hgip,hei,←List.drop_drop,hdin,List.drop_left]
  · have hgo : (g.out,g.kin,g.kout,g.kc)=(e.out,e.kin,e.kout,e.kc) :=
      congrArg (fun q => (q.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2)) hgs
    exact hgo.trans (hes.trans (hds.trans hbs))

end NearQuarticWires.StageCertificateControl
