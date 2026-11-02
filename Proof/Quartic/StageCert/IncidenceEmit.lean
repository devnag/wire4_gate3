import Proof.Quartic.StageCert.IncidenceHeavy
import Proof.Gates.Dispatch.Print

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:algorithm`, paper/paper.tex: one computed incidence or
heavy flag is written as an exact self-delimiting natural record. -/
def emitStoredNat (x : Fin VV) : St VV := .seq (.op (.copy t3 x)) emitNat

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: record emission preserves every caller register outside the
explicit binary-emitter scratch set. -/
theorem emitStoredNat_run (C : Ctx) (x : Fin VV) (hx : x≠t3)
    (a : DS VV) (hc : Cst a) (hW : 2≤C.Wd)
    (hfit : natBitLength (a.env x)+2<2^C.Wd) :
    Hs C (emitStoredNat x) a (40*natBitLength (a.env x)+42) (fun b =>
      b.out=a.out++natWord (a.env x) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ Cst b ∧
      Fr a b (t3::emitNatT)) := by
  unfold emitStoredNat
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40*natBitLength (a.env x)+40)
    (hs_copy C t3 x a (Ne.symm hx)) (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  have hbc : Cst (a.set t3 (a.env x)) := by
    refine Cst.of_fr (T := [t3]) hc (Fr.set _ _ (by simp)) (by decide) ?_
    rw [DS.set_env_ne _ _ (by decide)]
    exact hc.pos
  have h := emitNat_spec (a.set t3 (a.env x)) hbc hW (by simpa using hfit)
  simp only [DS.set_env_self] at h
  refine h.mono le_rfl ?_
  rintro b ⟨ho,hcp,hw,hc',hf⟩
  exact ⟨ho,hcp,hw,hc',(Fr.set _ _ (by simp)).trans
    (hf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))⟩

/-- `sec:algorithm`, paper/paper.tex: the coordinate record
contains the original raw incidence followed by its actual heavy bit. -/
def emitCoordinateRecord : St VV :=
  .seq (emitStoredNat StagePrep.censusTotal) (emitStoredNat heavyBit)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: exact physical writing of both computed coordinate fields. -/
theorem emitCoordinateRecord_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (hW : 2≤C.Wd)
    (hd : natBitLength (a.env StagePrep.censusTotal)+2<2^C.Wd)
    (hh : natBitLength (a.env heavyBit)+2<2^C.Wd) :
    Hs C emitCoordinateRecord a
      (40*(natBitLength (a.env StagePrep.censusTotal)+natBitLength (a.env heavyBit))+85)
      (fun b => b.out=a.out++natWord (a.env StagePrep.censusTotal)++natWord (a.env heavyBit) ∧
        b.cp=a.cp ∧ b.wq=a.wq ∧ Cst b ∧ Fr a b (t3::emitNatT)) := by
  unfold emitCoordinateRecord
  apply Hx.hs
  refine Hs.then (emitStoredNat_run C StagePrep.censusTotal (by decide) a hc hW hd) ?_
  rintro b ⟨bo,bc,bw,bconst,bf⟩ n1 hn1
  have bh : b.env heavyBit=a.env heavyBit := bf _ (by decide)
  refine Hs.last (emitStoredNat_run C heavyBit (by decide) b bconst hW (by rw [bh]; exact hh)) ?_
  rintro d ⟨doo,dc,dw,dconst,df⟩ n2 hn2
  refine ⟨⟨by rw [doo,bo,bh],dc.trans bc,dw.trans bw,dconst,bf.trans df⟩,?_⟩
  rw [bh] at hn2
  omega

end NearQuarticWires.StageCert.Incidence
