import Proof.Quartic.StageCert.IncidenceWeights

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep
open NearCubicWires.RepairRepresentation (natWord)

/-- `sec:cells`, paper/paper.tex: one physical raw-gate
scan extracts the selected original-coordinate incidence and skips its
threshold without charging it as an input wire. -/
def readCoordinateGate : St VV :=
  .seq readNat (.seq (.op (.copy weightLength t3))
    (.seq (.op (.zero weightIndex)) (.seq readCoordinateWeights readInt)))

/-- `sec:cells`, paper/paper.tex: the coordinate census
changes only its count and signed-weight parser scratch registers. -/
def gateScratch : List (Fin VV) :=
  [censusTotal,weightIndex,weightLength,t0,t1,t2,t3,t4,t8,vJ,vPOS]

/-- `sec:cells` and `prop:time`, paper/paper.tex: the actual original gate word contributes one precisely when
its selected signed weight is nonzero, with every encoded field consumed. -/
theorem readCoordinateGate_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (i : Fin n) (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcoord : a.env coordinate=i.val)
    (hin : C.cw.drop a.cp=gateWord g++rest)
    (hW : C.cw.length+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd)
    (ht : a.env censusTotal+n+2<2^C.Wd) :
    Hs C readCoordinateGate a (120*(C.cw.length+2)^2) (fun b =>
      b.env censusTotal=a.env censusTotal+wireBit (g.weight i) ∧
      b.cp=a.cp+(gateWord g).length ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b gateScratch) := by
  let ws := List.ofFn g.weight
  have hws : ws.length=n := by simp [ws]
  have hg : gateWord g=natWord ws.length++(ws.flatMap intWord++intWord g.threshold) := by
    simp [gateWord,listWord,ws,List.append_assoc]
  have hlen := len_le_of_drop hin
  have hnlen : n≤C.cw.length := by
    have hh := length_le_flatMap ws intWord intWord_len_pos
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  have hnbit : natBitLength ws.length≤C.cw.length := by
    have hh := natBitLength_le_len ws.length
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  have hthreshold : (intWord g.threshold).length≤C.cw.length := by
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  rw [hg,List.append_assoc] at hin
  unfold readCoordinateGate
  refine Hx.hs (Hs.then (readNat_spec a hc ws.length _ hin (by omega) hL)
    (fun b ⟨hb3,_hh,hbcp,hw,ho,hbc,hbf⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C weightLength t3 b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  refine Hs.then (hs_zero C weightIndex _) (fun e he n3 hn3 => ?_)
  subst he
  let d := (b.set weightLength (b.env t3)).set weightIndex 0
  have dc : Cst d := by
    refine Cst.of_fr (T := [weightLength,weightIndex]) hbc
      ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide))) (by decide) ?_
    simp only [d,DS.set_cp]
    rw [DS.set_env_ne _ _ (by decide),DS.set_env_ne _ _ (by decide)]
    exact hbc.pos
  have dt : d.env censusTotal=a.env censusTotal := by
    simp only [d]
    rw [DS.set_env_ne _ _ (by decide),DS.set_env_ne _ _ (by decide),hbf _ (by decide)]
  have di : d.env coordinate=i.val := by
    simp only [d]
    rw [DS.set_env_ne _ _ (by decide),DS.set_env_ne _ _ (by decide),hbf _ (by decide)]
    exact hcoord
  have dword : C.cw.drop d.cp=ws.flatMap intWord++intWord g.threshold++rest := by
    change C.cw.drop b.cp=_
    rw [hbcp,←List.drop_drop,hin,List.drop_left,List.append_assoc]
  refine Hs.then (readCoordinateWeights_run C ws (intWord g.threshold++rest) d dc i.val di
    (by simp [d]) (by simp only [d]; rw [DS.set_env_ne _ _ (by decide),DS.set_env_self,hb3])
    (by simpa only [List.append_assoc] using dword) hW hL (by rw [dt,hws]; omega))
    (fun f ⟨ft,fc,fw,fo,fconst,ff,_hi,_hl⟩ n4 hn4 => ?_)
  have fword : C.cw.drop f.cp=intWord g.threshold++rest := by
    rw [fc,←List.drop_drop]
    rw [show C.cw.drop d.cp=ws.flatMap intWord++(intWord g.threshold++rest) by
      simpa only [List.append_assoc] using dword,List.drop_left]
  refine Hs.last (readInt_spec f fconst g.threshold rest fword hW hL)
    (fun q ⟨_sgn,_mag,_bl,qcp,qw,qo,qconst,qf⟩ n5 hn5 => ?_)
  refine ⟨⟨?_,?_,qw.trans (fw.trans hw),qo.trans (fo.trans ho),qconst,
    (hbf.weaken (by decide)).trans
      ((Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))).trans
        ((ff.weaken (by decide)).trans (qf.weaken (by decide))))⟩,?_⟩
  · rw [qf censusTotal (by decide),ft,dt]
    have hii : i.val<ws.length := by rw [hws]; exact i.isLt
    have hv : ws.getD i.val 0=g.weight i := by
      rw [List.getD_eq_getElem ws 0 hii]
      simp [ws]
    simp only [coordinatePrefix,hws,i.isLt,if_pos,hv]
  · rw [qcp,fc]
    change b.cp+(ws.flatMap intWord).length+(intWord g.threshold).length=_
    rw [hbcp]
    simp only [hg,List.length_append]
    omega
  · rw [hws] at hn4
    have hprod := Nat.mul_le_mul_right (60*C.cw.length+78) hnlen
    nlinarith only [hn1,hn2,hn3,hn4,hn5,hnlen,hnbit,hthreshold,hprod]

end NearQuarticWires.StageCert.Incidence
