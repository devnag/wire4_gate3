import Proof.Quartic.StageCert.WidthGuards

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the body of a framed word,
without its final delimiter. -/
def framedBody (s : List Bool) : List Bool := s.flatMap (fun b => [true,b])

/-- `prop:time`, paper/paper.tex: the preserved preparation
word is copied with the exact outer framing. -/
theorem frame_eq_body (s : List Bool) : frame s = framedBody s ++ [false] := by
  induction s with
  | nil => rfl
  | cons b s ih => simpa [frame, framedBody] using congrArg (fun t => true::b::t) ih

/-- `sec:algorithm`, paper/paper.tex: registers of the
preparation-word copy loop. -/
def payloadLength : Fin VV := ⟨46, by decide⟩
def payloadIndex : Fin VV := ⟨47, by decide⟩
def payloadBit : Fin VV := ⟨48, by decide⟩

/-- `sec:algorithm`, paper/paper.tex: one actual read and
framed write of a preparation bit. -/
def copyPayloadBody : St VV MM :=
  .seq (.op (.rdI payloadBit)) (.seq (.op (.emit true))
    (.seq (emitB .emit payloadBit) (.op (.inc payloadIndex))))

/-- `sec:algorithm`, paper/paper.tex: the copy loop retains
every byte of the prepared call, parameter record and witness prefix. -/
def copyPayload : St VV MM := .loop (.lt payloadIndex payloadLength) copyPayloadBody

/-- `sec:algorithm`, paper/paper.tex: exact cursor, output,
and register frame of the physical preparation-word copy. -/
structure PayloadCopied (C : Ctx) (a b : DS VV MM) (s rest : List Bool) : Prop where
  cst : Cst b
  tail : C.inp.drop b.ip = rest
  out : b.out = a.out ++ framedBody s
  index : b.env payloadIndex = a.env payloadIndex+s.length
  keep : Fr a b [payloadBit,payloadIndex]

/-- `sec:algorithm`, paper/paper.tex: copying the preparation
word costs a constant number of binary operations per bit. -/
theorem copyPayload_run (C : Ctx) (s : List Bool) :
    ∀ (a : DS VV MM), Cst a → ∀ rest,
      C.inp.drop a.ip = s ++ rest →
      a.env payloadIndex+s.length = a.env payloadLength →
      a.env payloadLength < 2^C.Wd →
      Hs C copyPayload a (10*s.length+2) (fun b => PayloadCopied C a b s rest) := by
  induction s with
  | nil =>
    intro a hc rest hin hi hn
    have ht : Cnd.eval a (.lt payloadIndex payloadLength) = false := by
      simp only [Cnd.eval, decide_eq_false_iff_not]
      simp only [List.length_nil, Nat.add_zero] at hi
      omega
    refine ⟨a,2,Ex.loopF (by norm_num [Cnd.wf,payloadIndex,payloadLength]) ht, by simp, ?_⟩
    exact ⟨hc,by simpa using hin,by simp [framedBody],by simp,Fr.refl _ _⟩
  | cons bit s ih =>
    intro a hc rest hin hi hn
    have ht : Cnd.eval a (.lt payloadIndex payloadLength) = true := by
      simp only [Cnd.eval, decide_eq_true_eq]
      simp only [List.length_cons] at hi
      omega
    have hip : a.ip < C.inp.length := lt_of_drop hin 0 (by simp)
    have hbit : bitOf C.inp a.ip = bit.toNat := by
      have h := bitOf_drop hin 0 (by simp)
      simpa using h
    let b := {a.set payloadBit (bitOf C.inp a.ip) with ip := a.ip+1}
    have eb : Ex C (.op (.rdI payloadBit)) a b 1 := Ex.op (OpEx.rdI payloadBit a hip)
    have hbCst : Cst b := by
      exact ⟨by simpa [b,DS.set,payloadBit,vZ] using hc.z,
        by simpa [b,DS.set,payloadBit,v1] using hc.one,
        by simpa [b,DS.set,payloadBit,v2] using hc.two⟩
    let c := {b with out := b.out ++ [true]}
    have ec : Ex C (.op (.emit true)) b c 1 := Ex.op (OpEx.emit true b)
    have hcCst : Cst c := ⟨hbCst.z,hbCst.one,hbCst.two⟩
    obtain ⟨d,nd,ed,hdCost,hd⟩ := emitB_spec (snkO C) payloadBit (by decide) c hcCst trivial
    have hdEnv : d.env = b.env := hd.2.2
    have hdIp : d.ip = b.ip := congrArg Prod.fst hd.2.1
    have hdCst : Cst d := ⟨by rw [hdEnv]; exact hbCst.z,
      by rw [hdEnv]; exact hbCst.one, by rw [hdEnv]; exact hbCst.two⟩
    have hdI : d.env payloadIndex = a.env payloadIndex := by simp [hdEnv,b,DS.set,payloadIndex,payloadBit]
    have hdN : d.env payloadLength = a.env payloadLength := by simp [hdEnv,b,DS.set,payloadLength,payloadBit]
    have hinc : d.env payloadIndex+1 < 2^C.Wd := by simp only [List.length_cons] at hi; omega
    let e := d.set payloadIndex (d.env payloadIndex+1)
    have ee : Ex C (.op (.inc payloadIndex)) d e 1 := Ex.op (OpEx.inc payloadIndex d hinc)
    have ebody : Ex C copyPayloadBody a e (1+(1+(nd+1+1)+1)+1) := Ex.seq eb (Ex.seq ec (Ex.seq ed ee))
    have heCst : Cst e := Cst.of_fr hdCst (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
    have heTail : C.inp.drop e.ip = s ++ rest := by
      change C.inp.drop d.ip = _
      rw [hdIp]
      change C.inp.drop (a.ip+1) = _
      exact drop_adv (by simpa using hin : C.inp.drop a.ip = [bit] ++ (s ++ rest))
    have heI : e.env payloadIndex = a.env payloadIndex+1 := by simp [e,hdI]
    have heKeep : Fr a e [payloadBit,payloadIndex] := by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hy
      change (d.set payloadIndex _).env y = a.env y
      rw [DS.set_env_ne _ _ hy.2,hdEnv]
      simp only [b,DS.set]
      exact Function.update_of_ne hy.1 _ _
    obtain ⟨f,nf,ef,hfCost,hf⟩ := ih e heCst rest heTail
      (by rw [heI,heKeep payloadLength (by decide)]; simp only [List.length_cons] at hi; omega)
      (by rw [heKeep payloadLength (by decide)]; exact hn)
    refine ⟨f,1+(1+(nd+1+1)+1)+1+nf+2,
      Ex.loopT (by norm_num [Cnd.wf,payloadIndex,payloadLength]) ht ebody ef, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · refine ⟨hf.cst,hf.tail,?_,?_,heKeep.trans hf.keep⟩
      · have heOut : e.out = a.out ++ [true,bit] := by
          change d.out = _
          have hdo : d.out = c.out ++ [decide (c.env payloadBit=1)] := hd.1
          rw [hdo]
          have hv : decide (c.env payloadBit=1) = bit := by cases bit <;> simp [c,b,DS.set,hbit]
          rw [hv]
          simp [c,b,List.append_assoc]
        rw [hf.out,heOut]
        simp [framedBody,List.append_assoc]
      · rw [hf.index,heI]
        simp only [List.length_cons]
        omega

end NearQuarticWires.StageCert
