import Proof.Quartic.StageCertificateControl.BatchedLedger
import Proof.Wire_3_5.PrimAsmCopyNat

/-!
# Copy actual binary metadata without numeric threshold expansion

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)

variable {ns nr : ℕ}

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
natural metadata fields are copied as their actual binary codecs. -/
def rawFieldsWord (fields : List ℕ) : List Bool := fields.flatMap RepairRepresentation.natWord

/-- `prop:time`, paper/paper.tex: the counted
copy traverses each field's unary length prefix and literal payload bits;
it never decodes the potentially enormous natural threshold value. -/
def copyRawFields (src dst : Fin (ns+1)) (f c OP K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (copyNatM false src dst f c OP))

/-- `prop:time`, paper/paper.tex: the marked
metadata bytes and source movement are recorded by actual copy counters. -/
def rawFieldsEnd (σ : WState ns nr) (src dst : Fin (ns+1)) (OP K : Fin nr)
    (fields : List ℕ) : WState ns nr :=
  ((appendO σ dst OP (marks (rawFieldsWord fields))).seth src
    (σ.sh src+(rawFieldsWord fields).length)).setv K 0

/-- `prop:time`, paper/paper.tex: copying the
actual metadata costs only its encoded bit length and field count,
uniformly over arbitrarily large threshold values. -/
theorem copyRawFields_spec (cap : ℕ) (src dst : Fin (ns+1)) (f c OP K : Fin nr)
    (hsd : src≠dst) (hfc : f≠c) (hfO : f≠OP) (hcO : c≠OP)
    (hKf : K≠f) (hKc : K≠c) (hKO : K≠OP) :
    ∀(fields : List ℕ) (pre rest : List Bool) (σ : WState ns nr),
      σ.st src=pre++rawFieldsWord fields++rest→σ.sh src=pre.length→
      σ.sh dst=(σ.st dst).length→σ.val f=0→σ.val c=0→σ.val K=fields.length→
      fields.length≤cap→σ.val OP+2*(rawFieldsWord fields).length+2≤cap→
      WExec cap (copyRawFields src dst f c OP K) σ (rawFieldsEnd σ src dst OP K fields)
        (100*((rawFieldsWord fields).length+fields.length+1))
  | [],pre,rest,σ,_,_,_,_,_,hK,_,_ => by
    have he : rawFieldsEnd σ src dst OP K []=σ := by
      apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst i;simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hsd]
        · by_cases hd : i=dst
          · subst i;simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hi]
          · simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hi,hd]
      · funext i
        by_cases hi : i=dst
        · subst i;simp [rawFieldsEnd,appendO,rawFieldsWord,marks]
        · simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hi]
      · funext i
        by_cases hi : i=K
        · subst i;simp [rawFieldsEnd,hK]
        · by_cases ho : i=OP
          · subst i;simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hi]
          · simp [rawFieldsEnd,appendO,rawFieldsWord,marks,hi,ho]
      · rfl
    rw [he]
    exact (WExec.whrF (by simpa using hK)).mono (by simp [rawFieldsWord])
  | x::xs,pre,rest,σ,hst,hsh,hd,hf,hc,hK,hcount,hcap => by
    have hlen : (rawFieldsWord (x::xs)).length=(RepairRepresentation.natWord x).length+
        (rawFieldsWord xs).length := by simp [rawFieldsWord]
    have ed := WExec.dec (cap := cap) K σ (by rw [hK];exact hcount)
    let σ1 := σ.setv K xs.length
    have eσ1 : σ.setv K (σ.val K-1)=σ1 := by rw [hK];rfl
    rw [eσ1] at ed
    have ec := copyNatM_spec cap false src dst hsd f c OP hfc hfO hcO x pre
      (rawFieldsWord xs++rest) σ1
      (by simpa only [σ1,WState.setv_st,rawFieldsWord,List.flatMap_cons,List.append_assoc,
        NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,if_neg Bool.false_ne_true] using hst)
      hsh hd (by simp [σ1,hKf.symm,hf]) (by simp [σ1,hKc.symm,hc])
      (by simp only [σ1,WState.setv_val,Function.update_of_ne hKO.symm];rw [hlen] at hcap;omega)
    simp only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp,if_neg Bool.false_ne_true,one_mul] at ec
    let σ2 := (appendO σ1 dst OP (marks (RepairRepresentation.natWord x))).seth src
      (pre.length+(RepairRepresentation.natWord x).length)
    have hnext : σ2.st src=(pre++RepairRepresentation.natWord x)++rawFieldsWord xs++rest := by
      simpa [σ2,appendO,hsd,σ1,rawFieldsWord,List.append_assoc] using hst
    have hh : σ2.sh src=(pre++RepairRepresentation.natWord x).length := by simp [σ2]
    have hout : σ2.sh dst=(σ2.st dst).length := by
      simp [σ2,σ1,appendO,hsd.symm,hd]
    have hff : σ2.val f=0 := by simp [σ2,appendO,hfO,σ1,hKf.symm,hf]
    have hcc : σ2.val c=0 := by simp [σ2,appendO,hcO,σ1,hKc.symm,hc]
    have hKK : σ2.val K=xs.length := by simp [σ2,appendO,hKO,σ1]
    have htail : σ2.val OP+2*(rawFieldsWord xs).length+2≤cap := by
      simp only [σ2,WState.seth_val,appendO,WState.setv_val,Function.update_self,WState.seth_val,
        σ1,Function.update_of_ne hKO.symm,marks_length]
      rw [hlen] at hcap
      omega
    have er := copyRawFields_spec cap src dst f c OP K hsd hfc hfO hcO hKf hKc hKO
      xs (pre++RepairRepresentation.natWord x) rest σ2 hnext hh hout hff hcc hKK
      (by simp only [List.length_cons] at hcount;omega) htail
    refine (WExec.whrT (by rw [hK];simp) (ed.seq ec) er).cast cap ?_ ?_
    · apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst i;simp [rawFieldsEnd,σ2,σ1,appendO,hsd,rawFieldsWord,hsh];omega
        · by_cases ho : i=dst
          · subst i;simp [rawFieldsEnd,σ2,σ1,appendO,hi,rawFieldsWord,marks_length];omega
          · simp [rawFieldsEnd,σ2,σ1,appendO,hi,ho]
      · funext i
        by_cases hi : i=dst
        · subst i;simp [rawFieldsEnd,σ2,σ1,appendO,rawFieldsWord,
            NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
        · simp [rawFieldsEnd,σ2,σ1,appendO,hi]
      · funext i
        by_cases hi : i=K
        · subst i;simp [rawFieldsEnd]
        · by_cases ho : i=OP
          · subst i;simp [rawFieldsEnd,σ2,σ1,appendO,hi,rawFieldsWord,marks_length];omega
          · simp [rawFieldsEnd,σ2,σ1,appendO,hi,ho]
      · rfl
    · simp only [hlen,List.length_cons]
      omega

end NearQuarticWires.StageCertificateControl
