import Proof.Quartic.StageCertificateControl.MetadataPrefix

/-!
# Copy the actual fifth metadata field

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.WordPrograms
open StageCertTests (TestMetadata)

variable {ns nr : ℕ}

/-- `prop:time`, paper/paper.tex: a fixed
field census is installed by literal increments before the binary copy. -/
def copyFixedFields (src dst : Fin (ns+1)) (f c OP K : Fin nr) (n : ℕ) : WMX ns nr :=
  .seq (Control.incTimes K n) (.wm (copyRawFields src dst f c OP K))

/-- `prop:time`, paper/paper.tex: the actual
copy records the marked bytes and source distance while retaining its
initially zero field counter. -/
def fixedFieldsEnd (σ : WState ns nr) (src dst : Fin (ns+1)) (OP : Fin nr)
    (fields : List ℕ) : WState ns nr :=
  (appendO σ dst OP (marks (rawFieldsWord fields))).seth src
    (σ.sh src+(rawFieldsWord fields).length)

/-- `prop:time`, paper/paper.tex: copying a
fixed number of fields costs their binary length, uniformly over the
numeric values of every field. -/
theorem copyFixedFields_spec (cap : ℕ) (src dst : Fin (ns+1)) (f c OP K : Fin nr)
    (hsd : src≠dst) (hfc : f≠c) (hfO : f≠OP) (hcO : c≠OP)
    (hKf : K≠f) (hKc : K≠c) (hKO : K≠OP)
    (n : ℕ) (fields : List ℕ) (hlen : fields.length=n) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st src=pre++rawFieldsWord fields++rest)
    (hsh : σ.sh src=pre.length) (hd : σ.sh dst=(σ.st dst).length)
    (hf : σ.val f=0) (hc : σ.val c=0) (hK : σ.val K=0)
    (hn : n≤cap) (hcap : σ.val OP+2*(rawFieldsWord fields).length+2≤cap) :
    WXExec cap (copyFixedFields src dst f c OP K n) σ (fixedFieldsEnd σ src dst OP fields)
      (4*n+100*((rawFieldsWord fields).length+n+1)+1) := by
  have ei := Control.incTimes_exec cap K n σ (by rw [hK];simpa using hn)
  rw [hK,Nat.zero_add] at ei
  let a := σ.setv K n
  have er := copyRawFields_spec cap src dst f c OP K hsd hfc hfO hcO hKf hKc hKO
    fields pre rest a hst hsh hd
    (by simp [a,Function.update_of_ne hKf.symm,hf])
    (by simp [a,Function.update_of_ne hKc.symm,hc])
    (by simp [a,hlen]) (by rw [hlen];exact hn)
    (by simpa only [a,WState.setv_val,Function.update_of_ne hKO.symm] using hcap)
  have he : rawFieldsEnd a src dst OP K fields=fixedFieldsEnd σ src dst OP fields := by
    apply WState.eq
    · simp [rawFieldsEnd,fixedFieldsEnd,appendO,a]
    · simp [rawFieldsEnd,fixedFieldsEnd,appendO,a]
    · funext i
      by_cases hi : i=K
      · subst i;simp [rawFieldsEnd,fixedFieldsEnd,appendO,hKO,hK]
      · by_cases ho : i=OP
        · subst i;simp [rawFieldsEnd,fixedFieldsEnd,appendO,a,hKO.symm,hi]
        · simp [rawFieldsEnd,fixedFieldsEnd,appendO,a,hi,ho,hKO.symm]
    · rfl
  refine (ei.seq (WXExec.wm er)).cast cap he ?_
  rw [hlen]
  omega

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the first four metadata fields go to a discard tape and the fifth
binary field goes to a distinct threshold tape. -/
def copyThresholdFields (src discard value : Fin (ns+1)) (R : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (copyFixedFields src discard (R 0) (R 1) (R 3) (R 2) 4)
    (copyFixedFields src value (R 0) (R 1) (R 4) (R 2) 1)

/-- `prop:time`, paper/paper.tex: the
threshold extraction retains the exact source bytes and both actual
marked-byte counters. -/
def thresholdFieldsEnd (σ : WState ns nr) (src discard value : Fin (ns+1))
    (R : Fin 5 ↪ Fin nr) (m : TestMetadata) : WState ns nr :=
  fixedFieldsEnd (fixedFieldsEnd σ src discard (R 3) ((metadataFields m).take 4))
    src value (R 4) [m.threshold]

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the physical threshold extraction
has a clock linear in metadata bytes, with no unary threshold cost. -/
theorem copyThresholdFields_spec (cap : ℕ) (src discard value : Fin (ns+1))
    (R : Fin 5 ↪ Fin nr) (hsd : src≠discard) (hsv : src≠value) (hdv : discard≠value)
    (m : TestMetadata) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src=pre++m.word++rest) (hsh : σ.sh src=pre.length)
    (hd : σ.sh discard=(σ.st discard).length) (hv : σ.sh value=(σ.st value).length)
    (hz : ∀ i : Fin 3,σ.val (R i.castSucc.castSucc)=0)
    (hfour : 4≤cap) (hskip : σ.val (R 3)+2*m.word.length+2≤cap)
    (hvalue : σ.val (R 4)+2*m.word.length+2≤cap) :
    WXExec cap (copyThresholdFields src discard value R) σ
      (thresholdFieldsEnd σ src discard value R m) (1000*(m.word.length+1)) := by
  have rn {i j : Fin 5} (h : i≠j) : R i≠R j := R.injective.ne h
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have h2 : σ.val (R 2)=0 := hz 2
  let fields := (metadataFields m).take 4
  have hlen : fields.length=4 := by simp [fields,metadataFields]
  have hword : m.word=rawFieldsWord fields++rawFieldsWord [m.threshold] := by
    simpa [rawFieldsWord,fields] using metadataThreshold_word m
  have hlength : m.word.length=(rawFieldsWord fields).length+(rawFieldsWord [m.threshold]).length := by
    rw [hword,List.length_append]
  have ea := copyFixedFields_spec cap src discard (R 0) (R 1) (R 3) (R 2) hsd
    (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) 4 fields hlen pre
    (rawFieldsWord [m.threshold]++rest) σ
    (by simpa only [hword,List.append_assoc] using hst) hsh hd
    (hz 0) (hz 1) (hz 2) hfour (by omega)
  let a := fixedFieldsEnd σ src discard (R 3) fields
  have eb := copyFixedFields_spec cap src value (R 0) (R 1) (R 4) (R 2) hsv
    (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) 1 [m.threshold] rfl
    (pre++rawFieldsWord fields) rest a
    (by simpa [a,fixedFieldsEnd,appendO,hsd,hword,List.append_assoc] using hst)
    (by simp [a,fixedFieldsEnd,appendO,hsh])
    (by simp [a,fixedFieldsEnd,appendO,hdv.symm,hsv.symm,hv])
    (by simp [a,fixedFieldsEnd,appendO,rn (show (0 : Fin 5)≠3 by decide),h0])
    (by simp [a,fixedFieldsEnd,appendO,rn (show (1 : Fin 5)≠3 by decide),h1])
    (by simp [a,fixedFieldsEnd,appendO,rn (show (2 : Fin 5)≠3 by decide),h2])
    (by omega)
    (by simp only [a,fixedFieldsEnd,WState.seth_val,appendO,WState.setv_val,WState.sets_val,
      Function.update_of_ne (rn (show (4 : Fin 5)≠3 by decide))];omega)
  exact (ea.seq eb).mono (by omega)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the extracted threshold is its unchanged binary natural codec. -/
theorem thresholdFieldsEnd_value (σ : WState ns nr) (src discard value : Fin (ns+1))
    (R : Fin 5 ↪ Fin nr) (m : TestMetadata) (hdv : discard≠value) :
    (thresholdFieldsEnd σ src discard value R m).st value=
      σ.st value++marks (RepairRepresentation.natWord m.threshold) := by
  simp [thresholdFieldsEnd,fixedFieldsEnd,appendO,hdv.symm,rawFieldsWord]

end NearQuarticWires.StageCertificateControl
