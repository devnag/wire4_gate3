import Proof.Quartic.StagePrintTuple.SupportCopy
import Proof.Quartic.StagePrintTuple.Coefficient
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: support copying
uses its own output-position register and the fixed seven scratch slots. -/
def supportRegisters : Fin 8 ↪ Fin 11 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 8]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- `lem:print`, paper/paper.tex: coefficient
packet construction has a separate output cursor and preserves the
actual field width in register10 throughout the support copy. -/
def coefficientRegisters : Fin 8 ↪ Fin 11 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 9]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- `lem:print`, paper/paper.tex: the physical
monomial formatter retains the support exactly once, constructs a
small actual signed-coefficient packet and advances to the next term. -/
def monomialFormatProgramOn {ns : ℕ} (src supp coef : Fin (ns + 1)) : WM ns 11 :=
  .seq (FinalPass.Hash4.wcopyR 10 0 6)
    (.seq (writeNatM coef coefficientRegisters)
      (.seq (WM.clear 0)
        (.seq (supportCopyProgram src supp supportRegisters)
          (.seq (Codec.copyInt false src coef coefficientRegisters) (emitC coef 9 false)))))

/-- `prop:time`, paper/paper.tex: one monomial
pays its actual width header, one support-buffer copy and one literal
signed coefficient copy, with no repeated complete Terms scan. -/
def monomialFormatCost (W : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  30 * W + (natBitLength W + 10) * (100 * W + 200) + supportCopyCost support +
    60 * (intWord coefficient).length + 200

/-- `lem:print`, paper/paper.tex: the two buffers
are produced from the real monomial cursor; all logical lists and
integers in the statement specify the literal input bytes only. -/
theorem monomialFormatProgram_on_full_spec {ns : ℕ} (src supp coef : Fin (ns + 1))
    (hss : src ≠ supp) (hsc : src ≠ coef) (hpc : supp ≠ coef) (cap W : ℕ) (support : List ℕ) (coefficient : ℤ)
    (pre rest : List Bool) (σ : WState ns 11)
    (hsource : σ.st src = pre ++ listWord natWord support ++ intWord coefficient ++ rest)
    (hhead : σ.sh src = pre.length) (hS : σ.st supp = []) (hSH : σ.sh supp = 0)
    (hC : σ.st coef = []) (hCH : σ.sh coef = 0)
    (hW : σ.val 10 = W) (hz : ∀ i : Fin 11, i ≠ 10 → σ.val i = 0)
    (hwrite : W + 6 * natBitLength W + 6 ≤ cap)
    (hpow : 2 ^ (natBitLength support.length + 1) ≤ cap)
    (hlen : support.length ≤ cap)
    (hSw : support.length + 6 * natBitLength support.length + 6 ≤ cap)
    (hSo : 2 * (listWord natWord support).length + 3 ≤ cap)
    (hCo : 2 * (natWord W).length + 2 * (intWord coefficient).length + 4 ≤ cap) :
    ∃ b, WExec cap (monomialFormatProgramOn src supp coef) σ b (monomialFormatCost W support coefficient) ∧
      b.st supp = frame (listWord natWord support) ∧
      b.st coef = frame (natWord W ++ intWord coefficient) ∧ b.st src = σ.st src ∧
      b.sh src = pre.length + (listWord natWord support ++ intWord coefficient).length ∧
      b.val 10 = W ∧
      b.sh supp=(frame (listWord natWord support)).length ∧
      b.sh coef=(frame (natWord W++intWord coefficient)).length ∧
      b.val 8=(frame (listWord natWord support)).length ∧
      b.val 9=(frame (natWord W++intWord coefficient)).length := by
  have e1 := FinalPass.Hash4.wcopyR_spec cap (10 : Fin 11) 0 6
    (by decide) (by decide) (by decide) σ (hz _ (by decide)) (hz _ (by decide))
    (by rw [hW]; omega)
  let s1 := σ.setv 0 W
  have e1' : WExec cap (FinalPass.Hash4.wcopyR 10 0 6) σ s1 (18 * W + 3) := by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, hW] using e1
  have ew := writeNatM_spec cap coef coefficientRegisters s1
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz]) (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz]) (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz]) (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, hCH, hC])
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s1, coefficientRegisters, hz] using hwrite)
  let s2 := appendO s1 coef 9 (marks (natWord W))
  have ew' : WExec cap (writeNatM coef coefficientRegisters) s1 s2
      ((natBitLength W + 10) * (100 * W + 200)) := by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s2, s1, coefficientRegisters] using ew
  have ec := wclear_spec cap (0 : Fin 11) W s2 (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s2, s1, appendO])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s2, s1, appendO]; omega)
  let s3 := s2.setv 0 0
  have es := supportCopyProgram_spec cap src supp hss supportRegisters support
    pre (intWord coefficient ++ rest) s3
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s3, s2, s1, appendO, List.append_assoc] using hsource)
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s3, s2, s1, appendO] using hhead)
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s3, s2, s1, appendO, hSH, hS])
    (by intro i hi; fin_cases i <;> simp_all [s3, s2, s1, appendO, supportRegisters, hz])
    (2 * (listWord natWord support).length) (by omega) hpow hlen
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s3, s2, s1, appendO, supportRegisters, hz] using hSw)
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s3, s2, s1, appendO, supportRegisters, hz, Streaming.marks_length])
  let s4 := appendO ((appendO s3 supp 8 (marks (listWord natWord support))).seth src
    (pre.length + (listWord natWord support).length)) supp 8 [false]
  have es' : WExec cap (supportCopyProgram src supp supportRegisters) s3 s4 (supportCopyCost support) := by
    simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, supportRegisters] using es
  have hcsrc : s4.st src = (pre ++ listWord natWord support) ++ intWord coefficient ++ rest := by
    simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, s3, s2, s1, List.append_assoc] using hsource
  have ei := Codec.copyInt_spec cap false src coef hsc coefficientRegisters
    coefficient (pre ++ listWord natWord support) rest s4
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hcsrc)
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, List.length_append])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, s3, s2, s1, hCH, hC])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, s3, s2, s1, coefficientRegisters, hz])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, s3, s2, s1, coefficientRegisters, hz])
    (by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s4, appendO, s3, s2, s1, coefficientRegisters, hz, Streaming.marks_length] using hCo)
  let s5 := (appendO s4 coef 9 (marks (intWord coefficient))).seth src
    ((pre ++ listWord natWord support).length + (intWord coefficient).length)
  have ei' : WExec cap (Codec.copyInt false src coef coefficientRegisters) s4 s5
      (60 * (intWord coefficient).length + 121) := by simpa [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, coefficientRegisters, stp] using ei
  have ef := Codec.emitBit_spec cap coef (9 : Fin 11) false s5
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1, hCH, hC, Nat.add_assoc])
    (by simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1, hz, Streaming.marks_length] at *; omega)
  refine ⟨appendO s5 coef 9 [false], (e1'.seq (ew'.seq (ec.seq (es'.seq (ei'.seq ef))))).mono ?_, ?_⟩
  · unfold monomialFormatCost
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1, hS, Codec.frame_eq_marks]
    · simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1, hC, Codec.frame_eq_marks,
        Streaming.marks_append, List.append_assoc]
    · simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1]
    · simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, List.length_append, Nat.add_assoc]
    · simp [hss, hsc, hpc, hss.symm, hsc.symm, hpc.symm, s5, s4, appendO, s3, s2, s1, hW]
    · simp [hss,hsc,hpc,hss.symm,hsc.symm,hpc.symm,s5,s4,appendO,s3,s2,s1,hSH,hS,frame_length]
    · simp [hss,hsc,hpc,hss.symm,hsc.symm,hpc.symm,s5,s4,appendO,s3,s2,s1,hCH,hC,frame_length]
      omega
    · simp [hss,hsc,hpc,hss.symm,hsc.symm,hpc.symm,s5,s4,appendO,s3,s2,s1,hz,frame_length,supportRegisters,coefficientRegisters]
    · simp [hss,hsc,hpc,hss.symm,hsc.symm,hpc.symm,s5,s4,appendO,s3,s2,s1,hz,frame_length,supportRegisters,coefficientRegisters]
      omega

/-- `lem:print`, paper/paper.tex: the exact
source and field-buffer conclusions follow from the complete formatter
state, including its physically computed output-byte counters. -/
theorem monomialFormatProgram_on_spec {ns : ℕ} (src supp coef : Fin (ns + 1))
    (hss : src ≠ supp) (hsc : src ≠ coef) (hpc : supp ≠ coef) (cap W : ℕ) (support : List ℕ) (coefficient : ℤ)
    (pre rest : List Bool) (σ : WState ns 11)
    (hsource : σ.st src = pre ++ listWord natWord support ++ intWord coefficient ++ rest)
    (hhead : σ.sh src = pre.length) (hS : σ.st supp = []) (hSH : σ.sh supp = 0)
    (hC : σ.st coef = []) (hCH : σ.sh coef = 0)
    (hW : σ.val 10 = W) (hz : ∀ i : Fin 11, i ≠ 10 → σ.val i = 0)
    (hwrite : W + 6 * natBitLength W + 6 ≤ cap)
    (hpow : 2 ^ (natBitLength support.length + 1) ≤ cap)
    (hlen : support.length ≤ cap)
    (hSw : support.length + 6 * natBitLength support.length + 6 ≤ cap)
    (hSo : 2 * (listWord natWord support).length + 3 ≤ cap)
    (hCo : 2 * (natWord W).length + 2 * (intWord coefficient).length + 4 ≤ cap) :
    ∃ b, WExec cap (monomialFormatProgramOn src supp coef) σ b (monomialFormatCost W support coefficient) ∧
      b.st supp = frame (listWord natWord support) ∧
      b.st coef = frame (natWord W ++ intWord coefficient) ∧ b.st src = σ.st src ∧
      b.sh src = pre.length + (listWord natWord support ++ intWord coefficient).length ∧ b.val 10 = W := by
  obtain ⟨b,he,hs,hc,hsrc,hh,hw,_⟩ := monomialFormatProgram_on_full_spec src supp coef
    hss hsc hpc cap W support coefficient pre rest σ hsource hhead hS hSH hC hCH hW hz
    hwrite hpow hlen hSw hSo hCo
  exact ⟨b,he,hs,hc,hsrc,hh,hw⟩

/-- `lem:print`, paper/paper.tex: the three-stream
instance has the same actual source/support/coefficient layout. -/
def monomialFormatProgram : WM 2 11 := monomialFormatProgramOn 0 1 2

/-- `lem:print`, paper/paper.tex: the concrete
three-stream monomial formatter retains its exact source-cursor type. -/
theorem monomialFormatProgram_spec (cap W : ℕ) (support : List ℕ) (coefficient : ℤ)
    (pre rest : List Bool) (σ : WState 2 11)
    (hsource : σ.st 0 = pre ++ listWord natWord support ++ intWord coefficient ++ rest)
    (hhead : σ.sh 0 = pre.length) (hS : σ.st 1 = []) (hSH : σ.sh 1 = 0)
    (hC : σ.st 2 = []) (hCH : σ.sh 2 = 0)
    (hW : σ.val 10 = W) (hz : ∀ i : Fin 11, i ≠ 10 → σ.val i = 0)
    (hwrite : W + 6 * natBitLength W + 6 ≤ cap)
    (hpow : 2 ^ (natBitLength support.length + 1) ≤ cap)
    (hlen : support.length ≤ cap)
    (hSw : support.length + 6 * natBitLength support.length + 6 ≤ cap)
    (hSo : 2 * (listWord natWord support).length + 3 ≤ cap)
    (hCo : 2 * (natWord W).length + 2 * (intWord coefficient).length + 4 ≤ cap) :
    ∃ b, WExec cap monomialFormatProgram σ b (monomialFormatCost W support coefficient) ∧
      b.st 1 = frame (listWord natWord support) ∧
      b.st 2 = frame (natWord W ++ intWord coefficient) ∧ b.st 0 = σ.st 0 ∧
      b.sh 0 = pre.length + (listWord natWord support ++ intWord coefficient).length ∧
      b.val 10 = W := by
  exact monomialFormatProgram_on_spec (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    cap W support coefficient pre rest σ hsource hhead hS hSH hC hCH hW hz hwrite hpow hlen hSw hSo hCo

end NearQuarticWires.StageTuple
