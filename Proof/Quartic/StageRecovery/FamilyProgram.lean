import Proof.Quartic.StageRecovery.FamilyLoad
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand
open NearCubicGates.Close.Expand.PolyTab (idealStart)

/-- `lem:print`, paper/paper.tex: the exact support
family record stream, with the characteristic number and degree of
each support generated once in increasing degree order. -/
def FamilyRequest.output (r : FamilyRequest) : List Bool :=
  recStream ((famRecs r.arity r.degree).map (binary r.width))

/-- `prop:time`, paper/paper.tex: the finite support
constructor's capacity pays every generated family record and work word. -/
def FamilyRequest.capacity (r : FamilyRequest) : ℕ :=
  r.loadCapacity + ((fam r.arity r.degree).length + 3) * (2 * r.width + 1) +
    10 * r.width + 4 * r.arity + 4 * r.degree + 20

/-- `lem:print`, paper/paper.tex: family record values
fit the declared binary width before any generated list is constructed. -/
theorem FamilyRequest.records_fit (r : FamilyRequest) :
    (r.degree + 3) * 2 ^ r.arity < 2 ^ r.width := by
  have hd : r.degree + 3 < 2 ^ (r.degree + 8) :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  calc (r.degree + 3) * 2 ^ r.arity < 2 ^ (r.degree + 8) * 2 ^ r.arity :=
      Nat.mul_lt_mul_of_pos_right hd (by positivity)
    _ = 2 ^ r.width := by rw [← pow_add]; congr 1; unfold FamilyRequest.width; omega

/-- `lem:print`, paper/paper.tex: one actual family
program loads finite setup fields, reads its dimensions, generates the
family, copies the complete record stream and closes it exactly. -/
noncomputable def familyProgram : WMX 16 15 :=
  .seq (.mach Top.loadM familyLoadMap)
    (.seq (StagePrint.unaryRegister 9 14 10)
      (.seq (StagePrint.unaryRegister 10 14 8)
        (.seq (famPhase familyStreams familyRegisters)
          (.seq (copyAll 14 15 16 0 1 2 14) (closeOutX 16 14)))))

/-- `prop:time`, paper/paper.tex: the literal family
construction clock includes paid sequential copies and rewinds rather
than treating the output as a supplied indexed table. -/
def FamilyRequest.steps (r : FamilyRequest) : ℕ :=
  r.loadCost + 1 + (16 * r.arity + 14 + 1 + (16 * r.degree + 14 + 1 +
    (famPhaseCost r.width r.arity r.degree (fam r.arity r.degree).length + 1 +
      ((famRecs r.arity r.degree).length * (40 * r.width + 11 + (50 * r.width + 30)) + 3 + 1 +
        (5 * ((famRecs r.arity r.degree).length * (2 * r.width + 1)) + 3)))))

/-- `lem:print`, paper/paper.tex: the entire support
family is physically generated from the finite setup fields, without
precomputed characteristic sets or modular formula values in the input. -/
theorem familyProgram_spec (r : FamilyRequest) :
    Runs r.capacity familyProgram (idealStart 16 15 r.word r.lens) r.steps
      (fun τ => τ.st 16 = r.output) := by
  let cap := r.capacity
  have hcap : 4 * r.width + 4 ≤ cap := by dsimp [cap, FamilyRequest.capacity]; omega
  have hv : r.arity + 1 ≤ cap := by dsimp [cap, FamilyRequest.capacity]; omega
  have hd : r.degree + 1 ≤ cap := by dsimp [cap, FamilyRequest.capacity]; omega
  unfold familyProgram FamilyRequest.steps
  refine Runs.seqE (familyLoad_spec cap r) ?_
  refine Runs.seqE (StagePrint.unaryRegister_spec cap (9 : Fin 17) (14 : Fin 15) 10
    (by decide) r.loaded r.arity rfl rfl rfl rfl hv) ?_
  refine Runs.seqE (StagePrint.unaryRegister_spec cap (10 : Fin 17) (14 : Fin 15) 8
    (by decide) (r.loaded.setv 10 r.arity) r.degree rfl rfl rfl
    (by simp [FamilyRequest.loaded]) hd) ?_
  have ef := famPhase_spec cap r.width r.arity r.degree r.ready r.ready_pre
    rfl (by simp [FamilyRequest.ready, FamilyRequest.loaded, familyRegisters])
    (by unfold FamilyRequest.width; omega) r.records_fit hcap
    (by dsimp [cap, FamilyRequest.capacity]; omega)
    (by dsimp [cap, FamilyRequest.capacity]; omega)
    (by dsimp [cap, FamilyRequest.capacity]; nlinarith)
  refine Runs.seq ef fun τ ⟨hf, _, _⟩ => ?_
  obtain ⟨junk, hjunk⟩ := hf.fam
  have hout0 : τ.st (16 : Fin 17) = [] := by
    rw [hf.fr.st (by decide)]
    rfl
  have houth : τ.sh (16 : Fin 17) = 0 := by
    rw [hf.fr.sh (by decide)]
    rfl
  have hr14 : τ.val (14 : Fin 15) = 0 := by
    rw [hf.fr.val (by decide)]
    rfl
  have eco := copyAll_spec cap (I := (14 : Fin 17)) (Wk := 15) (O := 16)
    (CI := (0 : Fin 15)) (CW := 1) (CS := 2) (CO := 14) (by decide) (by decide)
    r.width (by unfold FamilyRequest.width; omega) (famRecs r.arity r.degree) τ junk [] []
    hjunk hf.famh (hf.regs 0 (by decide)) (hf.regs 1 (by decide)) (hf.regs 2 (by decide))
    hf.wkh hf.wkl ⟨hout0, by simpa [hout0] using houth, hr14⟩
    (by rw [famRecs_length]; dsimp [cap, FamilyRequest.capacity]; nlinarith)
    (by rw [famRecs_length]; dsimp [cap, FamilyRequest.capacity]; nlinarith)
  refine Runs.seq eco fun ρ ⟨ho, _, _, _⟩ => ?_
  refine (closeNum cap ρ _ _ ho
    (by
      simp only [List.nil_append, len_frames, famRecs_length]
      dsimp [cap, FamilyRequest.capacity]
      nlinarith)).mono (by simp only [List.nil_append, len_frames]; rfl) ?_
  rintro σ ⟨hst, _, _, _⟩
  simpa only [StablePartition.Workspace.overlay, List.drop_nil, List.append_nil,
    List.nil_append, FamilyRequest.output, recStream, List.flatMap_map, Function.comp_def] using hst

end NearQuarticWires.StageRecovery
