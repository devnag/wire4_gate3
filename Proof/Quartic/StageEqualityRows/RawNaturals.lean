import Proof.Quartic.StageEqualityRows.SkipFrames
import Proof.Gates.Codec.Circuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: arbitrary
binary metadata fields are skipped without decoding their values. -/
def skipRawNaturals (src : Fin (ns+1)) (F K : Fin nr) : ℕ → WM ns nr
  | 0=>.skip
  | n+1=>.seq (NearCubicGates.Close.Codec.skipNat false src F K) (skipRawNaturals src F K n)

def rawNaturalCost (values : List ℕ) : ℕ :=
  (values.map (fun value=>20*natBitLength value+21)).sum

theorem skipRawNaturals_run (cap : ℕ) (src : Fin (ns+1)) (F K : Fin nr) (hFK : F≠K) :
    ∀ (values : List ℕ) (pre rest : List Bool) (a : WState ns nr),
    a.st src=pre++values.flatMap natWord++rest → a.sh src=pre.length →
    a.val F=0 → a.val K=0 → (∀ v∈values,natBitLength v+1≤cap) →
    WExec cap (skipRawNaturals src F K values.length) a
      (a.seth src (pre.length+(values.flatMap natWord).length)) (rawNaturalCost values)
  | [],pre,rest,a,hst,hsh,hF,hK,hcap=>by
      have he : a.seth src (pre.length+(([] : List ℕ).flatMap natWord).length)=a := by
        apply WState.eq
        · funext i;by_cases h:i=src
          · subst i;simp [hsh]
          · simp [Function.update_of_ne h]
        · rfl
        · rfl
        · rfl
      rw [he]
      exact WExec.skip a
  | v::values,pre,rest,a,hst,hsh,hF,hK,hcap=>by
      have e1:=NearCubicGates.Close.Codec.skipNat_spec cap false src F K hFK v pre
        (values.flatMap natWord++rest) a
        (by simpa only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,Bool.false_eq_true,ite_false,List.flatMap_cons,List.append_assoc] using hst)
        hsh hF hK (hcap v (by simp))
      have e2:=skipRawNaturals_run cap src F K hFK values (pre++natWord v) rest
        (a.seth src (pre.length+stp false*(natWord v).length))
        (by simpa only [WState.seth_st,List.flatMap_cons,List.append_assoc] using hst)
        (by simp [stp]) hF hK (fun x hx=>hcap x (by simp [hx]))
      refine (e1.seq e2).cast cap ?_ ?_
      · simp only [seth_twice,List.flatMap_cons,List.length_append,stp,Bool.false_eq_true,
          ite_false,Nat.one_mul]
        congr 1
        omega
      · simp only [rawNaturalCost,List.map_cons,List.sum_cons]
        omega

end NearQuarticWires.StageEqualityRows
