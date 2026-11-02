import Proof.Quartic.StagePrint.CutStreamCount
import Proof.Quartic.StagePrint.NativeEquations

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutScan

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: these are the
literal signed fields already present in the equality-cut stream. -/
def nativeCutFields (p : ℕ) (c : MatrixScoreBatch.Cut) : List (List Bool) :=
  (MatrixScoreBatch.fields c).map (MatrixScoreBatch.signMagnitude p)

theorem nativeCutFields_word (p : ℕ) (c : MatrixScoreBatch.Cut) :
    rowWord (nativeCutFields p c)=MatrixScoreBatch.cutWord p c := by
  simp only [rowWord,nativeCutFields,List.flatMap_map,Function.comp_def,MatrixScoreBatch.cutWord]

theorem nativeCutFields_length (p : ℕ) (c : MatrixScoreBatch.Cut) :
    (nativeCutFields p c).length=c.leftWeights.length+c.rightWeights.length+2 := by
  simp [nativeCutFields,MatrixScoreBatch.fields,Nat.add_assoc]

theorem nativeCutFields_head (p : ℕ) (c : MatrixScoreBatch.Cut) :
    (rowWord (nativeCutFields p c)).headD false=true := by
  have hn : nativeCutFields p c≠[] := by
    intro h
    have hl:=nativeCutFields_length p c
    rw [h] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨field,fields,hfields⟩:=List.exists_cons_of_ne_nil hn
  have hm : field∈nativeCutFields p c := by rw [hfields];simp
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hm
  rw [hfields]
  unfold rowWord
  simp only [List.flatMap_cons]
  exact frame_head (by simp [MatrixScoreBatch.signMagnitude]) _

/-- `lem:print` and `prop:time`, paper/paper.tex: count the actual native equality rows by reading
their original encoded fields, including empty cut lists. -/
theorem nativeCutCount_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 6 ↪ Fin nr)
    (hsd : src≠dst) (width p : ℕ) (cuts : List MatrixScoreBatch.Cut)
    (hlengths : ∀ c∈cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width)
    (pre suffix : List Bool) (hsuffix : suffix.headD false=false) (a : WState ns nr)
    (hsource : a.st src=pre++cuts.flatMap (MatrixScoreBatch.cutWord p)++suffix)
    (hhead : a.sh src=pre.length) (hout : a.sh dst=(a.st dst).length)
    (hstride : a.val (R 2)=2*width+2) (hK : a.val (R 3)=0) (hT : a.val (R 4)=0)
    (hOP : a.val (R 0)≤cap)
    (hsourceCap : a.val (R 1)+(cuts.flatMap (MatrixScoreBatch.cutWord p)).length≤cap)
    (hstrideCap : 2*width+2≤cap) (hEQCap : a.val (R 5)+cuts.length≤cap) :
    WExec cap (countRows src R) a
      ((adv src dst (R 0) (R 1) a [] (cuts.flatMap (MatrixScoreBatch.cutWord p)).length).setv
        (R 5) (a.val (R 5)+cuts.length))
      (25*(cuts.flatMap (MatrixScoreBatch.cutWord p)).length+cuts.length*(22*(2*width+2)+11)+1) := by
  let rows:=cuts.map (nativeCutFields p)
  have hrows : rows.flatMap rowWord=cuts.flatMap (MatrixScoreBatch.cutWord p) := by
    simp only [rows,List.flatMap_map,Function.comp_def,nativeCutFields_word]
  have hrlen : rows.length=cuts.length := by simp only [rows,List.length_map]
  have he:=countRows_spec cap src dst R hsd (2*width+2) rows
    (by
      intro row hr
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hr
      rw [nativeCutFields_length,(hlengths c hc).1,(hlengths c hc).2]
      omega)
    (by
      intro row hr
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hr
      exact nativeCutFields_head p c)
    pre suffix hsuffix a (by rw [hrows];exact hsource) hhead hout hstride hK hT hOP
    (by rw [hrows];exact hsourceCap) hstrideCap (by rw [hrlen];exact hEQCap)
  simpa only [hrows,hrlen] using he

end NearQuarticWires.StagePrint.CutScan
