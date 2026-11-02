import Proof.Quartic.StageNativeKidsPool.Counted
import Proof.Quartic.StageNativeKidsPool.InitializationCost
import Proof.Quartic.StageNativeKidsPool.RawNatural
import Proof.Quartic.StageNativeKids.ReadSmall
import Proof.Quartic.StageGamma.Unframe
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageNativeKids

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: only
the small actual original-child count is decoded; all other metadata
remain finite bit streams. -/
def countReader : Fin 5 ↪ Fin 16:=⟨![0,1,9,2,3],by decide⟩

/-- `lem:print`, paper/paper.tex: actual
count bytes initialize the raw output prefix and small remaining loop
counter; the target-width field is copied solely as encoded bytes. -/
def initializeProgram (counter row : Program) : WM (streams counter row) 16:=
  let OUT : Fin (streams counter row+1):=⟨14,by unfold streams;omega⟩
  .seq (.whs (counterMap counter row counter.outputTape)
      (StageGamma.unframePair (counterMap counter row counter.outputTape) OUT 10))
    (.seq (wcopyR 10 13 12) (.seq (WM.rewind OUT 13)
      (.seq (readSmallProgram false OUT countReader)
        (copyRawNaturalReset ⟨4,by unfold streams;omega⟩ OUT 10 11 12))))

/-- `lem:print`, paper/paper.tex: the
exact initialized state retains the computed count codec and target
width ahead of the raw native pool, with its byte count measured. -/
def initialized (counter row : Program) (count width : ℕ)
    (σ : WState (streams counter row) 16) : WState (streams counter row) 16:=
  ((appendO σ ⟨14,by unfold streams;omega⟩ 10 (natWord count++natWord width)).seth
    (counterMap counter row counter.outputTape) (2*(natWord count).length)).setv 9 count

/-- `lem:print` and `prop:time`, paper/paper.tex: the real computed counter output is read
and copied into the actual pool prefix, with no count input and no
numeric loop in the target-width value. -/
theorem initialize_spec (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (cap : ℕ) (σ : WState (streams counter row) 16)
    (h : Counted F width countBudget counter row q σ)
    (hcap : 4*((F q).count+1)+2*(natWord (F q).count).length+
      (natWord (width q)).length+20≤cap) :
    WExec cap (initializeProgram counter row) σ
      (initialized counter row (F q).count (width q) σ)
      (initializeCost (F q).count (width q)) := by
  let OUT : Fin (streams counter row+1):=⟨14,by unfold streams;omega⟩
  let SRC : Fin (streams counter row+1):=counterMap counter row counter.outputTape
  let WID : Fin (streams counter row+1):=⟨4,by unfold streams;omega⟩
  let K:=(F q).count
  let A:=natWord K
  let B:=natWord (width q)
  change 4*(K+1)+2*A.length+B.length+20≤cap at hcap
  have hSO : SRC≠OUT:=counterMap_not_small counter row counter.outputTape OUT (by change 14<20;omega)
  have hSW : SRC≠WID:=counterMap_not_small counter row counter.outputTape WID (by change 4<20;omega)
  have hWO : WID≠OUT:=by intro he;have hv:=congrArg Fin.val he;change 4=14 at hv;omega
  have hout : σ.st OUT=[]:=by
    have ht:=(h.small OUT (by change 14<20;omega)).1
    simpa [OUT,loaded,lens] using ht
  have houth : σ.sh OUT=0:=(h.small OUT (by change 14<20;omega)).2
  have hwidth : σ.st WID=B:=by
    have ht:=(h.small WID (by change 4<20;omega)).1
    simpa [WID,loaded,fields,B] using ht
  have hwhead : σ.sh WID=0:=(h.small WID (by change 4<20;omega)).2
  have e1:=StageGamma.unframe_loop cap SRC OUT hSO (10 : Fin 16) [] A [] σ
    (by simpa [SRC,A,K] using h.count) (by simpa [SRC] using h.count_head)
    (by simp [hout,houth]) (by rw [h.registers 10];omega)
  simp only [List.length_nil,Nat.zero_add] at e1
  let s1:=(appendO σ OUT 10 A).seth SRC (2*A.length)
  have e2:=wcopyR_spec cap (10 : Fin 16) 13 12 (by decide) (by decide) (by decide) s1
    (by simp [s1,appendO,h.registers]) (by simp [s1,appendO,h.registers])
    (by simp only [s1,WState.seth_val,appendO,WState.setv_val,Function.update_self,h.registers 10,Nat.zero_add];omega)
  have ha : s1.val (10 : Fin 16)=A.length:=by simp [s1,appendO,h.registers]
  rw [ha] at e2
  let s2:=s1.setv 13 A.length
  have e3:=wrewind_spec cap OUT (13 : Fin 16) A.length s2 rfl (by simp only [s2,WState.setv_val,Function.update_self];omega)
  let s3:=(s2.setv 13 0).seth OUT (s2.sh OUT-A.length)
  have hs3out : s3.st OUT=A:=by simp [s3,s2,s1,appendO,hout]
  have hs3head : s3.sh OUT=0:=by simp [s3,s2,s1,appendO,hSO.symm,houth]
  have hs3zero : ∀i,s3.val (countReader i)=0:=by
    intro i;fin_cases i <;> simp [countReader,s3,s2,s1,appendO,h.registers]
  have e4:=readSmallProgram_spec cap false OUT countReader K [] [] s3
    (by simpa only [A,WireExponent3_5.PrimAsm.ParseNat.enc,Bool.false_eq_true,
      ite_false,List.nil_append,List.append_nil] using hs3out) (by simpa using hs3head) hs3zero (by omega)
  simp only [List.length_nil,WireExponent3_5.PrimAsm.ParseNat.stp,Bool.false_eq_true,
    ite_false,Nat.one_mul,Nat.zero_add] at e4
  let s4:=(s3.seth OUT A.length).setv 9 K
  have hO4 : s4.val (10 : Fin 16)=A.length:=by simp [s4,s3,s2,s1,appendO,h.registers]
  have e5:=copyRawNaturalReset_spec cap WID OUT (10 : Fin 16) 11 12 hWO
    (by decide) (by decide) (by decide) (width q) [] s4
    (by simp [s4,s3,s2,s1,appendO,hWO,hSW,hwidth,B])
    (by simp [s4,s3,s2,s1,appendO,hWO,hSW.symm,hwhead])
    (by simp [s4,hs3out])
    (by simp [s4,s3,s2,s1,appendO,h.registers])
    (by simp [s4,s3,s2,s1,appendO,h.registers])
    (by rw [hO4];change A.length+B.length+1≤cap;omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq e5)))).cast cap ?_ ?_
  · change appendO s4 OUT 10 B=
      ((appendO σ OUT 10 (A++B)).seth SRC (2*A.length)).setv 9 K
    apply WState.eq
    · funext i
      by_cases hi:i=OUT
      · subst hi;simp [s4,s3,s2,s1,appendO,hSO.symm,houth]
      · by_cases hc:i=SRC
        · subst hc;simp [s4,s3,s2,s1,appendO,hSO]
        · simp [s4,s3,s2,s1,appendO,hi,hc]
    · funext i
      by_cases hi:i=OUT
      · subst hi;simp [s4,s3,s2,s1,appendO,hout]
      · simp [s4,s3,s2,s1,appendO,Function.update_of_ne hi]
    · funext i
      fin_cases i <;> simp [s4,s3,s2,s1,appendO,h.registers]
    · rfl
  · unfold initializeCost
    simp only [A,B,K] at *
    omega

end NearQuarticWires.StageNativeKidsPool
