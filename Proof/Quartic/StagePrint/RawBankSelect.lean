import Proof.Quartic.StagePrint.RawGateFormatter
import Proof.Gates.Dispatch.ParseCirc

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (gateWord)
open NearCubicWires

/-- `lem:print`, paper/paper.tex: the selected original occurrence is an explicit finite integer index. -/
def selectedGate : Fin VV := 127
/-- `lem:print`, paper/paper.tex: the source-bank scan counts every original occurrence, including duplicates. -/
def sourceGateIndex : Fin VV := 128

/-- `lem:print`, paper/paper.tex: only original gate words preceding the selected occurrence are consumed. -/
def skipOriginalGates : St VV := .loop (.lt sourceGateIndex selectedGate)
  (.seq gateBody (.op (.inc sourceGateIndex)))

/-- `lem:print`, paper/paper.tex: the bank scan preserves all stored widths and selected indices. -/
def bankSelectScratch : List (Fin VV) := gateT++[sourceGateIndex]

/-- `lem:print` and `prop:time`, paper/paper.tex: selection scans the actual original gate prefix, rather than receiving the selected gate as a separately supplied input. -/
theorem skipOriginalGates_run (C : Ctx) {n : ℕ}
    (gs : List (NormalizedThresholdGate n)) (rest : List Bool) (a : DS VV)
    (hc : Cst a) (hzero : a.env cWOK=0) (hi : a.env sourceGateIndex=0)
    (hn : a.env selectedGate=gs.length)
    (hcw : C.cw.drop a.cp=gs.flatMap gateWord++rest)
    (hW : C.cw.length+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd)
    (hcount : gs.length<2^C.Wd) :
    Hs C skipOriginalGates a (gs.length*(100*(C.cw.length+2)^2+4)+2)
      (fun b=>b.cp=a.cp+(gs.flatMap gateWord).length ∧ b.wq=a.wq ∧
        b.out=a.out ∧ b.env cWOK=0 ∧ Cst b ∧ Fr a b bankSelectScratch) := by
  let P : ℕ→DS VV→Prop:=fun _ b=>b.env cWOK=0 ∧ b.wq=a.wq ∧
    b.out=a.out ∧ Cst b ∧ Fr a b bankSelectScratch
  have init : P 0 a:=⟨hzero,rfl,rfl,hc,Fr.refl _ _⟩
  have rr:=walk (C:=C) gs gateWord sourceGateIndex selectedGate (by decide) gateBody P
    (100*(C.cw.length+2)^2) rest ?_ ?_ hcount a init hi hn hcw
  · refine rr.mono le_rfl ?_
    rintro b ⟨⟨bz,bw,bo,bc,bf⟩,_,_,bp⟩
    exact ⟨bp,bw,bo,bz,bc,bf⟩
  · intro k b v ⟨bz,bw,bo,bc,bf⟩
    have sf : Fr b (b.set sourceGateIndex v) [sourceGateIndex] := Fr.set _ _ (by simp)
    exact ⟨by rw [sf cWOK (by decide)];exact bz,bw,bo,
      Cst.of_fr bc sf (by decide) (by rw [sf vPOS (by decide)];exact bc.pos),
      bf.trans (sf.weaken (by intro y hy;exact List.mem_append_right _ hy))⟩
  · intro k hk b ⟨bz,bw,bo,bc,bf⟩ bi bn bd
    refine (gateBody_spec (C:=C) b bc gs[k] _ False (by simpa [bnat] using bz)
      bd hW hL).mono le_rfl ?_
    rintro e ⟨ez,ep,ew,eo,ec,ef⟩
    refine ⟨⟨by simpa [bnat] using ez,ew.trans bw,eo.trans bo,ec,
      bf.trans (ef.weaken (by intro y hy;exact List.mem_append_left _ hy))⟩,?_,?_,ep⟩
    · rw [ef sourceGateIndex (by decide)];exact bi
    · rw [ef selectedGate (by decide)];exact bn

end NearQuarticWires.StagePrint.RawBits
