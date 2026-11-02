import Proof.Quartic.StageModularSetup.ModulusTail
import Proof.Quartic.StageModularSetup.Counters

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StageModularCuts

/-- `lem:print`, paper/paper.tex: parse the
actual modulus bit length, derive its padding, and initialize the
bounded binary modulus tape while returning all scratch and source heads. -/
def initializeModulus : WM 15 16 :=
  .seq readModulusLength (.seq prepareCounters writeModulusTail)

/-- `lem:print` and `prop:time`, paper/paper.tex: binary setup is linear in the retained work width and
preserves the complete unrelated cut stream and loaded source context. -/
theorem initializeModulus_spec (cap width q : ℕ) (a : State)
    (hsource : a.st 2=natWord q) (hhead : a.sh 2=0)
    (hword : a.st 7=[]) (houtputHead : a.sh 7=0)
    (h7 : a.val 7=width)
    (h0 : a.val 0=0) (h1 : a.val 1=0) (h3 : a.val 3=0)
    (h4 : a.val 4=0) (h9 : a.val 9=0) (h10 : a.val 10=0) (h11 : a.val 11=0)
    (hlen : natBitLength q≤width) (hcap : 4*width+10≤cap) :
    WExec cap initializeModulus a (a.sets 7 (frame (binary width q))) (500*(width+1)) := by
  have eRead:=readModulusLength_spec cap q a hsource hhead h0 h1 (by omega)
  let b:=lengthState a q
  have eCounters:=prepareCounters_spec cap width (natBitLength q) b
    (by simp [b,lengthState]) (by simp [b,lengthState,h7])
    (by simp [b,lengthState,h3]) (by simp [b,lengthState,h4])
    (by simp [b,lengthState,h9]) (by simp [b,lengthState,h10]) hlen (by omega)
  let c:=((b.setv 3 (natBitLength q)).setv 9 (width-natBitLength q)).setv 0 0
  have eTail:=writeModulusTail_spec cap width q c
    (by simp [c,b,lengthState,hsource]) (by simp [c,b,lengthState])
    (by simp [c,b,lengthState,hword]) (by simp [c,b,lengthState,houtputHead])
    (by simp [c,b,lengthState]) (by simp [c]) (by simp [c])
    (by simp [c,b,lengthState,h11]) hlen hcap
  refine (eRead.seq (eCounters.seq eTail)).cast cap ?_ (by omega)
  apply WState.eq
  · funext stream
    by_cases hs : stream=2
    · subst stream;simp [modulusTailState,c,b,lengthState,hhead]
    · simp [modulusTailState,c,b,lengthState,hs]
  · rfl
  · funext reg
    fin_cases reg <;> simp [modulusTailState,c,b,lengthState,h0,h1,h3,h9,h11]
  · rfl

end NearQuarticWires.StageModularSetup
