import Proof.Quartic.StageModularSetup.Stride
import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StageModularCuts

/-- `lem:print`, paper/paper.tex: read only
the unary bit-length prefix of the actual binary modulus codec. -/
def readModulusLength : WM 15 16 := WM.readU 2 1 0

/-- `lem:print`, paper/paper.tex: the length
counter and source cursor are obtained from the consumed literal prefix. -/
def lengthState (a : State) (q : ℕ) : State :=
  ((a.seth 2 (natBitLength q+1)).setv 1 (natBitLength q+1)).setv 0 (natBitLength q)

/-- `lem:print` and `prop:time`, paper/paper.tex: only modulus bit length enters a unary register;
every magnitude bit remains unchanged on the actual original source tape. -/
theorem readModulusLength_spec (cap q : ℕ) (a : State)
    (hsource : a.st 2=natWord q) (hhead : a.sh 2=0)
    (h0 : a.val 0=0) (h1 : a.val 1=0) (hcap : natBitLength q+1≤cap) :
    WExec cap readModulusLength a (lengthState a q) (11*natBitLength q+7) := by
  have er:=wreadU_spec cap (2 : Fin 16) (1 : Fin 16) 0 (by decide) (natBitLength q) a
    (by
      intro index hindex
      rw [hsource,hhead,Nat.zero_add]
      change (natWord q).getD index false=true
      exact NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_getD_one q index hindex)
    (by
      rw [hsource,hhead,Nat.zero_add]
      change (natWord q).getD (natBitLength q) false=false
      exact NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_getD_zero q)
    (by rw [h1];omega) (by rw [h0];omega)
  simpa only [readModulusLength,lengthState,hhead,h0,h1,Nat.zero_add] using er

end NearQuarticWires.StageModularSetup
