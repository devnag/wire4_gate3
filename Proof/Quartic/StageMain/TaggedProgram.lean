import Proof.Quartic.StageMain.TaggedLayout
import Proof.Quartic.StageMain.TaggedSide
import Proof.Gates.Expand.PolyTabPack

/-!
# A fixed selector for the main-pass ordinary subroutines

Step 4 of `sec:algorithm`, paper/paper.tex, and
`prop:time`: a Boolean tag selects one of two disjoint
cold computations. The selected input and framed answer are copied
physically; the cost depends only on that branch and its actual words.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

variable {A B : Type} {ia oa : A → List Bool} {ib ob : B → List Bool}
  {ba : A → ℕ} {bb : B → ℕ}

def taggedInput (ia : A → List Bool) (ib : B → List Bool) : A ⊕ B → List Bool
  | .inl a => false :: ia a
  | .inr b => true :: ib b

def taggedAnswer (oa : A → List Bool) (ob : B → List Bool) : A ⊕ B → List Bool
  | .inl a => oa a
  | .inr b => ob b

def taggedBranchBudget (ba : A → ℕ) (bb : B → ℕ) : A ⊕ B → ℕ
  | .inl a => ba a
  | .inr b => bb b

def taggedCost (ia oa : A → List Bool) (ib ob : B → List Bool)
    (ba : A → ℕ) (bb : B → ℕ) : A ⊕ B → ℕ
  | .inl a => 200 * ((ia a).length + (oa a).length + ba a + 1) + 12
  | .inr b => 200 * ((ib b).length + (ob b).length + bb b + 1) + 12

def taggedCapacity (ia oa : A → List Bool) (ib ob : B → List Bool)
    (ba : A → ℕ) (bb : B → ℕ) (r : A ⊕ B) : ℕ :=
  4 * ((taggedInput ia ib r).length + (taggedAnswer oa ob r).length +
    taggedBranchBudget ba bb r + 2)

def taggedLens (l r budget : ℕ) (i : Fin (l + r + 3)) : ℕ :=
  if i = sharedRuler l r then budget else 0

noncomputable def taggedProgram
    (f : WordFunction A ia (fun a => frame (oa a)) ba)
    (g : WordFunction B ib (fun b => frame (ob b)) bb) :
    WMX (f.program.tapeCount + g.program.tapeCount + 2) 1 :=
  let l := f.program.tapeCount
  let r := g.program.tapeCount
  .seq (.wm (.fwd 0)) (.ifs 0
    (branchFromTag g (rightBank l r) 0 1 (sharedRuler l r) 0)
    (branchFromTag f (leftBank l r) 0 1 (sharedRuler l r) 0))

end NearQuarticWires.StageMain.Tagged
