import Proof.Quartic.StageHamming.ParityLoop

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def parityInput : Fin VV := 104

def parityScratch : List (Fin VV) :=
  [paritySuccessor, parityPower, parityFlag, vJ, parityCounter]

/-- `imp:partition`, paper/paper.tex: ordinary scalar
initialization followed by the bounded scan computes the canonical
Hamming parity-position predicate from its coordinate and code width. -/
def parityPosition : St VV MM :=
  .seq (.op (.copy paritySuccessor parityInput))
    (.seq (.op (.inc paritySuccessor))
      (.seq (.op (.copy parityPower v1))
        (.seq (.op (.zero parityFlag)) parityPositionLoop)))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the complete physical predicate has linear code-width
cost, with no supplied parity table or initialized power register. -/
theorem parityPosition_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i s : ℕ) (hi : a.env parityInput = i) (hswidth : a.env parityWidth = s)
    (hinput : i + 1 < 2 ^ C.Wd) (hs : s < 2 ^ C.Wd)
    (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C parityPosition a (8 * s + 12) (fun b =>
      b.env parityFlag = (parityPrefix i s).toNat ∧
      b.sh = a.sh ∧ Fr a b parityScratch) := by
  unfold parityPosition
  refine Hx.hs (Hs.then (hs_copy C paritySuccessor parityInput a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let b := a.set paritySuccessor (a.env parityInput)
  refine Hs.then (hs_inc C paritySuccessor b (by
    rw [DS.set_env_self, hi]; exact hinput)) (fun c hc' n2 hn2 => ?_)
  subst hc'
  let c := b.set paritySuccessor (b.env paritySuccessor + 1)
  refine Hs.then (hs_copy C parityPower v1 c (by decide)) (fun d hd n3 hn3 => ?_)
  subst hd
  let d := c.set parityPower (c.env v1)
  refine Hs.then (hs_zero C parityFlag d) (fun e he n4 hn4 => ?_)
  subst he
  let e := d.set parityFlag 0
  have hf : Fr a e parityScratch :=
    (Fr.set a _ (by decide)).trans ((Fr.set b _ (by decide)).trans
      ((Fr.set c _ (by decide)).trans (Fr.set d _ (by decide))))
  have hce : Cst e := hc.of_fr hf (by decide)
  have hes : e.env paritySuccessor = i + 1 := by
    vsimp [e, d, c, b, hi]
  have hew : e.env parityWidth = s := (hf _ (by decide)).trans hswidth
  have hep : e.env parityPower = 1 := by
    vsimp [e, d, c, b, hc.one]
  have hef : e.env parityFlag = 0 := by rw [DS.set_env_self]
  refine Hs.last (parityPositionLoop_spec e hce i s hes hew hep hef hs hW) ?_
  rintro f ⟨_, hflag, hsh, hfr⟩ n5 hn5
  exact ⟨⟨hflag, hsh, hf.trans (hfr.weaken (by decide))⟩, by omega⟩

end NearQuarticWires.StageHamming
