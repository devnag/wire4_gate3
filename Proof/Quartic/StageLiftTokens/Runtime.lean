import Proof.Quartic.StageLiftTokens.AmplifierRun

/-!
# Cost of the actual residue-source printer

`lem:print`, paper/paper.tex: every original
occurrence, digit-chain, Fermat-factor and amplifier iteration is
included in one polynomial physical clock.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens

theorem amplifierSourceCost_mono (E J e : ℕ) (hJ : J≤E) (he : e≤E) :
    amplifierSourceCost E J e≤amplifierSourceCost E E E := by
  unfold amplifierSourceCost amplifierPrefixCost amplifierLoopCost amplifierTailCost
    amplifierTermCost fermatSourceCost allFactorCost circuitSourceCost rowSourceCost
    productCloserCost
  gcongr

theorem actual_source_clock (E J e : ℕ) (hJ : J≤E) (he : e≤E) :
    106+amplifierSourceCost E J e+1≤10^12*(E+1)^30 := by
  have hdiag : 106+amplifierSourceCost E E E+1≤10^8*(E+1)^6 := by
    unfold amplifierSourceCost amplifierPrefixCost amplifierLoopCost amplifierTailCost
      amplifierTermCost fermatSourceCost allFactorCost circuitSourceCost rowSourceCost
      productCloserCost factorSourceCost pairSourceCost linearSourceCost targetSourceCost sourceBits
    ring_nf
    omega
  have hm:=amplifierSourceCost_mono E J e hJ he
  have hp : (E+1)^6≤(E+1)^30 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith

end NearQuarticWires.StageLiftTokens
