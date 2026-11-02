import Proof.Quartic.StageNativeKidsPool.ColdLayout

set_option autoImplicit false
namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `prop:time`, paper/paper.tex: count
initialization costs a quadratic in the actual child count and a linear
scan of the literal binary count and target-width codecs. -/
def initializeCost (count width : ℕ) : ℕ:=
  500*(count+1)^2+100*((natWord count).length+(natWord width).length+1)

end NearQuarticWires.StageNativeKidsPool
