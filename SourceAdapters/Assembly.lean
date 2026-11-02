import NineInputs
import SourceAdapters.Normalization.IntegerThreshold
import SourceAdapters.Restriction.CentralBinomial
import SourceAdapters.Probability.BernsteinFinite
import SourceAdapters.Williams.Final
import SourceAdapters.Assembly.Field6Fixed
import SourceAdapters.Assembly.Field7
import SourceAdapters.Amplification.Field8
import SourceAdapters.Assembly.Field9Encoder

/-!
# From the published statements to the eight inputs

`sources_to_nine`: every field of `NineInputs` from the published statements of `PublishedInputs`, by the
adapter proving it.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters

open NearCubicGates.Close

/-- The eight inputs from the published statements: each field by its adapter. -/
theorem sources_to_nine (h : PublishedInputs) :
    NineInputs := {
  normalization := @NearCubicGates.Adapters.Normalization.threshold_normalization,
  restriction := @NearCubicGates.Adapters.Restriction.centralBinomialRestriction,
  bernstein := @NearCubicGates.Adapters.Probability.finiteBernstein,
  rectangularProduct := @NearCubicGates.Adapters.Williams.Final.williams14_of_leaf h.williams_rectangularProductLeaf,
  shortPCP := @NearCubicGates.Adapters.Assembly.Fixed.field6OrdinaryFixed h.bcgt13_theorem11_1 h.shoup_findIrrPolyAlgorithm17,
  refuter := @NearCubicGates.Adapters.Assembly.field7,
  amplification := @NearCubicGates.Adapters.Amplification.field8 h.stv_theorem29,
  threeQueryPCPP := @NearCubicGates.Adapters.Assembly.field9Encoder h.cw19Proximity_lemma22Half h.cw19Code_lemma26 }

end NearCubicGates.Adapters
