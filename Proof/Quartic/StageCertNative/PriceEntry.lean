import Proof.Quartic.StageCertNative.PricePrefix
import Proof.Quartic.StageCertNative.PricePair
import Proof.Quartic.StageCertNative.EntryFormatJoin

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

theorem price_exactPrefixLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(exactPrefixWord r).length) 0 := by
  have h:=(((JobPrice.constant 2).mul (price_prefixScalarBits B1 B2)).add
    (price_contextLength B1 B2)).add (JobPrice.constant 4)
  refine h.mono ?_
  intro r
  simp only [exactPrefixWord,List.length_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,natWord_length,prefixScalarBits]
  omega

theorem price_exactEntryLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(exactEntry r.moment).word.length) 1 := by
  have hh:=((price_exactPrefixLength B1 B2).raise (by decide : 0≤1)).add
    (((JobPrice.constant 2).mul (price_termsWord B1 B2)).add
      ((JobPrice.constant 1).raise (by decide : 0≤1)))
  refine hh.mono ?_
  intro r
  have hword : (exactEntry r.moment).word=exactPrefixWord r++
      frame (termsWord (exactTerms r.moment)) := by
    have he:=actualEntry_word r.base r.index
    change (exactEntry r.moment).word=_ at he
    rw [he]
    simp only [exactPrefixWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.append_assoc]
    rfl
  rw [hword,List.length_append,frame_length]

theorem price_entrySource (B1 B2 : ℕ) : JobPrice (@entrySourceBudget B1 B2) 4 := by
  have ht : JobPrice (fun r : TermJob B1 B2=>
      (frame (termsWord (exactTerms r.moment))).length) 4 := by
    have hh:=(((JobPrice.constant 2).mul (price_termsWord B1 B2)).add
      ((JobPrice.constant 1).raise (by decide : 0≤1))).raise (by decide : 1≤4)
    simpa only [frame_length] using hh
  have hp' : JobPrice (@entrySourcePairBudget B1 B2) 4 := by
    exact ((price_nFirstLength B1 B2).raise (by decide : 0≤4)).framedPair
      ((price_exactPrefixLength B1 B2).raise (by decide : 0≤4)) ht
      ((price_prefixBudget B1 B2).raise (by decide : 0≤4))
      (price_nFirstNestedTerms B1 B2)
  exact ((((JobPrice.constant 4).mul (price_nFirstSource B1 B2)).raise (by decide : 0≤4)).add
    ((JobPrice.constant 4).mul hp')).add ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_actualFormatter (B1 B2 : ℕ) : JobPrice (@actualFormatterBudget B1 B2) 1 := by
  obtain ⟨K,e,h⟩:=StagePrint.EntryFormat.formatterBudget_linear
    (entrySizingCoefficient B1 B2) (entrySizingExponent B1 B2) false
  have hp : JobPrice (fun r : TermJob B1 B2=>(r.moment.call.n+1)^e) 0 :=
    JobPrice.of_arity ⟨1,e,by intro r;simp⟩
  have hh:=((JobPrice.constant K).mul ((price_exactEntryLength B1 B2).add
    ((JobPrice.constant 1).raise (by decide : 0≤1)))).mul hp
  refine hh.mono ?_
  intro r
  exact h (boundedExactEntry r)

theorem price_termRequestSource (B1 B2 : ℕ) :
    JobPrice (@termRequestSourceBudget B1 B2) 4 :=
  (((JobPrice.constant 4).mul (price_entrySource B1 B2)).add
    (((JobPrice.constant 4).mul (price_actualFormatter B1 B2)).raise (by decide : 1≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

end NearQuarticWires.StageCertNative
