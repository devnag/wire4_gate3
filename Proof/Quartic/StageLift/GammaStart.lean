import Proof.Quartic.StageLift.PrintRequest
import Proof.Quartic.StageLift.GammaRead

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3, `sec:algorithm`, paper/paper.tex: the requested signed
split is reloaded from the first actual retained index record. -/
def loadPrintPart : St VV MM :=
  .seq (.op (.rwM indexStore)) (.op (.rdM indexStore partVar))

/-- Step 3, `sec:algorithm`, paper/paper.tex: the signed-split
selector is obtained from the normalized index bank by paid real reads. -/
theorem loadPrintPart_spec (C : Ctx) (side : Bool) (tail : List ℕ)
    (a : DS VV MM) (hc : Cst a) (hindex : a.ram indexStore = side.toNat :: tail) :
    Hs C loadPrintPart a (a.rc indexStore + 3) (fun b =>
      b.env partVar = side.toNat ∧ b.rc = Function.update a.rc indexStore 1 ∧
      b.ram = a.ram ∧ (b.ip, b.out, b.kin, b.kout, b.kc) =
        (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [partVar]) := by
  unfold loadPrintPart
  refine Hs.seq (t2 := 1) (hs_rwM C indexStore a) fun b hb => ?_
  subst b
  refine (hs_rdM C indexStore partVar (a.rew indexStore)
    (by simp [DS.rew, hindex])).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, rfl, rfl, ?_, Fr.set _ _ (by simp)⟩
  · simp [DS.set, DS.adv, DS.rew, hindex]
  · simp [DS.set, DS.adv, DS.rew, Function.update_idem]
  · exact Cst.of_fr (T := [partVar]) hc (Fr.set _ _ (by simp)) (by decide)

/-- `cor:conditional` and Step 3, paper/paper.tex: the retained Gamma source is rewound once, and its
actual list header supplies the runtime all-walk loop bound. -/
def startGamma (count : Fin VV) : St VV MM :=
  .seq (.op (.rwM gammaStore)) (readMemoryVariable gammaStore count)

/-- `cor:conditional` and Step 3, paper/paper.tex: the actual Gamma list count is read before its integer
payload. The head return is paid, and all source records are preserved. -/
theorem startGamma_spec (C : Ctx) (count : Fin VV) (hcount : count ∉ rdNatT)
    (hconst : count ≠ vZ ∧ count ≠ v1 ∧ count ≠ v2) (values : List ℤ)
    (a : DS VV MM) (hc : Cst a)
    (hgamma : a.ram gammaStore =
      (listWord NearCubicGates.Close.Interfaces.intWord values).map Bool.toNat)
    (hwidth : natBitLength values.length + 2 ≤ C.Wd) :
    Hs C (startGamma count) a (a.rc gammaStore + 30 * natBitLength values.length + 34)
      (fun b => b.env count = values.length ∧
        b.rc = Function.update a.rc gammaStore (natWord values.length).length ∧
        b.ram = a.ram ∧ (b.ip, b.out, b.kin, b.kout, b.kc) =
          (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b (count :: rdNatT)) := by
  unfold startGamma
  refine (Hs.seq (t2 := 30 * natBitLength values.length + 32)
    (hs_rwM C gammaStore a) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  have hr := readMemoryVariable_spec C gammaStore
    (listWord NearCubicGates.Close.Interfaces.intWord values) (a.rew gammaStore)
    ⟨hc.z, hc.one, hc.two⟩ hgamma
    count hcount hconst values.length
    (values.flatMap NearCubicGates.Close.Interfaces.intWord)
    (by simp [DS.rew, NearCubicGates.Close.Interfaces.listWord]) hwidth
  refine hr.mono le_rfl ?_
  rintro b ⟨hbv, hbcursor, hbrest, hbc, hbf⟩
  have hram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  have hrc : Function.update b.rc gammaStore 0 =
      Function.update a.rc gammaStore 0 := by
    simpa only [memorySourceRest, DS.rew, Function.update_idem] using
      congrArg (fun t => t.2.2.2.1) hbrest
  have hcursor : b.rc gammaStore = (natWord values.length).length := by
    simpa only [DS.rew, Function.update_self, zero_add] using hbcursor
  refine ⟨hbv, ?_, hram, ?_, hbc, hbf⟩
  · funext store
    by_cases hs : store = gammaStore
    · subst store
      simpa only [Function.update_self] using hcursor
    · have heq := congrFun hrc store
      simpa only [Function.update_of_ne hs] using heq
  · simpa only [memorySourceRest, DS.rew] using
      congrArg (fun t => (t.1, t.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) hbrest

/-- `cor:conditional` and Step 3, paper/paper.tex: the actual source count is exactly the full closed-walk
census, including zero coefficients rather than deleting them. -/
theorem actualGamma_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (Greedy.gammaTable r.child).length = r.child.cellCall.seed.N ^ 8 := by
  simp only [Greedy.gammaTable, List.length_map, Greedy.walkList_length]
  rfl

end NearQuarticWires.StageLift
