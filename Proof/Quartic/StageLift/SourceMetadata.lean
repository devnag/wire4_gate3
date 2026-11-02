import Proof.Quartic.StageLift.PrintHeaders
import Proof.Quartic.StageLift.CallKindSource
import Proof.Quartic.StageLift.GammaWalk
import Proof.Quartic.StageLift.RegisterFrame

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens

instance avoidsStoreOpDecidable {V M : ℕ} (x : Fin M) (o : Op V M) :
    Decidable (avoidsStoreOp x o) := by
  cases o <;> dsimp only [avoidsStoreOp] <;> infer_instance

instance avoidsStoreDecidable {V M : ℕ} (x : Fin M) (s : St V M) :
    Decidable (avoidsStore x s) :=
  match s with
  | .op _ => avoidsStoreOpDecidable _ _
  | .seq left right | .ite _ left right =>
      @instDecidableAnd _ _ (avoidsStoreDecidable x left) (avoidsStoreDecidable x right)
  | .loop _ body => avoidsStoreDecidable x body

/-- Step 3 and `lem:print`, paper/paper.tex: headers save the parsed prime before its temporary
register is reused for the selected Gamma side and circuit ordinal. -/
def initializePrintMetadata : St VV MM :=
  .seq computePrintHeaders (.seq readPrintPattern (.seq retainPrintKind startPrintWalks))

/-- Step 3 and `lem:print`, paper/paper.tex: each metadata field comes from a real parameter,
original-call, sign-record or Gamma-list read. Every retained source
except the new eight-record pattern copy is preserved. -/
theorem initializePrintMetadata_source_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (hc : Cst a)
    (ha : PrintRequestData r a)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0)
    (hW : 5 ≤ C.Wd) (hfit : 17 * (Builder.allGates r.child.call).length < 2 ^ C.Wd)
    (hroom : 16 * r.child.selected.1.Xmax +
      (2 * r.child.selected.1.e - 1) * (2 * (r.child.selected.1.J + 1)) * r.prime +
      2 * r.child.selected.1.e + 2 * (r.child.selected.1.J + 1) + r.prime + 17 < 2 ^ C.Wd)
    (hcap : 256 < 2 ^ C.Wd)
    (hn : natBitLength r.child.call.n + 2 ≤ C.Wd)
    (hk : natBitLength (kindTag r.child.call.kind) + 2 ≤ C.Wd)
    (hwalk : natBitLength (r.child.cellCall.seed.N ^ 8) + 2 ≤ C.Wd) :
    Hs C initializePrintMetadata a
      (a.rc parameterStore + a.rc indexStore + a.rc callStore + a.rc gammaStore +
        30 * natBitLength r.child.call.n +
        30 * natBitLength (kindTag r.child.call.kind) +
        30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 1918) (fun b =>
      b.env degreeVar = residueDegreeBound r.child.selected.1 r.prime ∧
      b.env printArityVar = 17 * (Builder.allGates r.child.call).length ∧
      b.env degreeExponent = r.child.selected.1.e ∧
      b.env degreeChain = r.child.selected.1.J ∧ b.env degreePrime = r.prime ∧
      b.env signCodeVar = printPatternCode r.pattern ∧
      b.env callKindVar = kindTag r.child.call.kind ∧
      b.env printWalkIndex = 0 ∧ b.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧
      b.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e ∧
      b.env preparedLength = a.env preparedLength ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      b.rc gammaStore = (RepairRepresentation.natWord (r.child.cellCall.seed.N ^ 8)).length ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  obtain ⟨b, nb, heb, hnb, hbD, hbV, hbe, hbJ, hbp, _hbG, _hbG1,
    hbram, hbsh, _hbcur, hbc, hbfr⟩ :=
    computePrintHeaders_spec C r.child.call hs r.prime a hc ha.scalarFields ha.prime
      (Reconstruct.PrintRequest.prime_prime r).two_le hW hfit hroom
  have hbi : b.ram indexStore = normalizedPrintIndex r := by rw [hbram]; exact ha.indexFields
  have hbiCur : b.rc indexStore = a.rc indexStore :=
    (avoidsStore_spec heb (by decide)).2
  have hbcCur : b.rc callStore = a.rc callStore :=
    (avoidsStore_spec heb (by decide)).2
  have hbgCur : b.rc gammaStore = a.rc gammaStore :=
    (avoidsStore_spec heb (by decide)).2
  have hbempty : b.ram patternStore = [] ∧ b.rc patternStore = 0 := by
    rw [hbram, (avoidsStore_spec heb (by decide)).2]
    exact hempty
  obtain ⟨d, nd, hed, hnd, _hdside, hdcode, hdram, hdrc, hdsh, hdc, hdfr⟩ :=
    readPrintPattern_spec C r b hbc hbi hbempty hcap
  rw [hbiCur] at hnd
  have hdcall : d.ram callStore = (callWord r.child.call).map Bool.toNat := by
    rw [hdram callStore (by decide), hbram]
    exact ha.originalCall
  have hdcCur : d.rc callStore = a.rc callStore :=
    (hdrc _ (by decide) (by decide)).trans hbcCur
  have hdgCur : d.rc gammaStore = a.rc gammaStore :=
    (hdrc _ (by decide) (by decide)).trans hbgCur
  obtain ⟨e, ne, hee, hne, hekind, herest, hec, hefr⟩ :=
    retainPrintKind_spec C r.child.call d hdc hdcall hn hk
  rw [hdcCur] at hne
  have heram : e.ram = d.ram := congrArg (fun t => t.2.2.1) herest
  have hesh : (e.ip, e.out, e.kin, e.kout, e.kc) =
      (d.ip, d.out, d.kin, d.kout, d.kc) :=
    congrArg (fun t => (t.1, t.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) herest
  have hegCur : e.rc gammaStore = a.rc gammaStore :=
    ((avoidsStore_spec hee (by decide)).2).trans hdgCur
  have hegamma : e.ram gammaStore =
      (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat := by
    rw [heram, hdram gammaStore (by decide), hbram]
    exact ha.gammaBits
  obtain ⟨z, nz, hez, hnz, hzindex, hzcount, _hzrc, hzram, hzsh, hzc, hzfr⟩ :=
    startPrintWalks_spec C r e hec hegamma hwalk
  rw [hegCur] at hnz
  have hex : Ex C initializePrintMetadata a z (nb + (nd + (ne + nz + 1) + 1) + 1) :=
    Ex.seq heb (Ex.seq hed (Ex.seq hee hez))
  refine ⟨z, _, hex, by omega, ?_⟩
  have hfirst : Fr b z
      ([partVar, t1, vJ, StagePrint.Header.count, StagePrint.Header.translation,
        StagePrint.Header.power, StagePrint.Header.index, c0, t3, signCodeVar] ++
        (callKindVar :: StageRecovery.widthVar :: StageCertTests.scheduleCallKindVar :: rdNatT) ++
        (printWalkIndex :: printWalkCount :: rdNatT)) :=
    (hdfr.weaken (by intro x hx; simp only [List.mem_append]; exact Or.inl (Or.inl hx))).trans
      ((hefr.weaken (by intro x hx; simp only [List.mem_append]; exact Or.inl (Or.inr hx))).trans
        (hzfr.weaken (by intro x hx; simp only [List.mem_append]; exact Or.inr hx)))
  refine ⟨(hfirst _ (by decide)).trans hbD, (hfirst _ (by decide)).trans hbV,
    (hfirst _ (by decide)).trans hbe, (hfirst _ (by decide)).trans hbJ,
    (hfirst _ (by decide)).trans hbp, ?_, ?_, hzindex, hzcount, ?_, ?_, ?_,
    by rw [_hzrc, Function.update_self],
    hzsh.trans (hesh.trans (hdsh.trans hbsh)), hzc⟩
  · exact (hzfr _ (by decide)).trans ((hefr _ (by decide)).trans hdcode)
  · exact (hzfr _ (by decide)).trans hekind
  · exact (avoidsRegister_spec hex (by decide)).trans ha.modulus
  · exact avoidsRegister_spec hex (by decide)
  · intro store hstore
    rw [hzram, heram, hdram store hstore, hbram]

/-- Step 3 and `lem:print`, paper/paper.tex: the original metadata contract follows by retaining
only its header and source-record conclusions. -/
theorem initializePrintMetadata_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (hc : Cst a)
    (ha : PrintRequestData r a)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0)
    (hW : 5 ≤ C.Wd) (hfit : 17 * (Builder.allGates r.child.call).length < 2 ^ C.Wd)
    (hroom : 16 * r.child.selected.1.Xmax +
      (2 * r.child.selected.1.e - 1) * (2 * (r.child.selected.1.J + 1)) * r.prime +
      2 * r.child.selected.1.e + 2 * (r.child.selected.1.J + 1) + r.prime + 17 < 2 ^ C.Wd)
    (hcap : 256 < 2 ^ C.Wd)
    (hn : natBitLength r.child.call.n + 2 ≤ C.Wd)
    (hk : natBitLength (kindTag r.child.call.kind) + 2 ≤ C.Wd)
    (hwalk : natBitLength (r.child.cellCall.seed.N ^ 8) + 2 ≤ C.Wd) :
    Hs C initializePrintMetadata a
      (a.rc parameterStore + a.rc indexStore + a.rc callStore + a.rc gammaStore +
        30 * natBitLength r.child.call.n +
        30 * natBitLength (kindTag r.child.call.kind) +
        30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 1918) (fun b =>
      b.env degreeVar = residueDegreeBound r.child.selected.1 r.prime ∧
      b.env printArityVar = 17 * (Builder.allGates r.child.call).length ∧
      b.env degreeExponent = r.child.selected.1.e ∧
      b.env degreeChain = r.child.selected.1.J ∧ b.env degreePrime = r.prime ∧
      b.env signCodeVar = printPatternCode r.pattern ∧
      b.env callKindVar = kindTag r.child.call.kind ∧
      b.env printWalkIndex = 0 ∧ b.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧
      b.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e ∧
      b.env preparedLength = a.env preparedLength ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  exact (initializePrintMetadata_source_spec C r a hc ha hempty hW hfit hroom hcap hn hk hwalk).mono
    le_rfl (fun _ ⟨hD,hV,he,hJ,hp,hs,hk,hi,hN,hq,hP,hr,_hcursor,hio,hc⟩ =>
      ⟨hD,hV,he,hJ,hp,hs,hk,hi,hN,hq,hP,hr,hio,hc⟩)

end NearQuarticWires.StageLift
