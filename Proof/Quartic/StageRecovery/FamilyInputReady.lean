import Proof.Quartic.StageRecovery.FamilyExecutionBounds
import Proof.Quartic.StageRecovery.FamilyReturn
import Proof.Quartic.StageRecovery.InputForward

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the genuine state at
the original Formula token cursor after the appended native family has
been physically loaded, counted and rewound. -/
structure FamilyCacheReady (r : FamilyCompileRequest) (sourceCursor : ℕ) (a : DS VV MM) : Prop where
  arity : a.env arityVar = r.source.arity
  modulus : a.env modulusVar = r.source.modulus
  tokens : a.env tokenCountVar = (toks r.source.formula).length
  tokenLength : a.env tokenLengthVar = (tokenStream (toks r.source.formula)).length
  radix : a.env coordinateBaseVar = 2 ^ r.source.arity
  width : a.env FixedBits.width = r.family.width
  count : a.env cacheCountVar = (famRecs r.source.arity r.degree).length
  sourcePosition : a.ip = sourceCursor
  records : a.ram familyRecordStore = famRecs r.source.arity r.degree
  recordCursor : a.rc familyRecordStore = 0
  others : ∀ m ≠ familyRecordStore, a.ram m = [] ∧ a.rc m = 0
  output : a.out = []
  constants : Cst a

/-- `lem:print`, paper/paper.tex: the native-family
join is an actual source program, including the single complete input
return and the genuine generated-record-store rewind. -/
def prepareFamilyCacheProgram : St VV MM :=
  .seq prepareFamilyProgram
    (.seq inputForwardProgram
      (.seq loadFamilyPacketProgram
        (.seq returnFromFamilyProgram (.op (.rwM familyRecordStore)))))

/-- `prop:time`, paper/paper.tex: native packet loading
and the one-time return have linear family-record and source-byte costs. -/
def FamilyCompileRequest.prepareCacheSteps (r : FamilyCompileRequest) : ℕ :=
  7 * r.source.arity + 5 * (tokenStream (toks r.source.formula)).length +
    (famRecs r.source.arity r.degree).length * (12 * r.family.width + 22) +
    5 * ((tokenStream (toks r.source.formula)).length +
      (famRecs r.source.arity r.degree).length * (2 * r.family.width + 1) + 1) +
    (famRecs r.source.arity r.degree).length + 100

/-- `lem:print`, paper/paper.tex: the actual appended
family packet produces the precise cold cache state, with its record
count obtained by parsing and every head movement included. -/
theorem prepareFamilyCacheProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : FamilyCompileRequest) (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd)
    (hV : a.env arityVar = r.source.arity) (hD : a.env familyBoundVar = r.degree)
    (hq : a.env modulusVar = r.source.modulus)
    (htokens : a.env tokenCountVar = (toks r.source.formula).length)
    (hL : a.env tokenLengthVar = (tokenStream (toks r.source.formula)).length)
    (hin : C.inp.drop a.ip = tokenStream (toks r.source.formula) ++ r.family.output)
    (hram : a.ram = fun _ => []) (hrc : a.rc = fun _ => 0) (hout : a.out = []) :
    Hs C prepareFamilyCacheProgram a r.prepareCacheSteps (FamilyCacheReady r a.ip) := by
  let W := r.family.width
  let records := famRecs r.source.arity r.degree
  let N := records.length
  let L := (tokenStream (toks r.source.formula)).length
  obtain ⟨hRW, hNfit, hLfit, hspan, hreturnfit⟩ := r.family_parser_bounds C hwidth
  have hWpos : 0 < W := by dsimp [W, FamilyCompileRequest.family, FamilyRequest.width]; omega
  have hdim : r.source.arity + r.degree + 10 ≤ C.Wd := by
    have h := r.setupHint_width
    dsimp [FamilyCompileRequest.family, FamilyRequest.width] at h
    omega
  unfold prepareFamilyCacheProgram
  refine Hx.hs (Hs.then (prepareFamilyProgram_spec C a hc r.family hV hD hdim)
    fun b ⟨hbW, hbBase, _, hbsh, hbc, hbf⟩ n1 hn1 => ?_)
  have hbsame := Same.of_sh hbsh
  have hbL : b.env tokenLengthVar = L := by rw [hbf _ (by decide), hL]
  have hinput : C.inp.drop b.ip = tokenStream (toks r.source.formula) ++ r.family.output := by rw [hbsame.ip]; exact hin
  refine Hs.then (inputForwardProgram_spec C b hbc (tokenStream (toks r.source.formula))
    r.family.output hbL hinput hLfit) fun d ⟨hdi, hdr, hdc, hdf⟩ n2 hn2 => ?_
  have hdram : d.ram = b.ram := congrArg (fun x => x.2.1) hdr
  have hdrc : d.rc = b.rc := congrArg (fun x => x.2.2.1) hdr
  have hdout : d.out = b.out := congrArg Prod.fst hdr
  have hdempty : d.ram = fun _ => [] := hdram.trans (hbsame.ram.trans hram)
  have hdcursor : d.rc = fun _ => 0 := hdrc.trans (hbsame.rc.trans hrc)
  have hpacket : C.inp.drop d.ip = nativeFamilyPacket W records ++ [] := by
    rw [hdi, ← List.drop_drop, hinput, List.drop_left]
    simp only [List.append_nil]
    rfl
  refine Hs.then (loadFamilyPacketProgram_spec C d hdc W records [] hWpos hRW
    r.family_records_fit hNfit hpacket (by rw [hdempty]) (by rw [hdcursor]))
    fun e ⟨heN, _, hei, heout, heram, herc, _, _, _, hec, hef⟩ n3 hn3 => ?_
  have heL : e.env tokenLengthVar = L := by rw [hef _ (by decide), hdf _ (by decide), hbL]
  have heW : e.env FixedBits.width = W := by rw [hef _ (by decide), hdf _ (by decide), hbW]
  have heip : e.ip = a.ip + (L + N * (2 * W + 1) + 1) := by
    rw [hei, hdi, hbsame.ip, nativeFamilyPacket_length]
    dsimp [L, N]
    omega
  refine Hs.then (returnFromFamilyProgram_spec C e hec L W N a.ip heL heW heN hspan hreturnfit heip)
    fun f ⟨hfi, hfL, hfr, hfc, hff⟩ n4 hn4 => ?_
  have hfram : f.ram = e.ram := congrArg (fun x => x.2.1) hfr
  have hfrc : f.rc = e.rc := congrArg (fun x => x.2.2.1) hfr
  have hfout : f.out = e.out := congrArg Prod.fst hfr
  have hfcursor : f.rc familyRecordStore = N := by rw [hfrc, herc]; simp; rfl
  refine Hs.last ((hs_rwM C familyRecordStore f).mono (show f.rc familyRecordStore + 1 ≤ N + 1 by rw [hfcursor]) (fun _ h => h))
    fun g hg n5 hn5 => ?_
  subst g
  refine ⟨⟨?_, ?_, ?_, hfL, ?_, ?_, ?_, hfi, ?_, ?_, ?_, ?_, ⟨hfc.z, hfc.one, hfc.two⟩⟩, ?_⟩
  · simp only [DS.rew]
    rw [hff _ (by decide), hef _ (by decide), hdf _ (by decide), hbf _ (by decide), hV]
  · simp only [DS.rew]
    rw [hff _ (by decide), hef _ (by decide), hdf _ (by decide), hbf _ (by decide), hq]
  · simp only [DS.rew]
    rw [hff _ (by decide), hef _ (by decide), hdf _ (by decide), hbf _ (by decide), htokens]
  · simp only [DS.rew]
    rw [hff _ (by decide), hef _ (by decide), hdf _ (by decide), hbBase]
    rfl
  · simp only [DS.rew]
    rw [hff _ (by decide), hef _ (by decide), hdf _ (by decide), hbW]
  · simp only [DS.rew]
    rw [hff _ (by decide), heN]
  · simp only [DS.rew]
    rw [hfram, heram]
    simp [records]
  · simp [DS.rew]
  · intro m hm
    constructor
    · simp only [DS.rew]
      rw [hfram, heram, Function.update_of_ne hm, hdempty]
    · simp only [DS.rew, Function.update_of_ne hm]
      rw [hfrc, herc, Function.update_of_ne hm, hdcursor]
  · simp only [DS.rew]
    rw [hfout, heout, hdout, hbsame.out, hout]
  · unfold FamilyCompileRequest.prepareCacheSteps
    dsimp [W, N, L, records] at *
    change n1 ≤ 7 * r.source.arity + 34 at hn1
    omega

end NearQuarticWires.StageRecovery
