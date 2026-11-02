import Proof.Quartic.StageFormulaMetadata.CountPass
import Proof.Quartic.StageFormulaMetadata.HeaderEmit

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream modulusVar)

/-- `lem:print`, paper/paper.tex: the emitted
prefix contains exactly the frozen computed scalar fields. -/
def packetFormattedHeader (packet : RawWalkPacket) (tokens : List Tok) : List Bool :=
  let length:=(tokenStream (normalizeTokens packet.modulus tokens)).length
  let hint:=hintValue packet.arity (tokens.map tokenAstSize).sum tokens.length length packet.modulus
  let setup:=setupValue packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length length packet.modulus
  natWord packet.index++natWord setup++natWord packet.degree++natWord length++natWord hint++
    natWord packet.modulus++natWord packet.arity++natWord tokens.length

/-- `lem:print`, paper/paper.tex: the actual
header stage computes its field lengths and hints, then writes them. -/
def buildHeader : St VV MM := .seq headerLengths (.seq hintArithmetic emitFormattedHeader)

/-- `prop:time`, paper/paper.tex: every scalar
scan and header bit is included in the complete source clock. -/
def headerSteps (packet : RawWalkPacket) (tokens : List Tok) (width : ℕ) : ℕ :=
  5*(natBitLength packet.arity+natBitLength tokens.length+natBitLength packet.modulus)+320*width+466

/-- `lem:print`, paper/paper.tex: the raw source
and scalar context remain after the actual final header is written. -/
structure HeaderReady (packet : RawWalkPacket) (tokens : List Tok) (a : DS VV MM) : Prop where
  index : a.env rawIndexVar=packet.index
  degree : a.env rawDegreeVar=packet.degree
  modulus : a.env modulusVar=packet.modulus
  arity : a.env rawArityVar=packet.arity
  payloadLength : a.env payloadLengthVar=packet.payload.length
  memory : a.ram 0=packet.payload.map Bool.toNat
  cursor : a.rc 0=packet.payload.length
  input : a.ip=packet.word.length
  output : a.out=packetFormattedHeader packet tokens
  constants : Cst a

/-- `lem:print` and `prop:time`, paper/paper.tex: the first-pass counters drive the actual complete
compiler header with no supplied metadata or workspace hint. -/
theorem buildHeader_spec (C : Ctx) (packet : RawWalkPacket) (tokens : List Tok)
    (hsource : packet.payload=tokenStream tokens) (hmode : packet.modulus=0 ∨ 2 ≤ packet.modulus)
    (hwidth : finiteWidth packet.word.length≤C.Wd) (a : DS VV MM) (ha : Counted packet tokens a) :
    Hs C buildHeader a (headerSteps packet tokens C.Wd) (HeaderReady packet tokens) := by
  let length:=(tokenStream (normalizeTokens packet.modulus tokens)).length
  let hint:=hintValue packet.arity (tokens.map tokenAstSize).sum tokens.length length packet.modulus
  let setup:=setupValue packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length length packet.modulus
  have cap:=raw_loopCapacity packet tokens C.Wd hsource hmode hwidth
  have bounds:=hint_partial_bounds packet.degree packet.arity (tokens.map tokenAstSize).sum tokens.length length packet.modulus
  dsimp only at bounds
  have hFormula : formulaLengthValue packet.arity tokens.length length<2^C.Wd :=
    lt_of_le_of_lt (bounds.2.2.1.trans (bounds.2.2.2.1.trans bounds.2.2.2.2.2.1)) cap.setup
  have hQword : (natWord packet.modulus).length<2^C.Wd :=
    lt_of_le_of_lt (bounds.2.2.2.2.1.trans bounds.2.2.2.2.2.1) cap.setup
  unfold buildHeader
  refine (Hs.seq (t2:=41+(8*(40*C.Wd+43)+1)+1)
    (headerLengths_spec C a ha.constants packet.arity tokens.length packet.modulus length
      ha.arity ha.tokenCount ha.modulus ha.emitted hFormula hQword)
    fun b ⟨hbL,hbq,hbsh,hbc,hbf⟩=>?_).mono
      (by unfold headerSteps;omega) (fun _ h=>h)
  have hbD : b.env rawDegreeVar=packet.degree := by rw [hbf _ (by decide),ha.degree]
  have hbA : b.env rawArityVar=packet.arity := by rw [hbf _ (by decide),ha.arity]
  have hbS : b.env syntaxSizeVar=(tokens.map tokenAstSize).sum := by rw [hbf _ (by decide),ha.syntaxCount]
  refine Hs.seq (t2:=8*(40*C.Wd+43)+1)
    (hintArithmetic_spec C b hbc packet.degree packet.arity (tokens.map tokenAstSize).sum
      tokens.length length packet.modulus hbD hbA hbS hbL hbq cap.setup)
    fun d ⟨hdH,hdU,hdsh,hdc,hdf⟩=>?_
  have hwhole : Fr a d [aw0,fieldBytesVar,vJ,arityLengthVar,countLengthVar,modulusBitsVar,
      formulaLengthVar,tenVar,hintBaseVar,squareScratchVar,innerHintVar,setupHintVar] :=
    (hbf.weaken (by decide)).trans (hdf.weaken (by decide))
  have hdI : d.env rawIndexVar=packet.index := by rw [hwhole _ (by decide),ha.index]
  have hdD : d.env rawDegreeVar=packet.degree := by rw [hwhole _ (by decide),ha.degree]
  have hdA : d.env rawArityVar=packet.arity := by rw [hwhole _ (by decide),ha.arity]
  have hdQ : d.env modulusVar=packet.modulus := by rw [hwhole _ (by decide),ha.modulus]
  have hdL : d.env emittedLengthVar=length := by rw [hwhole _ (by decide),ha.emitted]
  have hdN : d.env countedTokensVar=tokens.length := by rw [hwhole _ (by decide),ha.tokenCount]
  have hfieldFit : ∀ field∈formattedHeaderFields,d.env field<2^C.Wd := by
    intro field hfield
    simp only [formattedHeaderFields,List.mem_cons,List.not_mem_nil,or_false] at hfield
    have hscalar (value : ℕ) (hv : value∈packet.header) : value<2^C.Wd :=
      (rawField_value packet value hv).trans_le (Nat.pow_le_pow_right (by decide) (by
        unfold finiteWidth at hwidth;omega))
    rcases hfield with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hdI];exact hscalar _ (by simp [RawWalkPacket.header])
    · rw [hdU];exact cap.setup
    · rw [hdD];exact hscalar _ (by simp [RawWalkPacket.header])
    · rw [hdL];exact cap.normalized
    · rw [hdH];exact lt_of_le_of_lt bounds.2.2.2.2.2.1 cap.setup
    · rw [hdQ];exact hscalar _ (by simp [RawWalkPacket.header])
    · rw [hdA];exact hscalar _ (by simp [RawWalkPacket.header])
    · rw [hdN];exact cap.count
  have hfieldBits : ∀ field∈formattedHeaderFields,natBitLength (d.env field)≤C.Wd :=
    fun field hfield=>nbl_le_of_lt (hfieldFit field hfield) (by have h:=cap.widthBound;omega)
  refine (emitFormattedHeader_spec C d hdc packet.index setup packet.degree length hint packet.modulus
    packet.arity tokens.length C.Wd hdI hdU hdD hdL hdH hdQ hdA hdN hfieldBits
    (by have h:=cap.widthBound;omega) (binaryWidth_room C.Wd (by have h:=cap.widthBound;omega))).mono le_rfl ?_
  rintro last ⟨hlo,hlrest,hlc,hlf⟩
  have hsame:=Same.of_sh (hdsh.trans hbsh)
  simp only [Prod.mk.injEq] at hlrest
  rcases hlrest with ⟨hlip,hlram,hlrc,_hlkin,_hlkout,_hlkc⟩
  refine ⟨by rw [hlf _ (by decide),hdI],by rw [hlf _ (by decide),hdD],
    by rw [hlf _ (by decide),hdQ],by rw [hlf _ (by decide),hdA],?_,?_,?_,?_,?_,hlc⟩
  · rw [hlf _ (by decide),hwhole _ (by decide),ha.payloadLength]
  · rw [hlram,hsame.ram,ha.memory]
  · rw [hlrc,hsame.rc,ha.cursor]
  · rw [hlip,hsame.ip,ha.input]
  · rw [hlo,hsame.out,ha.output]
    rfl

end NearQuarticWires.StageFormulaMetadata
