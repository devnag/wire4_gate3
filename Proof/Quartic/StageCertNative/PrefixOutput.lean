import Proof.Quartic.StageCertNative.CopyFrames
import Proof.Quartic.StageCertNative.NativeBitsProgram
import Proof.Quartic.StageCertNative.NFirstSource
import Proof.Quartic.StageCert.MomentHeader

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens StageLift

/-- `lem:print`, paper/paper.tex: literal exact
native-format fields preceding its counted framed Terms payload. -/
noncomputable def exactPrefixWord {B1 B2 : ℕ} (r : TermJob B1 B2) : List Bool :=
  natWord r.moment.call.n++StagePrint.Context.word r.base.prepared++
    [r.index.val,r.moment.packet.degree,Cells.nativeCertificateBits B1 r.moment.call.n].flatMap natWord

structure PrefixOutputReady {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2) (a : DS VV MM) : Prop where
  arity : a.env StagePrint.Header.arity=r.moment.call.n
  index : a.env sourceTermIndex=r.index.val
  degree : a.env degreeVar=r.moment.packet.degree
  bits : a.env nativeBitsResult=Cells.nativeCertificateBits B1 r.moment.call.n
  source : C.inp.drop a.ip=StagePrint.Context.word r.base.prepared

noncomputable def prefixScalarBits {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  natBitLength r.moment.call.n+natBitLength r.index.val+
    natBitLength r.moment.packet.degree+natBitLength (Cells.nativeCertificateBits B1 r.moment.call.n)

/-- `lem:print`, paper/paper.tex: the common
cached context is copied exactly once into this term's actual request,
with original n, ordinal, selected degree and computed coefficient bits. -/
def emitExactPrefix : St VV MM :=
  .seq (emitNaturalFields [StagePrint.Header.arity])
    (.seq (copyRawFrames 11) (emitNaturalFields [sourceTermIndex,degreeVar,nativeBitsResult]))

noncomputable def prefixOutputSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  11*(StagePrint.Context.word r.base.prepared).length+160*prefixScalarBits r+300

theorem emitExactPrefix_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (a : DS VV MM) (hc : Cst a) (hr : PrefixOutputReady C r a)
    (hW : 2≤C.Wd) (hbits : prefixScalarBits r+2<2^C.Wd) :
    Hs C emitExactPrefix a (prefixOutputSteps r) (fun z=>z.out=a.out++exactPrefixWord r) := by
  unfold emitExactPrefix
  apply Hx.hs
  have ha : natBitLength r.moment.call.n≤prefixScalarBits r := by
    unfold prefixScalarBits
    omega
  refine Hs.then (emitNaturalFields_spec C [StagePrint.Header.arity] a hc (prefixScalarBits r)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;decide)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;rw [hr.arity];exact ha)
    hW hbits) (fun b ⟨bo,bs,bc,bf⟩ n1 hn1=>?_)
  have bip : b.ip=a.ip := congrArg Prod.fst bs
  refine Hs.then (copyContext_run C r.base.prepared [] b bc
    (by simpa only [bip,List.append_nil] using hr.source))
    (fun d ⟨_di,doo,_ds,dc,df⟩ n2 hn2=>?_)
  have dindex : d.env sourceTermIndex=r.index.val :=
    (df _ (by decide)).trans ((bf _ (by decide)).trans hr.index)
  have ddegree : d.env degreeVar=r.moment.packet.degree :=
    (df _ (by decide)).trans ((bf _ (by decide)).trans hr.degree)
  have dbits : d.env nativeBitsResult=Cells.nativeCertificateBits B1 r.moment.call.n :=
    (df _ (by decide)).trans ((bf _ (by decide)).trans hr.bits)
  have hvalues : ∀x∈[sourceTermIndex,degreeVar,nativeBitsResult],natBitLength (d.env x)≤prefixScalarBits r := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals first | rw [dindex] | rw [ddegree] | rw [dbits]
    all_goals unfold prefixScalarBits;omega
  refine Hs.last (emitNaturalFields_spec C [sourceTermIndex,degreeVar,nativeBitsResult] d dc
    (prefixScalarBits r) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> decide) hvalues hW hbits)
    (fun z ⟨zo,_zs,_zc,_zf⟩ n3 hn3=>?_)
  refine ⟨?_,?_⟩
  · rw [zo,doo,bo]
    simp only [exactPrefixWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      dindex,ddegree,dbits,hr.arity,List.append_assoc]
  · change n1≤1*(40*prefixScalarBits r+43)+1 at hn1
    change n3≤3*(40*prefixScalarBits r+43)+1 at hn3
    unfold prefixOutputSteps
    omega

end NearQuarticWires.StageCertNative
