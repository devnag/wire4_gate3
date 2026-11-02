import Proof.Quartic.StageCert.TupleOrderLoop
import Proof.Quartic.StageCert.SelectionToken

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: decode the next bounded occurrence index, fetch its actual
retained witness bit, and serialize its full original residual square. -/
def emitTupleFactor (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq decodeTupleDigit
    (.seq (.op (.copy atomOccurrence tupleDigit)) (emitSourceSquare store edge))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a tuple factor changes only actual arithmetic, occurrence,
record-scan and output-printer scratch fields. -/
def tupleFactorScratch : List (Fin VV) :=
  [tuplePower,tupleQuotient,tupleRemainder,tupleDigit,atomOccurrence,sourceRecordLimit,
    selectedTokenBit,sourceRecordIndex,sourceRecordDiscard,atomRole,atomValue]++StageLift.tokenScratch

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: every emitted tuple factor is
computed from original address arithmetic and actual witness records;
the source scan and every original atom token are paid explicitly. -/
theorem emitTupleFactor_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree position address k B : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hi : position<degree) (hb : a.env atomCount=G)
    (hp : a.env tuplePower=G^(degree-position)) (ha : a.env tupleAddress=address)
    (hk : a.env selectionStart=k) (hram : a.ram store=bits.map Bool.toNat)
    (hcursor : a.rc store≤bits.length) (hbits : k+G≤bits.length)
    (haddress : k+G≤2^C.Wd) (hfit : 2*G^degree≤2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitTupleFactor store edge) a
      (bits.length+5*(k+G)+160*B+530) (fun z=>
      z.out=a.out++(toks (StagePrint.selectedSquare (by decide : 0<4)
        (fun i : Fin G=>bits.getD (k+i.val) false) edge
        ⟨address/G^(degree-1-position)%G,Nat.mod_lt _ (by omega)⟩)).flatMap tokWord ∧
      z.env tuplePower=G^(degree-1-position) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z tupleFactorScratch) := by
  let g := address/G^(degree-1-position)%G
  have hg : g<G := Nat.mod_lt _ (by omega)
  unfold emitTupleFactor
  apply Hx.hs
  refine Hs.then (decodeTupleDigit_run C a hc G degree position address hG hi hb hp ha hfit)
    (fun d ⟨dp,dd,ds,dc,dfr⟩ n1 hn1=>?_)
  refine Hs.then (hs_copy C atomOccurrence tupleDigit d (by decide))
    (fun e he n2 hn2=>?_)
  subst he
  let e := d.set atomOccurrence (d.env tupleDigit)
  have ec : Cst e := Cst.of_fr (T := [atomOccurrence]) dc (Fr.set _ _ (by simp)) (by decide)
  have eG : e.env atomCount=G := by
    rw [DS.set_env_ne _ _ (by decide),dfr _ (by decide)]
    exact hb
  have eg : e.env atomOccurrence=g := by
    change d.env tupleDigit=g
    exact dd
  have ek : e.env selectionStart=k := by
    rw [DS.set_env_ne _ _ (by decide),dfr _ (by decide)]
    exact hk
  have eram : e.ram=a.ram := congrArg (fun q=>q.2.2.1) ds
  have erc : e.rc=a.rc := congrArg (fun q=>q.2.2.2.1) ds
  have eo : e.out=a.out := congrArg (fun q=>q.2.1) ds
  have esrc : (e.ip,e.ram,e.kin,e.kout,e.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at ds
    simp only [Prod.mk.injEq]
    exact ⟨ds.1,ds.2.2.1,ds.2.2.2.2.1,ds.2.2.2.2.2.1,ds.2.2.2.2.2.2⟩
  refine Hs.last (emitSourceSquare_run C store edge G g k B hg bits e ec eG eg ek
    (by rw [eram]; exact hram) (by omega) (by omega) hW hindex (hB g hg) hBit)
    (fun z ⟨zo,zsrc,zrc,zc,zfr⟩ n3 hn3=>?_)
  have zpow : z.env tuplePower=G^(degree-1-position) := by
    rw [zfr _ (by decide),DS.set_env_ne _ _ (by decide)]
    exact dp
  refine ⟨⟨by simpa only [eo] using zo,zpow,zsrc.trans esrc,by omega,zc,
    (dfr.weaken (by decide)).trans ((Fr.set _ _ (by simp [tupleFactorScratch])).trans
      (zfr.weaken (by decide)))⟩,?_⟩
  rw [erc] at hn3
  omega

end NearQuarticWires.StageCert.Tokens
