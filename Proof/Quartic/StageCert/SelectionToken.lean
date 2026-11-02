import Proof.Quartic.StageCert.SelectionAddress

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `def:mask`, (W2) and `lem:print`(c), paper/paper.tex: original witness bits are read from their
actual retained record store before any selected square is serialized. -/
def emitSourceSquare (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq prepareSelectionAddress
    (.seq (readSourceRecord store selectedTokenBit) (emitSelectedSquare edge))

/-- `def:mask`, (W2) and `lem:print`(c), paper/paper.tex: the complete selected-square token stream is
computed from original occurrence indices and literal retained witness
records, with all source records and input/callee streams preserved. -/
theorem emitSourceSquare_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G g k B : ℕ) (hgG : g<G) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : a.env atomCount=G) (hg : a.env atomOccurrence=g) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hbit : k+g<bits.length)
    (haddress : k+g<2^C.Wd) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hfit : B+2<2^C.Wd) :
    Hs C (emitSourceSquare store edge) a
      (a.rc store+5*(k+g)+160*B+520) (fun z=>
      z.out=a.out++(toks (StagePrint.selectedSquare (by decide : 0<4)
        (fun i : Fin G=>bits.getD (k+i.val) false) edge ⟨g,hgG⟩)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store=k+g+1 ∧ Cst z ∧
      Fr a z (sourceRecordLimit::selectedTokenBit::sourceRecordIndex::sourceRecordDiscard::
        atomRole::atomValue::StageLift.tokenScratch)) := by
  have hvalue : (a.ram store).getD (k+g) 0=(bits.getD (k+g) false).toNat := by
    rw [hram,List.getD_eq_getElem _ _ (by simpa using hbit),List.getElem_map]
    simp only [List.getD_eq_getElem _ _ hbit]
  unfold emitSourceSquare
  apply Hx.hs
  refine Hs.then (prepareSelectionAddress_run C a hc k g hk hg haddress)
    (fun b ⟨bi,bsh,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bsh
  have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.2.1) bsh
  refine Hs.then (readSourceRecord_run C store selectedTokenBit (by decide) b bc (k+g) bi
    (by rw [bram,hram,List.length_map]; exact hbit) haddress)
    (fun d ⟨ds,dr,drest,dc,dfr⟩ n2 hn2=>?_)
  have ds' : d.env selectedTokenBit=(bits.getD (k+g) false).toNat := by
    rw [ds,bram,hvalue]
  have ddG : d.env atomCount=G := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hG)
  have ddg : d.env atomOccurrence=g := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hg)
  have hdo : d.out=a.out := (congrArg (fun q=>q.2.1) drest).trans (congrArg (fun q=>q.2.1) bsh)
  have ddsrc : (d.ip,d.ram,d.kin,d.kout,d.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) := by
    simp only [StageLift.memorySourceRest,DS.sh,Prod.mk.injEq] at drest bsh
    simp only [Prod.mk.injEq]
    exact ⟨drest.1.trans bsh.1,drest.2.2.1.trans bsh.2.2.1,
      drest.2.2.2.2.1.trans bsh.2.2.2.2.1,
      drest.2.2.2.2.2.1.trans bsh.2.2.2.2.2.1,
      drest.2.2.2.2.2.2.trans bsh.2.2.2.2.2.2⟩
  refine Hs.last (emitSelectedSquare_run C edge G g B
    (fun i : Fin G=>bits.getD (k+i.val) false) hgG d dc ddG ddg ds' hW hindex hB hfit)
    (fun z ⟨zo,zsrc,zc,zfr⟩ n3 hn3=>?_)
  have zrc : z.rc=d.rc := congrArg (fun q=>q.2.2.1) zsrc
  have zsmall : (z.ip,z.ram,z.kin,z.kout,z.kc)=(d.ip,d.ram,d.kin,d.kout,d.kc) := by
    simp only [Prod.mk.injEq] at zsrc ⊢
    exact ⟨zsrc.1,zsrc.2.1,zsrc.2.2.2.1,zsrc.2.2.2.2.1,zsrc.2.2.2.2.2⟩
  refine ⟨⟨by simpa only [hdo] using zo,zsmall.trans ddsrc,by rw [zrc]; exact dr,zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  rw [brc] at hn2
  omega

end NearQuarticWires.StageCert.Tokens
