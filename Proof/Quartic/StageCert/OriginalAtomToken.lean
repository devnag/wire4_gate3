import Proof.Quartic.StageCert.AtomCodes
import Proof.Gates.Cells.Load2

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: each fixed original
offset role is combined with the physical occurrence stride before emitting
its literal atom token. -/
def emitOriginalAtom (role : ℕ) : St VV MM :=
  .seq (setK atomRole role) (.seq computeAtomIndex (emitAtom atomValue))

/-- `lem:print` and `prop:time`, paper/paper.tex: exact original-pool atom labels are computed and serialized by
one concrete binary program, retaining every other source field and store. -/
theorem emitOriginalAtom_run (C : Ctx) (role G g : ℕ) (a : DS VV MM) (hc : Cst a)
    (hG : a.env atomCount=G) (hg : a.env atomOccurrence=g)
    (hW : 2≤C.Wd) (hr : role<2^C.Wd) (hindex : role*G+g<2^C.Wd)
    (hbits : natBitLength (role*G+g)+2<2^C.Wd) :
    Hs C (emitOriginalAtom role) a (2*role+40*natBitLength (role*G+g)+60) (fun z=>
      z.out=a.out++tokWord (.var (role*G+g)) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z (atomRole::atomValue::StageLift.tokenScratch)) := by
  unfold emitOriginalAtom
  apply Hx.hs
  refine Hs.then (setK_spec atomRole (by decide) role a hr)
    (fun b ⟨brole,bsh,bfr⟩ n1 hn1=>?_)
  have bc : Cst b := Cst.of_fr hc bfr (by decide)
  have bG : b.env atomCount=G := (bfr _ (by decide)).trans hG
  have bg : b.env atomOccurrence=g := (bfr _ (by decide)).trans hg
  simp only [DS.sh,Prod.mk.injEq] at bsh
  obtain ⟨bip,bo,bram,brc,bkin,bkout,bkc⟩ := bsh
  refine Hs.then (computeAtomIndex_run C b bc (by rw [brole,bG,bg]; exact hindex))
    (fun d ⟨dv,dr,dc,df⟩ n2 hn2=>?_)
  have dindex : d.env atomValue=role*G+g := by simpa only [brole,bG,bg] using dv
  refine Hs.last (emitAtom_run C atomValue (by decide) (by decide) d dc hW
    (by rw [dindex]; exact hbits))
    (fun z ⟨zo,zr,zc,zf⟩ n3 hn3=>?_)
  have dout : d.out=a.out := by
    have hd : d.out=b.out := congrArg (fun t=>t.2.2.2.2.2.2) dr
    exact hd.trans bo
  have dext : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq] at dr
    obtain ⟨dip,dram,drc,dkin,dkout,dkc,_⟩ := dr
    simp only [Prod.mk.injEq]
    exact ⟨dip.trans bip,dram.trans bram,drc.trans brc,dkin.trans bkin,dkout.trans bkout,dkc.trans bkc⟩
  refine ⟨⟨by simpa only [dindex,dout] using zo,zr.trans dext,zc,?_⟩,?_⟩
  · exact (bfr.weaken (by simp [StageLift.tokenScratch])).trans
      ((df.weaken (by simp)).trans
        (zf.weaken (by intro y hy; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))))
  · rw [dindex] at hn3
    omega

end NearQuarticWires.StageCert.Tokens
