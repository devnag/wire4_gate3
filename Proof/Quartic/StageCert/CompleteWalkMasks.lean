import Proof.Quartic.StageCert.WalkMaskProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the full literal source
cost for one selected tuple mask, including every bounded tuple. -/
def maskSourceCost (G k X B Bn sourceLength : ℕ) : ℕ :=
  (X+1)*((G^X*(X*((sourceLength+5*(k+G)+160*B+530)+4)+50*X+200+20)+
    30*X+40*Bn+400)+20)+200

/-- `lem:print` and `prop:time`, paper/paper.tex: the original fixed m=4 walk has exactly eight masks. -/
def completeMaskSourceCost (G k X B Bn sourceLength : ℕ) : ℕ :=
  8*(maskSourceCost G k X B Bn sourceLength+20)+20

/-- `lem:print`, paper/paper.tex: complete literal
tuple-mask product for all eight original walk edges. -/
def completeWalkMaskFormula (G tau X k : ℕ) (bits : List Bool)
    (structural : Fin 8→Bool) : Formula (17*G) :=
  Mask.formulaListProd (selectedWalkMasks G tau k X bits structural (List.ofFn fun e : Fin 8=>e))

/-- `lem:print`, paper/paper.tex: physically read
and emit the complete original fixed eight-edge mask product. -/
def emitCompleteWalkMasks (store : Fin MM) : St VV MM :=
  emitWalkMaskProduct store (List.ofFn fun edge : Fin 8=>edge)

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal eight-bit mask source is consumed and its
complete integer polynomial is physically emitted, on all columns. -/
theorem emitCompleteWalkMasks_run (C : Ctx) (store : Fin MM)
    (G tau X k B Bn : ℕ) (bits : List Bool) (structural : Fin 8→Bool)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hin : C.inp.drop a.ip=List.ofFn structural++rest)
    (hb : a.env atomCount=G) (htau : a.env newtonTau=tau)
    (hlimit : a.env maskLimit=X+1) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^X≤2^C.Wd) (hwidth : 2*X+2≤C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤B)
    (hBit : B+2<2^C.Wd)
    (hBn : ∀ degree≤X,natBitLength (Mask.newtonCoeff tau degree).natAbs≤Bn)
    (hNBit : Bn+2<2^C.Wd) :
    Hs C (emitCompleteWalkMasks store) a (completeMaskSourceCost G k X B Bn bits.length) (fun z=>
      z.out=a.out++(NearCubicGates.Close.Interfaces.Formats.toks
        (completeWalkMaskFormula G tau X k bits structural)).flatMap
          NearCubicGates.Close.Interfaces.Formats.tokWord ∧
      z.ip=a.ip+8 ∧ (z.ram,z.kin,z.kout,z.kc)=(a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (maskStructural::newtonIndex::maskDegreeScratch)) := by
  have hi : C.inp.drop a.ip=
      (List.ofFn fun e : Fin 8=>e).map structural++rest := by
    simpa only [List.map_ofFn,Function.comp_def] using hin
  simpa only [emitCompleteWalkMasks,completeMaskSourceCost,maskSourceCost,
    completeWalkMaskFormula,List.length_ofFn] using
    (emitWalkMaskProduct_run C store G tau X k B Bn bits structural
      (List.ofFn fun edge : Fin 8=>edge) rest a hc hG hi hb htau hlimit hk hram hcursor
      hbits haddress hfit hwidth hW hindex hB hBit hBn hNBit)

end NearQuarticWires.StageCert.Tokens
