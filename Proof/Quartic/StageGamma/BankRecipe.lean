import Proof.Quartic.StageGamma.WriterCode
import Proof.Quartic.StageGamma.CompactRecipe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: a fixed
finite list of physical input-record writers. -/
def Writer.join : List Writer → Writer
  | [] => .literal []
  | first :: rest => .seq first (Writer.join rest)

/-- `cor:conditional`, paper/paper.tex: the finite
writer list prints its payloads in the exact kernel tape-index order. -/
theorem Writer.bits_join (ws : List Writer) (a : DS VV MM) :
    (Writer.join ws).bits a = ws.flatMap (fun w => w.bits a) := by
  induction ws <;> simp_all [join, bits]

/-- `cor:conditional`, paper/paper.tex: all source
registers of every fixed record are included in the physical interface. -/
theorem Writer.params_join (ws : List Writer) :
    (Writer.join ws).params = ws.flatMap Writer.params := by
  induction ws <;> simp_all [join, params]

/-- `cor:conditional`, paper/paper.tex: individually
safe finite record writers compose to one safe actual source producer. -/
theorem Writer.safe_join (ws : List Writer) :
    (Writer.join ws).Safe ↔ ∀ w ∈ ws, w.Safe := by
  induction ws <;> simp_all [join, Safe]

/-- `cor:conditional`, paper/paper.tex: the cached
primitive modulus has a binary variable outside every serializer scratch. -/
def gammaModulus : Fin VV := ⟨34, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the exact
unfixed seed-column count is retained outside serializer scratch. -/
def gammaRest : Fin VV := ⟨59, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the compact
31-port Gaussian bank has this fixed physical record recipe. -/
def bankPortRecipe (cons : Writer) : Fin 31 → Writer :=
  let ell := requestFieldRegister 0
  let plen := requestFieldRegister 3
  let pre := requestFieldRegister 4
  let zeroWord := (Writer.binaryWord ell vZ).framed
  ![.literal (List.replicate 8 true ++ [false]),
    .seq (.ruler ell [true]) (.literal [false]), zeroWord, zeroWord,
    .literal [], (Writer.binaryWord ell gammaModulus).framed, .literal [],
    zeroWord, zeroWord, .literal [], .literal [], .literal [], .literal [], .literal [],
    (Writer.binaryWord plen pre).framed, zeroWord, .literal [], .literal [], .literal [], .literal [],
    (Writer.binaryWord ell v1).framed, .literal [], cons, .literal [], .literal [], .literal [],
    .literal [], .literal [], .ruler gammaRest [true], .literal [false], .literal []]

/-- `cor:conditional`, paper/paper.tex: every actual
kernel port, including empty workspaces, is emitted as its own frame. -/
def bankRecipe (cons : Writer) : Writer :=
  Writer.join (List.ofFn fun i : Fin 31 => (bankPortRecipe cons i).framed)

/-- `cor:conditional`, paper/paper.tex: compact bank
serialization preserves all original fields and the cached modulus. -/
theorem bankRecipe_safe (cons : Writer) (hs : cons.Safe) : (bankRecipe cons).Safe := by
  rw [bankRecipe, Writer.safe_join]
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  rw [Writer.safe_framed]
  fin_cases i <;>
    simp [bankPortRecipe, Writer.Safe, Writer.safe_framed, Writer.binaryWord,
      requestFieldRegister, gammaModulus, gammaRest, writerScratch, binaryScratch,
      emitIndex, binaryIndex, binaryWork, binaryQuot, binaryRem, vJ, vZ, v1, hs]

/-- `cor:conditional`, paper/paper.tex: under the
decoded ORIGINAL fields, each physically printed port is the literal
already checked compact Gaussian port. -/
theorem bankPortRecipe_bits (cons : Writer) (a : DS VV MM)
    (ell plen pre modulus rest : ℕ)
    (hc : Cst a) (he : a.env (requestFieldRegister 0) = ell)
    (hl : a.env (requestFieldRegister 3) = plen)
    (hp : a.env (requestFieldRegister 4) = pre)
    (hm : a.env gammaModulus = modulus) (hr : a.env gammaRest = rest)
    (i : Fin 31) :
    (bankPortRecipe cons i).bits a = compactBank ell plen pre modulus rest (cons.bits a) i := by
  fin_cases i <;>
    simp [bankPortRecipe, compactBank, Writer.bits, Writer.bits_framed,
      Writer.bits_binaryWord, he, hl, hp, hm, hr, hc.z, hc.one,
      bitBlocks, List.replicate_succ]

/-- `cor:conditional`, paper/paper.tex: the complete
physical serialization equals the exact compact Gaussian request word. -/
theorem bankRecipe_bits (cons : Writer) (a : DS VV MM)
    (ell plen pre modulus rest : ℕ)
    (hc : Cst a) (he : a.env (requestFieldRegister 0) = ell)
    (hl : a.env (requestFieldRegister 3) = plen)
    (hp : a.env (requestFieldRegister 4) = pre)
    (hm : a.env gammaModulus = modulus) (hr : a.env gammaRest = rest) :
    (bankRecipe cons).bits a = rawInput (compactBank ell plen pre modulus rest (cons.bits a)) := by
  simp only [bankRecipe, Writer.bits_join, List.ofFn_eq_map, List.flatMap_map,
    Function.comp_def, Writer.bits_framed]
  simp only [rawInput, rawRecords, recordsWord, List.ofFn_eq_map, List.flatMap_map,
    Function.comp_def]
  apply congrArg (List.flatMap · (List.finRange 31))
  funext i
  rw [bankPortRecipe_bits cons a ell plen pre modulus rest hc he hl hp hm hr i]

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one actual serializer produces the entire Gaussian input,
preserving the ORIGINAL request and cached field source. -/
theorem bankRecipe_run (cons : Writer) (hs : cons.Safe) (C : Ctx) (a : DS VV MM)
    (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ (bankRecipe cons).params, a.env x < 2 ^ C.Wd)
    (hroom : a.kin.length + (bankRecipe cons).cost a ≤ C.Lk) :
    Hs C (bankRecipe cons).program a ((bankRecipe cons).cost a) (fun b =>
      b.kin = a.kin ++ (bankRecipe cons).bits a ∧
      NearCubicGates.Close.CounterMachine.CellTablesProg.SameN a b ∧ Cst b ∧
      Fr a b writerScratch) :=
  (bankRecipe cons).run (bankRecipe_safe cons hs) C a hc hW hfit hroom

end NearQuarticWires.StageGamma
