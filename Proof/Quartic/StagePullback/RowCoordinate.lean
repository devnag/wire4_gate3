import Proof.Quartic.StagePullback.NativeRoute
import Proof.Quartic.StageGamma.FixedRead

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

def fieldWidth : Fin VV := 35

def rowScratch : List (Fin VV) := StageGamma.fixedReadScratch SignedCoefficients.value ++
  Flips.scratch ++ SignedCoefficients.scratch ++ [Sides.result, vJ]

def retainedInputs : List (Fin VV) :=
  [21, 24, 27, 28, Flips.leftFlag, Flips.rightFlag, Flips.halfCount,
    MarkerCalls.originalCoordinate, Offsets.blockWidth, Digits.radix]

theorem inputs_of_equal {a b : DS VV MM} {q : PointRequest} {x : Fin q.parameters.n}
    (h : Flips.Inputs a q x) (hc : Cst b)
    (he : ∀ y ∈ retainedInputs, b.env y = a.env y) : Flips.Inputs b q x :=
  ⟨hc, (he _ (by decide)).trans h.blocks, (he _ (by decide)).trans h.translation,
    (he _ (by decide)).trans h.left, (he _ (by decide)).trans h.right,
    (he _ (by decide)).trans h.useLeft, (he _ (by decide)).trans h.useRight,
    (he _ (by decide)).trans h.half, (he _ (by decide)).trans h.coordinate,
    (he _ (by decide)).trans h.blockWidth, (he _ (by decide)).trans h.radix⟩

/-- `imp:pullback` and `lem:print`, paper/paper.tex: one original fixed signed coefficient is physically read,
flipped, included in the affine target, and routed to its native side. -/
def coordinateRowProgram : St VV MM :=
  .seq (StageGamma.fixedRead fieldWidth SignedCoefficients.value)
    (.seq Flips.program (.seq SignedCoefficients.program
      (.seq orientedSideProgram routeProgram)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the actual original-coordinate signed field produces one
native row record, using the canonical translation/errors and physically
computed side with the requested transpose. The target subtracts exactly
the original flipped coefficient. -/
theorem coordinateRowProgram_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (z : ℤ) (transpose : Bool) (Lin : ℕ) (rest : List Bool)
    (hi : Flips.Inputs a q x) (hwidth : q.parameters.n + 4 ≤ C.Wd)
    (hfield : a.env fieldWidth = Lin) (hfieldWidth : Lin + 1 ≤ C.Wd)
    (hz : SInt.encS z < 2 ^ Lin)
    (hin : C.inp.drop a.ip = binary Lin (SInt.encS z) ++ rest)
    (hleft : a.env Sides.leftEnd = q.parameters.r / 2 * q.parameters.b)
    (hblock : a.env Sides.blockedEnd = q.parameters.r * q.parameters.b)
    (hfree : a.env Sides.freeLeftEnd =
      q.parameters.r * q.parameters.b + (q.parameters.n - q.parameters.r * q.parameters.b + 1) / 2)
    (htranspose : a.env transposeFlag = transpose.toNat)
    (hpfit : a.env SignedCoefficients.positive + z.natAbs < 2 ^ C.Wd)
    (hnfit : a.env SignedCoefficients.negative + z.natAbs < 2 ^ C.Wd)
    (hlstore : a.rc leftStore ≤ (a.ram leftStore).length)
    (hrstore : a.rc rightStore ≤ (a.ram rightStore).length) :
    Hs C coordinateRowProgram a (10 * Lin + 21 * (x.val / q.parameters.b) + 200) (fun b =>
      b.env SignedCoefficients.value = SInt.encS (if q.flip x then -z else z) ∧
      (b.env SignedCoefficients.positive : ℤ) - b.env SignedCoefficients.negative =
        (a.env SignedCoefficients.positive : ℤ) - a.env SignedCoefficients.negative -
          (if q.flip x then z else 0) ∧
      b.env SignedCoefficients.positive + b.env SignedCoefficients.negative =
        a.env SignedCoefficients.positive + a.env SignedCoefficients.negative +
          (if q.flip x then z.natAbs else 0) ∧
      b.ip = a.ip + Lin ∧ b.out = a.out ∧
      b.ram = Function.update a.ram
        (if xor (q.parameters.centerSide x) transpose then leftStore else rightStore)
        (putAt (a.ram (if xor (q.parameters.centerSide x) transpose then leftStore else rightStore))
          (a.rc (if xor (q.parameters.centerSide x) transpose then leftStore else rightStore))
          (SInt.encS (if q.flip x then -z else z))) ∧
      b.rc = Function.update a.rc
        (if xor (q.parameters.centerSide x) transpose then leftStore else rightStore)
        (a.rc (if xor (q.parameters.centerSide x) transpose then leftStore else rightStore) + 1) ∧
      Cst b ∧ Fr a b rowScratch) := by
  have hfit : SInt.encS z + 1 < 2 ^ C.Wd := by
    have hp : 2 ^ Lin < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  unfold coordinateRowProgram
  refine Hx.hs (Hs.then (StageGamma.fixedRead_run C fieldWidth SignedCoefficients.value
    (by decide) (by decide) a hi.constants Lin (SInt.encS z) rest hfield hfieldWidth hin)
    (fun b ⟨hbv, _, hbip, hbrest, hbc, hbfr⟩ n1 hn1 => ?_))
  have hib : Flips.Inputs b q x := inputs_of_equal hi hbc (fun y hy => hbfr y
    ((show ∀ y ∈ retainedInputs, y ∉ StageGamma.fixedReadScratch SignedCoefficients.value by decide) y hy))
  have hbval : b.env SignedCoefficients.value = SInt.encS z := by
    simpa only [Nat.mod_eq_of_lt hz] using hbv
  have hbram : b.ram = a.ram := congrArg (fun v => v.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun v => v.2.2.1) hbrest
  have hbout : b.out = a.out := congrArg Prod.fst hbrest
  have hfba : Fr a b rowScratch := hbfr.weaken (by
    intro y hy
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hy)))
  refine Hs.then (Flips.program_run C b q x hib hwidth)
    (fun c ⟨hcv, hcsh, hcfr⟩ n2 hn2 => ?_)
  have hic := hib.frame hcfr
  have hcv0 : c.env SignedCoefficients.value = SInt.encS z := (hcfr _ (by decide)).trans hbval
  have hcp : c.env SignedCoefficients.positive = a.env SignedCoefficients.positive :=
    (hcfr _ (by decide)).trans (hbfr _ (by decide))
  have hcn : c.env SignedCoefficients.negative = a.env SignedCoefficients.negative :=
    (hcfr _ (by decide)).trans (hbfr _ (by decide))
  have hfc : Fr b c rowScratch := hcfr.weaken (by
    intro y hy
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hy)))
  refine Hs.then (SignedCoefficients.program_run_mass C c hic.constants z (q.flip x) hcv0 hcv
    (by omega) hfit (by rw [hcp]; exact hpfit) (by rw [hcn]; exact hnfit))
    (fun d ⟨hdv, hdiff, hmass, hdsh, hdfr⟩ n3 hn3 => ?_)
  have hdc : Cst d := hic.constants.of_fr hdfr (by decide)
  have hfd : Fr c d rowScratch := hdfr.weaken (by
    intro y hy
    exact List.mem_append_left _ (List.mem_append_right _ hy))
  have hretain (y : Fin VV) (hy1 : y ∉ StageGamma.fixedReadScratch SignedCoefficients.value)
      (hy2 : y ∉ Flips.scratch) (hy3 : y ∉ SignedCoefficients.scratch) : d.env y = a.env y :=
    (hdfr y hy3).trans ((hcfr y hy2).trans (hbfr y hy1))
  refine Hs.then (orientedSideProgram_run C d q.parameters x transpose hdc
    ((hretain _ (by decide) (by decide) (by decide)).trans hi.coordinate)
    ((hretain _ (by decide) (by decide) (by decide)).trans hleft)
    ((hretain _ (by decide) (by decide) (by decide)).trans hblock)
    ((hretain _ (by decide) (by decide) (by decide)).trans hfree)
    ((hretain _ (by decide) (by decide) (by decide)).trans htranspose))
    (fun e ⟨hev, hesh, hefr⟩ n4 hn4 => ?_)
  have hec : Cst e := hdc.of_fr hefr (by decide)
  have heval : e.env SignedCoefficients.value = SInt.encS (if q.flip x then -z else z) :=
    (hefr _ (by decide)).trans hdv
  have hediff : (e.env SignedCoefficients.positive : ℤ) - e.env SignedCoefficients.negative =
      (a.env SignedCoefficients.positive : ℤ) - a.env SignedCoefficients.negative -
        (if q.flip x then z else 0) := by
    rw [hefr _ (by decide : SignedCoefficients.positive ∉ [Sides.result, vJ]),
      hefr _ (by decide : SignedCoefficients.negative ∉ [Sides.result, vJ]), hdiff, hcp, hcn]
  have hemass : e.env SignedCoefficients.positive + e.env SignedCoefficients.negative =
      a.env SignedCoefficients.positive + a.env SignedCoefficients.negative +
        (if q.flip x then z.natAbs else 0) := by
    rw [hefr _ (by decide : SignedCoefficients.positive ∉ [Sides.result, vJ]),
      hefr _ (by decide : SignedCoefficients.negative ∉ [Sides.result, vJ]), hmass, hcp, hcn]
  have hs := Same.of_sh (hesh.trans (hdsh.trans hcsh))
  have heram : e.ram = a.ram := hs.ram.trans hbram
  have herc : e.rc = a.rc := hs.rc.trans hbrc
  have heip : e.ip = a.ip + Lin := hs.ip.trans hbip
  have heout : e.out = a.out := hs.out.trans hbout
  have hfe : Fr d e rowScratch := hefr.weaken (by intro y hy; exact List.mem_append_right _ hy)
  refine Hs.last (routeProgram_run C e hec _ hev
    (by rw [herc, heram]; exact hlstore) (by rw [herc, heram]; exact hrstore)) ?_
  rintro f hroute n5 hn5
  subst hroute
  have hall : Fr a e rowScratch := hfba.trans (hfc.trans (hfd.trans hfe))
  have hputc (m : Fin MM) : Cst (e.put m (e.env SignedCoefficients.value)) :=
    ⟨hec.z, hec.one, hec.two⟩
  cases hside : xor (q.parameters.centerSide x) transpose <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    exact ⟨⟨heval, hediff, hemass, heip, heout, by simp only [DS.put, heram, herc, heval],
      by simp only [DS.put, herc], hputc _, hall⟩, by omega⟩

end NearQuarticWires.StagePullback.NativeRows
