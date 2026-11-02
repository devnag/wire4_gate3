import Proof.Quartic.StageMain.RegisterPrint
import Proof.Quartic.StageMain.ParameterGet
import Proof.Quartic.StageLift.MemorySource

/-!
# Printing fields from the retained call and parameter records

Step 4 of `sec:algorithm`, paper/paper.tex,
passes the selected parameters and arity to Step 5. These programs
read the actual retained records and print their raw natural words;
every source rewind and binary field operation is charged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

def sourcePrintScratch : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, c0] ++ emitNatT

def printParameter (i : Fin 46) : St VV MM := .seq (readParameter i t3) emitNatO

theorem printParameter_run (C : Ctx) (p : Cells.Parameters) (i : Fin 46)
    (a : DS VV MM) (hc : Cst a) (hstore : a.ram parameterStore = parameterScalars p)
    (hindex : i.val < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength ((parameterScalars p).getD i.val 0) + 2 < 2 ^ C.Wd) :
    Hs C (printParameter i) a
      (a.rc parameterStore + 7 * i.val + 40 * natBitLength ((parameterScalars p).getD i.val 0) + 54)
      (fun b => b.out = a.out ++ natWord ((parameterScalars p).getD i.val 0) ∧
        (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
        b.rc parameterStore = i.val + 1 ∧
        (∀ store, store ≠ parameterStore → b.rc store = a.rc store) ∧
        Cst b ∧ Fr a b sourcePrintScratch) := by
  unfold printParameter
  refine (Hs.seq (t2 := 40 * natBitLength ((parameterScalars p).getD i.val 0) + 40)
    (readParameter_run C p i t3 a hc hstore hindex (by decide)) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbv, hbcursor, hbrest, hbc, hbfr⟩
  have h := emitNatO_spec (C := C) b hbc hW (by rw [hbv]; exact hfit)
  rw [hbv] at h
  refine h.mono le_rfl ?_
  rintro d ⟨hdout, hdrest, hdc, hdfr⟩
  rcases (by simpa only [Prod.mk.injEq] using hdrest) with ⟨hdi, hdram, hdrc, hdkin, hdkout, hdkc⟩
  rcases (by simpa only [parameterRest, Prod.mk.injEq] using hbrest) with
    ⟨hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc⟩
  refine ⟨by rw [hdout, hbo], by rw [hdi, hdram, hdkin, hdkout, hdkc, hbi, hbram, hbkin, hbkout, hbkc],
    by rw [hdrc, hbcursor], ?_, hdc, ?_⟩
  · intro store hs
    have he := congrFun hbrc store
    simp only [Function.update_of_ne hs] at he
    exact (congrFun hdrc store).trans he
  · exact (hbfr.weaken (by
      intro x hx; simp only [sourcePrintScratch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)).trans
        (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))

def printArity : St VV MM := .seq (.op (.rwM callStore))
  (.seq (readMemoryNatural callStore) emitNatO)

theorem printArity_run (C : Ctx) (c : Call) (a : DS VV MM) (hc : Cst a)
    (hstore : a.ram callStore = (callWord c).map Bool.toNat)
    (hW : 2 ≤ C.Wd) (hwidth : natBitLength c.n + 2 ≤ C.Wd)
    (hfit : natBitLength c.n + 2 < 2 ^ C.Wd) :
    Hs C printArity a (a.rc callStore + 70 * natBitLength c.n + 73) (fun b =>
      b.out = a.out ++ natWord c.n ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      b.rc callStore = (natWord c.n).length ∧
      (∀ store, store ≠ callStore → b.rc store = a.rc store) ∧
      Cst b ∧ Fr a b sourcePrintScratch) := by
  let d : DS VV MM := { a with rc := Function.update a.rc callStore 0 }
  have hd : Ex C (.op (.rwM callStore)) a d (a.rc callStore + 1) := Ex.op (OpEx.rwM callStore a)
  have hdc : Cst d := ⟨hc.z, hc.one, hc.two⟩
  have hread := readMemoryNatural_spec C callStore (callWord c) d hdc hstore c.n
    (natWord (kindTag c.kind) ++ circuitWord c.first ++ circuitWord c.second ++
      listWord natWord c.parity ++ ratWord c.radius)
    (by simp [d, callWord, List.append_assoc]) hwidth
  obtain ⟨b, n, hbe, hbn, hbv, _hbwidth, hbcursor, hbrest, hbfr⟩ := hread
  have hbc := cst_fr hdc hbfr
  have hemit := emitNatO_spec (C := C) b hbc hW (by rw [hbv]; exact hfit)
  rw [hbv] at hemit
  obtain ⟨e, k, he, hk, heout, herest, hec, hefr⟩ := hemit
  refine ⟨e, (a.rc callStore + 1) + (n + k + 1) + 1, Ex.seq hd (Ex.seq hbe he), by omega, ?_⟩
  rcases (by simpa only [Prod.mk.injEq] using herest) with ⟨hei, heram, herc, hekin, hekout, hekc⟩
  rcases (by simpa only [memorySourceRest, Prod.mk.injEq] using hbrest) with
    ⟨hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc⟩
  refine ⟨by rw [heout, hbo], by rw [hei, heram, hekin, hekout, hekc, hbi, hbram, hbkin, hbkout, hbkc],
    by rw [herc, hbcursor]; simp [d], ?_, hec, ?_⟩
  · intro store hs
    have heq := congrFun hbrc store
    simp only [d, Function.update_of_ne hs] at heq
    exact (congrFun herc store).trans heq
  · exact (hbfr.weaken (by
      intro x hx; simp only [sourcePrintScratch, rdNatT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)).trans
        (hefr.weaken (fun _ hx => List.mem_append_right _ hx))

end NearQuarticWires.StageMain.Controller
