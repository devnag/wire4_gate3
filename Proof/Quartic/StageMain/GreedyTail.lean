import Proof.Quartic.StageMain.SeedRead

/-!
# Consistency and chosen seed at the end of the greedy stage

Steps 3–4 of `sec:algorithm`, paper/paper.tex:
the actual consistency field and framed seed are decoded after the
certificate bitmap, preserving every retained call and parameter field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells
open Algorithm.CellCall (prefixValue)

def consistency : Fin VV := 109

def tailScratch : List (Fin VV) := consistency :: (rdNatT ++ seedReadScratch)

def readGreedyTail : St VV MM := .seq rdNatI
  (.seq (.op (.copy consistency t3)) readSeed)

theorem readGreedyTail_run (C : Ctx) (flag : Bool) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = bitWord flag ++ frame bits ++ rest)
    (hW : 3 ≤ C.Wd) (hseed : bits.length < C.Wd) :
    Hs C readGreedyTail a (11 * bits.length + 80) (fun b =>
      b.env consistency = flag.toNat ∧ b.env seed = prefixValue bits ∧
      b.env seedPower = 2 ^ bits.length ∧
      b.ip = a.ip + (bitWord flag).length + (frame bits).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b tailScratch) := by
  have hword : bitWord flag = NearCubicWires.RepairRepresentation.natWord flag.toNat := by
    cases flag <;> rfl
  rw [hword] at hin ⊢
  have hbit : natBitLength flag.toNat = 1 := by
    cases flag <;> rfl
  have hread := rdNatI_spec (C := C) a hc flag.toNat (frame bits ++ rest)
    (by simpa only [List.append_assoc] using hin)
    (by rw [hbit]; exact hW)
  rw [hbit] at hread
  unfold readGreedyTail
  refine (Hs.seq (t2 := 11 * bits.length + 10) hread ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbval, _hblen, hbip, hbrest, hbfr⟩
  have hbfr' : Fr a b tailScratch := hbfr.weaken (by
    intro y hy
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hy))
  have hbc := Cst.of_fr hc hbfr' (by decide)
  refine (Hs.seq (t2 := 11 * bits.length + 8) (hs_copy C consistency t3 b (by decide)) ?_).mono
    (by omega) (fun _ h => h)
  rintro d rfl
  have hf : Fr a (b.set consistency (b.env t3)) tailScratch :=
    hbfr'.trans (Fr.set b _ (by simp [tailScratch]))
  have hdc := Cst.of_fr hc hf (by decide)
  have hinput : C.inp.drop (b.set consistency (b.env t3)).ip = frame bits ++ rest := by
    rw [DS.set_ip, hbip, ← List.drop_drop, hin]
    simp only [List.append_assoc, List.drop_left]
  refine (readSeed_run C bits rest _ hdc hinput hseed).mono le_rfl ?_
  rintro e ⟨_hez, heip, heseed, hepow, herest, hec, hefr⟩
  refine ⟨?_, heseed, hepow, ?_, herest.trans hbrest, hec, ?_⟩
  · rw [hefr consistency (by decide), DS.set_env_self, hbval]
  · rw [heip, DS.set_ip, hbip]
  · exact hf.trans (hefr.weaken (by
      intro y hy
      exact List.mem_cons_of_mem _ (List.mem_append_right _ hy)))

end NearQuarticWires.StageMain.Controller
