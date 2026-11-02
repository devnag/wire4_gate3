import Proof.Quartic.StageNativeKids.BankBody
import Proof.Quartic.StageNativeKids.AcquiredLoad
import Proof.Quartic.Control.Frame

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the
acquired source is loaded on fourteen tapes, disjoint from the three
genuinely fresh selected-source, affine-header and tagged-output tapes. -/
def bankLoadMap : Fin 14 ↪ Fin 17 :=
  ⟨fun j => j.castAdd 3, by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 17 => k.val) h⟩

/-- `prop:time`, paper/paper.tex: the
cold bank selector uses only the actual acquired-record loader's blank
reset ruler; its selected sources and output initially contain no data. -/
def bankLens (r : NativeKidsRequest) (i : Fin 17) : ℕ :=
  if i.val = 13 then r.acquiredLoadCapacity else 0

/-- `lem:print`, paper/paper.tex: the
cold original-bank selector starts with only its actual acquired word
and the paid blank loader workspace, never decoded occurrence metadata. -/
def bankStart (r : NativeKidsRequest) : WState 16 16 :=
  idealStart 16 16 r.acquiredWord (bankLens r)

/-- `lem:print`, paper/paper.tex: actual
acquisition bytes are first decoded by the real existing source loader,
then selected and formatted by the original-bank source computation. -/
noncomputable def bankProgram : WMX 16 16 :=
  .seq (.mach Top.loadM bankLoadMap) bankBodyProgram

/-- `prop:time`, paper/paper.tex: both
the acquired-record loader and actual original-bank source computation
are paid, with their one real composition transition. -/
def bankClock (r : NativeKidsRequest) : ℕ :=
  r.acquiredLoadCost + bankBodyClock r + 1

/-- `lem:print`, paper/paper.tex: the
actual cold bank-loader input is exactly the acquired eleven-field word
and its reset ruler, with no decoded fields initially installed. -/
theorem bankStart_loader (r : NativeKidsRequest) :
    (fun j : Fin 14 => (bankStart r).st (bankLoadMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.acquiredWord, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.acquiredLoadCapacity false) := by
  funext j
  refine Fin.addCases (m := 13) (n := 1) (fun k => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    fin_cases k <;> simp [bankStart, idealStart, bankLoadMap, bankLens]
  · fin_cases k
    rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: an entirely cold acquired source produces
the exact tagged actual-pool input. Original occurrence, bank, selected
source and affine header are all physically computed from that source. -/
theorem bank_run (r : NativeKidsRequest) :
    ∃ τ, WXExec (bankBodyCapacity r) bankProgram (bankStart r) τ (bankClock r) ∧
      τ.st 16 = frame r.bankWord := by
  obtain ⟨loaded, eload, hl, hh, hv, _hc⟩ := acquiredLoad_run (bankBodyCapacity r) r
    bankLoadMap bankLoadMap.injective (bankStart r) (bankStart_loader r) (fun _ => rfl)
  have hoff (i : Fin 17) (hi : 14 ≤ i.val) :
      loaded.st i = [] ∧ loaded.sh i = 0 := by
    have h := NearQuarticWires.Control.WXExec.avoids eload (i := i) (by
      intro j he
      have he' := congrArg Fin.val he
      change j.val = i.val at he'
      have hj := j.isLt
      omega)
    have h0 : i ≠ 0 := by intro he; have hh := congrArg Fin.val he; simp at hh; omega
    have h13 : i.val ≠ 13 := by omega
    exact ⟨h.1.trans (by simp [bankStart, idealStart, bankLens, h0, h13]), h.2⟩
  obtain ⟨τ, ebody, hout⟩ := bankBody_run r loaded
    (by simpa [bankLoadMap, NativeKidsRequest.acquiredLoaded,
        NativeKidsRequest.acquiredFields, NativeKidsRequest.sourceFields] using hl 2)
    (by simpa [bankLoadMap, NativeKidsRequest.acquiredLoaded,
        NativeKidsRequest.acquiredFields, NativeKidsRequest.sourceFields] using hl 4)
    (by simpa [bankLoadMap, NativeKidsRequest.acquiredLoaded,
        NativeKidsRequest.acquiredFields] using hl 7)
    (by simpa [bankLoadMap, NativeKidsRequest.acquiredLoaded,
        NativeKidsRequest.acquiredFields, NativeKidsRequest.sourceFields] using hl 6)
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> exact (hoff _ (by decide)).1)
    (by intro i
        by_cases hi : i.val < 14
        · simpa [bankLoadMap] using hh ⟨i.val, hi⟩
        · exact (hoff i (by omega)).2)
    (by intro i; rw [hv]; rfl)
  exact ⟨τ, (eload.seq ebody).mono (by unfold bankClock; omega), hout⟩

/-- `prop:time`, paper/paper.tex: the
ordinary cold bank-selector budget pays the complete loaded computation
and its final ordinary tape and register return. -/
def bankBudget (r : NativeKidsRequest) : ℕ := 2 * bankClock r + 2

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual acquired word alone computes
one exact cold tagged pool request, with no decoded occurrence, selected
bank, selected gate, child row or count supplied by the caller. -/
noncomputable def bankWordFunction :
    WordFunction NativeKidsRequest (fun r => r.acquiredWord)
      (fun r => frame r.bankWord) bankBudget :=
  wordFunction_of_ideal bankProgram (16 : Fin 17) (by decide) bankBodyCapacity
    bankLens bankClock (fun _ => le_rfl) (by
      intro r
      exact ⟨by rfl, bank_run r⟩)

end NearQuarticWires.StageNativeKids
