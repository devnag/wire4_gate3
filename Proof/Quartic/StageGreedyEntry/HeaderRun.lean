import Proof.Quartic.StageGamma.BankLoad
import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Wire_3_5.PrimAsmWriteNat

/-!
# The common header from the formatted entry: the program and its run

Paper: `lem:print`, paper/paper.tex.

The input stream holds `frame (frame w)`, where `w` is the eleven-field record of the formatted entry: its field 1
is `frame` of the base header values `n, x₁, x₂, r, b, s, t` (each a `natWord`) and its field 4 is `natWord W`.
`hdrP` unframes the input twice, loads fields 0–4 onto their own streams, reads `n, x₁, x₂, r, b, s` (marked) and
`W` (plain), and writes `natWord n, natWord r, natWord b, natWord s, natWord (W + 1)` with an end mark on the output
stream. `hdr_run`: the output stream ends holding `frame` of these five fields, within `hdrCost`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec stp)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairRepresentation (natWord)
open NearQuarticWires.StageGamma

/-! ## Streams and registers -/

/-- The streams: the input, the two unframed copies, the loaded fields 0, 1, 2, 3, 4, the output. -/
def hdIN : Fin 9 := 0
def hdS1 : Fin 9 := 1
def hdS2 : Fin 9 := 2
def hdJ0 : Fin 9 := 3
def hdH : Fin 9 := 4
def hdJ2 : Fin 9 := 5
def hdJ3 : Fin 9 := 6
def hdWS : Fin 9 := 7
def hdOUT : Fin 9 := 8

/-- The registers: the loading counter, the scratch of `readNatM`, the values read, the output counter. -/
def hdOP : Fin 18 := 0
def hdF : Fin 18 := 1
def hdC : Fin 18 := 2
def hdP : Fin 18 := 3
def hdT : Fin 18 := 4
def hdN : Fin 18 := 5
def hdJ : Fin 18 := 6
def hdR : Fin 18 := 7
def hdB : Fin 18 := 8
def hdS : Fin 18 := 9
def hdW : Fin 18 := 10
def hdO : Fin 18 := 17

/-- The registers of one `writeNatM`: the value `v`, the scratch `11–16`, the output counter. -/
def hdWR (v : Fin 18) (h : Function.Injective ![v, 11, 12, 13, 14, 15, 16, 17]) : Fin 8 ↪ Fin 18 := ⟨_, h⟩

def hdwN : Fin 8 ↪ Fin 18 := hdWR hdN (by decide)
def hdwR : Fin 8 ↪ Fin 18 := hdWR hdR (by decide)
def hdwB : Fin 8 ↪ Fin 18 := hdWR hdB (by decide)
def hdwS : Fin 8 ↪ Fin 18 := hdWR hdS (by decide)
def hdwW : Fin 8 ↪ Fin 18 := hdWR hdW (by decide)

/-- One read of a `natWord` into `v`. -/
noncomputable def hdRd (ε : Bool) (i : Fin 9) (v : Fin 18) : WM 8 18 := readNatM ε i hdF hdC v hdP hdT

/-- **The header program.** -/
noncomputable def hdrP : WM 8 18 :=
  .seq (unframeRecord hdIN hdS1 hdOP) (.seq (unframeRecord hdS1 hdS2 hdOP)
  (.seq (loadTapeSlots hdS2 hdOP [hdJ0, hdH, hdJ2, hdJ3, hdWS])
  (.seq (hdRd true hdH hdN) (.seq (hdRd true hdH hdJ) (.seq (hdRd true hdH hdJ) (.seq (hdRd true hdH hdR)
  (.seq (hdRd true hdH hdB) (.seq (hdRd true hdH hdS) (.seq (hdRd false hdWS hdW) (.seq (.inc hdW)
  (.seq (writeNatM hdOUT hdwN) (.seq (writeNatM hdOUT hdwR) (.seq (writeNatM hdOUT hdwB) (.seq (writeNatM hdOUT hdwS)
  (.seq (writeNatM hdOUT hdwW) (emitC hdOUT hdO false))))))))))))))))

/-! ## Costs -/

/-- The cost of one read. -/
def hdRdCost (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

/-- The cost of one write. -/
def hdWrCost (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200)

/-- The cost of the header program on a record of length `L`. -/
def hdrCost (L n x1 x2 r b s W : ℕ) : ℕ :=
  (23 * (2 * L + 1) + 5) + (23 * L + 5) + (23 * L + 1) + hdRdCost n + hdRdCost x1 + hdRdCost x2 +
    hdRdCost r + hdRdCost b + hdRdCost s + hdRdCost W + 3 + hdWrCost n + hdWrCost r + hdWrCost b + hdWrCost s +
    hdWrCost (W + 1) + 7 + 16

theorem hd_two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hx)
    rw [pow_succ]; omega

theorem hd_nbl_le_self (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
  omega

/-! ## The run -/

/-- The state before the program: the input stream holds `frame u`, everything else is empty or `0`. -/
def hdStart (u : List Bool) : WState 8 18 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame u else List.replicate 0 false, fun _ => 0, false⟩

theorem hd_loadedRecords_val (src : Fin 9) (σ : WState 8 18) (records : TapeRecords 8) :
    (loadedRecords src σ records).val = σ.val := by
  induction records generalizing σ with
  | nil => rfl
  | cons r rs ih => simp only [loadedRecords]; rw [ih]; rfl

theorem hd_frame_eq (l : List Bool) : frame l = marks l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame, marks, ih]

theorem hd_natWord_length (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 :=
  NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length v

/-- A marked read of `natWord x` on `hdH`, after the marked words `us`. -/
theorem hdRdM (cap : ℕ) (v : Fin 18) (h1 : hdF ≠ v) (h2 : hdC ≠ v) (h3 : hdP ≠ v) (h4 : v ≠ hdT) (x : ℕ)
    (us rest : List Bool) (σ : WState 8 18) (hst : σ.st hdH = marks us ++ marks (natWord x) ++ rest)
    (hsh : σ.sh hdH = 2 * us.length) (hf : σ.val hdF = 0) (hc : σ.val hdC = 0) (hp : σ.val hdP = 0)
    (ht : σ.val hdT = 0) (hcap : σ.val v + 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (hdRd true hdH v) σ ((σ.seth hdH (2 * (us ++ natWord x).length)).setv v (σ.val v + x)) (hdRdCost x) := by
  have e := readNatM_spec cap true hdH hdF hdC v hdP hdT (by decide) h1 (by decide) (by decide) h2 (by decide)
    (by decide) h3 (by decide) h4 x (marks us) rest σ (by simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hst)
    (by rw [hsh, Streaming.marks_length]) hf hc hp ht hcap
  refine WExec.cast cap e ?_ (le_refl _)
  congr 2
  simp [stp, Streaming.marks_length, List.length_append]; ring

theorem hd_appendO_ho (σ : WState 8 18) (u : List Bool) (h : σ.sh hdOUT = (σ.st hdOUT).length) :
    (appendO σ hdOUT hdO u).sh hdOUT = ((appendO σ hdOUT hdO u).st hdOUT).length := by
  simp [appendO, h]

theorem hd_appendO_val_ne (σ : WState 8 18) (u : List Bool) (x : Fin 18) (hx : x ≠ hdO) :
    (appendO σ hdOUT hdO u).val x = σ.val x := by
  simp [appendO, Function.update_of_ne hx]

theorem hd_appendO_val_O (σ : WState 8 18) (u : List Bool) :
    (appendO σ hdOUT hdO u).val hdO = σ.val hdO + u.length := by
  simp [appendO]

theorem hd_appendO_st_O (σ : WState 8 18) (u : List Bool) :
    (appendO σ hdOUT hdO u).st hdOUT = σ.st hdOUT ++ u := by
  simp [appendO]

theorem ne_hdO (x : Fin 18) (hx : x.val ≤ 16) : x ≠ hdO := fun h => by subst h; simp [hdO] at hx

/-- One write of `natWord (σ.val v)` on the output stream. -/
theorem hdWrStep (cap : ℕ) (v : Fin 18) (h : Function.Injective ![v, 11, 12, 13, 14, 15, 16, 17]) (σ : WState 8 18)
    (hz : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ.val x = 0) (ho : σ.sh hdOUT = (σ.st hdOUT).length)
    (hcap : σ.val v + σ.val hdO + 6 * natBitLength (σ.val v) + 6 ≤ cap) :
    WExec cap (writeNatM hdOUT (hdWR v h)) σ (appendO σ hdOUT hdO (marks (natWord (σ.val v))))
      (hdWrCost (σ.val v)) :=
  writeNatM_spec cap hdOUT (hdWR v h) σ (hz 11 (by decide) (by decide)) (hz 12 (by decide) (by decide))
    (hz 13 (by decide) (by decide)) (hz 14 (by decide) (by decide)) (hz 15 (by decide) (by decide))
    (hz 16 (by decide) (by decide)) ho hcap

/-- The state after the program, as a function of the start state's stream contents. -/
theorem hdr_run (cap : ℕ) (w0 w2 w3 T : List Bool) (n x1 x2 r b s t W : ℕ) (w : List Bool)
    (hw : w = frame w0 ++ (frame (frame ([n, x1, x2, r, b, s, t].flatMap natWord)) ++ (frame w2 ++
      (frame w3 ++ (frame (natWord W) ++ T)))))
    (hcap : 2 * w.length + 1 + 20 * (n + x1 + x2 + r + b + s + W) + 200 ≤ cap) :
    ∃ τ, WExec cap hdrP (hdStart (frame w)) τ (hdrCost w.length n x1 x2 r b s W) ∧
      τ.st hdOUT = frame ([n, r, b, s, W + 1].flatMap natWord) := by
  have p1 := hd_two_pow_nbl_le n
  have p2 := hd_two_pow_nbl_le x1
  have p3 := hd_two_pow_nbl_le x2
  have p4 := hd_two_pow_nbl_le r
  have p5 := hd_two_pow_nbl_le b
  have p6 := hd_two_pow_nbl_le s
  have p7 := hd_two_pow_nbl_le W
  have q1 := hd_nbl_le_self n
  have q4 := hd_nbl_le_self r
  have q5 := hd_nbl_le_self b
  have q6 := hd_nbl_le_self s
  have q7 := hd_nbl_le_self (W + 1)
  have hfl : (frame w).length = 2 * w.length + 1 := frame_length w
  set σ0 := hdStart (frame w) with hσ0
  -- unframe twice
  have e1 := unframeRecord_run cap hdIN hdS1 (by decide) hdOP (frame w) [] [] σ0
    (by simp [hσ0, hdStart, hdIN]) rfl (by simp [hσ0, hdStart, hdS1]) rfl (by omega)
  set σ1 := (σ0.sets hdS1 (σ0.st hdS1 ++ frame w)).seth hdIN (([] : List Bool).length + 2 * (frame w).length + 1)
    with hσ1
  have e2 := unframeRecord_run cap hdS1 hdS2 (by decide) hdOP w [] [] σ1
    (by simp [hσ1, hσ0, hdStart, hdS1, hdIN]) (by simp [hσ1, hσ0, hdStart, hdS1, hdIN])
    (by simp [hσ1, hσ0, hdStart, hdS1, hdS2, hdIN]) (by simp [hσ1, hσ0, hdStart]) (by omega)
  set σ2 := (σ1.sets hdS2 (σ1.st hdS2 ++ w)).seth hdS1 (([] : List Bool).length + 2 * w.length + 1) with hσ2
  -- load fields 0–4
  set X := [n, x1, x2, r, b, s, t].flatMap natWord with hX
  set recs : TapeRecords 8 := [(hdJ0, w0), (hdH, frame X), (hdJ2, w2), (hdJ3, w3), (hdWS, natWord W)] with hrecs
  have hrw : recordsWord recs ++ T = w := by
    rw [hw]; simp [hrecs, recordsWord, List.append_assoc]
  have hrl : (recordsWord recs).length ≤ w.length := by rw [← hrw, List.length_append]; omega
  have hwl := congrArg List.length hw
  simp only [List.length_append, frame_length] at hwl
  have hmem : ∀ record ∈ recs, record.2.length ≤ cap := by
    intro record hr
    simp only [hrecs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [frame_length] <;> omega
  have hn3 : (recs.map Prod.fst).Nodup := by rw [hrecs]; simp only [List.map_cons, List.map_nil]; decide
  have e3 := loadRecords_run cap hdS2 hdOP recs hn3
    (by
      intro record hr
      simp only [hrecs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide))
    hmem [] T σ2
    (by simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN]; exact hrw.symm)
    (by simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN])
    (by simp [hσ2, hσ1, hσ0, hdStart])
    (by
      intro record hr
      simp only [hrecs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN, hdJ0, hdH, hdJ2, hdJ3, hdWS])
  set σ3 := loadedRecords hdS2 σ2 recs with hσ3
  have e3' : WExec cap (loadTapeSlots hdS2 hdOP [hdJ0, hdH, hdJ2, hdJ3, hdWS]) σ2 σ3 (loadRecordsCost recs) := by
    have h := e3
    rw [loadRecords_eq_slots] at h
    exact h
  have c3 : loadRecordsCost recs ≤ 23 * w.length + 1 := (loadRecordsCost_le recs).trans (by omega)
  have hH3 : σ3.st hdH = frame X := loadedRecords_mem hdS2 σ2 recs hn3 (hdH, frame X) (by simp [hrecs])
  have hW3 : σ3.st hdWS = natWord W := loadedRecords_mem hdS2 σ2 recs hn3 (hdWS, natWord W) (by simp [hrecs])
  have hHh3 : σ3.sh hdH = 0 := by
    rw [hσ3, loadedRecords_head hdS2 hdH (by decide)]; simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN, hdH]
  have hWh3 : σ3.sh hdWS = 0 := by
    rw [hσ3, loadedRecords_head hdS2 hdWS (by decide)]; simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN, hdWS]
  have hO3 : σ3.st hdOUT = [] := by
    rw [hσ3, loadedRecords_other hdS2 hdOUT σ2 recs (by rw [hrecs]; simp only [List.map_cons, List.map_nil]; decide)]
    simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN, hdOUT]
  have hOh3 : σ3.sh hdOUT = 0 := by
    rw [hσ3, loadedRecords_head hdS2 hdOUT (by decide)]; simp [hσ2, hσ1, hσ0, hdStart, hdS2, hdS1, hdIN, hdOUT]
  have hv3 : ∀ x, σ3.val x = 0 := by
    intro x; rw [hσ3, hd_loadedRecords_val]; simp [hσ2, hσ1, hσ0, hdStart]
  -- the marked header field
  have hHm : σ3.st hdH = marks (natWord n) ++ (marks (natWord x1) ++ (marks (natWord x2) ++ (marks (natWord r) ++
      (marks (natWord b) ++ (marks (natWord s) ++ (marks (natWord t) ++ [false])))))) := by
    rw [hH3, hd_frame_eq, hX]; simp [List.flatMap_cons, Streaming.marks_append, List.append_assoc]
  -- n
  have e4 := hdRdM cap hdN (by decide) (by decide) (by decide) (by decide) n []
    (marks (natWord x1) ++ (marks (natWord x2) ++ (marks (natWord r) ++ (marks (natWord b) ++ (marks (natWord s) ++
      (marks (natWord t) ++ [false])))))) σ3 (by rw [hHm]; simp [Streaming.marks]) (by rw [hHh3]; simp)
    (hv3 _) (hv3 _) (hv3 _) (hv3 _) (by rw [hv3]; omega)
  set σ4 := (σ3.seth hdH (2 * ([] ++ natWord n).length)).setv hdN (σ3.val hdN + n) with hσ4
  -- x1
  have e5 := hdRdM cap hdJ (by decide) (by decide) (by decide) (by decide) x1 (natWord n)
    (marks (natWord x2) ++ (marks (natWord r) ++ (marks (natWord b) ++ (marks (natWord s) ++
      (marks (natWord t) ++ [false]))))) σ4 (by simp [hσ4, hHm, Streaming.marks_append, List.append_assoc])
    (by simp [hσ4]) (by simp [hσ4, hv3, hdF, hdN]) (by simp [hσ4, hv3, hdC, hdN]) (by simp [hσ4, hv3, hdP, hdN])
    (by simp [hσ4, hv3, hdT, hdN]) (by simp [hσ4, hv3, hdJ, hdN]; omega)
  set σ5 := (σ4.seth hdH (2 * (natWord n ++ natWord x1).length)).setv hdJ (σ4.val hdJ + x1) with hσ5
  -- x2
  have e6 := hdRdM cap hdJ (by decide) (by decide) (by decide) (by decide) x2 (natWord n ++ natWord x1)
    (marks (natWord r) ++ (marks (natWord b) ++ (marks (natWord s) ++ (marks (natWord t) ++ [false])))) σ5
    (by simp [hσ5, hσ4, hHm, Streaming.marks_append, List.append_assoc])
    (by simp [hσ5]) (by simp [hσ5, hσ4, hv3, hdF, hdN, hdJ]) (by simp [hσ5, hσ4, hv3, hdC, hdN, hdJ])
    (by simp [hσ5, hσ4, hv3, hdP, hdN, hdJ]) (by simp [hσ5, hσ4, hv3, hdT, hdN, hdJ])
    (by simp [hσ5, hσ4, hv3, hdJ, hdN]; omega)
  set σ6 := (σ5.seth hdH (2 * ((natWord n ++ natWord x1) ++ natWord x2).length)).setv hdJ (σ5.val hdJ + x2)
    with hσ6
  -- r
  have e7 := hdRdM cap hdR (by decide) (by decide) (by decide) (by decide) r (natWord n ++ natWord x1 ++ natWord x2)
    (marks (natWord b) ++ (marks (natWord s) ++ (marks (natWord t) ++ [false]))) σ6
    (by simp [hσ6, hσ5, hσ4, hHm, Streaming.marks_append, List.append_assoc])
    (by simp [hσ6]) (by simp [hσ6, hσ5, hσ4, hv3, hdF, hdN, hdJ]) (by simp [hσ6, hσ5, hσ4, hv3, hdC, hdN, hdJ])
    (by simp [hσ6, hσ5, hσ4, hv3, hdP, hdN, hdJ]) (by simp [hσ6, hσ5, hσ4, hv3, hdT, hdN, hdJ])
    (by simp [hσ6, hσ5, hσ4, hv3, hdR, hdJ, hdN]; omega)
  set σ7 := (σ6.seth hdH (2 * ((natWord n ++ natWord x1 ++ natWord x2) ++ natWord r).length)).setv hdR
    (σ6.val hdR + r) with hσ7
  -- b
  have e8 := hdRdM cap hdB (by decide) (by decide) (by decide) (by decide) b
    (natWord n ++ natWord x1 ++ natWord x2 ++ natWord r)
    (marks (natWord s) ++ (marks (natWord t) ++ [false])) σ7
    (by simp [hσ7, hσ6, hσ5, hσ4, hHm, Streaming.marks_append, List.append_assoc])
    (by simp [hσ7]) (by simp [hσ7, hσ6, hσ5, hσ4, hv3, hdF, hdN, hdJ, hdR])
    (by simp [hσ7, hσ6, hσ5, hσ4, hv3, hdC, hdN, hdJ, hdR])
    (by simp [hσ7, hσ6, hσ5, hσ4, hv3, hdP, hdN, hdJ, hdR]) (by simp [hσ7, hσ6, hσ5, hσ4, hv3, hdT, hdN, hdJ, hdR])
    (by simp [hσ7, hσ6, hσ5, hσ4, hv3, hdB, hdR, hdJ, hdN]; omega)
  set σ8 := (σ7.seth hdH (2 * ((natWord n ++ natWord x1 ++ natWord x2 ++ natWord r) ++ natWord b).length)).setv hdB
    (σ7.val hdB + b) with hσ8
  -- s
  have e9 := hdRdM cap hdS (by decide) (by decide) (by decide) (by decide) s
    (natWord n ++ natWord x1 ++ natWord x2 ++ natWord r ++ natWord b)
    (marks (natWord t) ++ [false]) σ8
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hHm, Streaming.marks_append, List.append_assoc])
    (by simp [hσ8]) (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdF, hdN, hdJ, hdR, hdB])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdC, hdN, hdJ, hdR, hdB])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdP, hdN, hdJ, hdR, hdB])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdT, hdN, hdJ, hdR, hdB])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdS, hdB, hdR, hdJ, hdN]; omega)
  set σ9 := (σ8.seth hdH (2 * ((natWord n ++ natWord x1 ++ natWord x2 ++ natWord r ++ natWord b) ++
    natWord s).length)).setv hdS (σ8.val hdS + s) with hσ9
  -- W (plain)
  have e10 := readNatM_spec cap false hdWS hdF hdC hdW hdP hdT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W [] [] σ9
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hW3, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    (by have h7 : σ3.sh 7 = 0 := hWh3
        simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, h7, hdWS, hdH])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdF, hdN, hdJ, hdR, hdB, hdS])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdC, hdN, hdJ, hdR, hdB, hdS])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdP, hdN, hdJ, hdR, hdB, hdS])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdT, hdN, hdJ, hdR, hdB, hdS])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]; omega)
  set σ10 := (σ9.seth hdWS ([].length + stp false * (natWord W).length)).setv hdW (σ9.val hdW + W) with hσ10
  -- the values
  have vN : σ10.val hdN = n := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]
  have vR : σ10.val hdR = r := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]
  have vB : σ10.val hdB = b := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]
  have vS : σ10.val hdS = s := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]
  have vW : σ10.val hdW = W := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, hdW, hdN, hdJ, hdR, hdB, hdS]
  have vz : ∀ x : Fin 18, 11 ≤ x.val → σ10.val x = 0 := by
    intro x hx
    have h1 : x ≠ hdW := fun h => by subst h; simp [hdW] at hx
    have h2 : x ≠ hdS := fun h => by subst h; simp [hdS] at hx
    have h3 : x ≠ hdB := fun h => by subst h; simp [hdB] at hx
    have h4 : x ≠ hdR := fun h => by subst h; simp [hdR] at hx
    have h5 : x ≠ hdJ := fun h => by subst h; simp [hdJ] at hx
    have h6 : x ≠ hdN := fun h => by subst h; simp [hdN] at hx
    simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hv3, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]
  have oS : σ10.st hdOUT = [] := by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hO3]
  have oH : σ10.sh hdOUT = 0 := by
    have h8 : σ3.sh 8 = 0 := hOh3
    simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, h8, hdOUT, hdWS, hdH]
  -- W + 1
  have e11 := WExec.inc (cap := cap) hdW σ10 (by rw [vW]; omega)
  set σ11 := σ10.setv hdW (σ10.val hdW + 1) with hσ11
  have vz11 : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ11.val x = 0 := by
    intro x hx _
    have h1 : x ≠ hdW := fun h => by subst h; simp [hdW] at hx
    simp [hσ11, WState.setv, Function.update_of_ne h1, vz x hx]
  have vO11 : σ11.val hdO = 0 := by
    have := vz hdO (by decide)
    simp (config := { decide := true }) [hσ11, this]
  have vN11 : σ11.val hdN = n := by simp (config := { decide := true }) [hσ11, vN]
  have vR11 : σ11.val hdR = r := by simp (config := { decide := true }) [hσ11, vR]
  have vB11 : σ11.val hdB = b := by simp (config := { decide := true }) [hσ11, vB]
  have vS11 : σ11.val hdS = s := by simp (config := { decide := true }) [hσ11, vS]
  have vW11 : σ11.val hdW = W + 1 := by simp (config := { decide := true }) [hσ11, vW]
  -- the writes
  have hm : ∀ v, (marks (natWord v)).length = 4 * natBitLength v + 2 := by
    intro v; rw [Streaming.marks_length, hd_natWord_length]; ring
  have e12 := hdWrStep cap hdN (by decide) σ11 vz11 (by simp [hσ11, oS, oH]) (by rw [vN11, vO11]; omega)
  rw [vN11] at e12
  set σ12 := appendO σ11 hdOUT hdO (marks (natWord n)) with hσ12
  have ho11 : σ11.sh hdOUT = (σ11.st hdOUT).length := by simp [hσ11, oS, oH]
  have ho12 := hd_appendO_ho σ11 (marks (natWord n)) ho11
  have vz12 : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ12.val x = 0 := fun x h1 h2 => by
    rw [hσ12, hd_appendO_val_ne _ _ x (ne_hdO x h2)]; exact vz11 x h1 h2
  have vO12 : σ12.val hdO = (marks (natWord n)).length := by rw [hσ12, hd_appendO_val_O, vO11]; simp
  have e13 := hdWrStep cap hdR (by decide) σ12 vz12 ho12
    (by rw [hσ12, hd_appendO_val_ne _ _ hdR (by decide), vR11, ← hσ12, vO12, hm]; omega)
  rw [hσ12, hd_appendO_val_ne _ _ hdR (by decide), vR11, ← hσ12] at e13
  set σ13 := appendO σ12 hdOUT hdO (marks (natWord r)) with hσ13
  have ho13 := hd_appendO_ho σ12 (marks (natWord r)) ho12
  have vz13 : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ13.val x = 0 := fun x h1 h2 => by
    rw [hσ13, hd_appendO_val_ne _ _ x (ne_hdO x h2)]; exact vz12 x h1 h2
  have vO13 : σ13.val hdO = (marks (natWord n)).length + (marks (natWord r)).length := by
    rw [hσ13, hd_appendO_val_O, vO12]
  have vB13 : σ13.val hdB = b := by
    rw [hσ13, hd_appendO_val_ne _ _ hdB (by decide), hσ12, hd_appendO_val_ne _ _ hdB (by decide), vB11]
  have e14 := hdWrStep cap hdB (by decide) σ13 vz13 ho13 (by rw [vB13, vO13, hm, hm]; omega)
  rw [vB13] at e14
  set σ14 := appendO σ13 hdOUT hdO (marks (natWord b)) with hσ14
  have ho14 := hd_appendO_ho σ13 (marks (natWord b)) ho13
  have vz14 : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ14.val x = 0 := fun x h1 h2 => by
    rw [hσ14, hd_appendO_val_ne _ _ x (ne_hdO x h2)]; exact vz13 x h1 h2
  have vO14 : σ14.val hdO = (marks (natWord n)).length + (marks (natWord r)).length +
      (marks (natWord b)).length := by
    rw [hσ14, hd_appendO_val_O, vO13]
  have vS14 : σ14.val hdS = s := by
    rw [hσ14, hd_appendO_val_ne _ _ hdS (by decide), hσ13, hd_appendO_val_ne _ _ hdS (by decide), hσ12,
      hd_appendO_val_ne _ _ hdS (by decide), vS11]
  have e15 := hdWrStep cap hdS (by decide) σ14 vz14 ho14 (by rw [vS14, vO14, hm, hm, hm]; omega)
  rw [vS14] at e15
  set σ15 := appendO σ14 hdOUT hdO (marks (natWord s)) with hσ15
  have ho15 := hd_appendO_ho σ14 (marks (natWord s)) ho14
  have vz15 : ∀ x : Fin 18, 11 ≤ x.val → x.val ≤ 16 → σ15.val x = 0 := fun x h1 h2 => by
    rw [hσ15, hd_appendO_val_ne _ _ x (ne_hdO x h2)]; exact vz14 x h1 h2
  have vO15 : σ15.val hdO = (marks (natWord n)).length + (marks (natWord r)).length +
      (marks (natWord b)).length + (marks (natWord s)).length := by
    rw [hσ15, hd_appendO_val_O, vO14]
  have vW15 : σ15.val hdW = W + 1 := by
    rw [hσ15, hd_appendO_val_ne _ _ hdW (by decide), hσ14, hd_appendO_val_ne _ _ hdW (by decide), hσ13,
      hd_appendO_val_ne _ _ hdW (by decide), hσ12, hd_appendO_val_ne _ _ hdW (by decide), vW11]
  have e16 := hdWrStep cap hdW (by decide) σ15 vz15 ho15 (by rw [vW15, vO15, hm, hm, hm, hm]; omega)
  rw [vW15] at e16
  set σ16 := appendO σ15 hdOUT hdO (marks (natWord (W + 1))) with hσ16
  have ho16 := hd_appendO_ho σ15 (marks (natWord (W + 1))) ho15
  have vO16 : σ16.val hdO = (marks (natWord n)).length + (marks (natWord r)).length +
      (marks (natWord b)).length + (marks (natWord s)).length + (marks (natWord (W + 1))).length := by
    rw [hσ16, hd_appendO_val_O, vO15]
  -- the end mark
  have e17 := emitC_spec cap hdOUT hdO false σ16 ho16 (by rw [vO16, hm, hm, hm, hm, hm]; omega)
  have hout : σ16.st hdOUT = marks (natWord n) ++ marks (natWord r) ++ marks (natWord b) ++ marks (natWord s) ++
      marks (natWord (W + 1)) := by
    rw [hσ16, hd_appendO_st_O, hσ15, hd_appendO_st_O, hσ14, hd_appendO_st_O, hσ13, hd_appendO_st_O, hσ12, hd_appendO_st_O]
    simp [hσ11, oS]
  have e10' : WExec cap (hdRd false hdWS hdW) σ9 σ10 (hdRdCost W) := e10
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3' (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10' (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 (WExec.seq e15 (WExec.seq e16 e17)))))))))))))))) ?_, ?_⟩
  · unfold hdrCost; rw [hfl]; omega
  · simp only [WState.setv, WState.seth, WState.sets, Function.update_self]
    rw [hout, hd_frame_eq]
    simp [List.flatMap_cons, Streaming.marks_append, List.append_assoc]

end NearQuarticWires.StageGreedyEntry
