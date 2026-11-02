import Proof.Quartic.StageLift.FrameRead
import Proof.Gates.Cells.Forms2

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a unary field
length is represented by physical marker records, with a zero sentinel,
instead of an arithmetic register containing the possibly huge length. -/
def unaryFlag (n : ℕ) : Bool := decide (0 < n)

/-- `lem:print`, paper/paper.tex: after its first
bit, a unary field header contains the remaining actual marker bits. -/
def unaryTail : ℕ → List Bool
  | 0 => []
  | n + 1 => unaryFlag n :: unaryTail n

/-- `lem:print`, paper/paper.tex: the explicit
marker/sentinel header is exactly the original natural-word length code. -/
theorem unaryWord_eq (n : ℕ) :
    unaryFlag n :: unaryTail n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [unaryTail, unaryFlag, Nat.zero_lt_succ, decide_true,
        List.replicate_succ, List.cons_append]
      exact congrArg (List.cons true) ih

/-- `lem:print`, paper/paper.tex: one real unary
one becomes one retained marker and the next header bit is read. -/
def markUnaryBody (store : Fin MM) : St VV MM :=
  .seq (.op (.wrM store v1)) (.op (.rdI t0))

/-- `lem:print`, paper/paper.tex: each marker is
actually written before the next header bit is inspected. -/
theorem markUnaryBody_spec (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (hc : Cst a) (bit : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = bit :: rest) (hcur : a.rc store ≤ (a.ram store).length) :
    Hs C (markUnaryBody store) a 3 (fun b =>
      b = { (a.put store 1).set t0 bit.toNat with ip := a.ip + 1 }) := by
  unfold markUnaryBody
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C store v1 a hcur) fun b hb => ?_
  subst b
  rw [hc.one]
  exact (readInputBit_spec C t0 (a.put store 1) bit rest hin).mono le_rfl
    (by rintro b rfl; rfl)

/-- `lem:print`, paper/paper.tex: the unary loop
has no numeric length register or bound on the raw field's bit length.
Its termination is by the actual zero header bit. -/
theorem markUnaryLoop_spec (C : Ctx) (store : Fin MM) (n : ℕ)
    (original pre : List ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (unaryFlag n).toNat)
    (hin : C.inp.drop a.ip = unaryTail n ++ rest)
    (hram : a.ram store = wr original 0 pre) (hrc : a.rc store = pre.length) :
    Hs C (.loop (.eq t0 v1) (markUnaryBody store)) a (5 * n + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + n ∧
      b.ram store = wr original 0 (pre ++ List.replicate n 1) ∧
      b.rc store = pre.length + n ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0]) := by
  induction n generalizing pre a with
  | zero =>
      have ht : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, unaryFlag, hc.one]
      exact ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) ht, by simp,
        by simpa [unaryFlag] using hflag, by simp, by simpa using hram,
        by simpa using hrc, fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  | succ n ih =>
      have ht : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, unaryFlag, hc.one]
      have hinput : C.inp.drop a.ip = unaryFlag n :: (unaryTail n ++ rest) := hin
      obtain ⟨b, s, he, hs, hb⟩ := markUnaryBody_spec C store a hc
        (unaryFlag n) (unaryTail n ++ rest) hinput
        (by rw [hrc, hram]; exact wr_length _ _)
      subst b
      let b : DS VV MM := { (a.put store 1).set t0 (unaryFlag n).toNat with ip := a.ip + 1 }
      have hbf : Fr a b [t0] := Fr.set a _ (by simp)
      have hbc : Cst b := Cst.of_fr hc hbf (by decide)
      have hbram : b.ram store = wr original 0 (pre ++ [1]) := by
        simp only [b, DS.set, DS.put, Function.update_self]
        rw [hram, hrc, wr_zero]
      have hbrc : b.rc store = (pre ++ [1]).length := by
        simp only [b, DS.set, DS.put, Function.update_self, List.length_append, List.length_singleton]
        omega
      have hbin : C.inp.drop b.ip = unaryTail n ++ rest := by
        change C.inp.drop (a.ip + 1) = _
        rw [← List.drop_drop, hinput]
        rfl
      obtain ⟨d, k, hd, hk, hdz, hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩ :=
        ih (pre ++ [1]) b hbc (by simp [b]) hbin hbram hbrc
      refine ⟨d, s + k + 2, Ex.loopT (show t0 ≠ v1 by decide) ht he hd, by omega,
        hdz, ?_, ?_, ?_, ?_, ?_, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.ip + 1 + n = a.ip + (n + 1)
        omega
      · rw [hdr, List.append_assoc]
        congr 2
      · rw [hdrc]
        simp only [List.length_append, List.length_singleton]
        omega
      · intro other hother
        simpa only [b, DS.put, DS.set, Function.update_of_ne hother] using hdo other hother
      · exact hdsh

/-- `lem:print`, paper/paper.tex: the real unary
header is consumed once into reusable marker storage and terminated
by an explicit zero record, without constructing its length in a register. -/
def readUnaryMarkers (store : Fin MM) : St VV MM :=
  .seq (.op (.rwM store)) (.seq (.op (.rdI t0))
    (.seq (.loop (.eq t0 v1) (markUnaryBody store)) (.op (.wrM store vZ))))

/-- `lem:print`, paper/paper.tex: even arbitrary
raw integer bit lengths are parsed with constant arithmetic-register
width. Every store rewind and marker/sentinel write is paid explicitly. -/
theorem readUnaryMarkers_spec (C : Ctx) (store : Fin MM) (n : ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = (List.replicate n true ++ [false]) ++ rest) :
    Hs C (readUnaryMarkers store) a (a.rc store + 5 * n + 9) (fun b =>
      b.ip = a.ip + n + 1 ∧
      b.ram store = wr (a.ram store) 0 (List.replicate n 1 ++ [0]) ∧
      b.rc store = n + 1 ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0]) := by
  unfold readUnaryMarkers
  refine (Hs.seq (t1 := a.rc store + 1) (t2 := 5 * n + 7)
    (hs_rwM C store a) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  have hinput : C.inp.drop (a.rew store).ip = unaryFlag n :: (unaryTail n ++ rest) := by
    change C.inp.drop a.ip = _
    rw [hin, ← unaryWord_eq]
    rfl
  refine (Hs.seq (t1 := 1) (t2 := 5 * n + 5)
    (readInputBit_spec C t0 (a.rew store) (unaryFlag n) (unaryTail n ++ rest) hinput)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let b : DS VV MM := { (a.rew store).set t0 (unaryFlag n).toNat with ip := a.ip + 1 }
  have hbc : Cst b := ⟨by simpa (config := {decide := true}) [b, DS.rew, DS.set] using hc.z,
    by simpa (config := {decide := true}) [b, DS.rew, DS.set] using hc.one,
    by simpa (config := {decide := true}) [b, DS.rew, DS.set] using hc.two⟩
  have hbin : C.inp.drop b.ip = unaryTail n ++ rest := by
    change C.inp.drop (a.ip + 1) = _
    change C.inp.drop a.ip = unaryFlag n :: (unaryTail n ++ rest) at hinput
    rw [← List.drop_drop, hinput]
    rfl
  refine (Hs.seq (t1 := 5 * n + 2) (t2 := 1)
    (markUnaryLoop_spec C store n (a.ram store) [] (rest) b hbc
      (by simp [b]) hbin (by simp [b, DS.rew, wr_nil]) (by simp [b, DS.rew]))
    fun d ⟨_hdz, hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  refine (hs_wrM C store vZ d (by
    rw [hdr, hdrc]
    simpa using (wr_length (a.ram store) (List.replicate n 1)))).mono le_rfl ?_
  rintro e rfl
  refine ⟨?_, ?_, ?_, ?_, hdsh, ⟨hdc.z, hdc.one, hdc.two⟩, ?_⟩
  · change d.ip = _
    rw [hdi]
    change a.ip + 1 + n = a.ip + n + 1
    omega
  · simp only [DS.put, Function.update_self]
    rw [hdc.z, hdr, hdrc]
    simpa using (wr_zero (a.ram store) (List.replicate n 1) 0)
  · simp only [DS.put, Function.update_self, hdrc, List.length_nil, Nat.zero_add]
  · intro other ho
    simpa only [DS.put, b, DS.rew, DS.set, Function.update_of_ne ho] using hdo other ho
  · exact (Fr.set (T := [t0]) a _ (by simp)).trans hdf

end NearQuarticWires.StageLift
