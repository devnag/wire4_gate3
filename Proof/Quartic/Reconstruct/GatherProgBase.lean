import Proof.Quartic.Reconstruct.GatherProg
import Proof.Quartic.Reconstruct.EmitHead

/-!
# The gathering program: variables, stores and the reading steps

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

Every field of the printed tables and of the gathered items is a `natWord`, so the gathering program reads numbers
(`rdNatI`) and writes them at depth `1` of marks (`emitNatD 1`). This file fixes its variables and stores, the
effect `Ran` of a phase (input consumed, output written, the stores outside a list unchanged), the overwriting of a
store from its start (`ovw`), and the reading steps with the rest of the input as a list of numbers.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Reconstruct

variable {C : Ctx}

/-! ## Variables and stores -/

/-- The part `s` of the current table. -/
def gS : Fin VV := ⟨90, by decide⟩
/-- A count read from the input. -/
def gN : Fin VV := ⟨91, by decide⟩
/-- An inner counter. -/
def gK : Fin VV := ⟨92, by decide⟩
/-- The number of `true` bits of the pattern. -/
def gPar : Fin VV := ⟨93, by decide⟩
/-- The parity of the pattern (`0` iff `κ_σ ≠ 0`). -/
def gAct : Fin VV := ⟨94, by decide⟩
/-- A quotient (scratch). -/
def gQ : Fin VV := ⟨95, by decide⟩
/-- The prime of the current table. -/
def gP : Fin VV := ⟨96, by decide⟩
/-- The number of digits `|δ|`. -/
def gDn : Fin VV := ⟨97, by decide⟩
/-- The column counter. -/
def gZ : Fin VV := ⟨98, by decide⟩
/-- The sign of an entry. -/
def gSg : Fin VV := ⟨99, by decide⟩
/-- The certified bit of a column. -/
def gB : Fin VV := ⟨100, by decide⟩
/-- The sum of the certified counts of a group. -/
def gSum : Fin VV := ⟨101, by decide⟩
/-- The table counter of a group. -/
def gTk : Fin VV := ⟨102, by decide⟩
/-- The number of tables per group. -/
def gTG : Fin VV := ⟨103, by decide⟩
/-- The number of certified columns. -/
def gCC : Fin VV := ⟨105, by decide⟩
/-- The record base `1 + Σ c`. -/
def gPW : Fin VV := ⟨106, by decide⟩
/-- The certified-column counter. -/
def gJ : Fin VV := ⟨107, by decide⟩
/-- A record. -/
def gRec : Fin VV := ⟨108, by decide⟩
/-- The group counter. -/
def gGI : Fin VV := ⟨109, by decide⟩
/-- The number of groups. -/
def gGN : Fin VV := ⟨110, by decide⟩
/-- The number of printed tables. -/
def gM : Fin VV := ⟨111, by decide⟩
/-- The number of listed systems. -/
def gMs : Fin VV := ⟨112, by decide⟩
/-- A count read from a store. -/
def gC : Fin VV := ⟨113, by decide⟩
/-- The record counter. -/
def gI : Fin VV := ⟨114, by decide⟩
/-- A remainder (scratch). -/
def gRem : Fin VV := ⟨115, by decide⟩
/-- A record (scratch). -/
def gT : Fin VV := ⟨116, by decide⟩
/-- The number of records `tg · n_c`. -/
def gNR : Fin VV := ⟨117, by decide⟩

/-- The certified bits. -/
def sZc : Fin MM := ⟨0, by decide⟩
/-- The digits `δ` of the current group (sign and magnitude of each). -/
def sHd : Fin MM := ⟨1, by decide⟩
/-- The rows `(p, |ρ_1|, |ρ_2|)` of the current group. -/
def sI : Fin MM := ⟨2, by decide⟩
/-- The certified counts of the current group, table by table. -/
def sC : Fin MM := ⟨3, by decide⟩
/-- The records of the current group. -/
def sR : Fin MM := ⟨4, by decide⟩

/-! ## Overwriting a store from its start -/

/-- The store `old` after writing `w` from its start. -/
def ovw (old w : List ℕ) : List ℕ := w ++ old.drop w.length

theorem ovw_nil (old : List ℕ) : ovw old [] = old := by simp [ovw]

theorem ovw_of_le (old w : List ℕ) (h : old.length ≤ w.length) : ovw old w = w := by
  simp [ovw, List.drop_eq_nil_of_le h]

theorem ovw_length (old w : List ℕ) : (ovw old w).length = max old.length w.length := by
  simp [ovw]; omega

theorem putAt_ovw (old w : List ℕ) (v : ℕ) : putAt (ovw old w) w.length v = ovw old (w ++ [v]) := by
  unfold putAt ovw
  split_ifs with h
  · simp only [List.length_append, List.length_drop] at h
    rw [List.set_append_right _ _ (le_refl _), Nat.sub_self]
    have e : old.drop w.length = old[w.length] :: old.drop (w.length + 1) := List.drop_eq_getElem_cons (by omega)
    rw [e, List.set_cons_zero]
    simp
  · simp only [List.length_append, List.length_drop, not_lt] at h
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    simp

theorem ovw_getD (old w : List ℕ) (i : ℕ) (hi : i < w.length) : (ovw old w).getD i 0 = w.getD i 0 := by
  unfold ovw
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

/-! ## The effect of a phase -/

/-- The input cursor advances by `k`, the output grows by `w`, the stores outside `S` and the call buffers are
unchanged, and only the variables in `T` change. -/
structure Ran (a b : DS VV MM) (k : ℕ) (w : List Bool) (T : List (Fin VV)) (S : List (Fin MM)) : Prop where
  ip : b.ip = a.ip + k
  out : b.out = a.out ++ w
  ram : ∀ m, m ∉ S → b.ram m = a.ram m
  rc : ∀ m, m ∉ S → b.rc m = a.rc m
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

namespace Ran

variable {a b c : DS VV MM} {k k' : ℕ} {w w' : List Bool} {T T' : List (Fin VV)} {S S' : List (Fin MM)}

theorem refl (a : DS VV MM) (T : List (Fin VV)) (S : List (Fin MM)) : Ran a a 0 [] T S :=
  ⟨by simp, by simp, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Fr.refl a T⟩

theorem trans (h1 : Ran a b k w T S) (h2 : Ran b c k' w' T S) : Ran a c (k + k') (w ++ w') T S :=
  ⟨by rw [h2.ip, h1.ip, Nat.add_assoc], by rw [h2.out, h1.out, List.append_assoc],
    fun m hm => (h2.ram m hm).trans (h1.ram m hm), fun m hm => (h2.rc m hm).trans (h1.rc m hm),
    h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr⟩

theorem weaken (h : Ran a b k w T S) (hT : ∀ y ∈ T, y ∈ T') (hS : ∀ m ∈ S, m ∈ S') : Ran a b k w T' S' :=
  ⟨h.ip, h.out, fun m hm => h.ram m (fun h' => hm (hS m h')), fun m hm => h.rc m (fun h' => hm (hS m h')),
    h.kin, h.kout, h.kc, h.fr.weaken hT⟩

theorem set (h : Ran a b k w T S) {x : Fin VV} (v : ℕ) (hx : x ∈ T) : Ran a (b.set x v) k w T S :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

theorem put (h : Ran a b k w T S) {m : Fin MM} (v : ℕ) (hm : m ∈ S) : Ran a (b.put m v) k w T S :=
  ⟨h.ip, h.out, fun m' hm' => by
      show Function.update b.ram m _ m' = _
      rw [Function.update_of_ne (fun e => hm' (by rw [e]; exact hm)), h.ram m' hm'],
    fun m' hm' => by
      show Function.update b.rc m _ m' = _
      rw [Function.update_of_ne (fun e => hm' (by rw [e]; exact hm)), h.rc m' hm'], h.kin, h.kout, h.kc, h.fr⟩

theorem adv (h : Ran a b k w T S) {m : Fin MM} (hm : m ∈ S) : Ran a (b.adv m) k w T S :=
  ⟨h.ip, h.out, h.ram, fun m' hm' => by
      show Function.update b.rc m _ m' = _
      rw [Function.update_of_ne (fun e => hm' (by rw [e]; exact hm)), h.rc m' hm'], h.kin, h.kout, h.kc, h.fr⟩

theorem rew (h : Ran a b k w T S) {m : Fin MM} (hm : m ∈ S) : Ran a (b.rew m) k w T S :=
  ⟨h.ip, h.out, h.ram, fun m' hm' => by
      show Function.update b.rc m _ m' = _
      rw [Function.update_of_ne (fun e => hm' (by rw [e]; exact hm)), h.rc m' hm'], h.kin, h.kout, h.kc, h.fr⟩

theorem srt (h : Ran a b k w T S) {m : Fin MM} (hm : m ∈ S) : Ran a (b.srt m) k w T S :=
  ⟨h.ip, h.out, fun m' hm' => by
      show Function.update b.ram m _ m' = _
      rw [Function.update_of_ne (fun e => hm' (by rw [e]; exact hm)), h.ram m' hm'], h.rc, h.kin, h.kout, h.kc, h.fr⟩

theorem of_moved {k : ℕ} (h : Moved a b k w T) (S : List (Fin MM)) : Ran a b k w T S :=
  ⟨h.ip, h.out, fun m _ => by rw [h.ram], fun m _ => by rw [h.rc], h.kin, h.kout, h.kc, h.fr⟩

theorem of_wrote (h : Wrote a b w T) (S : List (Fin MM)) : Ran a b 0 w T S :=
  ⟨by rw [h.ip]; simp, h.out, fun m _ => by rw [h.ram], fun m _ => by rw [h.rc], h.kin, h.kout, h.kc, h.fr⟩

theorem cst (h : Ran a b k w T S) (hc : Cst a) (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.fr hT

end Ran

@[simp] theorem DS.put_env (a : DS VV MM) (m : Fin MM) (v : ℕ) : (a.put m v).env = a.env := rfl
@[simp] theorem DS.put_ip (a : DS VV MM) (m : Fin MM) (v : ℕ) : (a.put m v).ip = a.ip := rfl
@[simp] theorem DS.put_out (a : DS VV MM) (m : Fin MM) (v : ℕ) : (a.put m v).out = a.out := rfl
@[simp] theorem DS.put_ram_self (a : DS VV MM) (m : Fin MM) (v : ℕ) :
    (a.put m v).ram m = putAt (a.ram m) (a.rc m) v := by simp [DS.put]
@[simp] theorem DS.put_rc_self (a : DS VV MM) (m : Fin MM) (v : ℕ) : (a.put m v).rc m = a.rc m + 1 := by
  simp [DS.put]
theorem DS.put_ram_ne (a : DS VV MM) {m m' : Fin MM} (v : ℕ) (h : m' ≠ m) : (a.put m v).ram m' = a.ram m' := by
  simp [DS.put, Function.update_of_ne h]
theorem DS.put_rc_ne (a : DS VV MM) {m m' : Fin MM} (v : ℕ) (h : m' ≠ m) : (a.put m v).rc m' = a.rc m' := by
  simp [DS.put, Function.update_of_ne h]
@[simp] theorem DS.adv_env (a : DS VV MM) (m : Fin MM) : (a.adv m).env = a.env := rfl
@[simp] theorem DS.adv_ip (a : DS VV MM) (m : Fin MM) : (a.adv m).ip = a.ip := rfl
@[simp] theorem DS.adv_out (a : DS VV MM) (m : Fin MM) : (a.adv m).out = a.out := rfl
@[simp] theorem DS.adv_ram (a : DS VV MM) (m : Fin MM) : (a.adv m).ram = a.ram := rfl
@[simp] theorem DS.adv_rc_self (a : DS VV MM) (m : Fin MM) : (a.adv m).rc m = a.rc m + 1 := by simp [DS.adv]
theorem DS.adv_rc_ne (a : DS VV MM) {m m' : Fin MM} (h : m' ≠ m) : (a.adv m).rc m' = a.rc m' := by
  simp [DS.adv, Function.update_of_ne h]
@[simp] theorem DS.rew_env (a : DS VV MM) (m : Fin MM) : (a.rew m).env = a.env := rfl
@[simp] theorem DS.rew_ip (a : DS VV MM) (m : Fin MM) : (a.rew m).ip = a.ip := rfl
@[simp] theorem DS.rew_out (a : DS VV MM) (m : Fin MM) : (a.rew m).out = a.out := rfl
@[simp] theorem DS.rew_ram (a : DS VV MM) (m : Fin MM) : (a.rew m).ram = a.ram := rfl
@[simp] theorem DS.rew_rc_self (a : DS VV MM) (m : Fin MM) : (a.rew m).rc m = 0 := by simp [DS.rew]
theorem DS.rew_rc_ne (a : DS VV MM) {m m' : Fin MM} (h : m' ≠ m) : (a.rew m).rc m' = a.rc m' := by
  simp [DS.rew, Function.update_of_ne h]
@[simp] theorem DS.srt_env (a : DS VV MM) (m : Fin MM) : (a.srt m).env = a.env := rfl
@[simp] theorem DS.srt_ip (a : DS VV MM) (m : Fin MM) : (a.srt m).ip = a.ip := rfl
@[simp] theorem DS.srt_out (a : DS VV MM) (m : Fin MM) : (a.srt m).out = a.out := rfl
@[simp] theorem DS.srt_rc (a : DS VV MM) (m : Fin MM) : (a.srt m).rc = a.rc := rfl
@[simp] theorem DS.srt_ram_self (a : DS VV MM) (m : Fin MM) :
    (a.srt m).ram m = (a.ram m).insertionSort (· ≤ ·) := by simp [DS.srt]
theorem DS.srt_ram_ne (a : DS VV MM) {m m' : Fin MM} (h : m' ≠ m) : (a.srt m).ram m' = a.ram m' := by
  simp [DS.srt, Function.update_of_ne h]

theorem cst_set {a : DS VV MM} (hc : Cst a) {x : Fin VV} (v : ℕ) (hx : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) :
    Cst (a.set x v) :=
  ⟨by rw [DS.set_env_ne _ _ (fun h => hx.1 h.symm)]; exact hc.z,
    by rw [DS.set_env_ne _ _ (fun h => hx.2.1 h.symm)]; exact hc.one,
    by rw [DS.set_env_ne _ _ (fun h => hx.2.2 h.symm)]; exact hc.two⟩

theorem cst_put {a : DS VV MM} (hc : Cst a) (m : Fin MM) (v : ℕ) : Cst (a.put m v) := ⟨hc.z, hc.one, hc.two⟩
theorem cst_adv {a : DS VV MM} (hc : Cst a) (m : Fin MM) : Cst (a.adv m) := ⟨hc.z, hc.one, hc.two⟩
theorem cst_rew {a : DS VV MM} (hc : Cst a) (m : Fin MM) : Cst (a.rew m) := ⟨hc.z, hc.one, hc.two⟩
theorem cst_srt {a : DS VV MM} (hc : Cst a) (m : Fin MM) : Cst (a.srt m) := ⟨hc.z, hc.one, hc.two⟩

/-! ## Reading and writing numbers -/

/-- The cost unit of one read or one write of a number of at most `ℓ` bits. -/
def unitC (ℓ : ℕ) : ℕ := 30 * ℓ + 100

theorem emitNatDCost_one (ℓ : ℕ) : emitNatDCost 1 ℓ = 28 * ℓ + 84 := by unfold emitNatDCost; norm_num; ring

/-- **Reading a number** off a list of numbers. -/
theorem rdN_spec (a : DS VV MM) (hc : Cst a) (v : ℕ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (v :: vs).flatMap natWord ++ rest) (ℓ : ℕ) (hv : natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C rdNatI a (30 * ℓ + 30) (fun b => b.env t3 = v ∧ Ran a b (natWord v).length [] rdNatT [] ∧ Cst b ∧
      C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hin' : C.inp.drop a.ip = natWord v ++ (vs.flatMap natWord ++ rest) := by
    rw [hin, List.flatMap_cons, List.append_assoc]
  refine (rdNatI_spec a hc v _ hin' (by omega)).mono (by omega) ?_
  rintro b ⟨h1, -, h3, h4, h5⟩
  simp only [Prod.mk.injEq] at h4
  obtain ⟨o4, r4, c4, i4, k4, kc4⟩ := h4
  exact ⟨h1, ⟨h3, by rw [o4, List.append_nil], fun _ _ => by rw [r4], fun _ _ => by rw [c4], i4, k4, kc4, h5⟩,
    cst_fr hc h5, by rw [h3]; exact drop_step hin'⟩

/-- **Reading a number into a variable** off a list of numbers. -/
theorem rdX_spec (x : Fin VV) (hx0 : x ∉ rdNatT ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (a : DS VV MM) (hc : Cst a) (v : ℕ)
    (vs : List ℕ) (rest : List Bool) (hin : C.inp.drop a.ip = (v :: vs).flatMap natWord ++ rest) (ℓ : ℕ)
    (hv : natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (rdTo x) a (unitC ℓ) (fun b => b.env x = v ∧ b.env t3 = v ∧ Ran a b (natWord v).length [] (x :: rdNatT) [] ∧
      Cst b ∧ C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hxt : x ≠ t3 := fun h => hx0.1 (by rw [h]; decide)
  refine Hs.seq (t1 := 30 * ℓ + 30) (t2 := 1) (rdN_spec a hc v vs rest hin ℓ hv hℓ) (fun b ⟨h1, h2, h3, h4⟩ => ?_) |>.mono (by unfold unitC; omega)
    (fun _ h => h)
  refine Hs.mono (hs_copy C x t3 b hxt) le_rfl ?_
  rintro d rfl
  refine ⟨by rw [DS.set_env_self, h1], by rw [DS.set_env_ne _ _ (Ne.symm hxt), h1], ?_,
    cst_set h3 _ ⟨hx0.2.1, hx0.2.2.1, hx0.2.2.2⟩, h4⟩
  exact (h2.weaken (fun y hy => List.mem_cons_of_mem _ hy) (fun _ h => h)).set _ List.mem_cons_self

/-- **Writing the number in `t3`** at depth `1`. -/
theorem emN_spec (a : DS VV MM) (hc : Cst a) (ℓ : ℕ) (hv : natBitLength (a.env t3) ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (emitNatD 1) a (unitC ℓ) (fun b => Ran a b 0 (marksD 1 (natWord (a.env t3))) emitNatDT [] ∧ Cst b) := by
  have hW : 2 ≤ C.Wd := by omega
  have hlt : natBitLength (a.env t3) + 2 < 2 ^ C.Wd :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine (emitNatD_spec 1 a hc hW hlt).mono (by rw [emitNatDCost_one]; unfold unitC; omega) ?_
  rintro b ⟨w, cb⟩
  exact ⟨Ran.of_wrote w [], cb⟩

/-! ## Counted loops -/

/-- **A loop counted by `x < y`**: the invariant fixes `x = k` and `y = N`. -/
theorem loopCnt (x y : Fin VV) (hxy : x ≠ y) (body : St VV MM) (N t : ℕ) (I : ℕ → DS VV MM → Prop)
    (hI : ∀ k b, I k b → b.env x = k ∧ b.env y = N)
    (hstep : ∀ k < N, ∀ b, I k b → Hs C body b t (I (k + 1))) :
    ∀ a, I 0 a → Hs C (.loop (.lt x y) body) a (N * (t + 2) + 2) (I N) := by
  refine Hs.loopN (c := .lt x y) hxy I N t (fun k hk b hb => ⟨?_, hstep k hk b hb⟩) (fun b hb => ?_)
  · obtain ⟨h1, h2⟩ := hI k b hb
    simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk
  · obtain ⟨h1, h2⟩ := hI N b hb
    simp [Cnd.eval, h1, h2]

theorem lt_two_pow_of_bits {v ℓ W : ℕ} (hv : natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ W) : v + 1 < 2 ^ W := by
  have h1 : v < 2 ^ natBitLength v := lt_natBitLength v
  have h2 : 2 ^ natBitLength v ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hv
  have h3 : 2 * 2 ^ ℓ ≤ 2 ^ W := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  omega

end NearQuarticWires.Reconstruct.GatherProg
