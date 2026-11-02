import Proof.Quartic.StagePullback.SignedCoefficient
import Proof.Gates.CounterMachine.CellTablesLem
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.FieldOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTables (binary_snoc toNat_bit)

def width : Fin VV := 36
def work : Fin VV := 110
def quotient : Fin VV := 111
def remainder : Fin VV := 112
def index : Fin VV := 113
def scratch : List (Fin VV) := [work, quotient, remainder, index, vJ]

/-- `lem:print`, paper/paper.tex: one physically
computed data bit is emitted with its actual field marker. -/
def pairProgram : St VV MM :=
  .seq (.op (.emit true))
    (.ite (.eq remainder v1) (.op (.emit true)) (.op (.emit false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: a field marker and its actual binary bit require four
literal source operations, without changing any retained variable. -/
theorem pairProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit : Bool)
    (hb : a.env remainder = bit.toNat) :
    Hs C pairProgram a 4 (fun b => b = { a with out := a.out ++ [true, bit] }) := by
  unfold pairProgram
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_emit C true a) ?_
  rintro b rfl
  cases bit with
  | false =>
    refine Hs.iteF (show remainder ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
    refine Hs.mono (hs_emit C false _) le_rfl ?_
    rintro b rfl
    simp only [List.append_assoc]
    rfl
  | true =>
    refine Hs.iteT (show remainder ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
    refine Hs.mono (hs_emit C true _) le_rfl ?_
    rintro b rfl
    simp only [List.append_assoc]
    rfl

/-- `lem:print`, paper/paper.tex: repeatedly divide
the retained signed encoding by two and emit its original low bits. -/
def bitProgram : St VV MM :=
  .seq (.op (.dm work v2 quotient remainder))
    (.seq pairProgram (.op (.copy work quotient)))

/-- `lem:print`, paper/paper.tex: a fixed signed
native field is emitted as its exact framed binary record. -/
def program : St VV MM :=
  .seq (.op (.copy work SignedCoefficients.value))
    (.seq (forS index width bitProgram) (.op (.emit false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual signed field bits, including all zero padding,
are physically serialized in linear field width. -/
theorem program_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (N v : ℕ)
    (hwidth : a.env width = N) (hv : a.env SignedCoefficients.value = v)
    (hN : N < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C program a (12 * N + 8) (fun b =>
      b.out = a.out ++ frame (binary N v) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b scratch) := by
  have hfour : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide) hW
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env work = v / 2 ^ k ∧ b.out = a.out ++ frameP (binary k v) ∧
    (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
      (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b scratch
  have hI : ∀ k b val, I k b → I k (b.set index val) := by
    rintro k b val ⟨hb, hout, hrest, hbc, hfr⟩
    exact ⟨(DS.set_env_ne _ _ (by decide : work ≠ index)).trans hb, hout, hrest,
      hbc.of_fr (T := scratch) (Fr.set b _ (by simp [scratch])) (by decide),
      hfr.trans (Fr.set b _ (by simp [scratch]))⟩
  have hbody : ∀ k < N, ∀ b, I k b → b.env index = k → b.env width = N →
      Hs C bitProgram b 8 (fun d => I (k + 1) d ∧ d.env index = k ∧ d.env width = N) := by
    rintro k hk b ⟨hb, hout, hrest, hbc, hfr⟩ hki hcn
    unfold bitProgram
    refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C work v2 quotient remainder b
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hbc.two]; decide) (by rw [hbc.two]; omega)) ?_
    rintro c he
    subst he
    let c := (b.set quotient (b.env work / b.env v2)).set remainder (b.env work % b.env v2)
    have hcf : Fr b c [quotient, remainder] :=
      (Fr.set b _ (by simp)).trans (Fr.set _ _ (by simp))
    have hcc : Cst c := hbc.of_fr hcf (by decide)
    have hq : c.env quotient = v / 2 ^ (k + 1) := by
      simp only [c, DS.set_env_ne _ _ (by decide : quotient ≠ remainder), DS.set_env_self,
        hb, hbc.two, Nat.div_div_eq_div_mul, pow_succ]
    have hr : c.env remainder = (v / 2 ^ k % 2 == 1).toNat := by
      simp only [c, DS.set_env_self, hb, hbc.two, toNat_bit]
    refine Hs.seq (t1 := 4) (t2 := 1)
      (pairProgram_run C c hcc (v / 2 ^ k % 2 == 1) hr) ?_
    rintro d hd
    subst hd
    let d : DS VV MM := { c with out := c.out ++ [true, (v / 2 ^ k % 2 == 1)] }
    have hdc : Cst d := ⟨hcc.z, hcc.one, hcc.two⟩
    refine Hs.mono (hs_copy C work quotient d (by decide)) le_rfl ?_
    rintro e he
    subst he
    have hfstep : Fr b (d.set work (d.env quotient)) [work, quotient, remainder] :=
      (hcf.weaken (by intro y hy; exact List.mem_cons_of_mem work hy)).trans
        (Fr.set d _ (by simp))
    have hfa : Fr a (d.set work (d.env quotient)) scratch := hfr.trans
      (hfstep.weaken (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl <;> decide))
    refine ⟨⟨?_, ?_, hrest,
      hdc.of_fr (T := scratch) (Fr.set d _ (by simp [scratch])) (by decide), hfa⟩,
      (hfstep _ (by decide)).trans hki, (hfstep _ (by decide)).trans hcn⟩
    · exact (DS.set_env_self _ _ _).trans hq
    · change b.out ++ [true, (v / 2 ^ k % 2 == 1)] =
        a.out ++ frameP (binary (k + 1) v)
      rw [hout, binary_snoc]
      simp [NearCubicWires.WireExponent3_5.FinalPass.Tm.frameP, List.append_assoc]
  unfold program
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 12 * N + 6)
    (hs_copy C work SignedCoefficients.value a (by decide)) ?_) (by omega) (fun _ h => h)
  rintro b hb
  subst hb
  let b := a.set work (a.env SignedCoefficients.value)
  have h0 : I 0 b := by
    refine ⟨by simp [b, hv], by simp [b, binary, frameP], rfl,
      hc.of_fr (T := scratch) (Fr.set a _ (by simp [scratch])) (by decide), Fr.set a _ (by simp [scratch])⟩
  have hbn : b.env width = N := (DS.set_env_ne _ _ (by decide : width ≠ work)).trans hwidth
  refine Hs.seq (t1 := 12 * N + 4) (t2 := 1)
    (Hs.mono (forS_spec' index width (by decide) bitProgram b N hN I 8 hI h0 hbn hbody)
      (by omega) (fun _ h => h)) ?_
  rintro c ⟨⟨_, hout, hrest, hcc, hfr⟩, _, _⟩
  refine Hs.mono (hs_emit C false c) le_rfl ?_
  rintro d rfl
  refine ⟨?_, hrest, ⟨hcc.z, hcc.one, hcc.two⟩, hfr⟩
  rw [hout, frame_eq_frameP]
  simp only [List.append_assoc]

end NearQuarticWires.StagePullback.FieldOutput
