import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
first-bank size is subtracted from a copy of the original occurrence
index; an exhausted index marks the first-bank branch. -/
def bankSplitProgram (R : Fin 3 ↪ Fin nr) : WM ns nr :=
  .whr (R 1) (.ifr (R 0) (.seq (.dec (R 0)) (.dec (R 1)))
    (.seq (WM.clear (R 1)) (WM.clear (R 2))))

/-- `lem:print`, paper/paper.tex: physical bank
normalization changes only its two working counters and bank flag. -/
structure BankSplitResult (R : Fin 3 ↪ Fin nr) (a b : ℕ)
    (σ τ : WState ns nr) : Prop where
  difference : τ.val (R 0)=a-b
  remainder : τ.val (R 1)=0
  second : τ.val (R 2)=(decide (b≤a)).toNat
  other : ∀ i, i∉[R 0,R 1,R 2] → τ.val i=σ.val i
  heads : τ.sh=σ.sh
  tapes : τ.st=σ.st
  flag : τ.cell=σ.cell

/-- `lem:print` and `prop:time`, paper/paper.tex: the real small occurrence counters determine both the
bank and exact relative index. Equality with the first-bank size selects
the second bank, and an empty first bank is handled by the same code. -/
theorem bankSplitProgram_spec (cap : ℕ) (R : Fin 3 ↪ Fin nr) :
    ∀ (b a : ℕ) (σ : WState ns nr), σ.val (R 0)=a → σ.val (R 1)=b →
      σ.val (R 2)=1 → a≤cap → b≤cap → 1≤cap →
      ∃ τ,WExec cap (bankSplitProgram R) σ τ (14*(a+b+1)) ∧ BankSplitResult R a b σ τ := by
  intro b
  induction b with
  | zero =>
    intro a σ ha hb hf _ha _hb _hc
    refine ⟨σ,(WExec.whrF hb).mono (by omega),ha, hb,?_,?_,rfl,rfl,rfl⟩
    · simpa only [Nat.zero_le,decide_true,Bool.toNat_true] using hf
    · intro i _hi;rfl
  | succ b ih =>
    intro a σ ha hb hf hac hbc hc
    have hn : σ.val (R 1)≠0 := by omega
    cases a with
    | zero =>
      have e1 := wclear_spec cap (R 1) (b+1) σ hb (by rw [hb];exact hbc)
      let d := σ.setv (R 1) 0
      have e2 := wclear_spec cap (R 2) 1 d
        (by simp [d,R.injective.ne (by decide : (2:Fin 3)≠1),hf])
        (by simpa [d,R.injective.ne (by decide : (2:Fin 3)≠1),hf] using hc)
      let e := d.setv (R 2) 0
      have e3 : WExec cap (bankSplitProgram R) e e 1 := by
        unfold bankSplitProgram
        exact WExec.whrF (by simp [e,d,R.injective.ne (by decide : (1:Fin 3)≠2)])
      refine ⟨e,(WExec.whrT hn (WExec.ifrF ha (e1.seq e2)) e3).mono (by omega),?_,?_,?_,?_,rfl,rfl,rfl⟩
      · simp [e,d,R.injective.ne (by decide : (0:Fin 3)≠1),
          R.injective.ne (by decide : (0:Fin 3)≠2),ha]
      · simp [e,d,R.injective.ne (by decide : (1:Fin 3)≠2)]
      · simp [e]
      · intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
        simp [e,d,hi.2.1,hi.2.2]
    | succ a =>
      have e1 := WExec.dec (cap:=cap) (R 0) σ (by omega)
      let d := σ.setv (R 0) a
      have e1' : WExec cap (.dec (R 0)) σ d 1 := by simpa [ha,d] using e1
      have e2 := WExec.dec (cap:=cap) (R 1) d
        (by simp [d,R.injective.ne (by decide : (1:Fin 3)≠0),hb];omega)
      let e := d.setv (R 1) b
      have e2' : WExec cap (.dec (R 1)) d e 1 := by
        simpa [e,d,R.injective.ne (by decide : (1:Fin 3)≠0),hb] using e2
      obtain ⟨τ,et,ht⟩ := ih a e
        (by simp [e,d,R.injective.ne (by decide : (0:Fin 3)≠1)])
        (by simp [e])
        (by simp [e,d,R.injective.ne (by decide : (2:Fin 3)≠1),
          R.injective.ne (by decide : (2:Fin 3)≠0),hf])
        (by omega) (by omega) hc
      refine ⟨τ,(WExec.whrT hn (WExec.ifrT (by omega) (e1'.seq e2')) et).mono (by omega),
        ?_,ht.remainder,?_,?_,ht.heads,ht.tapes,ht.flag⟩
      · simpa only [Nat.add_sub_add_right] using ht.difference
      · simpa only [Nat.succ_le_succ_iff] using ht.second
      · intro i hi
        rw [ht.other i hi]
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
        simp [e,d,hi.1,hi.2.1]

end NearQuarticWires.StageTuple
