import Proof.Gates.CounterMachine.CellTablesBody2
import Proof.Gates.Cells.Comp

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `sec:walks`, paper/paper.tex: all state components
other than the output stream and arithmetic registers remain fixed. -/
structure SameOutput (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

/-- `sec:walks`, paper/paper.tex: reflexivity of the
output-stream frame. -/
theorem SameOutput.refl (a : DS VV MM) : SameOutput a a := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- `sec:walks`, paper/paper.tex: composition of
output-stream frames. -/
theorem SameOutput.trans {a b d : DS VV MM} (h : SameOutput a b) (g : SameOutput b d) :
    SameOutput a d := ⟨g.ip.trans h.ip,g.ram.trans h.ram,g.rc.trans h.rc,
      g.kin.trans h.kin,g.kout.trans h.kout,g.kc.trans h.kc⟩

/-- `sec:walks`, paper/paper.tex: changing an arithmetic
register preserves the complete external-state frame. -/
theorem SameOutput.set (a : DS VV MM) (x : Fin VV) (v : ℕ) :
    SameOutput a (a.set x v) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- `sec:walks`, paper/paper.tex: one self-delimiting
coordinate is emitted directly to the output tape. -/
def emitOutputNat (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) emitNatO

/-- `sec:walks`, paper/paper.tex: exact physical emission
of one walk coordinate, preserving the input and all record stores. -/
theorem emitOutputNat_run (C : Ctx) (x : Fin VV) (hx : x ≠ t3)
    (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (v : ℕ)
    (hv : a.env x = v) (hvW : v < 2^C.Wd) :
    Hs C (emitOutputNat x) a (40*natBitLength v+42)
      (fun e => e.out=a.out++natWord v ∧ SameOutput a e ∧ Cst e ∧ Fr a e emT) := by
  unfold emitOutputNat
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40*natBitLength v+40)
    (hs_copy C t3 x a (Ne.symm hx)) (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  have hb3 : (a.set t3 (a.env x)).env t3=v := by simp [hv]
  have hc' : Cst (a.set t3 (a.env x)) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
     by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
     by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two⟩
  have h := emitNatO_spec (C := C) (a.set t3 (a.env x)) hc' (by omega)
    (by rw [hb3]; exact nbl_fit C v hvW hW)
  rw [hb3] at h
  refine Hs.mono h le_rfl ?_
  rintro e ⟨e1,e2,e3,e4⟩
  simp only [Prod.mk.injEq] at e2
  obtain ⟨g1,g2,g3,g4,g5,g6⟩ := e2
  exact ⟨by rw [e1]; rfl,⟨g1,g2,g3,g4,g5,g6⟩,e3,
    Fr.trans (Fr.set a _ (by decide)) (Fr.weaken e4 (by decide))⟩

/-- `sec:walks`, paper/paper.tex: the arithmetic decoder
emits one most-significant-first digit and updates its positional power. -/
def outputDigit : St VV MM :=
  .seq (.op (.dm bPw lQ bQu bJk)) (.seq (.op (.copy bPw bQu))
  (.seq (.op (.dm lT bPw bQu bJk)) (.seq (.op (.dm bQu lQ bJk bDig))
  (.seq (emitOutputNat bDig) (.seq (.op (.mul bKey kB2 bTmp))
  (.seq (.op (.copy bKey bTmp)) (.op (.add bKey bDig))))))))

/-- `sec:walks`, paper/paper.tex: the exact radix decoder
uses a fixed finite coordinate loop. -/
def outputRadix : St VV MM := forS bI kD outputDigit

/-- `sec:walks`, paper/paper.tex: only the listed arithmetic
registers are changed by a radix-coordinate block. -/
def outputRadixScratch : List (Fin VV) :=
  [bI,bPw,bQu,bJk,bDig,bTmp,bKey,t3,t5,t6,t7,t8,t9]

/-- `sec:walks`, paper/paper.tex and `prop:time`: exact coordinate emission costs linearly many binary operations
in the coordinate count and radix height, with no padded field census. -/
theorem outputRadix_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (q t D B key0 Λ : ℕ) (hq : 1 ≤ q)
    (hQ : a.env lQ = q) (hT : a.env lT = t) (hD : a.env kD = D) (hB : a.env kB2 = B) (hP : a.env bPw = q ^ D)
    (hK : a.env bKey = key0) (hqD : 2 * q ^ D ≤ 2 ^ C.Wd) (hDW : D < 2 ^ C.Wd) (hqB : q ≤ B)
    (hkey : (key0 + 1) * B ^ D ≤ 2 ^ C.Wd) (hΛ : natBitLength q ≤ Λ)
    :
    Hs C outputRadix a (D * (40 * Λ + 60 + 4) + 4) (fun e => e.out = a.out ++ (digs q t D).flatMap natWord ∧
      e.env bKey = hfold B key0 (digs q t D) ∧ SameOutput a e ∧ Cst e ∧ Fr a e outputRadixScratch) := by
  have hqpos : 0 < q := by omega
  have hdl : ∀ x ∈ digs q t D, x < B := by
    intro x hx; unfold digs at hx; simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx; exact lt_of_lt_of_le (Nat.mod_lt _ hqpos) hqB
  let I : ℕ → DS VV MM → Prop := fun i e => e.env bPw = q ^ (D - i) ∧ e.env bKey = hfold B key0 ((digs q t D).take i) ∧
    e.out = a.out ++ ((digs q t D).take i).flatMap natWord ∧ SameOutput a e ∧ Cst e ∧ Fr a e outputRadixScratch
  refine Hs.mono (forS_spec' (C := C) bI kD (by decide) outputDigit a D hDW I (40 * Λ + 60)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, i3, i4.trans (SameOutput.set _ _ _),
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i5.z, by rw [DS.set_env_ne _ _ (by decide)]; exact i5.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact i5.two⟩, Fr.trans i6 (Fr.set e v (by decide))⟩)
    ⟨by rw [hP]; simp, by rw [hK]; simp [hfold], by simp, SameOutput.refl _, hc, Fr.refl _ _⟩ hD ?_) le_rfl ?_
  · intro i hi e ⟨i1, i2, i3, i4, i5, i6⟩ hei hem
    have eQ : e.env lQ = q := by rw [i6 lQ (by decide)]; exact hQ
    have eT : e.env lT = t := by rw [i6 lT (by decide)]; exact hT
    have eB : e.env kB2 = B := by rw [i6 kB2 (by decide)]; exact hB
    have hpw : q ^ (D - i) = q ^ (D - 1 - i) * q := by rw [← pow_succ]; congr 1; omega
    have hpwle : q ^ (D - i) ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    have hpw1 : 0 < q ^ (D - 1 - i) := Nat.pow_pos hqpos
    have hq1 : q ≤ q ^ D := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    set dg := t / q ^ (D - 1 - i) % q with hdg
    have hdgq : dg < q := Nat.mod_lt _ hqpos
    have htk := digs_take q t D i hi
    rw [← hdg] at htk
    have hlt := foldl_lt B ((digs q t D).take (i + 1)) key0 (fun x hx => hdl x (List.mem_of_mem_take hx))
    have hlen : ((digs q t D).take (i + 1)).length = i + 1 := by simp [digs]; omega
    rw [hlen] at hlt
    have hBi : B ^ (i + 1) ≤ B ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    have hkeyW : hfold B key0 ((digs q t D).take (i + 1)) < 2 ^ C.Wd := by
      have := Nat.mul_le_mul_left (key0 + 1) hBi; omega
    rw [htk, hfold_snoc] at hkeyW
    apply Hx.hs
    refine Hs.then (hs_dm C bPw lQ bQu bJk e (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [eQ]; omega) (by rw [eQ]; omega)) (fun e1 he1 n1 hn1 => ?_); subst he1
    refine Hs.then (hs_copy C bPw bQu _ (by decide)) (fun e2 he2 n2 hn2 => ?_); subst he2
    have v2 : ((((e.set bQu (e.env bPw / e.env lQ)).set bJk (e.env bPw % e.env lQ)).set bPw
        (((e.set bQu (e.env bPw / e.env lQ)).set bJk (e.env bPw % e.env lQ)).env bQu)).env bPw) = q ^ (D - 1 - i) := by
      vsimp [i1, eQ, hpw]; exact Nat.mul_div_cancel _ hqpos
    have hpw2 : q ^ (D - 1 - i) ≤ q ^ D := Nat.pow_le_pow_right hqpos (by omega)
    refine Hs.then (hs_dm C lT bPw bQu bJk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [v2]; exact hpw1) (by rw [v2]; omega)) (fun e3 he3 n3 hn3 => ?_); subst he3
    refine Hs.then (hs_dm C bQu lQ bJk bDig _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by vsimp [eQ]; omega) (by vsimp [eQ]; omega)) (fun e4 he4 n4 hn4 => ?_)
    have hdiv : e.env bPw / q = q ^ (D - 1 - i) := by rw [i1, hpw]; exact Nat.mul_div_cancel _ hqpos
    have v4 : e4.env bDig = dg := by rw [he4, hdg]; vsimp [eQ, eT, hdiv]
    have s4 : SameOutput e e4 := by
      rw [he4]
      exact (SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans
        ((SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans (SameOutput.set _ _ _))))))
    have c4 : Cst e4 := by rw [he4]; exact ⟨by vsimp [i5.z], by vsimp [i5.one], by vsimp [i5.two]⟩
    have hdgW : dg < 2 ^ C.Wd := by omega
    refine Hs.then (emitOutputNat_run C bDig (by decide) e4 c4 hW dg v4 hdgW) (fun e5 ⟨k5, s5, c5, f5⟩ n5 hn5 => ?_)
    have e5K : e5.env bKey = hfold B key0 ((digs q t D).take i) := by
      rw [f5 bKey (by decide), he4]; vsimp [i2]
    have e5B : e5.env kB2 = B := by rw [f5 kB2 (by decide), he4]; vsimp [eB]
    have e5D : e5.env bDig = dg := by rw [f5 bDig (by decide)]; exact v4
    refine Hs.then (hs_mul C bKey kB2 bTmp e5 (by decide) (by decide) (by decide) (by rw [e5K, e5B]; omega))
      (fun e6 he6 n6 hn6 => ?_); subst he6
    refine Hs.then (hs_copy C bKey bTmp _ (by decide)) (fun e7 he7 n7 hn7 => ?_); subst he7
    refine Hs.last (hs_add C bKey bDig _ (by decide) (by vsimp [e5K, e5B, e5D]; omega)) (fun e8 he8 n8 hn8 => ?_)
    subst he8
    have fr4 : Fr e e4 outputRadixScratch := by
      rw [he4]
      exact Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.set _ _ (by decide)))))))
    have hfr : Fr e e5 outputRadixScratch := Fr.trans fr4 (Fr.weaken f5 (by decide))
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide),
        f5 bPw (by decide), he4, show D - (i + 1) = D - 1 - i by omega]
      vsimp [eQ, hdiv]
    · rw [htk, hfold_snoc]; vsimp [e5K, e5B, e5D]
    · rw [htk]; simp only [DS.set]; rw [k5, he4]; simp [i3, List.flatMap_append]
    · exact i4.trans (s4.trans (s5.trans ((SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans (SameOutput.set _ _ _)))))
    · exact ⟨by vsimp [c5.z], by vsimp [c5.one], by vsimp [c5.two]⟩
    · exact Fr.trans i6 (Fr.trans hfr (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.set _ _ (by decide)))))
    · vsimp [f5 bI (by decide), he4, hei]
    · vsimp [f5 kD (by decide), he4, hem]
    · have hnb : natBitLength dg ≤ natBitLength q := by
        unfold natBitLength
        have := Nat.log_mono_right (b := 2) (le_of_lt hdgq)
        omega
      omega
  · rintro e ⟨⟨i1, i2, i3, i4, i5, i6⟩, _, _⟩
    have : (digs q t D).take D = digs q t D := List.take_of_length_le (by simp [digs])
    rw [this] at i2 i3
    exact ⟨i3, i2, i4, i5, i6⟩


end NearQuarticWires.StageCert
