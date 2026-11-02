import Proof.Quartic.Reconstruct.PrintNest2

/-!
# The loops of the printing stage: digit vectors, patterns and parts

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the tables run over the parts `s`, the patterns
`σ`, the digit vectors `δ`, the primes and the residue vectors).

`d1S`, `d0S`: the digit-vector counters of the two circuits; `sigS`: the pattern counter; `partS`: the part
(`partS_spec`). The output is the list of requests, outermost the part.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- The parameters of the loop nest. -/
structure NP where
  ps : List ℕ
  pb : ℕ
  Pm : ℕ
  A0 : ℕ
  A1 : ℕ

/-- The facts of the loop nest. -/
structure NPok (rp : RP) (np : NP) (a0 : DS VV MM) (W : ℕ) : Prop where
  ps : a0.ram sPr = np.ps
  npc : a0.env kPc = np.ps.length
  pb : a0.env kPair = np.pb
  pm : ∀ p ∈ np.ps, p ≤ np.Pm
  pm1 : 1 ≤ np.Pm
  pmW : np.Pm < 2 ^ W
  pmb : natBitLength np.Pm ≤ rp.ℓ
  nW : np.ps.length < 2 ^ W
  a0v : a0.env qA0 = np.A0
  a1v : a0.env qA1 = np.A1
  c256 : a0.env q256 = 256
  A0W : np.A0 < 2 ^ W
  A1W : np.A1 < 2 ^ W
  hA0 : np.A0 = rp.B ^ rp.J1
  hJ1 : 1 ≤ rp.J1
  sbb : natBitLength 1 ≤ rp.ℓ

/-- The cost of the prime loop. -/
def primeCost (rp : RP) (np : NP) : ℕ :=
  np.ps.length * ((np.ps.length + 1 + (np.ps.length * 5 + 4) + 3) + 3 + resCost rp np.Pm + 2 + 4) + 4

/-- The words of one digit-vector pair. -/
def dWord (rp : RP) (np : NP) (sb is x0 x1 : ℕ) : List Bool :=
  np.ps.flatMap fun p => primeWord rp np.pb sb is x0 x1 p

/-- The second digit vectors. -/
def d1S : St VV MM := forS qX1 qA1 primeS

/-- The variables written by the digit loops. -/
def d1T : List (Fin VV) := primeT ++ [qX1]

theorem d1S_spec (rp : RP) (np : NP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hnp : NPok rp np a0 C.Wd)
    (hB : 0 < rp.B) (b : DS VV MM) (hb : RS a0 b) (sb is x0 : ℕ) (hsb : b.env qSb = sb) (his : b.env qSig = is)
    (hx0 : b.env qX0 = x0) (hsbb : natBitLength sb ≤ rp.ℓ) :
    Hs C d1S b (np.A1 * (primeCost rp np + 4) + 4)
      (fun c => OutMoved b c ((List.range np.A1).flatMap fun x1 => dWord rp np sb is x0 x1) d1T ∧ RS a0 c ∧
        ∀ y ∈ [qSb, qSig, qX0], c.env y = b.env y) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c d1T
  have hset : ∀ k c v, Inv k c → Inv k (c.set qX1 v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qX1 (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qX1 qA1 (by decide) primeS np.A1 (primeCost rp np) (fun x1 => dWord rp np sb is x0 x1) Inv hset
    ?_ b ⟨hb, Fr.refl b d1T⟩ (by rw [hb.vars qA1 (by decide), hnp.a1v]) hnp.A1W).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      fun y hy => c2 y (by revert hy y; decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ d1T → c.env y = b.env y := h2
  refine (primeS_spec rp a0 hrp hB np.ps np.pb np.Pm hnp.ps hnp.npc hnp.pb hnp.pm hnp.pm1 hnp.pmW hnp.pmb hnp.nW c h1
    sb is x0 k (by rw [kv qSb (by decide), hsb]) (by rw [kv qSig (by decide), his]) (by rw [kv qX0 (by decide), hx0])
    hik hsbb).mono le_rfl ?_
  intro d ⟨m, rs, keep⟩
  refine ⟨⟨rs, Fr.trans h2 (m.fr.weaken (fun y hy => List.mem_append_left _ hy))⟩,
    by rw [keep qX1 (by simp), hik], by rw [m.fr qA1 (by decide), hnk], m.out⟩

/-- The first digit vectors. -/
def d0S : St VV MM := forS qX0 qA0 d1S

/-- The variables written by `d0S`. -/
def d0T : List (Fin VV) := d1T ++ [qX0]

/-- The cost of `d1S`. -/
def d1Cost (rp : RP) (np : NP) : ℕ := np.A1 * (primeCost rp np + 4) + 4

theorem d0S_spec (rp : RP) (np : NP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hnp : NPok rp np a0 C.Wd)
    (b : DS VV MM) (hb : RS a0 b) (sb is : ℕ) (hsb : b.env qSb = sb) (his : b.env qSig = is)
    (hsbb : natBitLength sb ≤ rp.ℓ) :
    Hs C d0S b (np.A0 * (d1Cost rp np + 4) + 4)
      (fun c => OutMoved b c ((List.range np.A0).flatMap fun x0 => (List.range np.A1).flatMap fun x1 =>
        dWord rp np sb is x0 x1) d0T ∧ RS a0 c ∧ ∀ y ∈ [qSb, qSig], c.env y = b.env y) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c d0T
  have hset : ∀ k c v, Inv k c → Inv k (c.set qX0 v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qX0 (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qX0 qA0 (by decide) d1S np.A0 (d1Cost rp np)
    (fun x0 => (List.range np.A1).flatMap fun x1 => dWord rp np sb is x0 x1) Inv hset
    ?_ b ⟨hb, Fr.refl b d0T⟩ (by rw [hb.vars qA0 (by decide), hnp.a0v]) hnp.A0W).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      fun y hy => c2 y (by revert hy y; decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ d0T → c.env y = b.env y := h2
  have hB : 0 < rp.B := by
    rcases Nat.eq_zero_or_pos rp.B with h | h
    · rw [hnp.hA0, h, zero_pow (by have := hnp.hJ1; omega)] at hk; omega
    · exact h
  refine (d1S_spec rp np a0 hrp hnp hB c h1 sb is k (by rw [kv qSb (by decide), hsb])
    (by rw [kv qSig (by decide), his]) hik hsbb).mono le_rfl ?_
  intro d ⟨m, rs, keep⟩
  refine ⟨⟨rs, Fr.trans h2 (m.fr.weaken (fun y hy => List.mem_append_left _ hy))⟩,
    by rw [keep qX0 (by simp), hik], by rw [m.fr qA0 (by decide), hnk], m.out⟩

/-- The patterns. -/
def sigS : St VV MM := forS qSig q256 d0S

/-- The variables written by `sigS`. -/
def sigT : List (Fin VV) := d0T ++ [qSig]

/-- The cost of `d0S`. -/
def d0Cost (rp : RP) (np : NP) : ℕ := np.A0 * (d1Cost rp np + 4) + 4

/-- The words of one pattern. -/
def sigWord (rp : RP) (np : NP) (sb is : ℕ) : List Bool :=
  (List.range np.A0).flatMap fun x0 => (List.range np.A1).flatMap fun x1 => dWord rp np sb is x0 x1

theorem sigS_spec (rp : RP) (np : NP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hnp : NPok rp np a0 C.Wd)
    (b : DS VV MM) (hb : RS a0 b) (sb : ℕ) (hsb : b.env qSb = sb) (hsbb : natBitLength sb ≤ rp.ℓ) :
    Hs C sigS b (256 * (d0Cost rp np + 4) + 4)
      (fun c => OutMoved b c ((List.range 256).flatMap fun is => sigWord rp np sb is) sigT ∧ RS a0 c ∧
        c.env qSb = b.env qSb) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c sigT
  have hset : ∀ k c v, Inv k c → Inv k (c.set qSig v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qSig (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qSig q256 (by decide) d0S 256 (d0Cost rp np) (fun is => sigWord rp np sb is) Inv hset
    ?_ b ⟨hb, Fr.refl b sigT⟩ (by rw [hb.vars q256 (by decide), hnp.c256]) (by
      have := hrp.h512; omega)).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      c2 qSb (by decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ sigT → c.env y = b.env y := h2
  refine (d0S_spec rp np a0 hrp hnp c h1 sb k (by rw [kv qSb (by decide), hsb]) hik hsbb).mono le_rfl ?_
  intro d ⟨m, rs, keep⟩
  refine ⟨⟨rs, Fr.trans h2 (m.fr.weaken (fun y hy => List.mem_append_left _ hy))⟩,
    by rw [keep qSig (by simp), hik], by rw [m.fr q256 (by decide), hnk], m.out⟩

/-- The bit of the part: `1` for the first part. -/
def setSbS : St VV MM := .ite (.eq qS vZ) (.op (.copy qSb v1)) (.op (.zero qSb))

/-- The parts. -/
def partS : St VV MM := forS qS v2 (.seq setSbS sigS)

/-- The variables written by `partS`. -/
def partT : List (Fin VV) := sigT ++ [qS, qSb]

/-- The cost of `sigS`. -/
def sigCost (rp : RP) (np : NP) : ℕ := 256 * (d0Cost rp np + 4) + 4

/-- **The loop nest**: the requests of both parts. -/
theorem partS_spec (rp : RP) (np : NP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hnp : NPok rp np a0 C.Wd)
    (b : DS VV MM) (hb : RS a0 b) :
    Hs C partS b (2 * (sigCost rp np + 3 + 4) + 4)
      (fun c => OutMoved b c ((List.range 2).flatMap fun iS =>
        (List.range 256).flatMap fun is => sigWord rp np (if iS = 0 then 1 else 0) is) partT ∧ RS a0 c) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c partT
  have hset : ∀ k c v, Inv k c → Inv k (c.set qS v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qS (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qS v2 (by decide) _ 2 (sigCost rp np + 3)
    (fun iS => (List.range 256).flatMap fun is => sigWord rp np (if iS = 0 then 1 else 0) is) Inv hset
    ?_ b ⟨hb, Fr.refl b partT⟩ hb.cst.two (by have := hrp.h512; omega)).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have hsbt : Hs C setSbS c 2 (fun d => d.env qSb = (if k = 0 then 1 else 0) ∧ RS a0 d ∧ Fr c d [qSb] ∧
      d.out = c.out) := by
    refine Hs.ite (t := 1) (show qS ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have h0 : k = 0 := by simpa [Cnd.eval, hik, h1.cst.z] using he
      refine Hs.mono (hs_copy C qSb v1 c (by decide)) le_rfl ?_
      rintro d rfl
      exact ⟨by rw [DS.set_env_self, h1.cst.one, if_pos h0], h1.set qSb (by decide) _, Fr.set c _ (by decide), rfl⟩
    · have h0 : k ≠ 0 := by simpa [Cnd.eval, hik, h1.cst.z] using he
      refine Hs.mono (hs_zero C qSb c) le_rfl ?_
      rintro d rfl
      exact ⟨by rw [DS.set_env_self, if_neg h0], h1.set qSb (by decide) _, Fr.set c _ (by decide), rfl⟩
  refine Hx.hs (Hs.then hsbt (fun d1 ⟨s1, r1, f1, o1⟩ n1 hn1 => ?_))
  have hsbb : natBitLength (if k = 0 then 1 else 0) ≤ rp.ℓ := by
    split
    · exact hnp.sbb
    · have := hnp.sbb; simp [natBitLength] at this ⊢; omega
  refine Hs.last (sigS_spec rp np a0 hrp hnp d1 r1 _ s1 hsbb) (fun d ⟨m, rs, keep⟩ n2 hn2 => ⟨⟨⟨rs, ?_⟩, ?_, ?_, ?_⟩, ?_⟩)
  · exact Fr.trans h2 (Fr.trans (f1.weaken (by decide)) (m.fr.weaken (fun y hy => List.mem_append_left _ hy)))
  · rw [m.fr qS (by decide), f1 qS (by decide), hik]
  · rw [m.fr v2 (by decide), f1 v2 (by decide), hnk]
  · rw [m.out, o1]
  · unfold sigCost; omega

end NearQuarticWires.Reconstruct
