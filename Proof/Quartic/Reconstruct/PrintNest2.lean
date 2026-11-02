import Proof.Quartic.Reconstruct.PrintNest

/-!
# The loops of the printing stage: the primes

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the tables run over the primes `p ∈ 𝒫` and the
residue vectors modulo `p`).

`res0S`: all residue vectors of one prime (`res0S_spec`); `getPrimeS`: read the `k`-th prime of the store `sPr`
(`getPrimeS_spec`); `primeS`: all primes (`primeS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- All residue vectors of one prime. -/
def res0S : St VV MM := forS qR0 qP res1S

theorem res0S_spec (rp : RP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hB : 0 < rp.B) (b : DS VV MM) (hb : RS a0 b)
    (sb is x0 x1 p Q : ℕ) (hsb : b.env qSb = sb) (his : b.env qSig = is) (hx0 : b.env qX0 = x0)
    (hx1 : b.env qX1 = x1) (hp : b.env qP = p) (hQ : b.env qQn = Q) (hpW : p < 2 ^ C.Wd) (hQW : Q < 2 ^ C.Wd)
    (hbits : ∀ v ∈ [sb, p, Q], natBitLength v ≤ rp.ℓ) :
    Hs C res0S b (p * ((Q * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4) + 4) + 4)
      (fun c => OutMoved b c ((List.range p).flatMap fun y0 => (List.range Q).flatMap fun y1 =>
        rpWord rp sb is x0 x1 p y0 y1) resT ∧ RS a0 c ∧ ∀ y ∈ [qSb, qSig, qX0, qX1, qP, qQn], c.env y = b.env y) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c resT
  have hset : ∀ k c v, Inv k c → Inv k (c.set qR0 v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qR0 (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qR0 qP (by decide) res1S p (Q * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4)
    (fun y0 => (List.range Q).flatMap fun y1 => rpWord rp sb is x0 x1 p y0 y1) Inv hset ?_ b ⟨hb, Fr.refl b resT⟩
    hp hpW).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      fun y hy => c2 y (by revert hy y; decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ resT → c.env y = b.env y := h2
  have hk' : natBitLength k ≤ rp.ℓ := (natBitLength_mono hk.le).trans (hbits p (by simp))
  refine (res1S_spec rp a0 hrp hB c h1 sb is x0 x1 p k Q (by rw [kv qSb (by decide), hsb])
    (by rw [kv qSig (by decide), his]) (by rw [kv qX0 (by decide), hx0]) (by rw [kv qX1 (by decide), hx1])
    (by rw [kv qP (by decide), hp]) hik (by rw [kv qQn (by decide), hQ]) hQW (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hbits _ (by simp)
      · exact hbits _ (by simp)
      · exact hk'
      · exact hbits _ (by simp))).mono le_rfl ?_
  intro d ⟨m, rs, keep⟩
  refine ⟨⟨rs, Fr.trans h2 (m.fr.weaken (fun y hy => by
      simp only [res1T, resT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))⟩,
    by rw [keep qR0 (by simp), hik], by rw [keep qP (by simp), hnk], m.out⟩

/-- A counter for reading the primes. -/
def qk2 : Fin VV := ⟨45, by decide⟩

/-- Read the prime number `qIp` of the store `sPr` into `qP`. -/
def getPrimeS : St VV MM := .seq (.op (.rwM sPr)) (.seq (forS qk2 qIp (.op (.rdM sPr qP))) (.op (.rdM sPr qP)))

theorem getPrimeS_spec (a0 : DS VV MM) (ps : List ℕ) (hps : a0.ram sPr = ps) (b : DS VV MM) (hb : RS a0 b) (k : ℕ)
    (hk : b.env qIp = k) (hkl : k < ps.length) (hW : ps.length < 2 ^ C.Wd) :
    Hs C getPrimeS b (ps.length + 1 + (k * (1 + 4) + 4) + 1 + 2)
      (fun c => c.env qP = ps.getD k 0 ∧ OutMoved b c [] [qk2, qP] ∧ RS a0 c) := by
  refine Hx.hs (Hs.then (rwM_spec' sPr b hb.rcok [qk2, qP]) (fun b0 ⟨o0, r0, e0⟩ n0 hn0 => ?_))
  have rs0 : RS a0 b0 := hb.step o0 ⟨by rw [e0]; exact hb.cst.z, by rw [e0]; exact hb.cst.one, by rw [e0]; exact hb.cst.two⟩
    (by decide)
  let Inv : ℕ → DS VV MM → Prop := fun j c => RS a0 c ∧ c.rc sPr = j ∧ OutMoved b c [] [qk2, qP]
  have hset : ∀ j c v, Inv j c → Inv j (c.set qk2 v) := fun j c v ⟨h1, h2, h3⟩ =>
    ⟨h1.set qk2 (by decide) v, h2, h3.set v (by decide)⟩
  refine Hs.then (forS_spec qk2 qIp (by decide) (.op (.rdM sPr qP)) k 1 (fun _ => []) Inv hset ?_ b0
    ⟨rs0, r0, o0⟩ (by rw [e0, hk]) (by omega)) (fun b1 ⟨⟨h1, h2, h3⟩, _, _⟩ n1 hn1 => ?_)
  · intro j hj c ⟨h1, h2, h3⟩ hjj hkj
    have hl : c.rc sPr < (c.ram sPr).length := by rw [h2, h1.ram, hps]; omega
    refine (rdM_spec' sPr qP c hl h1.rcok).mono le_rfl (fun d ⟨x1, x2, x3⟩ => ⟨⟨h1.step x3
      (x3.cst h1.cst (by decide)) (by decide), by rw [x2, h2], ?_⟩, by rw [x3.fr qk2 (by decide), hjj],
      by rw [x3.fr qIp (by decide), hkj], by rw [x3.out, List.append_nil]⟩)
    simpa using h3.trans (x3.weaken (by decide))
  have hl : b1.rc sPr < (b1.ram sPr).length := by rw [h2, h1.ram, hps]; exact hkl
  refine Hs.last (rdM_spec' sPr qP b1 hl h1.rcok) (fun c ⟨x1, x2, x3⟩ n2 hn2 => ⟨⟨?_, ?_, ?_⟩, ?_⟩)
  · rw [x1, h1.ram, hps, h2]
  · simpa using h3.trans (x3.weaken (by decide))
  · exact h1.step x3 (x3.cst h1.cst (by decide)) (by decide)
  · have := hb.rcok sPr
    rw [hb.ram, hps] at this
    have hn1' : n1 ≤ k * (1 + 4) + 4 := hn1
    omega

/-- The number of second residues: `p` for two circuits, `1` otherwise. -/
def setQS : St VV MM := .ite (.eq kPair v1) (.op (.copy qQn qP)) (.op (.copy qQn v1))

/-- The number of second residues of a prime. -/
def resQ (pb p : ℕ) : ℕ := if pb = 1 then p else 1

theorem setQS_spec (b : DS VV MM) (hc : Cst b) (pb p : ℕ) (hpb : b.env kPair = pb) (hp : b.env qP = p) :
    Hs C setQS b 2 (fun c => c.env qQn = resQ pb p ∧ c = b.set qQn (resQ pb p)) := by
  refine Hs.ite (t := 1) (show kPair ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · have h1 : pb = 1 := by simpa [Cnd.eval, hpb, hc.one] using he
    refine Hs.mono (hs_copy C qQn qP b (by decide)) le_rfl ?_
    rintro c rfl
    rw [resQ, if_pos h1, hp]
    exact ⟨DS.set_env_self _ _ _, rfl⟩
  · have h1 : pb ≠ 1 := by simpa [Cnd.eval, hpb, hc.one] using he
    refine Hs.mono (hs_copy C qQn v1 b (by decide)) le_rfl ?_
    rintro c rfl
    rw [resQ, if_neg h1, hc.one]
    exact ⟨DS.set_env_self _ _ _, rfl⟩

/-- All primes. -/
def primeS : St VV MM := forS qIp kPc (.seq getPrimeS (.seq setQS res0S))

/-- The variables written by the prime loop. -/
def primeT : List (Fin VV) := resT ++ [qIp, qk2, qP, qQn]

/-- The cost bound of one residue loop for primes at most `Pm`. -/
def resCost (rp : RP) (Pm : ℕ) : ℕ := Pm * ((Pm * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4) + 4) + 4

/-- The words of all requests of one prime. -/
def primeWord (rp : RP) (pb sb is x0 x1 p : ℕ) : List Bool :=
  (List.range p).flatMap fun y0 => (List.range (resQ pb p)).flatMap fun y1 => rpWord rp sb is x0 x1 p y0 y1

theorem primeS_spec (rp : RP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hB : 0 < rp.B) (ps : List ℕ) (pb Pm : ℕ)
    (hps : a0.ram sPr = ps) (hnp : a0.env kPc = ps.length) (hpb : a0.env kPair = pb)
    (hpm : ∀ p ∈ ps, p ≤ Pm) (hPm1 : 1 ≤ Pm) (hPmW : Pm < 2 ^ C.Wd) (hPmb : natBitLength Pm ≤ rp.ℓ) (hnW : ps.length < 2 ^ C.Wd)
    (b : DS VV MM) (hb : RS a0 b) (sb is x0 x1 : ℕ) (hsb : b.env qSb = sb) (his : b.env qSig = is)
    (hx0 : b.env qX0 = x0) (hx1 : b.env qX1 = x1) (hsbb : natBitLength sb ≤ rp.ℓ) :
    Hs C primeS b (ps.length * ((ps.length + 1 + (ps.length * 5 + 4) + 3) + 3 + resCost rp Pm + 2 + 4) + 4)
      (fun c => OutMoved b c (ps.flatMap fun p => primeWord rp pb sb is x0 x1 p) primeT ∧ RS a0 c ∧
        ∀ y ∈ [qSb, qSig, qX0, qX1], c.env y = b.env y) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c primeT
  have hset : ∀ k c v, Inv k c → Inv k (c.set qIp v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qIp (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qIp kPc (by decide) _ ps.length ((ps.length + 1 + (ps.length * 5 + 4) + 3) + 3 + resCost rp Pm + 2)
    (fun k => primeWord rp pb sb is x0 x1 (ps.getD k 0)) Inv hset ?_ b ⟨hb, Fr.refl b primeT⟩
    (by rw [hb.vars kPc (by decide), hnp]) hnW).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3, getD_range_flatMap], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      fun y hy => c2 y (by revert hy y; decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ primeT → c.env y = b.env y := h2
  set p := ps.getD k 0 with hpdef
  have hpmem : p ∈ ps := by rw [hpdef, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hpP := hpm p hpmem
  refine Hx.hs (Hs.then (getPrimeS_spec a0 ps hps c h1 k hik hk hnW) (fun c1 ⟨gp1, m1, r1⟩ n1 hn1 => ?_))
  refine Hs.then (setQS_spec c1 r1.cst pb p (by rw [r1.vars kPair (by decide), hpb]) gp1)
    (fun c2 ⟨q2, e2⟩ n2 hn2 => ?_)
  have r2 : RS a0 c2 := by rw [e2]; exact r1.set qQn (by decide) _
  have k2 : ∀ y, y ∉ [qk2, qP, qQn] → c2.env y = c.env y := fun y hy => by
    rw [e2, DS.set_env_ne _ _ (fun h => hy (by rw [h]; simp)), m1.fr y (fun h => hy (by simp at h ⊢; tauto))]
  have hQ : resQ pb p ≤ Pm := by unfold resQ; split <;> omega
  refine Hs.last (res0S_spec rp a0 hrp hB c2 r2 sb is x0 x1 p (resQ pb p)
    (by rw [k2 qSb (by decide), kv qSb (by decide), hsb]) (by rw [k2 qSig (by decide), kv qSig (by decide), his])
    (by rw [k2 qX0 (by decide), kv qX0 (by decide), hx0]) (by rw [k2 qX1 (by decide), kv qX1 (by decide), hx1])
    (by rw [e2, DS.set_env_ne _ _ (by decide), gp1]) q2 (by omega) (by omega) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hsbb
      · exact (natBitLength_mono hpP).trans hPmb
      · exact (natBitLength_mono hQ).trans hPmb)) (fun d ⟨m, rs, keep⟩ n3 hn3 => ⟨⟨⟨rs, ?_⟩, ?_, ?_, ?_⟩, ?_⟩)
  · intro y hy
    rw [m.fr y (fun h => hy (by simp only [resT, primeT, List.mem_append] at h ⊢; tauto)),
      k2 y (fun h => hy (by simp only [primeT, List.mem_append, List.mem_cons] at h ⊢; tauto)), kv y hy]
  · rw [m.fr qIp (by decide), k2 qIp (by decide), hik]
  · rw [m.fr kPc (by decide), k2 kPc (by decide), hnk]
  · rw [m.out, e2, DS.set_out, m1.out, List.append_nil]
    rfl
  · have hr : (p * ((resQ pb p * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4) + 4) + 4) ≤ resCost rp Pm := by
      unfold resCost
      have := Nat.mul_le_mul_right (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) hQ
      have := Nat.mul_le_mul hpP (show (resQ pb p * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4) + 4 ≤
        (Pm * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4) + 4 by omega)
      omega
    have hk5 : k * (1 + 4) ≤ ps.length * 5 := by nlinarith
    omega

end NearQuarticWires.Reconstruct
