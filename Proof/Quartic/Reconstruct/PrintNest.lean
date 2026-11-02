import Proof.Quartic.Reconstruct.PrintReq

/-!
# The loops of the printing stage: the residues

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the tables run over the residue vectors `ρ_Y`).

`RS a₀ b`: the state `b` keeps the stores, the input cursor and the constants of the request phase of `a₀`.
`resLoopS` writes the requests of all residue vectors `(y₀, y₁)` of one prime (`resLoopS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- The number of second residues. -/
def qQn : Fin VV := ⟨39, by decide⟩
/-- The prime counter. -/
def qIp : Fin VV := ⟨40, by decide⟩
/-- The part counter. -/
def qS : Fin VV := ⟨41, by decide⟩
/-- The constant `256`. -/
def q256 : Fin VV := ⟨42, by decide⟩
/-- The number of digit vectors of the first circuit. -/
def qA0 : Fin VV := ⟨43, by decide⟩
/-- The number of digit vectors of the second circuit. -/
def qA1 : Fin VV := ⟨44, by decide⟩

/-- The constants of the request phase. -/
def constVars : List (Fin VV) := [q8, q128, qLen, qTop, qBase, qJp1, qO0, qO1, kPL, kPc, q256, qA0, qA1, kPair]

/-- The state keeps the stores, the input cursor and the constants of `a₀`. -/
structure RS (a0 b : DS VV MM) : Prop where
  cst : Cst b
  rcok : ∀ m, b.rc m ≤ (b.ram m).length
  ram : b.ram = a0.ram
  ip : b.ip = a0.ip
  kin : b.kin = a0.kin
  kout : b.kout = a0.kout
  kc : b.kc = a0.kc
  vars : ∀ x ∈ constVars, b.env x = a0.env x

theorem RS.step {a0 b c : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : RS a0 b) (m : OutMoved b c w T)
    (hc : Cst c) (hT : ∀ x ∈ constVars, x ∉ T) : RS a0 c :=
  ⟨hc, m.rcok, m.ram.trans h.ram, m.ip.trans h.ip, m.kin.trans h.kin, m.kout.trans h.kout, m.kc.trans h.kc,
    fun x hx => (m.fr x (hT x hx)).trans (h.vars x hx)⟩

theorem RS.set {a0 b : DS VV MM} (h : RS a0 b) (x : Fin VV) (hx : x ∉ constVars ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2)
    (v : ℕ) : RS a0 (b.set x v) :=
  ⟨Cst.of_fr h.cst (Fr.set b v (List.mem_singleton_self x)) (by
    simp only [List.mem_singleton]; exact ⟨fun e => hx.2.1 e.symm, fun e => hx.2.2.1 e.symm, fun e => hx.2.2.2 e.symm⟩),
    h.rcok, h.ram, h.ip, h.kin, h.kout, h.kc, fun y hy => by
      rw [DS.set_env_ne _ _ (fun e => hx.1 (by rw [← e]; exact hy))]; exact h.vars y hy⟩

/-- The data of the request phase. -/
structure RP where
  pw : List Bool
  u : List Bool
  B : ℕ
  J1 : ℕ
  o0 : ℕ
  o1 : ℕ
  len : ℕ
  ℓ : ℕ

/-- The constants and the bounds of the request phase in `a₀`. -/
structure RPok (rp : RP) (a0 : DS VV MM) (W : ℕ) : Prop where
  c8 : a0.env q8 = 8
  c128 : a0.env q128 = 128
  len : a0.env qLen = rp.len
  top : a0.env qTop = rp.B ^ (rp.J1 - 1)
  base : a0.env qBase = rp.B
  jp1 : a0.env qJp1 = rp.J1
  o0 : a0.env qO0 = rp.o0
  o1 : a0.env qO1 = rp.o1
  pl : a0.env kPL = rp.pw.length
  sp : a0.ram sP = rp.pw.map Bool.toNat
  sg : a0.ram sG = (frame rp.u).map Bool.toNat
  hW : rp.ℓ + 3 ≤ W
  hBW : 2 * rp.B ^ rp.J1 ≤ 2 ^ W
  hJW : rp.J1 < 2 ^ W
  h512 : 512 ≤ 2 ^ W
  hPW : rp.pw.length < 2 ^ W
  bits : ∀ v ∈ [8, rp.len, 2, rp.B + rp.o0, rp.B + rp.o1], natBitLength v ≤ rp.ℓ

/-- The word of one request of the phase. -/
def rpWord (rp : RP) (sb is x0 x1 p y0 y1 : ℕ) : List Bool :=
  reqWord (printIdxW sb is p rp.len rp.B rp.J1 x0 x1 rp.o0 rp.o1 y0 y1) rp.pw rp.u

/-- The second residues of one prime. -/
def res1S : St VV MM := forS qR1 qQn reqS

/-- The variables written by the loop of the second residues. -/
def res1T : List (Fin VV) := reqT ++ [qR1]

/-- The variables written by the residue loops. -/
def resT : List (Fin VV) := reqT ++ [qR1, qR0]

theorem res1S_spec (rp : RP) (a0 : DS VV MM) (hrp : RPok rp a0 C.Wd) (hB : 0 < rp.B) (b : DS VV MM) (hb : RS a0 b)
    (sb is x0 x1 p y0 Q : ℕ) (hsb : b.env qSb = sb) (his : b.env qSig = is) (hx0 : b.env qX0 = x0)
    (hx1 : b.env qX1 = x1) (hp : b.env qP = p) (hy0 : b.env qR0 = y0) (hQ : b.env qQn = Q) (hQW : Q < 2 ^ C.Wd)
    (hbits : ∀ v ∈ [sb, p, y0, Q], natBitLength v ≤ rp.ℓ) :
    Hs C res1S b (Q * (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length + 4) + 4)
      (fun c => OutMoved b c ((List.range Q).flatMap fun y1 => rpWord rp sb is x0 x1 p y0 y1) res1T ∧ RS a0 c ∧
        ∀ y ∈ [qSb, qSig, qX0, qX1, qP, qR0, qQn], c.env y = b.env y) := by
  let Inv : ℕ → DS VV MM → Prop := fun _ c => RS a0 c ∧ Fr b c res1T
  have hset : ∀ k c v, Inv k c → Inv k (c.set qR1 v) := fun k c v ⟨h1, h2⟩ =>
    ⟨h1.set qR1 (by decide) v, Fr.trans h2 (Fr.set c v (by decide))⟩
  refine (forS_spec qR1 qQn (by decide) reqS Q (reqCost rp.ℓ rp.J1 rp.pw.length rp.u.length)
    (fun y1 => rpWord rp sb is x0 x1 p y0 y1) Inv hset ?_ b ⟨hb, Fr.refl b res1T⟩ hQ hQW).mono le_rfl
    (fun c ⟨⟨c1, c2⟩, _, c3⟩ => ⟨⟨by rw [c3], c1.ip.trans hb.ip.symm, c1.ram.trans hb.ram.symm,
      c1.kin.trans hb.kin.symm, c1.kout.trans hb.kout.symm, c1.kc.trans hb.kc.symm, c2, c1.rcok⟩, c1,
      fun y hy => c2 y (by revert hy y; decide)⟩)
  intro k hk c ⟨h1, h2⟩ hik hnk
  have kv : ∀ y, y ∉ res1T → c.env y = b.env y := h2
  have hk' : natBitLength k ≤ rp.ℓ := (natBitLength_mono hk.le).trans (hbits Q (by simp))
  refine (reqS_spec c h1.cst h1.rcok sb is p rp.len rp.B rp.J1 x0 x1 rp.o0 rp.o1 y0 k
    (by rw [kv qSb (by decide), hsb]) (by rw [h1.vars q8 (by decide), hrp.c8])
    (by rw [h1.vars q128 (by decide), hrp.c128]) (by rw [kv qSig (by decide), his])
    (by rw [kv qP (by decide), hp]) (by rw [h1.vars qLen (by decide), hrp.len])
    (by rw [h1.vars qTop (by decide), hrp.top]) (by rw [h1.vars qBase (by decide), hrp.base])
    (by rw [h1.vars qJp1 (by decide), hrp.jp1]) (by rw [kv qX0 (by decide), hx0]) (by rw [kv qX1 (by decide), hx1])
    (by rw [h1.vars qO0 (by decide), hrp.o0]) (by rw [h1.vars qO1 (by decide), hrp.o1])
    (by rw [kv qR0 (by decide), hy0]) hik hB rp.ℓ (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbits _ (by simp)
      · exact hrp.bits _ (by simp)
      · exact hbits _ (by simp)
      · exact hrp.bits _ (by simp)
      · exact hrp.bits _ (by simp)
      · exact hrp.bits _ (by simp)
      · exact hrp.bits _ (by simp)
      · exact hbits _ (by simp)
      · exact hk') hrp.hW hrp.hBW hrp.hJW hrp.h512 rp.pw rp.u (by rw [h1.ram, hrp.sp])
    (by rw [h1.vars kPL (by decide), hrp.pl]) hrp.hPW (by rw [h1.ram, hrp.sg])).mono le_rfl ?_
  intro d ⟨m, cd⟩
  refine ⟨⟨h1.step m cd (by decide), Fr.trans h2 (m.fr.weaken (fun y hy => List.mem_append_left _ hy))⟩,
    by rw [m.fr qR1 (by decide), hik], by rw [m.fr qQn (by decide), hnk], m.out⟩

end NearQuarticWires.Reconstruct
