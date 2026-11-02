import Proof.Quartic.StageGamma.BankCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the actual
Gaussian nullity is retained in a binary source variable. -/
def gammaExponent : Fin VV := ⟨63, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the actual
Gaussian consistency flag is retained independently of the nullity. -/
def gammaFlag : Fin VV := ⟨64, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the exact
read set of the compact reply decoder. -/
def replyScratch : List (Fin VV) := [gammaExponent, gammaFlag, t0]

/-- `cor:conditional`, paper/paper.tex: decoding
changes only the reply cursor and its explicitly named binary registers. -/
structure ReplyFrame (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout

/-- `cor:conditional`, paper/paper.tex: a reply
register change preserves every original input and cached source. -/
theorem ReplyFrame.set (a : DS VV MM) (x : Fin VV) (v : ℕ) :
    ReplyFrame a (a.set x v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `cor:conditional`, paper/paper.tex: composition
of actual reply-source frame preservation. -/
theorem ReplyFrame.trans {a b d : DS VV MM} (h : ReplyFrame a b) (g : ReplyFrame b d) :
    ReplyFrame a d := ⟨g.ip.trans h.ip, g.out.trans h.out, g.ram.trans h.ram,
      g.rc.trans h.rc, g.kin.trans h.kin, g.kout.trans h.kout⟩

/-- `cor:conditional`, paper/paper.tex: the unary
prefix's last read is its zero delimiter, including nullity zero. -/
theorem gaussReply_bit (e : ℕ) (flag : Bool) (i : ℕ) (hi : i ≤ e) :
    bitOf (List.replicate e true ++ [false, flag]) i = if i < e then 1 else 0 := by
  unfold bitOf
  by_cases h : i < e
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · have he : i = e := by omega
    subst he
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- `cor:conditional`, paper/paper.tex: the exact
consistency bit immediately follows the unary nullity delimiter. -/
theorem gaussReply_flag (e : ℕ) (flag : Bool) :
    bitOf (List.replicate e true ++ [false, flag]) (e + 1) = flag.toNat := by
  unfold bitOf
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- `cor:conditional`, paper/paper.tex: one real
reply-reader iteration counts a true bit and physically reads the next. -/
def readGaussBody : St VV MM :=
  .seq (.op (.inc gammaExponent)) (.op (.rdK t0))

/-- `cor:conditional`, paper/paper.tex: a finite
ordinary decoder for the exact consistency/nullity source response. -/
def readGaussReply : St VV MM :=
  .seq (.op (.zero gammaExponent)) (.seq (.op (.rdK t0))
    (.seq (.loop (.eq t0 v1) readGaussBody) (.op (.rdK gammaFlag))))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual compact response is decoded in linear time,
preserving all ORIGINAL request registers and the cached primitive field. -/
theorem readGaussReply_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (e : ℕ) (flag : Bool) (hk : a.kout = List.replicate e true ++ [false, flag])
    (hcursor : a.kc = 0) (hfit : e < 2 ^ C.Wd) :
    Hs C readGaussReply a (5 * e + 8) (fun b =>
      b.env gammaExponent = e ∧ b.env gammaFlag = flag.toNat ∧ b.kc = e + 2 ∧
      ReplyFrame a b ∧ Cst b ∧ Fr a b replyScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env gammaExponent = k ∧ b.env t0 = (if k < e then 1 else 0) ∧
    b.kc = k + 1 ∧ ReplyFrame a b ∧ Cst b ∧ Fr a b replyScratch
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq t0 v1) readGaussBody) b
      (5 * e + 2) (I e) := by
    intro b h0
    refine Hs.mono (Hs.loopN (C := C) (c := .eq t0 v1) (s := readGaussBody)
      (by change t0 ≠ v1; decide) I e 3 ?_ ?_ b h0) (by omega) (fun _ h => h)
    · intro k hke b ⟨hb, ht, hkc, hf, hbc, hfr⟩
      refine ⟨by simp [Cnd.eval, ht, hke, hbc.one], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1)
        (hs_inc C gammaExponent b (by rw [hb]; omega)) ?_
      intro d hd
      subst hd
      have hread := hs_rdK C t0 (b.set gammaExponent (b.env gammaExponent + 1)) (by
        change b.kc < b.kout.length
        rw [hkc, hf.kout, hk]
        simp
        omega)
      refine Hs.mono hread le_rfl ?_
      rintro d rfl
      have hbit : bitOf b.kout b.kc = if k + 1 < e then 1 else 0 := by
        rw [hf.kout, hk, hkc]
        exact gaussReply_bit e flag (k + 1) (by omega)
      refine ⟨?_, ?_, by simp [hkc], ?_, ?_, ?_⟩
      · vsimp [hb]
      · vsimp [hbit]
      · exact ⟨hf.ip, hf.out, hf.ram, hf.rc, hf.kin, hf.kout⟩
      · exact ⟨by vsimp [hbc.z], by vsimp [hbc.one], by vsimp [hbc.two]⟩
      · intro x hx
        have hxe : x ≠ gammaExponent := by intro h; exact hx (by simp [replyScratch, h])
        have hxt : x ≠ t0 := by intro h; exact hx (by simp [replyScratch, h])
        simp only [DS.set, Function.update_of_ne hxe, Function.update_of_ne hxt]
        exact hfr x hx
    · intro b ⟨hb, ht, hkc, hf, hbc, hfr⟩
      simp [Cnd.eval, ht, hbc.one]
  unfold readGaussReply
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 5 * e + 6) (hs_zero C gammaExponent a) ?_)
    (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 5 * e + 4)
    (hs_rdK C t0 (a.set gammaExponent 0) (by simp [hcursor, hk])) ?_)
    (by omega) (fun _ h => h)
  intro b hb
  subst hb
  have hi : I 0 { (a.set gammaExponent 0).set t0 (bitOf a.kout a.kc) with kc := a.kc + 1 } := by
    refine ⟨by vsimp [], ?_, by simp [hcursor], ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩, ?_⟩
    · change bitOf a.kout a.kc = _
      rw [hk, hcursor, gaussReply_bit e flag 0 (by omega)]
    · intro x hx
      have hxe : x ≠ gammaExponent := by intro h; exact hx (by simp [replyScratch, h])
      have hxt : x ≠ t0 := by intro h; exact hx (by simp [replyScratch, h])
      simp [DS.set, Function.update_of_ne hxe, Function.update_of_ne hxt]
  refine Hs.seq (t1 := 5 * e + 2) (t2 := 1) (hloop _ hi) ?_
  intro b ⟨hb, ht, hkc, hf, hbc, hfr⟩
  refine Hs.mono (hs_rdK C gammaFlag b (by rw [hkc, hf.kout, hk]; simp)) le_rfl ?_
  rintro d rfl
  refine ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb, ?_, by simp [hkc],
    ⟨hf.ip,hf.out,hf.ram,hf.rc,hf.kin,hf.kout⟩,
    ⟨by vsimp [hbc.z], by vsimp [hbc.one], by vsimp [hbc.two]⟩, ?_⟩
  · change bitOf b.kout b.kc = flag.toNat
    rw [hf.kout, hk, hkc, gaussReply_flag]
  · intro x hx
    have hxg : x ≠ gammaFlag := by intro h; exact hx (by simp [replyScratch, h])
    simp only [DS.set, Function.update_of_ne hxg]
    exact hfr x hx

end NearQuarticWires.StageGamma
