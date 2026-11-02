import Proof.Quartic.StagePullback.Marker
import Proof.Quartic.StagePullback.Canonical

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Offsets

open NearCubicGates.Close.Cells

def coordinate : Fin VV := 89
def blockWidth : Fin VV := 90
def blockCount : Fin VV := 91
def limit : Fin VV := 92

/-- `imp:pullback`, paper/paper.tex: locate an original
coordinate's block, one-hot position and blocked-coordinate boundary. -/
def prepare : St VV MM :=
  .seq (.op (.dm coordinate blockWidth Digits.block Markers.wanted))
    (.seq (.op (.inc Markers.wanted)) (.op (.mul blockCount blockWidth limit)))

def prepared (a : DS VV MM) : DS VV MM :=
  let b := (a.set Digits.block (a.env coordinate / a.env blockWidth)).set Markers.wanted
    (a.env coordinate % a.env blockWidth)
  let c := b.set Markers.wanted (b.env Markers.wanted + 1)
  c.set limit (c.env blockCount * c.env blockWidth)

def prepareScratch : List (Fin VV) := [Digits.block, Markers.wanted, limit]

theorem prepared_frame (a : DS VV MM) : Fr a (prepared a) prepareScratch :=
  (Fr.set a _ (by simp [prepareScratch])).trans
    ((Fr.set _ _ (by simp [prepareScratch])).trans
      ((Fr.set _ _ (by simp [prepareScratch])).trans (Fr.set _ _ (by simp [prepareScratch]))))

theorem prepared_block (a : DS VV MM) :
    (prepared a).env Digits.block = a.env coordinate / a.env blockWidth := by
  simp only [prepared, DS.set_env_ne _ _ (by decide : Digits.block ≠ limit),
    DS.set_env_ne _ _ (by decide : Digits.block ≠ Markers.wanted), DS.set_env_self]

theorem prepared_wanted (a : DS VV MM) :
    (prepared a).env Markers.wanted = a.env coordinate % a.env blockWidth + 1 := by
  simp only [prepared, DS.set_env_ne _ _ (by decide : Markers.wanted ≠ limit), DS.set_env_self]

theorem prepared_limit (a : DS VV MM) :
    (prepared a).env limit = a.env blockCount * a.env blockWidth := by
  simp only [prepared, DS.set_env_self,
    DS.set_env_ne _ _ (by decide : blockCount ≠ Markers.wanted),
    DS.set_env_ne _ _ (by decide : blockCount ≠ Digits.block),
    DS.set_env_ne _ _ (by decide : blockWidth ≠ Markers.wanted),
    DS.set_env_ne _ _ (by decide : blockWidth ≠ Digits.block)]

/-- `imp:pullback` and `prop:time`, paper/paper.tex: block location and the original-coordinate boundary
are obtained by actual division, increment and multiplication. -/
theorem prepare_run (C : Ctx) (a : DS VV MM)
    (hb : 0 < a.env blockWidth) (hbfit : 2 * a.env blockWidth ≤ 2 ^ C.Wd)
    (hprod : a.env blockCount * a.env blockWidth < 2 ^ C.Wd) :
    Hs C prepare a 5 (fun b => b = prepared a) := by
  unfold prepare
  refine Hx.hs (Hs.then (hs_dm C coordinate blockWidth Digits.block Markers.wanted a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hb hbfit)
    (fun b h n1 hn1 => ?_))
  subst h
  refine Hs.then (hs_inc C Markers.wanted _ (by
    rw [DS.set_env_self]
    have hmod := Nat.mod_lt (a.env coordinate) hb
    omega)) (fun c h n2 hn2 => ?_)
  subst h
  refine Hs.last (hs_mul C blockCount blockWidth limit _ (by decide) (by decide) (by decide)
    (by simpa only [DS.set_env_ne _ _ (by decide : blockCount ≠ Markers.wanted),
      DS.set_env_ne _ _ (by decide : blockCount ≠ Digits.block),
      DS.set_env_ne _ _ (by decide : blockWidth ≠ Markers.wanted),
      DS.set_env_ne _ _ (by decide : blockWidth ≠ Digits.block)] using hprod)) ?_
  rintro d h n3 hn3
  subst h
  exact ⟨rfl, by omega⟩

/-- `imp:pullback`, paper/paper.tex: a marker outside
the original blocked coordinates is zero. -/
def program : St VV MM := .seq prepare (.seq Markers.program
  (.ite (.lt coordinate limit) skipS (.op (.zero Markers.result))))

def scratch : List (Fin VV) := prepareScratch ++ Markers.scratch ++ [vJ]

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the canonical offset marker is physically computed
from the original coordinate and the scalar translation code. -/
theorem program_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hb : 0 < a.env blockWidth) (hbfit : 2 * a.env blockWidth ≤ 2 ^ C.Wd)
    (hprod : a.env blockCount * a.env blockWidth < 2 ^ C.Wd)
    (hxfit : a.env coordinate < 2 ^ C.Wd)
    (hr : 0 < a.env Digits.radix) (hrfit : 2 * a.env Digits.radix ≤ 2 ^ C.Wd) :
    Hs C program a (7 * (a.env coordinate / a.env blockWidth) + 20) (fun b =>
      b.env Markers.result = (decide (a.env coordinate < a.env blockCount * a.env blockWidth ∧
        a.env Digits.number / a.env Digits.radix ^ (a.env coordinate / a.env blockWidth) %
          a.env Digits.radix = a.env coordinate % a.env blockWidth + 1)).toNat ∧
      b.sh = a.sh ∧ Fr a b scratch) := by
  unfold program
  refine Hx.hs (Hs.then (prepare_run C a hb hbfit hprod)
    (fun e he n1 hn1 => ?_))
  subst he
  have hpf := prepared_frame a
  have hpc : Cst (prepared a) := Cst.of_fr hc hpf (by decide)
  have hrad : (prepared a).env Digits.radix = a.env Digits.radix := hpf _ (by decide)
  have hnum : (prepared a).env Digits.number = a.env Digits.number := hpf _ (by decide)
  have hx : (prepared a).env coordinate = a.env coordinate := hpf _ (by decide)
  have hbl : (prepared a).env Digits.block < 2 ^ C.Wd := by
    rw [prepared_block]
    exact (Nat.div_le_self _ _).trans_lt hxfit
  refine Hs.then (Markers.program_run C (prepared a) hpc
    (by rw [hrad]; exact hr) (by rw [hrad]; exact hrfit) hbl)
    (fun b ⟨hm, hsh, hf⟩ n2 hn2 => ?_)
  have hval : b.env Markers.result =
      (decide (a.env Digits.number /
        a.env Digits.radix ^ (a.env coordinate / a.env blockWidth) % a.env Digits.radix =
          a.env coordinate % a.env blockWidth + 1)).toNat := by
    simpa only [hnum, hrad, prepared_block, prepared_wanted] using hm
  have bx : b.env coordinate = a.env coordinate := (hf _ (by decide)).trans hx
  have blim : b.env limit = a.env blockCount * a.env blockWidth :=
    (hf _ (by decide)).trans (prepared_limit a)
  have hguard : Hs C (.ite (.lt coordinate limit) skipS (.op (.zero Markers.result))) b 2
      (fun d => d.env Markers.result =
        (if a.env coordinate < a.env blockCount * a.env blockWidth then b.env Markers.result else 0) ∧
        d.sh = b.sh ∧ Fr b d [Markers.result, vJ]) := by
    refine Hs.ite (show coordinate ≠ limit by decide) (fun h => ?_) (fun h => ?_)
    · have hxlt : a.env coordinate < a.env blockCount * a.env blockWidth := by
        simpa only [Cnd.eval, bx, blim, decide_eq_true_eq] using h
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      exact ⟨by rw [if_pos hxlt, DS.set_env_ne _ _ (by decide)], rfl,
        Fr.set b _ (by simp)⟩
    · have hxge : ¬ a.env coordinate < a.env blockCount * a.env blockWidth := by
        simpa only [Cnd.eval, bx, blim, decide_eq_false_iff_not] using h
      refine Hs.mono (hs_zero C Markers.result b) le_rfl ?_
      rintro d rfl
      exact ⟨by rw [if_neg hxge, DS.set_env_self], rfl, Fr.set b _ (by simp)⟩
  refine Hs.last hguard ?_
  rintro d ⟨hd, hs, hff⟩ n3 hn3
  refine ⟨⟨?_, hs.trans hsh, ?_⟩, ?_⟩
  · rw [hd, hval]
    by_cases h : a.env coordinate < a.env blockCount * a.env blockWidth <;> simp [h]
  · have hpff : Fr a (prepared a) scratch := hpf.weaken (by
      intro y hy
      simp only [scratch, List.mem_append]
      exact Or.inl (Or.inl hy))
    have hmf : Fr (prepared a) b scratch := hf.weaken (by
      intro y hy
      simp only [scratch, List.mem_append]
      exact Or.inl (Or.inr hy))
    have hg : Fr b d scratch := hff.weaken (by
      intro y hy
      simp only [scratch, Markers.scratch, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy ⊢
      tauto)
    exact hpff.trans (hmf.trans hg)
  · rw [prepared_block] at hn2
    omega

end NearQuarticWires.StagePullback.Offsets
