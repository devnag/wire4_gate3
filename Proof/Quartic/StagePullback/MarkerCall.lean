import Proof.Quartic.StagePullback.BitArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.MarkerCalls

open NearCubicGates.Close.Cells

def originalCoordinate : Fin VV := 31

def installScratch : List (Fin VV) := [Offsets.blockCount, Digits.number, Offsets.coordinate]

/-- `imp:pullback`, paper/paper.tex: retained source
metadata physically installs the count, pattern and original coordinate
for one canonical block-marker computation. -/
def install (count code : Fin VV) : St VV MM :=
  .seq (.op (.copy Offsets.blockCount count))
    (.seq (.op (.copy Digits.number code)) (.op (.copy Offsets.coordinate originalCoordinate)))

def installed (a : DS VV MM) (count code : Fin VV) : DS VV MM :=
  ((a.set Offsets.blockCount (a.env count)).set Digits.number (a.env code)).set
    Offsets.coordinate (a.env originalCoordinate)

theorem installed_frame (a : DS VV MM) (count code : Fin VV) :
    Fr a (installed a count code) installScratch :=
  (Fr.set a _ (by simp [installScratch])).trans
    ((Fr.set _ _ (by simp [installScratch])).trans (Fr.set _ _ (by simp [installScratch])))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: marker metadata installation uses three literal copies
and preserves every retained source field. -/
theorem install_run (C : Ctx) (a : DS VV MM) (count code : Fin VV)
    (hcount : count ∉ installScratch) (hcode : code ∉ installScratch) :
    Hs C (install count code) a 5 (fun b => b = installed a count code) := by
  have hcn : count ≠ Offsets.blockCount := by
    intro h; exact hcount (by simp [installScratch, h])
  have hco : code ≠ Digits.number := by
    intro h; exact hcode (by simp [installScratch, h])
  have hcb : code ≠ Offsets.blockCount := by
    intro h; exact hcode (by simp [installScratch, h])
  unfold install
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C Offsets.blockCount count a hcn.symm) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C Digits.number code _ hco.symm) ?_
  rintro b rfl
  refine Hs.mono (hs_copy C Offsets.coordinate originalCoordinate _ (by decide)) le_rfl ?_
  rintro b rfl
  simp only [DS.set_env_ne _ _ hcb,
    DS.set_env_ne _ _ (by decide : originalCoordinate ≠ Digits.number),
    DS.set_env_ne _ _ (by decide : originalCoordinate ≠ Offsets.blockCount)]
  rfl

def scratch : List (Fin VV) := installScratch ++ RightErrors.scratch

/-- `imp:pullback`, paper/paper.tex: the scalar
metadata are followed by the literal left-marker program. -/
def leftCall (count code : Fin VV) : St VV MM := .seq (install count code) Offsets.program

/-- `imp:pullback`, paper/paper.tex: the scalar
metadata are followed by the literal right-marker program. -/
def rightCall (count code : Fin VV) : St VV MM := .seq (install count code) RightErrors.program

theorem installed_values (a : DS VV MM) (count code : Fin VV) :
    (installed a count code).env Offsets.blockCount = a.env count ∧
    (installed a count code).env Digits.number = a.env code ∧
    (installed a count code).env Offsets.coordinate = a.env originalCoordinate := by
  simp only [installed, DS.set_env_self,
    DS.set_env_ne _ _ (by decide : Offsets.blockCount ≠ Offsets.coordinate),
    DS.set_env_ne _ _ (by decide : Offsets.blockCount ≠ Digits.number),
    DS.set_env_ne _ _ (by decide : Digits.number ≠ Offsets.coordinate), and_self]

/-- `imp:pullback` and `prop:time`, paper/paper.tex: one actual metadata-driven call computes the exact
original-coordinate left marker with no supplied decoded pattern. -/
theorem leftCall_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (count code : Fin VV)
    (hcount : count ∉ installScratch) (hcode : code ∉ installScratch)
    (hb : 0 < a.env Offsets.blockWidth)
    (hbfit : 2 * a.env Offsets.blockWidth ≤ 2 ^ C.Wd)
    (hprod : a.env count * a.env Offsets.blockWidth < 2 ^ C.Wd)
    (hxfit : a.env originalCoordinate < 2 ^ C.Wd)
    (hr : 0 < a.env Digits.radix) (hrfit : 2 * a.env Digits.radix ≤ 2 ^ C.Wd) :
    Hs C (leftCall count code) a
      (7 * (a.env originalCoordinate / a.env Offsets.blockWidth) + 32) (fun b =>
        b.env Markers.result = (decide
          (a.env originalCoordinate < a.env count * a.env Offsets.blockWidth ∧
            a.env code / a.env Digits.radix ^
              (a.env originalCoordinate / a.env Offsets.blockWidth) % a.env Digits.radix =
              a.env originalCoordinate % a.env Offsets.blockWidth + 1)).toNat ∧
        b.sh = a.sh ∧ Fr a b scratch) := by
  have hf := installed_frame a count code
  have hbc : (installed a count code).env Offsets.blockWidth = a.env Offsets.blockWidth :=
    hf _ (by decide)
  have hrad : (installed a count code).env Digits.radix = a.env Digits.radix := hf _ (by decide)
  have hs := installed_values a count code
  have hc1 : Cst (installed a count code) := hc.of_fr hf (by decide)
  unfold leftCall
  refine Hx.hs (Hs.then (install_run C a count code hcount hcode) (fun b h n1 hn1 => ?_))
  subst h
  refine Hs.last (Offsets.program_run C (installed a count code) hc1
    (by rw [hbc]; exact hb) (by rw [hbc]; exact hbfit)
    (by rw [hs.1, hbc]; exact hprod) (by rw [hs.2.2]; exact hxfit)
    (by rw [hrad]; exact hr) (by rw [hrad]; exact hrfit)) ?_
  rintro d ⟨hd, hsh, hfr⟩ n2 hn2
  refine ⟨⟨by simpa only [hs.1, hs.2.1, hs.2.2, hrad, hbc] using hd,
    hsh, ?_⟩, ?_⟩
  · exact (hf.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans
      (hfr.weaken (by
        intro y hy
        exact List.mem_append_right _ (by simp only [RightErrors.scratch, List.mem_append]; exact Or.inr hy)))
  · rw [hs.2.2, hbc] at hn2
    omega

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the original coordinate is retained across physical
right-half decoding, including coordinates before the right boundary. -/
theorem rightCall_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (count code : Fin VV)
    (hcount : count ∉ installScratch) (hcode : code ∉ installScratch)
    (hb : 0 < a.env Offsets.blockWidth)
    (hbfit : 2 * a.env Offsets.blockWidth ≤ 2 ^ C.Wd)
    (hprod : a.env count * a.env Offsets.blockWidth < 2 ^ C.Wd)
    (hxfit : a.env originalCoordinate < 2 ^ C.Wd)
    (hr : 0 < a.env Digits.radix) (hrfit : 2 * a.env Digits.radix ≤ 2 ^ C.Wd) :
    Hs C (rightCall count code) a
      (7 * (a.env originalCoordinate / a.env Offsets.blockWidth) + 32) (fun b =>
        b.env Markers.result = (decide
          (a.env count * a.env Offsets.blockWidth ≤ a.env originalCoordinate ∧
            a.env originalCoordinate - a.env count * a.env Offsets.blockWidth <
              a.env count * a.env Offsets.blockWidth ∧
            a.env code / a.env Digits.radix ^
              ((a.env originalCoordinate - a.env count * a.env Offsets.blockWidth) /
                a.env Offsets.blockWidth) % a.env Digits.radix =
              (a.env originalCoordinate - a.env count * a.env Offsets.blockWidth) %
                a.env Offsets.blockWidth + 1)).toNat ∧
        b.sh = a.sh ∧ Fr a b scratch) := by
  have hf := installed_frame a count code
  have hbc : (installed a count code).env Offsets.blockWidth = a.env Offsets.blockWidth :=
    hf _ (by decide)
  have hrad : (installed a count code).env Digits.radix = a.env Digits.radix := hf _ (by decide)
  have hs := installed_values a count code
  have hc1 : Cst (installed a count code) := hc.of_fr hf (by decide)
  unfold rightCall
  refine Hx.hs (Hs.then (install_run C a count code hcount hcode) (fun b h n1 hn1 => ?_))
  subst h
  refine Hs.last (RightErrors.program_run C (installed a count code) hc1
    (by rw [hbc]; exact hb) (by rw [hbc]; exact hbfit)
    (by rw [hs.1, hbc]; exact hprod) (by rw [hs.2.2]; exact hxfit)
    (by rw [hrad]; exact hr) (by rw [hrad]; exact hrfit)) ?_
  rintro d ⟨hd, hsh, hfr⟩ n2 hn2
  refine ⟨⟨by simpa only [hs.1, hs.2.1, hs.2.2, hrad, hbc] using hd,
    hsh, ?_⟩, ?_⟩
  · exact (hf.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans
      (hfr.weaken (by intro y hy; exact List.mem_append_right _ hy))
  · rw [hs.2.2, hbc] at hn2
    omega

end NearQuarticWires.StagePullback.MarkerCalls
