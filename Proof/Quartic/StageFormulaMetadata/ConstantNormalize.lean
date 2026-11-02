import Proof.Quartic.StageRecovery.ModReduce
import Proof.Quartic.StageRecovery.ModNegate

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicGates.Close.Cells
open StageRecovery

/-- `lem:print` and `lem:residue`, paper/paper.tex: modulus zero preserves the original
signed constant; positive modular requests normalize its magnitude. -/
def normalizeConstant : St VV MM :=
  .ite (.eq modulusVar vZ) skipS
    (.seq reduceLeftProgram
      (.seq (.ite (.eq signVar v1) (negateModProgram leftVar) skipS)
        (.op (.zero signVar))))

/-- `lem:print`, paper/paper.tex: the original
sign is retained precisely in the exact constant mode. -/
def normalizedSign (modulus : ℕ) (negative : Bool) : ℕ :=
  if modulus=0 then negative.toNat else 0

/-- `lem:print` and `lem:residue`, paper/paper.tex: the residue magnitude is obtained by
the actual binary divisions, including signed and zero constants. -/
def normalizedMagnitude (modulus magnitude : ℕ) (negative : Bool) : ℕ :=
  if modulus=0 then magnitude else signedNaturalResidue modulus magnitude negative

/-- `prop:time`, paper/paper.tex: the shared
constant handler copies exact signed data at modulus zero and uses
bounded binary arithmetic only in the positive modular branch. -/
theorem normalizeConstant_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (modulus magnitude : ℕ) (negative : Bool)
    (hq : a.env modulusVar=modulus) (hm : a.env leftVar=magnitude)
    (hs : a.env signVar=negative.toNat)
    (hmode : modulus = 0 ∨ 2 ≤ modulus)
    (hfit : 2*modulus≤2^C.Wd) :
    Hs C normalizeConstant a 15 (fun b=>
      b.env leftVar=normalizedMagnitude modulus magnitude negative ∧
      b.env signVar=normalizedSign modulus negative ∧
      b.sh=a.sh ∧ Cst b ∧
      Fr a b [leftVar,signVar,productVar,quotientVar,remainderVar,vJ]) := by
  unfold normalizeConstant
  rcases hmode with hzero | hpositive
  · have he : (Cnd.eq modulusVar vZ).eval a=true := by
      simp [Cnd.eval,hq,hzero,hc.z]
    refine (Hs.iteT (c:=.eq modulusVar vZ) (show modulusVar≠vZ by decide) he
      (skip_spec a)).mono (by omega) ?_
    rintro b rfl
    exact ⟨by simpa (config:={decide:=true}) [normalizedMagnitude,hzero,DS.set] using hm,
      by simpa (config:={decide:=true}) [normalizedSign,hzero,DS.set] using hs,rfl,
      Cst.of_fr hc (Fr.set a 0 (T:=[vJ]) (by decide)) (by decide),
      Fr.set a 0 (by decide)⟩
  · have hnz : modulus≠0 := by omega
    have he : (Cnd.eq modulusVar vZ).eval a=false := by
      simp [Cnd.eval,hq,hc.z,hnz]
    refine (Hs.iteF (t:=14) (c:=.eq modulusVar vZ) (show modulusVar≠vZ by decide) he ?_).mono
      (by omega) (fun _ h=>h)
    refine Hs.seq (t2:=10) (reduceLeftProgram_spec C a (by rw [hq];omega)
      (by rwa [hq])) fun b ⟨hb,hbsh,hbf⟩=>?_
    have hbc := Cst.of_fr hc hbf (by decide)
    have hbq : b.env modulusVar=modulus := by rw [hbf _ (by decide),hq]
    have hbs : b.env signVar=negative.toNat := by rw [hbf _ (by decide),hs]
    have hbm : b.env leftVar=magnitude%modulus := by simpa only [hm,hq] using hb
    have eSign : Hs C (.ite (.eq signVar v1) (negateModProgram leftVar) skipS) b 8
        (fun d=>d.env leftVar=signedNaturalResidue modulus magnitude negative ∧
          d.sh=b.sh ∧ Cst d ∧
          Fr b d [leftVar,productVar,quotientVar,remainderVar,vJ]) := by
      cases negative with
      | false =>
          have htest : (Cnd.eq signVar v1).eval b=false := by simp [Cnd.eval,hbs,hbc.one]
          refine (Hs.iteF (c:=.eq signVar v1) (show signVar≠v1 by decide) htest
            (skip_spec b)).mono (by omega) ?_
          rintro d rfl
          exact ⟨by simpa (config:={decide:=true}) [signedNaturalResidue,DS.set] using hbm,rfl,
            Cst.of_fr hbc (Fr.set b 0 (T:=[vJ]) (by decide)) (by decide),
            Fr.set b 0 (by decide)⟩
      | true =>
          have htest : (Cnd.eq signVar v1).eval b=true := by simp [Cnd.eval,hbs,hbc.one]
          refine (Hs.iteT (c:=.eq signVar v1) (show signVar≠v1 by decide) htest
            (negateModProgram_spec C b leftVar (by decide) (by rw [hbq];omega)
              (by rwa [hbq]) (by rw [hbm,hbq];exact (Nat.mod_lt _ (by omega)).le))).mono
              le_rfl ?_
          rintro d ⟨hd,hdsh,hdf⟩
          exact ⟨by simpa only [signedNaturalResidue,if_true,hbm,hbq] using hd,
            hdsh,Cst.of_fr hbc hdf (by decide),hdf.weaken (by decide)⟩
    refine Hs.seq (t2:=1) eSign fun d ⟨hd,hdsh,hdc,hdf⟩=>?_
    refine (hs_zero C signVar d).mono le_rfl ?_
    rintro e rfl
    refine ⟨?_,by simp [normalizedSign,hnz],hdsh.trans hbsh,
      Cst.of_fr hdc (Fr.set d 0 (T:=[signVar]) (by decide)) (by decide),?_⟩
    · simpa only [DS.set_env_ne _ _ (show leftVar≠signVar by decide),
        normalizedMagnitude,if_neg hnz] using hd
    · exact (hbf.weaken (by decide)).trans
        ((hdf.weaken (by decide)).trans (Fr.set d 0 (by decide)))

end NearQuarticWires.StageFormulaMetadata
