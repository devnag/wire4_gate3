import Proof.Quartic.StageNativeRowCount.Request

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: scan the actual
unary bit-length prefix and skip precisely that many binary payload bits.
The payload's numerical value is never accumulated. -/
def skipNatural (rd : Fin VV → Op VV MM) : St VV MM :=
  .seq (.op (.zero t4)) (.seq (.op (rd t0))
    (.seq (.loop (.eq t0 v1) (.seq (.op (.inc t4)) (.op (rd t0))))
      (.seq (.op (.zero t2))
        (.loop (.lt t2 t4) (.seq (.op (rd t0)) (.op (.inc t2)))))))

/-- `prop:time`, paper/paper.tex: binary codec
skipping costs only its actual bit length, independently of its value. -/
theorem skipNatural_spec {C : Ctx} {R : Type} (S : Src C R)
    (a : DS VV MM) (hc : Cst a) (hok : S.ok a) (v : ℕ) (rest : List Bool)
    (hin : S.word.drop (S.pos a) = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (skipNatural S.op) a (20 * natBitLength v + 20) (fun b =>
      S.pos b = S.pos a + (natWord v).length ∧ S.rest b = S.rest a ∧
      Fr a b rdNatT) := by
  let L := natBitLength v
  have hlen := natWord_length v
  have hcap : L + 1 < 2 ^ C.Wd := by
    have hp : 2 ^ (L + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by dsimp [L]; omega)
    exact Nat.lt_two_pow_self.trans_le hp
  have nenv : ∀ b y, S.ok b → y ≠ t0 → (S.nxt b t0).env y = b.env y := by
    intro b y hb hy
    rw [S.env b t0 hb, Function.update_of_ne hy]
  have n0 : ∀ b, S.ok b → (S.nxt b t0).env t0 = bitOf S.word (S.pos b) := by
    intro b hb
    rw [S.env b t0 hb, Function.update_self]
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env t4 = k ∧ b.env t0 = bitOf S.word (S.pos a + k) ∧
      S.pos b = S.pos a + k + 1 ∧ S.rest b = S.rest a ∧ Fr a b rdNatT
  have hpref : ∀ b, I 0 b →
      Hs C (.loop (.eq t0 v1) (.seq (.op (.inc t4)) (.op (S.op t0)))) b
        (L * (3 + 2) + 2) (I L) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I L 3 ?_ ?_
    · intro k hk b ⟨h1,h2,h3,h4,h5⟩
      have bv1 : b.env v1 = 1 := by rw [h5 v1 (by decide)]; exact hc.one
      refine ⟨?_, ?_⟩
      · simp only [Cnd.eval,h2,bv1,decide_eq_true_eq]
        rw [bitOf_drop hin k (by dsimp [L] at hk; omega), natWord_one v k hk]
        rfl
      · refine Hs.seq (t1:=1) (t2:=1) (hs_inc C t4 b (by rw [h1]; omega)) ?_
        rintro d rfl
        have ho : S.ok (b.set t4 (b.env t4 + 1)) := S.ok_of _ _ (by rw [S.rest_set,h4]) hok
        refine (src_hs S _ t0 ho (by
          rw [S.pos_set,h3]
          have hh := lt_of_drop hin (k+1) (by dsimp [L] at hk; omega)
          omega)).mono le_rfl ?_
        rintro e rfl
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [nenv _ _ ho (by decide)]; vsimp [h1]
        · rw [n0 _ ho,S.pos_set,h3]; congr 1
        · rw [S.posn,S.pos_set,h3]; omega
        · rw [S.restn,S.rest_set,h4]
        · exact h5.trans ((Fr.set b _ (by decide)).trans
            (fun y hy => nenv _ y ho (fun he => hy (he ▸ by decide))))
    · intro b ⟨_,h2,_,_,h5⟩
      have bv1 : b.env v1 = 1 := by rw [h5 v1 (by decide)]; exact hc.one
      simp only [Cnd.eval,h2,bv1,decide_eq_false_iff_not]
      rw [bitOf_drop hin L (by dsimp [L]; omega), natWord_zero v]
      simp
  let J : ℕ → DS VV MM → Prop := fun k b =>
    b.env t2 = k ∧ b.env t4 = L ∧ S.pos b = S.pos a + L + 1 + k ∧
      S.rest b = S.rest a ∧ Fr a b rdNatT
  have hbits : ∀ b, J 0 b →
      Hs C (.loop (.lt t2 t4) (.seq (.op (S.op t0)) (.op (.inc t2)))) b
        (L * (3 + 2) + 2) (J L) := by
    refine Hs.loopN (c := .lt t2 t4) (show t2 ≠ t4 by decide) J L 3 ?_ ?_
    · intro k hk b ⟨h1,h2,h3,h4,h5⟩
      have ho : S.ok b := S.ok_of _ _ h4 hok
      refine ⟨by simp [Cnd.eval,h1,h2,hk], ?_⟩
      refine Hs.seq (t1:=1) (t2:=1) (src_hs S b t0 ho (by
        rw [h3]
        have hh := lt_of_drop hin (L+1+k) (by dsimp [L] at hk ⊢; omega)
        omega)) ?_
      rintro d rfl
      refine (hs_inc C t2 (S.nxt b t0) (by rw [nenv _ _ ho (by decide),h1]; omega)).mono le_rfl ?_
      rintro e rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · vsimp [nenv _ _ ho (by decide : t2 ≠ t0),h1]
      · rw [DS.set_env_ne _ _ (by decide : t4 ≠ t2),nenv _ _ ho (by decide),h2]
      · rw [S.pos_set,S.posn,h3]; omega
      · rw [S.rest_set,S.restn,h4]
      · have hf : Fr b (S.nxt b t0) rdNatT :=
          fun y hy => nenv _ y ho (fun he => hy (he ▸ by decide))
        exact h5.trans (hf.trans (Fr.set _ _ (by decide)))
    · intro b ⟨h1,h2,_⟩
      simp [Cnd.eval,h1,h2]
  unfold skipNatural
  refine Hx.hs (Hs.then (hs_zero C t4 a) ?_)
  rintro b rfl n1 hn1
  have ho : S.ok (a.set t4 0) := S.ok_of _ _ (S.rest_set _ _ _) hok
  refine Hs.then (src_hs S _ t0 ho (by rw [S.pos_set]; exact lt_of_drop hin 0 (by omega))) ?_
  rintro c rfl n2 hn2
  have hi : I 0 (S.nxt (a.set t4 0) t0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [nenv _ _ ho (by decide)]; vsimp []
    · rw [n0 _ ho,S.pos_set]; rfl
    · rw [S.posn,S.pos_set]
    · rw [S.restn,S.rest_set]
    · exact (Fr.set a _ (by decide)).trans
        (fun y hy => nenv _ y ho (fun he => hy (he ▸ by decide)))
  refine Hs.then (hpref _ hi) ?_
  rintro d ⟨d1,_,d3,d4,d5⟩ n3 hn3
  refine Hs.then (hs_zero C t2 d) ?_
  rintro e rfl n4 hn4
  refine Hs.last (hbits (d.set t2 0) ⟨by simp, by rw [DS.set_env_ne _ _ (by decide),d1],
    by rw [S.pos_set,d3], by rw [S.rest_set,d4],d5.trans (Fr.set _ _ (by decide))⟩) ?_
  rintro f ⟨_,_,f3,f4,f5⟩ n5 hn5
  refine ⟨⟨?_,f4,f5⟩, ?_⟩
  · rw [f3,hlen]
    dsimp [L]
    omega
  · dsimp [L] at *
    omega

end NearQuarticWires.StageNativeRowCount
