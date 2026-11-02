import Proof.Quartic.StageNativeRowCount.SkipNatural

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def readScalar (rd : Fin VV → Op VV MM) (x : Fin VV) : St VV MM :=
  .seq (rdNat rd) (.op (.copy x t3))

/-- `lem:print`, paper/paper.tex: decode only a
requested bounded scalar from actual retained binary source bits. -/
theorem readScalar_spec {C : Ctx} {R : Type} (S : Src C R) (x : Fin VV)
    (hx : x ∉ [vZ,v1,v2]) (hxt : x ≠ t3) (a : DS VV MM) (hc : Cst a)
    (hok : S.ok a) (v : ℕ) (rest : List Bool)
    (hin : S.word.drop (S.pos a) = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (readScalar S.op x) a (30 * natBitLength v + 32) (fun b =>
      b.env x = v ∧ S.pos b = S.pos a + (natWord v).length ∧
      S.rest b = S.rest a ∧ Cst b ∧ Fr a b (x :: rdNatT)) := by
  unfold readScalar
  refine (Hs.seq (t2:=1) (rdNat_spec S a hc hok v rest hin hW) ?_).mono le_rfl (fun _ h=>h)
  rintro b ⟨bv,_,bp,br,bfr⟩
  refine (hs_copy C x t3 b hxt).mono le_rfl ?_
  rintro d rfl
  refine ⟨by rw [DS.set_env_self,bv], by rw [S.pos_set,bp], by rw [S.rest_set,br], ?_, ?_⟩
  · have hbc := cst_fr hc bfr
    have hz : vZ ≠ x := by intro he; exact hx (by simp [←he])
    have h1 : v1 ≠ x := by intro he; exact hx (by simp [←he])
    have h2 : v2 ≠ x := by intro he; exact hx (by simp [←he])
    exact hbc.of_fr (Fr.set b _ (by simp : x ∈ [x]))
      ⟨by simpa only [List.mem_singleton] using hz,
        by simpa only [List.mem_singleton] using h1,
        by simpa only [List.mem_singleton] using h2⟩
  · exact (bfr.weaken (by intro y hy; simp [hy])).trans (Fr.set _ _ (by simp))

theorem source_tail {C : Ctx} {R : Type} (S : Src C R) {a b : DS VV MM}
    {word rest : List Bool} (hp : S.pos b = S.pos a + word.length)
    (hin : S.word.drop (S.pos a) = word ++ rest) : S.word.drop (S.pos b) = rest := by
  rw [hp,←List.drop_drop,hin,List.drop_left]

end NearQuarticWires.StageNativeRowCount
