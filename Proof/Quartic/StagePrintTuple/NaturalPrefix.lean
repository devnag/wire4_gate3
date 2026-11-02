import Proof.Gates.Dispatch.Zero

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Dispatch

/-- `lem:print`, paper/paper.tex: the actual
binary source-prefix scanner is the existing natural-codec scan loop;
its selected position is an actual runtime register, not a supplied row. -/
def naturalPrefixProgram : St VV := skipW

/-- `lem:print` and `prop:time`, paper/paper.tex: the real support-prefix scan consumes exactly the first
j canonical variable codecs and preserves all support-index metadata. -/
theorem naturalPrefixProgram_run (C : Ctx) (support : List ℕ) (j : ℕ)
    (rest : List Bool) (a : DS VV) (hc : Cst a) (hj : j ≤ support.length)
    (hJ : a.env oJ = j) (hin : C.cw.drop a.cp = support.flatMap natWord ++ rest)
    (hWb : ∀ v ∈ support, natBitLength v + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hlen : support.length < 2 ^ C.Wd) :
    Hs C naturalPrefixProgram a (j * (30 * C.Wd + 64) + 4)
      (fun b => C.cw.drop b.cp = (support.drop j).flatMap natWord ++ rest ∧
        Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT) := by
  unfold naturalPrefixProgram skipW
  refine Hx.hs (Hs.then (hs_zero C oI a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  have htake : (support.take j).length = j := by simp; omega
  let P : ℕ → DS VV → Prop := fun _ b => Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT
  have w := walk (C := C) (support.take j) natWord oI oJ (by decide) readNat P
    (30 * C.Wd + 60) ((support.drop j).flatMap natWord ++ rest)
    (fun k b v ⟨h1, h2, h3, h4⟩ =>
      ⟨Cst.set h1 _ _ (by decide), h2, h3, h4.trans (Fr.set _ _ (by decide))⟩)
    (fun k hk d ⟨d1, d2, d3, d4⟩ dI dN dcw => by
      have hmem : (support.take j)[k] ∈ support := List.mem_of_mem_take (List.getElem_mem hk)
      have hb := hWb _ hmem
      refine (readNat_spec d d1 _ _ dcw (by omega) hL).mono (by nlinarith) ?_
      rintro e ⟨_, _, ep, ew, eo, ec, ef⟩
      exact ⟨⟨ec, ew.trans d2, eo.trans d3, d4.trans (ef.weaken (by decide))⟩,
        by rw [ef oI (by decide), dI], by rw [ef oJ (by decide), dN], ep⟩)
    (by rw [htake]; omega)
  refine Hs.last (w (a.set oI 0)
    ⟨Cst.set hc _ _ (by decide), rfl, rfl, Fr.set _ _ (by decide)⟩
    (by rw [DS.set_env_self])
    (by rw [DS.set_env_ne _ _ (by decide), hJ, htake]) (by
      show C.cw.drop a.cp = _
      rw [hin, take_flatMap_drop support natWord j rest]))
    (fun g ⟨⟨g1, g2, g3, g4⟩, _, _, gp⟩ k2 hk2 => ?_)
  refine ⟨⟨?_, g1, g2, g3, g4⟩, ?_⟩
  · rw [gp]
    show C.cw.drop (a.cp + _) = _
    rw [← List.drop_drop, hin, take_flatMap_drop support natWord j rest, List.drop_left]
  · rw [htake] at hk2
    have he : j * (30 * C.Wd + 60 + 2 + 2) = j * (30 * C.Wd + 64) := by ring
    omega

end NearQuarticWires.StageTuple
