import Proof.Quartic.StageOutput.Endpoints

/-!
# Retaining the two outward-rounded endpoints

Paper: `sec:algorithm`, paper/paper.tex. The lower
endpoint is retained in sign-magnitude form while the upper endpoint is
computed. The upper endpoint is nonnegative, so its magnitude is its exact
integer value, including the zero case.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def savedF : Fin VV := ⟨52, by decide⟩
def savedSign : Fin VV := ⟨53, by decide⟩
def savedG : Fin VV := ⟨54, by decide⟩
def endpointPairScratch : List (Fin VV) := endpointScratch ++ [savedF, savedSign, savedG]

def endpointPair : St VV := .seq lowerEndpoint
  (.seq (.op (.copy savedF roundQ)) (.seq (.op (.copy savedSign roundSign))
    (.seq upperEndpoint (.op (.copy savedG roundQ)))))

theorem endpointPair_spec {C : Ctx} (d : Input) (B : ℕ) (a : DS VV)
    (hc : Cst a) (hs : d.Stored a.env) (hn : a.env powerN = 2 ^ d.n)
    (hk : a.env powerK = 2 ^ d.k)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hnB : d.n ≤ B) (hkB : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ C.Wd) (hD : 0 < d.denominator) (hG : 0 ≤ d.ceilValue) :
    Hs C endpointPair a 281 (fun b =>
      (if b.env savedSign = 0 then (b.env savedF : ℤ) else -(b.env savedF : ℤ)) = d.floorValue ∧
      (b.env savedG : ℤ) = d.ceilValue ∧ b.env savedSign ≤ 1 ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b endpointPairScratch) := by
  refine Hx.hs (Hs.then (lowerEndpoint_spec d B a hc hs hk hf hkB hw hD)
    (fun b ⟨bv, bs, bd, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C savedF roundQ b (by decide)) (fun c1 hc1 n2 hn2 => ?_)
  subst hc1
  refine Hs.then (hs_copy C savedSign roundSign _ (by decide)) (fun c2 hc2 n3 hn3 => ?_)
  subst hc2
  let c := (b.set savedF (b.env roundQ)).set savedSign ((b.set savedF (b.env roundQ)).env roundSign)
  have cc : Cst c := (bc.set _ _ (by decide)).set _ _ (by decide)
  have cf : FrS a c endpointPairScratch := FrS.trans (bf.weaken (by decide))
    (Fr.trans (Fr.set _ (x := savedF) _ (by decide)) (Fr.set _ (x := savedSign) _ (by decide))).toS
  have cs : d.Stored c.env := d.stored_of_frame hs cf (by decide)
  have cn : c.env powerN = 2 ^ d.n := (cf _ (by decide) (by decide)).trans hn
  have ck : c.env powerK = 2 ^ d.k := (cf _ (by decide) (by decide)).trans hk
  have cd : c.env roundD = d.denominator := by
    simpa (config := { decide := true }) [c] using bd
  refine Hs.then (upperEndpoint_spec d B c cc cs cn ck cd hf hnB hkB hw hD)
    (fun e ⟨ev, es, ed, ep, ew, eo, ec, ef⟩ n4 hn4 => ?_)
  have eg : (e.env roundQ : ℤ) = d.ceilValue := by
    split_ifs at ev <;> omega
  refine Hs.last (hs_copy C savedG roundQ e (by decide)) ?_
  rintro f rfl n5 hn5
  have eff : FrS c e endpointPairScratch := ef.weaken (by decide)
  refine ⟨⟨?_, by simpa using eg, ?_, by rw [DS.set_cp, ep]; exact bp,
    by rw [DS.set_wq, ew]; exact bw, by rw [DS.set_out, eo]; exact bo,
    ec.set _ _ (by decide), FrS.trans cf (FrS.trans eff (Fr.set _ _ (by decide)).toS)⟩, by omega⟩
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide),
      ef savedSign (by decide) (by decide), ef savedF (by decide) (by decide)]
    simpa (config := { decide := true }) [c] using bv
  · rw [DS.set_env_ne _ _ (by decide), ef savedSign (by decide) (by decide)]
    simpa (config := { decide := true }) [c] using bs

end NearQuarticWires.StageOutput
