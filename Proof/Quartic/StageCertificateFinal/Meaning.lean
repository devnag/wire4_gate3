import Proof.Quartic.StageCertificateFinal.Requests
import Proof.Quartic.StageCertificateControl.CertificateMeaning
import Proof.Quartic.StageCertificateControl.AppendSemantics

/-!
# Every generated signed test has the literal original-column meaning

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl StageCertTests

/-- `sec:algorithm`, paper/paper.tex: selected
metadata indices enumerate precisely the literal whole-test kinds,
including all sign patterns, both circuits and every chain position. -/
theorem selected_ordinals (B1 B2 : ℕ) (c : Call) (w : List Bool)
    (p : Program.Selected c) (hd : Program.dispatch B1 B2 c=some p) :
    actualTestPlan c p.1=List.ofFn (fun j : Fin (certificateMetadata p.1 c.kind).length =>
      (StageCertNative.actualOrdinal (⟨⟨c,w,p,hd⟩,j⟩ : IndexedRequest B1 B2)).kind) := by
  have hs := Cells.prepare_spec _ p.1 p.2
  have hm := certificateMetadata_eq_ordinalTestPlan c p.1 hs.J_pos
  rw [actualTestPlan,←ordinalTestPlan_kind]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn]
    simpa only [List.length_map] using (congrArg List.length hm).symm
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_ofFn,StageCertNative.actualOrdinal]

/-- `eq:testX`–`eq:testPhi` and `sec:algorithm`, paper/paper.tex: the entire physically ordered native
batch has the literal original-uniform moment prefix and exact strict
threshold, without presuming that any column passes its certificate. -/
theorem tests_realize {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    (c : Call) (w : List Bool) (p : Program.Selected c)
    (hd : Program.dispatch B1 B2 c=some p) :
    List.Forall₂ (fun test kind =>
      test.bound=actualTestThreshold p.1 kind ∧
      test.values.take (2^(c.n-p.1.k))=List.ofFn (fun z =>
        (actualTestTable c (Cells.prepare_spec _ p.1 p.2) w kind z).1))
      (tests tables c w) (actualTestPlan c p.1) := by
  have ht : tests tables c w=List.ofFn (fun j : Fin (certificateMetadata p.1 c.kind).length =>
      let r : IndexedRequest B1 B2 := ⟨⟨c,w,p,hd⟩,j⟩
      tableTest r.metadata.threshold (tables.table r)) := by
    unfold tests certificatePoolFamily
    split
    · rename_i hn
      simp only [hd] at hn
      contradiction
    · rename_i q hq
      have he : q=p := Option.some.inj (hq.symm.trans hd)
      subst q
      rfl
  rw [ht,selected_ordinals B1 B2 c w p hd]
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi hi'
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  let r : IndexedRequest B1 B2 := ⟨⟨c,w,p,hd⟩,⟨i,by simpa using hi⟩⟩
  change r.metadata.threshold=actualTestThreshold p.1 (StageCertNative.actualOrdinal r).kind ∧ _
  constructor
  · have h := congrArg TestMetadata.threshold (StageCertNative.actualOrdinal_metadata r)
    exact h.symm.trans (TestOrdinal.metadata_threshold _ _)
  · exact tables.originalPrefix r

/-- `sec:algorithm`, paper/paper.tex: the full
padded native fold followed by its sole crop produces exactly the
literal certificate bitmap for every original witness. -/
theorem bitmap_certifiedBits {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    (c : Call) (w : List Bool) (p : Program.Selected c)
    (hd : Program.dispatch B1 B2 c=some p) :
    (nativeTestFlags (tests tables c w)
      (List.replicate (paddedCount c.n p.1.k) true)).take (centerCount c.n p.1.k)=
      Program.certifiedBits (Program.runCall c p w) := by
  exact nativeFlags_eq_certifiedBits c (Cells.prepare_spec _ p.1 p.2) w
    (tests tables c w) (paddedCount c.n p.1.k) (Nat.pow_le_pow_right (by decide) (by omega))
    (tests_realize tables c w p hd)

/-- `sec:algorithm` and the default in `sec:params`,
paper/paper.tex: the actual bitmap machine
returns a framed certificate suffix, including an empty default suffix. -/
theorem bitmap_output {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    (bitmapRequest tables c w).output=frame (certificateSuffix B1 B2 c w) := by
  simp only [BitmapRequest.output,bitmapRequest,certificateSuffix]
  split
  · rename_i hd
    simp only [hd]
  · rename_i p hd
    rw [bitmap_certifiedBits tables c w p hd]
    simp only [hd]

end NearQuarticWires.StageCertificateFinal
