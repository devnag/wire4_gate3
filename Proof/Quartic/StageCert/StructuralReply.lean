import Proof.Quartic.StageCert.StructuralInvoke
import Proof.Quartic.StageMainMask.StructuralBytes

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces

/-- `def:mask` and `lem:print`, paper/paper.tex: read the actual three-bit framed Boolean reply of
the concrete structural source. -/
def decodeStructuralReply : St VV MM :=
  .seq (.op (.rdK t0)) (.seq (.op (.rdK maskStructural))
    (.op (.rdK t0)))

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: all reply markers and
the original Boolean mask bit are physically consumed; no decoded
flag is an input to this program. -/
theorem decodeStructuralReply_run (C : Ctx) (flag : Bool) (a : DS VV MM) (hc : Cst a)
    (hreply : a.kout=[true,flag,false]) (hcursor : a.kc=0) :
    Hs C decodeStructuralReply a 5 (fun z=>
      z.env maskStructural=flag.toNat ∧ z.kc=3 ∧
      (z.ip,z.out,z.ram,z.rc,z.kin,z.kout)=(a.ip,a.out,a.ram,a.rc,a.kin,a.kout) ∧
      Cst z ∧ Fr a z [t0,maskStructural]) := by
  unfold decodeStructuralReply
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_rdK C t0 a (by simp [hreply,hcursor])) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_rdK C maskStructural _ (by simp [DS.set,hreply,hcursor])) ?_
  rintro d rfl
  refine (hs_rdK C t0 _ (by simp [DS.set,hreply,hcursor])).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,by simp [hcursor],rfl,?_,
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩
  · cases flag <;> simp [DS.set,hreply,hcursor,bitOf,maskStructural,t0]
  · exact Cst.of_fr (T := [t0,maskStructural]) hc
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        (Fr.set _ _ (by simp)))) (by decide)

end NearQuarticWires.StageCert.Tokens
