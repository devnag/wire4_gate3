import Proof.Quartic.StageCert.ColumnBlock

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells

/-- `sec:algorithm`, paper/paper.tex: one framed bit is emitted
without a delimiter so successive column bits share a single frame. -/
def emitFrameBit : St VV MM := .seq (.op (.emit true)) (emitB .emit testAccept)

/-- `sec:algorithm`, paper/paper.tex: a bit writer changes only
the output stream and preserves the input cursor and arithmetic registers. -/
structure WrittenBit (a b : DS VV MM) (bits : List Bool) : Prop where
  out : b.out = a.out ++ bits
  ip : b.ip = a.ip
  env : b.env = a.env

/-- `sec:algorithm`, paper/paper.tex: exact physical framed-bit
writing with all global scan registers preserved. -/
theorem emitFrameBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit : Bool)
    (hb : a.env testAccept = if bit then 1 else 0) :
    Hs C emitFrameBit a 4 (fun b => WrittenBit a b [true,bit]) := by
  unfold emitFrameBit
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_emit C true a) (fun c hc' => ?_)
  subst c
  have hcc : Cst {a with out := a.out ++ [true]} := ⟨hc.z,hc.one,hc.two⟩
  refine (emitB_spec (snkO C) testAccept (by decide) _ hcc trivial).mono le_rfl ?_
  intro b h
  have hb' : decide (({a with out := a.out ++ [true]} : DS VV MM).env testAccept=1) = bit := by
    cases bit <;> simp [hb]
  refine ⟨?_,congrArg Prod.fst h.2.1,h.2.2⟩
  have ho : b.out = (a.out ++ [true]) ++ [decide (a.env testAccept=1)] := h.1
  simpa [hb',List.append_assoc] using ho

/-- `sec:algorithm`, paper/paper.tex: two layers of framing for
one bit of the certified-column list. -/
def writeCertBit : St VV MM :=
  .seq (.op (.emit true)) (.seq (.op (.emit true)) emitFrameBit)

/-- `sec:algorithm`, paper/paper.tex: a certified-column bit is
written inside both its list frame and the outer stage frame. -/
theorem writeCertBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit : Bool)
    (hb : a.env testAccept = if bit then 1 else 0) :
    Hs C writeCertBit a 8 (fun b => WrittenBit a b [true,true,true,bit]) := by
  unfold writeCertBit
  refine Hs.seq (t1 := 1) (t2 := 6) (hs_emit C true a) (fun c hc' => ?_)
  subst c
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_emit C true _) (fun d hd => ?_)
  subst d
  have hdc : Cst {a with out := (a.out ++ [true]) ++ [true]} := ⟨hc.z,hc.one,hc.two⟩
  refine (emitFrameBit_run C _ hdc bit hb).mono le_rfl ?_
  intro b h
  exact ⟨by simpa [List.append_assoc] using h.out,h.ip,h.env⟩

end NearQuarticWires.StageCert
