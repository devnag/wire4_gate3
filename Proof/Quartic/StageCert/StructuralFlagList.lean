import Proof.Quartic.StageCert.EdgeFlagSource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain.Compact

/-- `def:mask` and `lem:print`, paper/paper.tex: the literal structural factors for a finite original
edge sequence, in exactly the order consumed by the mask serializer. -/
noncomputable def structuralFlagList {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (edges : List (Fin 8)) : List Bool :=
  edges.map (StagePrint.callStructural r.call r.rules r.walk)

/-- `def:mask` and `lem:print`, paper/paper.tex: each structural factor is computed by its actual
ordinary source call, never by a supplied Boolean flag table. -/
def emitStructuralFlags : List (Fin 8)→St VV MM
  | [] => skipS
  | edge::edges => .seq (emitEdgeStructural edge) (emitStructuralFlags edges)

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: one or eight original
structural calls produce the exact finite flag suffix, with all retained
source bytes and the original term ordinal preserved. -/
theorem emitStructuralFlags_run {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (edges : List (Fin 8)) (width : ℕ) (input : List Bool) (L B K : ℕ)
    (hW : 2≤width) (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^width)
    (hNfit : 2*r.selected.1.N≤2^width)
    (hlfit : ∀edge,natBitLength (r.edgeRequest edge).left.val+2<2^width)
    (hrfit : ∀edge,natBitLength (r.edgeRequest edge).right.val+2<2^width)
    (hroom : ∀edge,(StageMainMask.structuralWord (r.edgeRequest edge)).length≤L)
    (hbudget : ∀edge,StageMainMask.structuralBudget (r.edgeRequest edge)≤B)
    (hcost : ∀edge,9*(Program.prepWord B1 B2 r.call r.witness).length+
      40*natBitLength (r.edgeRequest edge).left.val+
      40*natBitLength (r.edgeRequest edge).right.val+L+B+180≤K)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength=(Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length)
    (hb : a.env patternBase=r.selected.1.N) (hi : a.env sourceTermIndex=r.index.val) :
    Hs (structuralSourceContext B1 B2 width input L B) (emitStructuralFlags edges) a
      (edges.length*(K+2)+1) (fun z=>
      z.out=a.out++structuralFlagList r edges ∧ z.ip=a.ip ∧ z.ram=a.ram ∧ z.rc=a.rc ∧
      z.kin=[] ∧ Cst z ∧ Fr a z (vJ::edgeStructuralScratch)) := by
  induction edges generalizing a with
  | nil =>
    refine (hs_zero _ vJ a).mono (by simp) ?_
    rintro z rfl
    exact ⟨by simp [structuralFlagList],rfl,rfl,rfl,hkin,
      Cst.of_fr hc (Fr.set _ _ (T := [vJ]) (by simp)) (by decide),Fr.set _ _ (by simp)⟩
  | cons edge edges ih =>
    unfold emitStructuralFlags
    apply Hx.hs
    refine Hs.then (emitEdgeStructural_run r edge width input L B a hc hkin hbits hlen hcursor
      hb hi hW hfit hNfit (hlfit edge) (hrfit edge) (hroom edge) (hbudget edge))
      (fun b ⟨bo,bi,br,brc,bkin,bc,bf⟩ n1 hn1=>?_)
    refine Hs.last (ih b bc bkin (by rw [br]; exact hbits)
      ((bf _ (by decide)).trans hlen) (by rw [brc]; exact hcursor)
      ((bf _ (by decide)).trans hb) ((bf _ (by decide)).trans hi))
      (fun z ⟨zo,zi,zr,zrc,zkin,zc,zf⟩ n2 hn2=>?_)
    refine ⟨⟨?_,zi.trans bi,zr.trans br,zrc.trans brc,zkin,zc,
      (bf.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx)).trans zf⟩,?_⟩
    · rw [zo,bo]
      simp only [structuralFlagList,List.map_cons,List.singleton_append,List.append_assoc]
    · have hh := hcost edge
      simp only [List.length_cons] at ⊢
      nlinarith

end NearQuarticWires.StageCert.Tokens
