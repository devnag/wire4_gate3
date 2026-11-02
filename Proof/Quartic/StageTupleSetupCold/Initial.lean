import Proof.Quartic.StageTupleSetupCold.CoefficientStages

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: the
bounded source primitives have a common private tape/counter capacity.
Complete Terms occur only linearly; this capacity is not an arithmetic
input, a supplied hint or a term-count decode. -/
def capacity (r : TermCutRequest) : ℕ :=1000000*(r.word.length+r.setupStructuralMagnitude+
  (natWord r.stackWidth).length+r.contextWord.length+(natWord r.degree).length+
  (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)).length+
  (natWord (r.stackWidth+1)++intWord 0).length+
  (natWord (r.stackWidth+1)++intWord 1).length+1)

namespace Helpers

/-- `lem:print` and `prop:time`, paper/paper.tex: each internally proved finite
blank margin belongs to exactly one source loader or small helper.
No private bank has a public allocator or cache input. -/
def lens (F : Helpers) (r : TermCutRequest) (i : Fin (F.ns+1)) : ℕ :=
  if i.val=13 then r.sourceLoadCapacity else
  if i.val=20 then F.widthBudget r.stackWidth else
  if i.val=21 then F.rowBudget (rowRequest r) else
  if i.val=22 then F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 0) else
  if i.val=23 then F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 1) else 0

def initial (F : Helpers) (r : TermCutRequest) : WState F.ns 8 :=
  idealStart F.ns 8 r.word (F.lens r)

/-- `lem:print`, paper/paper.tex: every
initial physical tape head starts at its ordinary zero cursor. -/
theorem initial_zero_heads (F : Helpers) (r : TermCutRequest) : ∀i,(F.initial r).sh i=0 :=fun _=>rfl

/-- `lem:print`, paper/paper.tex: the
cold controller begins with no precomputed register values. -/
theorem initial_zero_registers (F : Helpers) (r : TermCutRequest) :
    ∀i,(F.initial r).val i=0 :=fun _=>rfl

/-- `lem:print`, paper/paper.tex: every
private helper bank is empty outside the explicit retained-data slots. -/
theorem initial_other (F : Helpers) (r : TermCutRequest) (i : Fin (F.ns+1))
    (h : ∀j : Fin 24,i≠F.data j) : (F.initial r).st i=[] := by
  have hz : i.val≠0 :=by
    intro hi
    exact h 0 (Fin.ext hi)
  have hn (j : Fin 24) : i.val≠j.val :=fun hi=>h j (Fin.ext hi)
  have h13 : i.val≠13:=hn 13
  have h20 : i.val≠20:=hn 20
  have h21 : i.val≠21:=hn 21
  have h22 : i.val≠22:=hn 22
  have h23 : i.val≠23:=hn 23
  simp only [initial,idealStart,if_neg hz,lens,if_neg h13,if_neg h20,
    if_neg h21,if_neg h22,if_neg h23,List.replicate_zero]

/-- `lem:print`, paper/paper.tex: the
actual loader receives only the unchanged framed original source and
its own internally justified finite blank workspace. -/
theorem initial_loader_input (F : Helpers) (r : TermCutRequest) :
    (fun j : Fin 14=>(F.initial r).st (F.loader j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.sourceLoadCapacity false) := by
  funext j
  fin_cases j <;> rfl

/-- `lem:print`, paper/paper.tex: each
retained-data slot has exactly its specified ordinary initial bytes. -/
theorem initial_data (F : Helpers) (r : TermCutRequest) (i : Fin 24) :
    (F.initial r).st (F.data i)=
      if i.val=0 then frame r.word else List.replicate (F.lens r (F.data i)) false :=rfl

/-- `lem:print`, paper/paper.tex: the
final physical output tape is genuinely fresh at the cold entry. -/
theorem lens_output (F : Helpers) (r : TermCutRequest) : F.lens r (F.data 16)=0 :=rfl

/-- `lem:print`, paper/paper.tex: the
actual cold loader starts at the unchanged framed original request,
retains its eleven genuine source fields and leaves every private
helper bank unchanged. All heads and controller registers remain zero. -/
theorem load_ready (F : Helpers) (r : TermCutRequest) :
    ∃σ tout,WXExec (capacity r) (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadM F.loader)
      (F.initial r) σ r.sourceLoadCost ∧
      Docked F.loader (F.initial r) σ (fun _=>0) tout ∧
      (∀j : Fin 13,σ.st (F.loader (Fin.castAdd 1 j))=r.loadedSource j) ∧
      (∀i,σ.sh i=0) ∧ (∀i,σ.val i=0) := by
  obtain ⟨σ,tout,he,hd,ht⟩:=sourceLoad_docked (capacity r) r F.loader
    StageTupleSetup.BankLayout.loaderBank_injective (F.initial r)
    (F.initial_loader_input r) (fun _=>rfl)
  exact ⟨σ,tout,he,hd,fun j=>(hd.st _).trans (ht j),
    docked_zero_heads hd (F.initial_zero_heads r),fun i=>(congrFun hd.val i)⟩

end Helpers

end NearQuarticWires.StageTupleSetupCold
