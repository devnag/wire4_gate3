import Proof.Quartic.StageGreedyContext.Resources

/-!
# The literal carrier prepares one actual common-context computation

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: only
the actual context call's reset ruler has a nonzero blank length. -/
noncomputable def Request.blankLengths {B1 B2 : ℕ} (r : Request B1 B2)
    (i : Fin ((setup B1 B2).program.tapeCount+4)) : ℕ :=
  if i=ruler (setup B1 B2).program then r.setupBudget else 0

/-- `lem:print`, paper/paper.tex: the
ordinary input convention places the sole original framed carrier
on tape zero and no semantic data on any working tape. -/
noncomputable def Request.start {B1 B2 : ℕ} (r : Request B1 B2) :
    WState ((setup B1 B2).program.tapeCount+3) 24 :=
  idealStart _ _ r.word r.blankLengths

/-- `lem:print`, paper/paper.tex: one
finite preparation acquisition and measured arity pass precede the
single actual common-context computation. -/
def prepareContext (p : Program) : WM (p.tapeCount+3) 24 :=
  .seq (acquirePrep 0 (bank p (tape0 p)) registers)
    (arityPrefix (bank p (tape0 p)) 1 registers)

/-- `lem:print`, paper/paper.tex: the
physical pre-call state retains the original carrier and unread
suffix, has the exact framed prepared input and reset call-bank heads,
and already holds the measured original-arity context prefix. -/
structure PrefixReady {B1 B2 : ℕ} (r : Request B1 B2)
    (a : WState ((setup B1 B2).program.tapeCount+3) 24) : Prop where
  source : a.st 0=frame r.word
  position : a.sh 0=2*(natWord r.prep.length++r.prep).length
  contextPrefix : a.st 1=Streaming.marks (natWord r.prepared.call.n)
  contextHead : a.sh 1=2*(natWord r.prepared.call.n).length
  contextCount : a.val (registers 13)=2*(natWord r.prepared.call.n).length
  input : a.st (bank (setup B1 B2).program (tape0 (setup B1 B2).program))=frame r.prep
  blank : ∀j,j≠tape0 (setup B1 B2).program→a.st (bank (setup B1 B2).program j)=[]
  heads : ∀j,a.sh (bank (setup B1 B2).program j)=0
  rulerWord : a.st (ruler (setup B1 B2).program)=List.replicate r.setupBudget false
  rulerHead : a.sh (ruler (setup B1 B2).program)=0
  output : a.st 2=[]
  outputHead : a.sh 2=0
  outputCount : a.val 20=0
  scanCount : a.val 21=0

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual carrier instructions
construct the complete pre-call state from empty workspace, reading
only the finite preparation and leaving every suffix byte untouched. -/
theorem prepareContext_spec {B1 B2 : ℕ} (r : Request B1 B2) :
    ∃a,WExec r.capacity (prepareContext (setup B1 B2).program) r.start a r.prefixSteps ∧
      PrefixReady r a := by
  let p:=(setup B1 B2).program
  let IN:=bank p (tape0 p)
  let σ:=r.start
  have hIN0 : IN≠(0 : Fin (p.tapeCount+4)) := (bank_off p (tape0 p)).1
  have hIN1 : IN≠(1 : Fin (p.tapeCount+4)) := (bank_off p (tape0 p)).2.1
  have hIN2 : IN≠(2 : Fin (p.tapeCount+4)) := (bank_off p (tape0 p)).2.2
  have hINR : IN≠ruler p:=bank_ne_ruler p _
  have oneval : (1 : Fin (p.tapeCount+4)).val=1:=by
    change 1%(p.tapeCount+4)=1
    exact Nat.mod_eq_of_lt (by omega)
  have twoval : (2 : Fin (p.tapeCount+4)).val=2:=by
    change 2%(p.tapeCount+4)=2
    exact Nat.mod_eq_of_lt (by omega)
  have h10 : (1 : Fin (p.tapeCount+4))≠0 := by
    intro h;have hh:=congrArg Fin.val h;simp only [oneval,Fin.val_zero] at hh;omega
  have h20 : (2 : Fin (p.tapeCount+4))≠0 := by
    intro h;have hh:=congrArg Fin.val h;simp only [twoval,Fin.val_zero] at hh;omega
  have h21 : (2 : Fin (p.tapeCount+4))≠1 := by
    intro h;have hh:=congrArg Fin.val h;simp only [twoval,oneval] at hh;omega
  have init_st (t : Fin (p.tapeCount+4)) : σ.st t=
      if t.val=0 then frame r.word else List.replicate
        (if t=ruler p then r.setupBudget else 0) false := rfl
  have init_sh (t : Fin (p.tapeCount+4)) : σ.sh t=0:=rfl
  have h1R : (1 : Fin (p.tapeCount+4))≠ruler p := by
    intro h;have hh:=congrArg Fin.val h
    change (1 : Fin (p.tapeCount+4)).val=3 at hh
    rw [oneval] at hh;omega
  have h2R : (2 : Fin (p.tapeCount+4))≠ruler p := by
    intro h;have hh:=congrArg Fin.val h
    change (2 : Fin (p.tapeCount+4)).val=3 at hh
    rw [twoval] at hh;omega
  have initBlank (j : Fin p.tapeCount) : σ.st (bank p j)=[] := by
    rw [init_st,if_neg (show (bank p j).val≠0 by change 4+j.val≠0;omega),
      if_neg (bank_ne_ruler p j),List.replicate_zero]
  have initContext : σ.st (1 : Fin (p.tapeCount+4))=[] ∧ σ.sh 1=0 := by
    constructor
    · rw [init_st,oneval,if_neg (by decide),if_neg h1R,List.replicate_zero]
    · exact init_sh 1
  have initOutput : σ.st (2 : Fin (p.tapeCount+4))=[] ∧ σ.sh 2=0 := by
    constructor
    · rw [init_st,twoval,if_neg (by decide),if_neg h2R,List.replicate_zero]
    · exact init_sh 2
  have initRuler : σ.st (ruler p)=List.replicate r.setupBudget false ∧ σ.sh (ruler p)=0 := by
    constructor
    · rw [init_st,if_neg (show (ruler p).val≠0 from by change (3:ℕ)≠0;decide),if_pos rfl]
    · exact init_sh _
  obtain ⟨a,ea,has,hapos,hai,haih,ha2,ha3,ha5,ha10,haz,haoff,hatapes⟩:=
    acquirePrep_spec r.capacity (0 : Fin (p.tapeCount+4)) IN registers hIN0.symm
      r.prep r.suffix [] σ
      (by rw [init_st,Fin.val_zero,if_pos rfl]
          simp only [Request.word,NearCubicGates.Close.Codec.frame_eq_marks,Streaming.marks_append,List.append_assoc,List.nil_append])
      rfl (initBlank _) rfl (by intro j;rfl) r.acquire_capacity
  have haContext : a.st (1 : Fin (p.tapeCount+4))=[] ∧ a.sh 1=0 := by
    have h:=hatapes 1 h10 hIN1.symm
    exact ⟨h.1.trans initContext.1,h.2.trans initContext.2⟩
  have haOutput : a.st (2 : Fin (p.tapeCount+4))=[] ∧ a.sh 2=0 := by
    have h:=hatapes 2 h20 hIN2.symm
    exact ⟨h.1.trans initOutput.1,h.2.trans initOutput.2⟩
  have haRuler : a.st (ruler p)=List.replicate r.setupBudget false ∧ a.sh (ruler p)=0 := by
    have h:=hatapes (ruler p) (by simp [ruler]) hINR.symm
    exact ⟨h.1.trans initRuler.1,h.2.trans initRuler.2⟩
  have haBlank (j : Fin p.tapeCount) (hj : j≠tape0 p) : a.st (bank p j)=[] := by
    have hne : bank p j≠IN:=fun h=>hj (bank_injective p h)
    exact (hatapes (bank p j) (bank_off p j).1 hne).1.trans (initBlank j)
  have haHeads (j : Fin p.tapeCount) : a.sh (bank p j)=0 := by
    by_cases hj : j=tape0 p
    · subst j;exact haih
    · have hne : bank p j≠IN:=fun h=>hj (bank_injective p h)
      exact (hatapes (bank p j) (bank_off p j).1 hne).2
  have haZero (q : Fin 24) (hq : ∀i : Fin 16,registers i≠q) : a.val q=0 := by
    exact haoff q hq
  have ha20 : a.val (20 : Fin 24)=0 := by
    apply haZero
    intro i h
    have hv:=congrArg Fin.val h
    change i.val+4=20 at hv
    have hi:=i.isLt
    omega
  have ha21 : a.val (21 : Fin 24)=0 := by
    apply haZero
    intro i h
    have hv:=congrArg Fin.val h
    change i.val+4=21 at hv
    have hi:=i.isLt
    omega
  obtain ⟨tail,hprep⟩:=r.prep_prefix
  have earity:=arityPrefix_spec r.capacity IN (1 : Fin (p.tapeCount+4)) registers hIN1
    r.prepared.call.n tail a (hai.trans (congrArg frame hprep)) haih
    haContext.1 haContext.2 haz (by
      rw [ha2,ha10]
      convert r.arity_capacity using 1
      omega)
  let b:=arityPrefixState 1 registers a r.prepared.call.n
  refine ⟨b,(ea.seq earity).mono ?_,?_⟩
  · unfold Request.prefixSteps arityPrefixCost
    rw [ha2,ha10]
    omega
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hs : a.st 0=frame r.word:=by rw [has,init_st,Fin.val_zero,if_pos rfl]
      simpa [b,arityPrefixState,appendO] using hs
    · simpa [b,arityPrefixState,appendO] using hapos
    · simp [b,arityPrefixState,appendO,haContext.1]
    · simp [b,arityPrefixState,appendO,haContext.2,Streaming.marks_length]
    · have hz17 : a.val (17 : Fin 24)=0:=haz 13 (by decide) (by decide)
      simp [b,arityPrefixState,appendO,registers,Streaming.marks_length,hz17]
    · change b.st IN=frame r.prep
      simpa [b,arityPrefixState,appendO,hIN1] using hai
    · intro j hj
      change b.st (bank p j)=[]
      simpa [b,arityPrefixState,appendO,(bank_off p j).2.1] using haBlank j hj
    · intro j
      change b.sh (bank p j)=0
      simpa [b,arityPrefixState,appendO,(bank_off p j).2.1] using haHeads j
    · simpa [b,arityPrefixState,appendO,ruler] using haRuler.1
    · simpa [b,arityPrefixState,appendO,ruler] using haRuler.2
    · change b.st (2 : Fin (p.tapeCount+4))=[]
      simpa [b,arityPrefixState,appendO,h21] using haOutput.1
    · change b.sh (2 : Fin (p.tapeCount+4))=0
      simpa [b,arityPrefixState,appendO,h21] using haOutput.2
    · simpa [b,arityPrefixState,appendO,registers] using ha20
    · simpa [b,arityPrefixState,appendO,registers] using ha21

end NearQuarticWires.StageGreedyContext
