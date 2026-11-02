import Proof.Quartic.StageCert.WriteBit
import Proof.Quartic.StageCert.CopyPayload

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: global column-count registers. -/
def columnCount : Fin VV := ⟨50, by decide⟩
def columnIndex : Fin VV := ⟨51, by decide⟩

/-- `sec:algorithm`, paper/paper.tex: exact nested framing of the
sequence of certified-column bits, without its final delimiters. -/
noncomputable def certBitsBody (columns : List (List MomentRecord)) : List Bool :=
  framedBody (framedBody (columns.map columnPass))

/-- `prop:time`, paper/paper.tex: the number of column
headers and signed moment records visited by the scan. -/
def streamWork : List (List MomentRecord) → ℕ
  | [] => 0
  | rs :: tail => rs.length+1+streamWork tail

/-- `sec:algorithm`, paper/paper.tex: one physical column step. -/
def columnBody : St VV MM :=
  .seq columnBlock (.seq writeCertBit (.op (.inc columnIndex)))

/-- `sec:algorithm`, paper/paper.tex: the complete column loop. -/
def columnStream : St VV MM := .loop (.lt columnIndex columnCount) columnBody

/-- `sec:algorithm`, paper/paper.tex: the global column scan has
an exact output, input cursor, and arithmetic-register frame. -/
structure StreamReduced (C : Ctx) (a b : DS VV MM)
    (columns : List (List MomentRecord)) (rest : List Bool) : Prop where
  cst : Cst b
  tail : C.inp.drop b.ip = rest
  out : b.out = a.out ++ certBitsBody columns
  index : b.env columnIndex = a.env columnIndex+columns.length
  keep : Fr a b (columnIndex :: blockScratch)

/-- `sec:algorithm`, paper/paper.tex: the physical column-major
scan computes exactly the complete certificate bit stream. -/
theorem columnStream_run (C : Ctx) (columns : List (List MomentRecord)) :
    ∀ (a : DS VV MM), Cst a → ∀ rest,
      C.inp.drop a.ip = columns.flatMap (listWord momentRecordWord) ++ rest →
      a.env columnIndex+columns.length = a.env columnCount →
      a.env columnCount < 2^C.Wd →
      (∀ rs ∈ columns, natBitLength rs.length+2 ≤ C.Wd ∧
        ∀ r ∈ rs, natBitLength (if r.1<0 then 1 else 0)+2 ≤ C.Wd ∧
          natBitLength r.1.natAbs+2 ≤ C.Wd ∧ natBitLength r.2+2 ≤ C.Wd) →
      Hs C columnStream a (10000*(streamWork columns+1)*(C.Wd+1))
        (fun b => StreamReduced C a b columns rest) := by
  classical
  induction columns with
  | nil =>
    intro a hc rest hin hi hn hw
    have ht : Cnd.eval a (.lt columnIndex columnCount) = false := by
      simp only [Cnd.eval,decide_eq_false_iff_not]
      simp only [List.length_nil,Nat.add_zero] at hi
      omega
    refine ⟨a,2,Ex.loopF (by norm_num [Cnd.wf,columnIndex,columnCount]) ht,?_,?_⟩
    · simp only [streamWork,zero_add,mul_one]
      omega
    · exact ⟨hc,by simpa using hin,by simp [certBitsBody,framedBody],by simp,Fr.refl _ _⟩
  | cons rs columns ih =>
    intro a hc rest hin hi hn hw
    have hwr := hw rs (by simp)
    have ht : Cnd.eval a (.lt columnIndex columnCount) = true := by
      simp only [Cnd.eval,decide_eq_true_eq]
      simp only [List.length_cons] at hi
      omega
    obtain ⟨b,nb,eb,hbCost,hb⟩ := columnBlock_run C a hc rs
      (columns.flatMap (listWord momentRecordWord) ++ rest)
      (by simpa [List.flatMap_cons,List.append_assoc] using hin) hwr.1 hwr.2
    obtain ⟨d,nd,ed,hdCost,hd⟩ := writeCertBit_run C b hb.cst (columnPass rs) hb.accept
    have hdCst : Cst d := ⟨by rw [hd.env]; exact hb.cst.z,
      by rw [hd.env]; exact hb.cst.one,by rw [hd.env]; exact hb.cst.two⟩
    have hdI : d.env columnIndex = a.env columnIndex := by rw [hd.env]; exact hb.keep _ (by decide)
    have hdN : d.env columnCount = a.env columnCount := by rw [hd.env]; exact hb.keep _ (by decide)
    have hinc : d.env columnIndex+1 < 2^C.Wd := by simp only [List.length_cons] at hi; omega
    let e := d.set columnIndex (d.env columnIndex+1)
    have ee : Ex C (.op (.inc columnIndex)) d e 1 := Ex.op (OpEx.inc columnIndex d hinc)
    have ebody : Ex C columnBody a e (nb+(nd+1+1)+1) := Ex.seq eb (Ex.seq ed ee)
    have heCst : Cst e := Cst.of_fr hdCst (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
    have heTail : C.inp.drop e.ip = columns.flatMap (listWord momentRecordWord) ++ rest := by
      change C.inp.drop d.ip = _
      rw [hd.ip]
      exact hb.tail
    have heI : e.env columnIndex = a.env columnIndex+1 := by simp [e,hdI]
    have heKeep : Fr a e (columnIndex :: blockScratch) := by
      intro y hy
      simp only [List.mem_cons,not_or] at hy
      change (d.set columnIndex _).env y = _
      rw [DS.set_env_ne _ _ hy.1,hd.env]
      exact hb.keep y hy.2
    obtain ⟨f,nf,ef,hfCost,hf⟩ := ih e heCst rest heTail
      (by rw [heI,heKeep columnCount (by decide)]; simp only [List.length_cons] at hi; omega)
      (by rw [heKeep columnCount (by decide)]; exact hn)
      (fun r hr => hw r (by simp [hr]))
    refine ⟨f,nb+(nd+1+1)+1+nf+2,
      Ex.loopT (by norm_num [Cnd.wf,columnIndex,columnCount]) ht ebody ef,?_,?_⟩
    · simp only [streamWork]
      nlinarith
    · refine ⟨hf.cst,hf.tail,?_,?_,heKeep.trans hf.keep⟩
      · rw [hf.out]
        change d.out ++ _ = _
        rw [hd.out,hb.out]
        simp [certBitsBody,framedBody,List.append_assoc]
      · rw [hf.index,heI]
        simp only [List.length_cons]
        omega

end NearQuarticWires.StageCert
