import Proof.Quartic.StageNativeRowCount.Request
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells

def Request.sourceWidth (r : Request) : ℕ :=
  (4*r.header.call.n+1)*Nat.clog 2 (r.header.call.n+1)+5

def Request.nativeWidth (r : Request) : ℕ := r.sourceWidth+r.header.call.n+6

def Request.firstFive (r : Request) : List ℕ :=
  [r.header.call.n,r.sourceWidth,r.nativeWidth,r.header.parameters.r,r.header.parameters.b]

theorem Request.payload_split (r : Request) : r.payload = r.firstFive.flatMap natWord ++
    [r.header.parameters.s,StagePullback.translationNumber
      (Builder.star r.header.call r.header.prepared)
      (Builder.translation r.header.call r.header.prepared r.header.witness)].flatMap natWord := by
  simp only [Request.payload,StagePrint.Header.baseHeaderValues,Request.firstFive,
    Request.sourceWidth,Request.nativeWidth,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]

theorem Request.firstFive_bound (r : Request) :
    ∀ v ∈ r.firstFive, v ≤ 16*(r.header.call.n+1)^2 := by
  let n := r.header.call.n
  have hc : Nat.clog 2 (n+1) ≤ n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hh := Nat.mul_le_mul_left (4*n+1) hc
  have hg := r.geometry_bounds
  intro v hv
  simp only [Request.firstFive,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · change n ≤ 16*(n+1)^2
    nlinarith
  · change (4*n+1)*Nat.clog 2 (n+1)+5 ≤ 16*(n+1)^2
    nlinarith
  · change (4*n+1)*Nat.clog 2 (n+1)+5+n+6 ≤ 16*(n+1)^2
    nlinarith
  · exact hg.2.1.trans (by change n≤16*(n+1)^2; nlinarith)
  · exact hg.2.2.trans (by change n≤16*(n+1)^2; nlinarith)

theorem bitLength_le (v : ℕ) : natBitLength v ≤ v+1 := by
  unfold natBitLength
  have h := Nat.log_le_self 2 v
  omega

theorem leadOnes_framed_prefix (L : ℕ) (rest : List Bool) :
    leadOnes (frame (List.replicate L true ++ false :: rest)) = 2*L+1 := by
  induction L with
  | zero => simp [List.replicate_zero,frame,leadOnes]
  | succ L ih =>
      simp only [List.replicate_succ,List.cons_append,frame,leadOnes]
      rw [ih]
      omega

/-- `prop:time`, paper/paper.tex: the existing
framed header's real first arity codec supplies the workspace prefix. -/
theorem Request.leading (r : Request) : leadOnes r.word=2*natBitLength r.header.call.n+1 := by
  change leadOnes (frame r.payload)=_
  have hp : r.payload = natWord r.header.call.n ++
      (StagePrint.Header.baseHeaderValues r.header).tail.flatMap natWord := by
    rfl
  rw [hp,Pool.natWord_eq,List.append_assoc,List.cons_append]
  exact leadOnes_framed_prefix _ _

def rowCountSizes : Sz := ⟨10000,1,0,0,0,0⟩

theorem Request.setup_exact (r : Request) :
    rowCountSizes.W (leadOnes r.word)=20000*(2^natBitLength r.header.call.n)^2 := by
  change 2^(1*leadOnes r.word)*10000=_
  rw [one_mul,r.leading,pow_succ,show 2*natBitLength r.header.call.n=
    natBitLength r.header.call.n*2 by omega,pow_mul]
  ring

/-- `prop:time`, paper/paper.tex: all bounded
scalar/width guards follow from the actual original-arity input prefix. -/
theorem Request.setup_lower (r : Request) :
    100*(r.header.call.n+1)^2 ≤ rowCountSizes.W (leadOnes r.word) := by
  rw [r.setup_exact]
  have hh := lt_natBitLength r.header.call.n
  nlinarith

theorem Request.setup_upper (r : Request) :
    rowCountSizes.W (leadOnes r.word) ≤ 80000*(r.header.call.n+1)^2 := by
  rw [r.setup_exact]
  have hh : 2^natBitLength r.header.call.n ≤ 2*(r.header.call.n+1) := by
    simp only [natBitLength,pow_succ]
    have h := Nat.pow_log_le_add_one 2 r.header.call.n
    omega
  have hsq := Nat.pow_le_pow_left hh 2
  nlinarith only [hsq]

end NearQuarticWires.StageNativeRowCount
