import Proof.Quartic.StageCertNative.PriceOriginal
import Proof.Quartic.StageCertNative.Width
import Proof.Quartic.StageCertNative.HeaderData
import Proof.Quartic.StagePrint.FullTableBounds

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms
open StageCertificateControl

theorem price_tableWidth (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(actualTable r.base).q+3) 0 :=
  JobPrice.of_arity ⟨nativeWidthCoefficient B1,nativeWidthDegree B1,
    fun r=>actualTable_width r.base⟩

theorem original_count_price (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>(actualTable r).count) := by
  refine ⟨2,0,fun r=>?_⟩
  simpa only [pow_zero,mul_one] using (actualTable_count r).2

private theorem native_square_scale {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    ((actualTable r).matrix.U+1)^2≤8*2^(r.prepared.call.n-r.prepared.selected.1.k) := by
  have hu : 1≤(actualTable r).matrix.U := Nat.one_le_two_pow
  have hc:=(actualTable_count r).2
  change (actualTable r).matrix.U*(actualTable r).matrix.U≤
    2*2^(r.prepared.call.n-r.prepared.selected.1.k) at hc
  nlinarith

theorem original_table_cost (a : WilliamsAlgorithm) (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>StagePrint.fullTableCost a (actualTable r)) := by
  let e:=CompetitorCrossScheduler.exponent a
  refine ⟨8*(CompetitorCountTable.coefficient a+13000)*(nativeWidthCoefficient B1)^e,
    nativeWidthDegree B1*e,fun r=>?_⟩
  have hw : (actualTable r).matrix.d+(actualTable r).matrix.p+1≤
      nativeWidthCoefficient B1*(r.prepared.call.n+1)^nativeWidthDegree B1 := by
    have hh:=actualTable_width r
    unfold StagePrint.TableRequest.q at hh
    omega
  calc
    _≤(CompetitorCountTable.coefficient a+13000)*((actualTable r).matrix.U+1)^2*
        ((actualTable r).matrix.d+(actualTable r).matrix.p+1)^e :=
      StagePrint.fullTableCost_bound a (actualTable r)
    _≤(CompetitorCountTable.coefficient a+13000)*
        (8*2^(r.prepared.call.n-r.prepared.selected.1.k))*
        (nativeWidthCoefficient B1*(r.prepared.call.n+1)^nativeWidthDegree B1)^e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (native_square_scale r))
        (Nat.pow_le_pow_left hw _)
    _=_ := by rw [mul_pow,←pow_mul];ring

private theorem table_output_length (t : StagePrint.TableRequest) :
    t.output.length=t.count*(2*t.q+3)+1 := by
  have hlen : (pvals false (StagePrint.cutTable t.matrix)).length=t.count := by
    simp only [pvals,Bool.false_eq_true,if_false,StagePrint.TableRequest.count,
      List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn]
    simp
  simp only [StagePrint.TableRequest.output,recStream,List.length_append,List.length_cons,
    List.length_nil,List.length_flatMap,List.map_map,Function.comp_def,frame_length,
    SignedSortKey.binary_length,List.map_const',List.sum_replicate,hlen,
    smul_eq_mul]
  ring

theorem original_table_output (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>(actualTable r).output.length) := by
  have hwidth:=((JobPrice.constant 2).mul (price_tableWidth B1 B2)).mono
    (fun r=>show 2*(actualTable r.base).q+3≤2*((actualTable r.base).q+3) by omega)
  have hh:=((original_count_price B1 B2).mul_arity
    (g:=fun r=>2*(actualTable r).q+3) hwidth).add (OriginalPrice.constant 1)
  exact hh.mono (fun r=>by rw [table_output_length])

theorem original_native_steps (a : WilliamsAlgorithm) (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>StageRecovery.NativeTableFrame.steps a (actualTable r)) := by
  have ht:=(original_table_cost a B1 B2).mul_arity (g:=fun _=>4) (JobPrice.constant 4)
  have ho:=(original_table_output B1 B2).mul_arity (g:=fun _=>100) (JobPrice.constant 100)
  have hh:=(ht.add ho).add (OriginalPrice.constant 27)
  refine hh.mono ?_
  intro r
  unfold StageRecovery.NativeTableFrame.steps
  omega

theorem original_native_stream (B1 B2 : ℕ) :
    OriginalPrice (fun r : IndexedRequest B1 B2=>(nativeHeaderRequest r).stream.length) := by
  have hc : OriginalPrice (fun r : IndexedRequest B1 B2=>
      ((actualTable r).matrix.U+1)^2) := ⟨8,0,fun r=>by
    simpa only [pow_zero,mul_one] using native_square_scale r⟩
  have hp:=hc.mul_arity (g:=fun r=>100*((actualTable r).q+3)^2)
    ((JobPrice.constant 100).mul ((price_tableWidth B1 B2).pow 2))
  refine hp.mono ?_
  intro r
  have hs : (nativeHeaderRequest r).stream.length≤
      (MatrixScoreBatch.physicalInput (actualTable r).matrix).length := by
    change ((actualTable r).matrix.cuts.flatMap
      (MatrixScoreBatch.cutWord (actualTable r).matrix.p)).length≤_
    simp only [MatrixScoreBatch.physicalInput,MatrixScoreBatch.word,frame_length,List.length_append]
    omega
  have hi:=StagePrint.table_input_length (actualTable r)
  have hu : (actualTable r).matrix.U+1≤((actualTable r).matrix.U+1)^2 :=
    Nat.le_self_pow (by decide) _
  have hq : (actualTable r).matrix.d+(actualTable r).matrix.p+1≤(actualTable r).q+3 := by
    unfold StagePrint.TableRequest.q
    omega
  refine hs.trans (hi.trans ?_)
  calc
    _≤100*((actualTable r).matrix.U+1)^2*((actualTable r).q+3)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hu) (Nat.pow_le_pow_left hq _)
    _=_ := by ring

end NearQuarticWires.StageCertNative
