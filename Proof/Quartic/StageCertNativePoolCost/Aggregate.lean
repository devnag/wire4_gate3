import Proof.Quartic.StageCertNativePoolCost.Cache
import Proof.Quartic.StageCertNativePoolCost.Reserve

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativePoolCost

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertNative StageCertificateControl

/-- `prop:time`, paper/paper.tex: each
actual term includes the same complete cached-source and count costs,
its literal input length, actual compiler clock and signed output bytes. -/
noncomputable def jobCharge {B1 B2 : ℕ} (budget : TermJob B1 B2→ℕ) (j : TermJob B1 B2) : ℕ :=
  cachedSourceBudget j.base+cachedCountBudget j.base+(cachedSourceWord j.base).length+
    natBitLength (termCount j.base)+j.word.length+budget j+(termWeakWord j).length+1

theorem price_jobCharge {B1 B2 : ℕ} {budget : TermJob B1 B2→ℕ} (hb : JobPrice budget 4) :
    JobPrice (jobCharge budget) 4 := by
  have h0:=(price_cachedSourceBudget B1 B2).raise (e:=4) (by decide)
  have h1:=(price_cachedCountBudget B1 B2).raise (e:=4) (by decide)
  have h2:=(price_cachedSourceLength B1 B2).raise (e:=4) (by decide)
  have h3:=(price_countBits B1 B2).raise (e:=4) (by decide)
  have h4:=(price_wordLength B1 B2).raise (e:=4) (by decide)
  have h5:=(price_termWeakLength B1 B2).raise (e:=4) (by decide)
  have h6:=(JobPrice.constant (B1:=B1) (B2:=B2) 1).raise (e:=4) (by decide)
  exact ((((((h0.add h1).add h2).add h3).add h4).add hb).add h5).add h6

/-- `prop:time`, paper/paper.tex: the
literal binary count decoder is priced using its actual binary-height
factor, including its head return and cached-count bootstrap. -/
theorem countHeader_cost_bound (T H : ℕ) (hT : 1≤T) (hH : 1≤H)
    (hb : natBitLength T≤H) : countHeaderReadCost T≤10000*T*H := by
  have hp:=NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le T
  have hm:=Nat.mul_le_mul (show natBitLength T+2≤H+2 by omega)
    (show 40*2^natBitLength T+40≤80*T+120 by omega)
  have hTH : T≤T*H:=Nat.le_mul_of_pos_right _ (by omega)
  have hHT : H≤T*H:=Nat.le_mul_of_pos_left _ (by omega)
  unfold countHeaderReadCost
  nlinarith only [hm,hTH,hHT,hT,hH,hb]

private theorem finite_sum_bound {T : ℕ} (f : Fin T→ℕ) (H : ℕ)
    (h : ∀i,f i≤H) : (List.ofFn f).sum≤T*H := by
  have hh:=List.sum_le_card_nsmul (List.ofFn f) H (by
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact h i)
  simpa only [List.length_ofFn,smul_eq_mul] using hh

/-- `prop:time`, paper/paper.tex: the
actual signed payload cache contains every original term exactly once,
including all framing bytes and zero or negative contributions. -/
theorem cache_prefix_bound {B1 B2 : ℕ} (r : IndexedRequest B1 B2) (H : ℕ)
    (hp : ∀i : Fin (termCount r),(termWeakWord ⟨r,i⟩).length≤H) :
    (StagePrint.poolPrefix ((termFamily r).caches termWeakWord) (termCount r)).length≤
      termCount r*(2*H+1) := by
  unfold StagePrint.poolPrefix
  simp only [List.length_flatMap]
  have hh:=List.sum_le_card_nsmul
    ((List.range (termCount r)).map fun j=>(frame ((termFamily r).caches termWeakWord j)).length)
    (2*H+1) (by
      intro v hv
      obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hv
      have hj':=List.mem_range.mp hj
      simp only [StagePrint.PoolFamily.caches,termFamily,dif_pos hj',frame_length]
      have hb:=hp ⟨j,hj'⟩
      omega)
  simpa only [List.length_map,List.length_range,smul_eq_mul] using hh

/-- `prop:time`, paper/paper.tex: the
legacy index-squared writer is summed over all actual terms before
the conservative outer loop-count multiplication is applied. -/
theorem loop_cost_bound {B1 B2 : ℕ} (budget : TermJob B1 B2→ℕ)
    (r : IndexedRequest B1 B2) (H : ℕ) (hH : 1≤H)
    (hs : (cachedSourceWord r).length≤H)
    (hi : ∀i : Fin (termCount r),(TermJob.word ⟨r,i⟩).length≤H)
    (hb : ∀i : Fin (termCount r),budget ⟨r,i⟩≤H) :
    (termFamily r).loopBudget budget≤10000*(termCount r)^4+
      2000*(termCount r)^2*H+10*termCount r+1 := by
  have hstep : (termFamily r).stepBudget budget≤
      termCount r*(10000*(termCount r)^2+2000*H) := by
    apply finite_sum_bound
    intro i
    have hix : i.val<termCount r := i.isLt
    have hx : i.val+1≤termCount r := by omega
    have hx2:=Nat.pow_le_pow_left hx 2
    have hii:=hi i
    have hbb:=hb i
    change StagePrint.poolOccurrenceCost i.val (cachedSourceWord r).length
      (TermJob.word ⟨r,i⟩).length (budget ⟨r,i⟩)≤_
    unfold StagePrint.poolOccurrenceCost StagePrint.writeIndexedCost StagePrint.callAppendCost
    nlinarith only [hx2,hs,hii,hbb,hH]
  have hh:=Nat.mul_le_mul_left (termCount r) hstep
  unfold StagePrint.PoolFamily.loopBudget
  change termCount r*((termFamily r).stepBudget budget+10)+1≤_
  nlinarith only [hh]

/-- `prop:time`, paper/paper.tex: all
literal cached-source construction, binary bootstrap, numeric index
writing, actual per-term calls and final signed cache scans are charged. -/
theorem whole_budget_bound {B1 B2 : ℕ} (budget : TermJob B1 B2→ℕ)
    (r : IndexedRequest B1 B2) (H : ℕ)
    (hj : ∀i : Fin (termCount r),jobCharge budget ⟨r,i⟩≤H) :
    wholeWeakOriginalBudget (termBudget:=budget) r≤
      10^7*((termCount r)^4+(termCount r)^2*H) := by
  let T:=termCount r
  have hT : 1≤T:=termCount_pos r
  have hfirst:=hj ⟨0,termCount_pos r⟩
  dsimp only [jobCharge] at hfirst
  have hH : 1≤H := by omega
  have hsource : (cachedSourceWord r).length≤H := by omega
  have hcount : cachedCountBudget r≤H := by omega
  have hcache : cachedSourceBudget r≤H := by omega
  have hbits : natBitLength T≤H := by dsimp only [T];omega
  have hi (i : Fin T) : (TermJob.word ⟨r,i⟩).length≤H := by have hh:=hj i;dsimp only [jobCharge] at hh;omega
  have hb (i : Fin T) : budget ⟨r,i⟩≤H := by have hh:=hj i;dsimp only [jobCharge] at hh;omega
  have hp (i : Fin T) : (termWeakWord ⟨r,i⟩).length≤H := by have hh:=hj i;dsimp only [jobCharge] at hh;omega
  have hhead:=countHeader_cost_bound T H hT hH hbits
  have hloop:=loop_cost_bound budget r H hH hsource hi hb
  have hprefix:=cache_prefix_bound r H hp
  have hTH : T*H≤T^2*H := Nat.mul_le_mul_right H (Nat.le_self_pow (by decide) _)
  have hHT : H≤T*H:=Nat.le_mul_of_pos_left _ (by omega)
  have hT4 : T≤T^4 := Nat.le_self_pow (by decide) _
  have h1 : 1≤T^4 := Nat.one_le_pow _ _ hT
  have hT2 : T≤T^2*H := (Nat.le_mul_of_pos_right _ (by omega)).trans hTH
  unfold wholeWeakOriginalBudget wholeWeakOnlyBudget payloadBatchCost poolCountCost
  change 4*cachedSourceBudget r+4*(2*(400*((cachedSourceWord r).length+cachedCountBudget r+1)+
    countHeaderReadCost T+100+(termFamily r).loopBudget budget+
    1000*((StagePrint.poolPrefix ((termFamily r).caches termWeakWord) T).length+T+1)+2)+2)+12≤_
  change (termFamily r).loopBudget budget≤10000*T^4+2000*T^2*H+10*T+1 at hloop
  change (StagePrint.poolPrefix ((termFamily r).caches termWeakWord) T).length≤T*(2*H+1) at hprefix
  nlinarith only [hcache,hsource,hcount,hhead,hloop,hprefix,hTH,hHT,hT4,h1,hT2]

end NearQuarticWires.StageCertNativePoolCost
