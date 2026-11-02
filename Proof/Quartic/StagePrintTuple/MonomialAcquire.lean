import Proof.Quartic.StagePrintTuple.MonomialCell
import Proof.Gates.TabMachine.Mono3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: monomial
source acquisition clears only its ten local scratch slots, preserving
the field width and every actual global Terms/tuple/output counter. -/
def monomialScratch (R : Fin 11↪Fin nr) : List (Fin nr) :=
  List.ofFn fun i : Fin 10=>R ⟨i.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the actual
monomial reader produces its two literal small cache packets and
resets its local scratch, with no whole-Terms cleanup sweep. -/
def monomialAcquireProgram (P : Fin 3↪Fin (ns+1)) (R : Fin 11↪Fin nr) : WMX ns nr :=
  .seq (.wm (monomialReadyIn P R)) (clearAll (monomialScratch R))

/-- `lem:print`, paper/paper.tex: acquisition
advances exactly one actual monomial codec and stores its support and
signed coefficient packet, preserving all other state components. -/
def monomialAcquireState (P : Fin 3↪Fin (ns+1)) (L : ℕ)
    (support : List ℕ) (coefficient : ℤ) (pre : List Bool) (σ : WState ns nr) : WState ns nr :=
  (((σ.sets (P 1) (frame (listWord natWord support))).sets (P 2)
    (frame (natWord L++intWord coefficient))).seth (P 0)
      (pre.length+(listWord natWord support++intWord coefficient).length))

/-- `prop:time`, paper/paper.tex: acquisition
charges the actual codec scan and only its small local capacity for
scratch cleanup, independently of the complete Terms census. -/
def monomialAcquireCost (smallCap L : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  monomialReadyCost L support coefficient+1+10*(3*smallCap+2)

/-- `lem:print` and `prop:time`, paper/paper.tex: genuine source bytes establish both ready monomial
caches and the next source cursor, with exact exterior-state and result
cell preservation and a source-local cleanup clock. -/
theorem monomialAcquireProgram_spec (P : Fin 3↪Fin (ns+1)) (R : Fin 11↪Fin nr)
    (smallCap cap L : ℕ) (hcap : smallCap ≤ cap)
    (support : List ℕ) (coefficient : ℤ) (pre rest : List Bool) (σ : WState ns nr)
    (hsource : σ.st (P 0)=pre++listWord natWord support++intWord coefficient++rest)
    (hhead : σ.sh (P 0)=pre.length) (hS : σ.st (P 1)=[]) (hSH : σ.sh (P 1)=0)
    (hC : σ.st (P 2)=[]) (hCH : σ.sh (P 2)=0)
    (hL : σ.val (R 10)=L) (hz : ∀i:Fin 11,i≠10→σ.val (R i)=0)
    (hwrite : L+6*natBitLength L+6 ≤ smallCap)
    (hpow : 2^(natBitLength support.length+1) ≤ smallCap)
    (hlen : support.length ≤ smallCap)
    (hSw : support.length+6*natBitLength support.length+6 ≤ smallCap)
    (hSo : 2*(listWord natWord support).length+3 ≤ smallCap)
    (hCo : 2*(natWord L).length+2*(intWord coefficient).length+4 ≤ smallCap) :
    WXExec cap (monomialAcquireProgram P R) σ
      (monomialAcquireState P L support coefficient pre σ)
      (monomialAcquireCost smallCap L support coefficient) := by
  obtain ⟨b,eb,bs,bsh,bc,bch,bsrc,bh,bL,hout,hb⟩ := monomialReadyIn_spec
    P R smallCap cap L hcap support coefficient pre rest σ hsource hhead hS hSH hC hCH
    hL hz hwrite hpow hlen hSw hSo hCo
  have cb := monomialReadyIn_cell P R eb
  obtain ⟨c,ec,hz',hf⟩ := clearAll_spec cap smallCap (monomialScratch R) b
    (by
      intro j hj
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
      exact hb ⟨i.val,by omega⟩) hcap
  have hp {i j:Fin 3} : P i=P j ↔ i=j := P.injective.eq_iff
  have hcout {j : Fin nr} (hj : ∀i,R i≠j) : j∉monomialScratch R := by
    intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact hj ⟨i.val,by omega⟩ hi
  have he : c=monomialAcquireState P L support coefficient pre σ := by
    apply WState.eq
    · funext j
      rw [hf.sh (by simp)]
      by_cases hj:∃i,P i=j
      · obtain ⟨i,rfl⟩ := hj
        fin_cases i <;> simp [monomialAcquireState,hp,bh,bsh,bch,hSH,hCH]
      · have hj' : ∀i,P i≠j := by intro i hi;exact hj ⟨i,hi⟩
        rw [(hout.1 j hj').1]
        simp [monomialAcquireState,Function.update_of_ne (hj' 0).symm]
    · funext j
      rw [hf.st (by simp)]
      by_cases hj:∃i,P i=j
      · obtain ⟨i,rfl⟩ := hj
        fin_cases i <;> simp [monomialAcquireState,hp,bs,bc,bsrc]
      · have hj' : ∀i,P i≠j := by intro i hi;exact hj ⟨i,hi⟩
        rw [(hout.1 j hj').2]
        simp [monomialAcquireState,Function.update_of_ne (hj' 1).symm,
          Function.update_of_ne (hj' 2).symm]
    · funext j
      by_cases hj:∃i,R i=j
      · obtain ⟨i,rfl⟩ := hj
        by_cases hi:i=10
        · subst i
          have hnot : R 10∉monomialScratch R := by
            intro hm
            obtain ⟨k,hk⟩ := List.mem_ofFn.mp hm
            have hki := congrArg Fin.val (R.injective hk)
            change k.val=10 at hki
            have hkb := k.isLt
            omega
          rw [hf.val hnot,bL]
          simpa [monomialAcquireState] using hL.symm
        · have hib : i.val<10 := by
            have hlt:=i.isLt
            have hn : i.val≠10 := by intro he;exact hi (Fin.ext he)
            omega
          have him : R i∈monomialScratch R := List.mem_ofFn.mpr
            ⟨⟨i.val,hib⟩,congrArg R (Fin.ext rfl)⟩
          rw [hz' _ him]
          simpa [monomialAcquireState] using (hz i hi).symm
      · have hj' : ∀i,R i≠j := by intro i hi;exact hj ⟨i,hi⟩
        rw [hf.val (hcout hj'),hout.2 j hj']
        rfl
    · exact hf.cell.trans cb
  exact (WXExec.wm eb |>.seq ec).cast cap he
    (by simp [monomialAcquireCost,monomialScratch])

end NearQuarticWires.StageTuple
