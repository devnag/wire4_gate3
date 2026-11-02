import Proof.Quartic.StageTupleFinishPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleFinishPrice

open StageTuple StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: the actual
Stack formatter magnitude and serialized source are linear in its
real tuple count, with a fixed structural dimension polynomial. -/
theorem stack_input_size (r : StagePrint.StackRequest) (S : ℕ)
    (hW : r.W≤S) (hs : r.s≤S) (hm : r.m≤S) :
    stackInputMagnitude r+r.word.length≤100*(S+1)^4*(r.tuples.length+1) := by
  let F:=fun W s m T : ℕ=>
    T*(m*(s+1))*(2*(W+1)+1)+W+m*(s+1)+(s+1)+m+T+10+
    (2*(T*(m*(s+1))*(2*(W+1)+1)+1+5*(2*(W+1)+1)+m*(s+1)+(s+1)+m+T)+11)
  have heq : stackInputMagnitude r+r.word.length=F r.W r.s r.m r.tuples.length := by
    rw [stack_word_length]
    unfold stackInputMagnitude
    rw [stack_field_records_length]
  have hmono : F r.W r.s r.m r.tuples.length≤F S S S r.tuples.length := by
    dsimp only [F]
    gcongr
  have hpoly (T : ℕ) : F S S S T≤100*(S+1)^4*(T+1) := by
    dsimp only [F]
    ring_nf
    omega
  rw [heq]
  exact hmono.trans (hpoly r.tuples.length)

/-- `prop:time`, paper/paper.tex: literal
Stack source and formatter work fit the same square census factor
of the actual support, independently of all earlier source bytes. -/
theorem input_size_selected (j : Case) :
    stackInputMagnitude (stack j)+(stack j).word.length≤
      3200*j.small^4*j.childCap^(2*j.card) := by
  obtain ⟨hW,hs,hm⟩:=stack_dimensions j
  have hp:=j.small_pos
  calc
    _≤100*(j.small+1)^4*((stack j).tuples.length+1) := stack_input_size _ _ hW hs hm
    _≤100*(2*j.small)^4*(2*j.childCap^(2*j.card)) := by
      gcongr
      · omega
      · exact stack_tuples_square_census j
    _=_ := by ring

end NearQuarticWires.StageTupleFinishPrice
