import Proof.Quartic.StageTupleSetupCost.Helpers

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCost

/-- `prop:time`, paper/paper.tex: the actual
twelve-stage setup clock contains complete input bytes only linearly;
the six small framing passes and four arithmetic calls are separate. -/
theorem scalar_clock (L S T nw ctx deg hdr z o bw br bz bo : ℕ)
    (hS : S≤T) (hT : 1≤T)
    (hnw : nw≤4*S) (hctx : ctx≤4*S) (hdeg : deg≤4*S)
    (hhdr : hdr≤4*S) (hz : z≤4*S) (ho : o≤4*S)
    (hbw : bw≤T) (hbr : br≤T) (hbz : bz≤T) (hbo : bo≤T) :
    6*L+27+1000*(nw+1)+(2*bw+2)+
      1000*(ctx+1)+1000*(deg+1)+1000*(hdr+1)+(2*br+2)+
      1000*(z+1)+(2*bz+2)+1000*(o+1)+(2*bo+2)+
      100000*(L+S)+11≤100006*L+200000*T := by
  omega

/-- `prop:time`, paper/paper.tex: the
ordinary final reset preserves the additive linear input contribution. -/
theorem scalar_reset (L P A c : ℕ) (hA : 1≤A) (hP : 1≤P)
    (hc : c≤100006*L+200000*(A*P)) :
    2*c+2≤(10^7*A)*(L+1)+(10^7*A)*P := by
  have hAL : L≤A*L := Nat.le_mul_of_pos_left _ hA
  have hAP : 1≤A*P := Nat.mul_pos hA hP
  nlinarith only [hc,hAL,hAP]

end NearQuarticWires.StageTupleSetupCost
