import Proof.Quartic.StageCertNative.FixedConstant
import Proof.Quartic.Cells.ParametersCertNativeBits
import Proof.Quartic.StagePrint.CallArityMemory

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicGates.Close.Cells

def nativeBitsBase : Fin VV:=90
def nativeBitsExponent : Fin VV:=91
def nativeBitsPower : Fin VV:=92
def nativeBitsCoefficient : Fin VV:=93
def nativeBitsResult : Fin VV:=94

def nativeBitsFactor (B1 : ℕ) : ℕ :=
  100*(Cells.ParameterArithmetic.preparationCoefficient B1+1)^2

def nativeBitsExponentValue (B1 : ℕ) : ℕ := 2*(B1+12)

/-- `lem:print`, paper/paper.tex: the exact
coefficient-bit width is computed from actual original arity by
integer powers and fixed arithmetic constants, not supplied with
Terms or obtained from Formula weight. -/
def polynomialBitsProgram (F E : ℕ) : St VV MM :=
  .seq (.op (.copy nativeBitsBase StagePrint.Header.arity))
    (.seq (.op (.inc nativeBitsBase))
      (.seq (setFixedConstant nativeBitsExponent E)
        (.seq (powP nativeBitsBase nativeBitsExponent nativeBitsPower)
          (.seq (setFixedConstant nativeBitsCoefficient F)
            (.seq (.op (.mul nativeBitsPower nativeBitsCoefficient nativeBitsResult))
              (.seq (.op (.inc nativeBitsResult)) (.op (.inc nativeBitsResult))))))))

def polynomialBitsSteps (F E : ℕ) : ℕ := 10*E+2*F+50

def computeNativeBits (B1 : ℕ) : St VV MM :=
  polynomialBitsProgram (nativeBitsFactor B1) (nativeBitsExponentValue B1)

def nativeBitsSteps (B1 : ℕ) : ℕ :=
  polynomialBitsSteps (nativeBitsFactor B1) (nativeBitsExponentValue B1)

def nativeBitsScratch : List (Fin VV) :=
  [nativeBitsBase,nativeBitsExponent,nativeBitsPower,nativeBitsCoefficient,nativeBitsResult,a1,c4,vJ]

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal ordinary arithmetic computes the original
uniform coefficient-bit field, with all constants and powers charged. -/
theorem polynomialBitsProgram_run (C : Ctx) (F E n : ℕ) (hF : 1≤F) (hE : 1≤E)
    (a : DS VV MM) (hc : Cst a) (hn : a.env StagePrint.Header.arity=n)
    (hroom : (F*(n+1)^E+2)+F+E+n+10<2^C.Wd) :
    Hs C (polynomialBitsProgram F E) a (polynomialBitsSteps F E) (fun z=>
      z.env nativeBitsResult=F*(n+1)^E+2 ∧ z.sh=a.sh ∧
      Cst z ∧ Fr a z nativeBitsScratch) := by
  have hprod : (n+1)^E*F+2<2^C.Wd := by
    rw [Nat.mul_comm]
    omega
  have hp : (n+1)^E≤F*(n+1)^E+2 := by
    have hh:=Nat.le_mul_of_pos_left ((n+1)^E) hF
    omega
  unfold polynomialBitsProgram
  apply Hx.hs
  refine Hs.then (hs_copy C nativeBitsBase StagePrint.Header.arity a (by decide))
    (fun b hb n1 hn1=>?_)
  subst b
  let b:=a.set nativeBitsBase n
  have hbEq : a.set nativeBitsBase (a.env StagePrint.Header.arity)=b := by rw [hn]
  rw [hbEq]
  have bc : Cst b := Cst.of_fr hc (Fr.set (T:=[nativeBitsBase]) a n (by simp)) (by decide)
  refine Hs.then (hs_inc C nativeBitsBase b (by change n+1<_;omega))
    (fun d hd n2 hn2=>?_)
  subst d
  let d:=b.set nativeBitsBase (n+1)
  have dc : Cst d := Cst.of_fr bc (Fr.set (T:=[nativeBitsBase]) b (n+1) (by simp)) (by decide)
  refine Hs.then (setFixedConstant_run C nativeBitsExponent (by decide) E d dc (by decide)
    (by omega)) (fun e ⟨ee,es,ec,ef⟩ n3 hn3=>?_)
  have ebase : e.env nativeBitsBase=n+1 := (ef _ (by decide)).trans rfl
  refine Hs.then (powP_spec nativeBitsBase nativeBitsExponent nativeBitsPower (by decide) e
    (by
      intro k hk
      rw [ebase]
      have hkE : k≤E := hk.trans_eq ee
      exact (Nat.pow_le_pow_right (by omega : 0<n+1) hkE).trans_lt
        (hp.trans_lt (by omega)))
    (by rw [ee];omega) (by omega))
    (fun f ⟨fp,fs,ff⟩ n4 hn4=>?_)
  have fc : Cst f := Cst.of_fr ec ff (by decide)
  have fpower : f.env nativeBitsPower=(n+1)^E := by rw [fp,ebase,ee]
  refine Hs.then (setFixedConstant_run C nativeBitsCoefficient (by decide) F f fc (by decide)
    (by omega)) (fun g ⟨gg,gs,gc,gf⟩ n5 hn5=>?_)
  have gpower : g.env nativeBitsPower=(n+1)^E := (gf _ (by decide)).trans fpower
  refine Hs.then (hs_mul C nativeBitsPower nativeBitsCoefficient nativeBitsResult g
    (by decide) (by decide) (by decide) (by rw [gpower,gg];omega))
    (fun q hq n6 hn6=>?_)
  subst q
  let q:=g.set nativeBitsResult ((n+1)^E*F)
  have hqEq : g.set nativeBitsResult (g.env nativeBitsPower*g.env nativeBitsCoefficient)=q := by
    rw [gpower,gg]
  rw [hqEq]
  have qc : Cst q := Cst.of_fr gc (Fr.set (T:=[nativeBitsResult]) g _ (by simp)) (by decide)
  refine Hs.then (hs_inc C nativeBitsResult q (by change (n+1)^E*F+1<2^C.Wd;omega))
    (fun s hs n7 hn7=>?_)
  subst s
  let s:=q.set nativeBitsResult ((n+1)^E*F+1)
  refine Hs.last (hs_inc C nativeBitsResult s (by
    change (n+1)^E*F+1+1<2^C.Wd
    omega)) (fun z hz n8 hn8=>?_)
  subst z
  have hf0 : Fr a d nativeBitsScratch :=
    (Fr.set (T:=nativeBitsScratch) a _ (by simp [nativeBitsScratch])).trans
      (Fr.set b _ (by simp [nativeBitsScratch]))
  have hf1 : Fr a g nativeBitsScratch := hf0.trans
    ((ef.weaken (by decide)).trans ((ff.weaken (by decide)).trans (gf.weaken (by decide))))
  have hf2 : Fr a (s.set nativeBitsResult (s.env nativeBitsResult+1)) nativeBitsScratch :=
    hf1.trans ((Fr.set (T:=nativeBitsScratch) g _ (by simp [nativeBitsScratch])).trans
      ((Fr.set q _ (by simp [nativeBitsScratch])).trans
        (Fr.set s _ (by simp [nativeBitsScratch]))))
  refine ⟨⟨?_,?_,Cst.of_fr hc hf2 (by decide),hf2⟩,?_⟩
  · change (n+1)^E*F+1+1=F*(n+1)^E+2
    ring
  · exact gs.trans (fs.trans es)
  · change n4≤1+(1+(e.env nativeBitsExponent*(3+4)+4)+1)+1 at hn4
    rw [ee] at hn4
    dsimp only [polynomialBitsSteps]
    change n3≤2*E+3 at hn3
    change n5≤2*F+3 at hn5
    omega

/-- `lem:print` and `prop:time`, paper/paper.tex: specialization computes the actual selected coefficient
bit field from original n, including all fixed arithmetic constants. -/
theorem computeNativeBits_run (C : Ctx) (B1 n : ℕ) (a : DS VV MM) (hc : Cst a)
    (hn : a.env StagePrint.Header.arity=n)
    (hroom : Cells.nativeCertificateBits B1 n+nativeBitsFactor B1+
      nativeBitsExponentValue B1+n+10<2^C.Wd) :
    Hs C (computeNativeBits B1) a (nativeBitsSteps B1) (fun z=>
      z.env nativeBitsResult=Cells.nativeCertificateBits B1 n ∧ z.sh=a.sh ∧
      Cst z ∧ Fr a z nativeBitsScratch) := by
  have hF : 1≤nativeBitsFactor B1 := by
    have hp : 1≤(Cells.ParameterArithmetic.preparationCoefficient B1+1)^2 :=
      Nat.one_le_pow _ _ (by omega)
    unfold nativeBitsFactor
    omega
  have hE : 1≤nativeBitsExponentValue B1 := by unfold nativeBitsExponentValue;omega
  exact polynomialBitsProgram_run C (nativeBitsFactor B1) (nativeBitsExponentValue B1) n
    hF hE a hc hn hroom

end NearQuarticWires.StageCertNative
