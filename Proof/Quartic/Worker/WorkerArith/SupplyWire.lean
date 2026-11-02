import Proof.Quartic.Worker.WorkerArith.Supply

/-!
# The weak machine for the wire measure (`lem:ae-machine`, paper/paper.tex)

For every wire counter, every size limit `b(q) ≤ q⁴`, every threshold and every radius, the weak machine `M_wire`
exists (`workerSupply4`): one multitape machine whose accepted witness words carry certified guesses, which accepts
every certified guess within the size limits with a witness word of `⌊N/16⌋` bits (`guessEnvelope4`: the guesses
have descriptions of `q^{O(1)}` bits, `lem:ae-machine` (i)), and whose running time splits into a polynomial part and a
part `o(2^q)` per `q^σ` (`lem:ae-machine` (ii)).

Adapted from `Proof.Gates.WorkerArith.{Envelope, Rest, SupplyDefs, Supply}` of the near-cubic gate proof, with the
size limit `b(q) ≤ q⁴` in place of `b(q) ≤ η q³` and the wire counter `Counter4`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.WorkerArith.WorkerBounds
open NearCubicGates NearCubicGates.Close

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.PolynomialSchedule NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.Close NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Worker NearQuarticWires.Worker4.Worker NearQuarticWires.Worker4.Worker.Format

section Env
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2)

/-- The guess envelope for a size limit `b(q) ≤ q⁴` (`lem:ae-machine` (i)). -/
theorem guessEnvelope4 (budget : ℕ → ℕ) (hb : ∃ q1 : ℕ, ∀ q, q1 ≤ q → budget q ≤ q ^ 4) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (x : BitInput N) (G : Guess (width s g N)),
    G.SizeOK P x ctr budget →
    (encodeGuess s P g x G).length ≤ N / 16 ∧
      ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length := by
  obtain ⟨q1, hq1⟩ := hb
  obtain ⟨Nq, hNq⟩ := width_unbounded s g q1
  obtain ⟨F, hF, hFm⟩ := Closure.checked_m_le s P g
  obtain ⟨K, e, hsize⟩ := P.outputSize
  obtain ⟨Cw, kw, hw⟩ := ctr.witnessPoly
  let Mb : ℕ → ℕ := fun q => 2 ^ (g.clauseDegree + 1) * (q + 1) ^ g.clauseDegree
  let Ab : ℕ → ℕ := fun q => K * F q ^ e + Mb q
  let Cb : ℕ → ℕ := fun q => (q ^ 4 + 1) * ((q + 1) * (2 * (4 * q * (q + 1)) + 2) + 12)
  let Wb : ℕ → ℕ := fun q => 2 * (Cw * (q + 1) ^ kw) + 1
  let Phi : ℕ → ℕ := fun q => 2 * (2 * (8192 * (q + oracleSizeBound g.degree q + 4 + 1) ^ 10) + 1) + Ab q * Cb q +
    10 * Mb q * Wb q
  have pc := polynomiallyBounded_constant
  have pid := polynomiallyBounded_id
  have p1 : PolynomiallyBounded (fun q : ℕ => q + 1) := polynomiallyBounded_add pid (pc 1)
  have hMb : PolynomiallyBounded Mb := polynomiallyBounded_mul (pc _) (polynomiallyBounded_pow p1 _)
  have hAb : PolynomiallyBounded Ab :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc K) (polynomiallyBounded_pow hF e)) hMb
  have hCb : PolynomiallyBounded Cb :=
    polynomiallyBounded_mul (polynomiallyBounded_add (polynomiallyBounded_pow pid 4)
      (pc 1)) (polynomiallyBounded_add (polynomiallyBounded_mul p1 (polynomiallyBounded_add (polynomiallyBounded_mul
        (pc 2) (polynomiallyBounded_mul (polynomiallyBounded_mul (pc 4) pid) p1)) (pc 2))) (pc 12))
  have hWb : PolynomiallyBounded Wb :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) (polynomiallyBounded_mul (pc Cw)
      (polynomiallyBounded_pow p1 kw))) (pc 1)
  have hO : PolynomiallyBounded (fun q => 2 * (8192 * (q + oracleSizeBound g.degree q + 4 + 1) ^ 10) + 1) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) (polynomiallyBounded_mul (pc 8192)
      (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add pid
        (oracleSizeBound_polynomiallyBounded g.degree)) (pc 4)) (pc 1)) 10))) (pc 1)
  have hPhi : PolynomiallyBounded Phi :=
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) hO) (polynomiallyBounded_mul hAb hCb))
      (polynomiallyBounded_mul (polynomiallyBounded_mul (pc 10) hMb) hWb)
  obtain ⟨c, dd, -, hc⟩ := hPhi
  obtain ⟨N1, hN1⟩ := Setup.qpoly_le s g dd (16 * c)
  refine ⟨max (N1 + 4) Nq, fun N hN' x G hG => ?_⟩
  have hN : N1 + 4 ≤ N := (le_max_left _ _).trans hN'
  have hwq : q1 ≤ width s g N := hNq N ((le_max_right _ _).trans hN')
  obtain ⟨hsrc, hpf, hcirc, hwit⟩ := hG
  have hq2 : 2 ≤ width s g N := two_le_nativeWidth s g N (by omega)
  refine ⟨?_, fun j hj => ((hcirc j hj).1.1).symm⟩
  -- the pair
  have hp1 : natBitLength (encodeBooleanCircuit G.oracle.src) ≤
      8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10 :=
    (RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter G.oracle.src (by omega) (by omega)
      (by omega)).trans (RepairOrdinary.PCPPRequestBoundary.canonical_circuit_bound _)
  have hp2 : natBitLength (encodeBooleanCircuit G.oracle.pf) ≤
      8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10 :=
    (RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter G.oracle.pf (by omega) (by omega)
      (by omega)).trans (RepairOrdinary.PCPPRequestBoundary.canonical_circuit_bound _)
  have h1 : (numWord (encodeBooleanCircuit G.oracle.src)).length + (numWord (encodeBooleanCircuit G.oracle.pf)).length ≤
      2 * (2 * (8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10) + 1) := by
    rw [numWord_length, numWord_length]; omega
  -- the circuits
  have hM : gadgets s g N ≤ Mb (width s g N) := gadgets_le _ _
  have hm := hFm N x G.oracle hpf hq2 (by omega)
  have hpb : (pcpp s P g x G.oracle).proofBits ≤ K * F (width s g N) ^ e := by
    rw [pcpp_eq]
    exact (hsize _).1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm e))
  have haux : G.auxCount P x ≤ Ab (width s g N) := by
    show (pcpp s P g x G.oracle).proofBits + gadgets s g N ≤ _
    exact Nat.add_le_add hpb hM
  have hB0 : 1 ≤ Call.B0 (width s g N) := B0_pos _ (by omega)
  have hcw : ∀ a ∈ (List.range (G.auxCount P x)).map G.circuits, (circuitWordF a).length ≤ Cb (width s g N) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hj
    obtain ⟨hwf, htw⟩ := hcirc j hj
    have h := circuitWordF_le hB0 (G.circuits j) hwf
    have h2 : (G.circuits j).topWeight + 1 ≤ width s g N ^ 4 + 1 :=
      Nat.add_le_add_right (htw.trans (hq1 _ hwq)) 1
    have h3 : (width s g N + 1) * (2 * Call.B0 (width s g N) + 2) + 12 ≤
        (width s g N + 1) * (2 * (4 * width s g N * (width s g N + 1)) + 2) + 12 := by
      have := B0_le (width s g N)
      have : 2 * Call.B0 (width s g N) + 2 ≤ 2 * (4 * width s g N * (width s g N + 1)) + 2 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 12
    exact h.trans (Nat.mul_le_mul h2 h3)
  have h2 := Setup.flatMap_len_le circuitWordF (Cb (width s g N)) _ hcw
  rw [List.length_map, List.length_range] at h2
  have h2' : (((List.range (G.auxCount P x)).map G.circuits).flatMap circuitWordF).length ≤
      Ab (width s g N) * Cb (width s g N) := h2.trans (Nat.mul_le_mul_right _ haux)
  -- the witnesses
  have hwl : ∀ a ∈ witnessList G (gadgets s g N), (fieldWord a).length ≤ Wb (width s g N) := by
    intro a ha
    unfold witnessList at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hi
    rw [fieldWord_length]
    have h := hwit (i / 10) (by omega) ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩
    have := hw (width s g N)
    show 2 * _ + 1 ≤ 2 * (Cw * (width s g N + 1) ^ kw) + 1
    omega
  have h3 := Setup.flatMap_len_le fieldWord (Wb (width s g N)) _ hwl
  have hwlen : (witnessList G (gadgets s g N)).length = 10 * gadgets s g N := by simp [witnessList]
  rw [hwlen] at h3
  have h3' : ((witnessList G (gadgets s g N)).flatMap fieldWord).length ≤ 10 * Mb (width s g N) * Wb (width s g N) :=
    h3.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM))
  -- total
  have hlen : (encodeGuess s P g x G).length ≤ Phi (width s g N) := by
    unfold encodeGuess
    simp only [List.length_append]
    show _ ≤ 2 * (2 * (8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10) + 1) +
      Ab (width s g N) * Cb (width s g N) + 10 * Mb (width s g N) * Wb (width s g N)
    omega
  have h16 : 16 * Phi (width s g N) ≤ N := by
    have a := hN1 N (by omega)
    have b := Nat.mul_le_mul_left 16 (hc (width s g N))
    calc 16 * Phi (width s g N) ≤ 16 * (c * (width s g N + 1) ^ dd) := b
      _ = 16 * c * (width s g N + 1) ^ dd := by ring
      _ ≤ N := a
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  omega

end Env

end NearQuarticWires.Worker4.WorkerArith.WorkerBounds

namespace NearQuarticWires.Worker4.WorkerArith
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Setup NearQuarticWires.Worker4.Setup NearQuarticWires.Worker4.TermLoop
open NearQuarticWires.Worker4.WorkerArith.WeakWorker NearQuarticWires.Worker4.WorkerArith.WorkerBounds NearCubicGates.Close.WordPrograms
open NearQuarticWires.Worker4.Worker (width pcpp gadgets sysCount)

/-- The weak machine exists for every wire counter and every size limit `b(q) ≤ q⁴` (eventually). -/
def WorkerSupplyWire : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ),
    (∃ q1 : ℕ, ∀ q, q1 ≤ q → budget q ≤ q ^ 4) → 0 < ω →
    ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 → Nonempty (Closure.WorkerMachine s P g ctr budget εT ω)

/-- **Everything `WeakWorkerOf` asks beyond the machines.** -/
theorem hrest_of4 (hCF : CircuitSizeFit) (hRF : RowSizeFit) (hSU : Setup.SetupSupply) :
    ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ)
      (hD : Counter.DenOK ctr), Counter.OutOK ctr → (∃ q1 : ℕ, ∀ q, q1 ≤ q → budget q ≤ q ^ 4) → 0 < ω →
      ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 →
        ∃ D : SetupData s P g, (∃ prog : WMX (nsW D) nrW, SetupSpec D prog) ∧
          ctr.program.program.tapeCount = D.tc ∧
          VmapFacts D (verdictMachine P.gamma εT) ∧
          WeakWorkerRest s P g ctr hD budget εT ω D (verdictMachine P.gamma εT) := by
  intro s P B1 B2 ctr budget εT ω hD hO hbud4 _hω
  obtain ⟨E0, hU⟩ := hSU s P
  obtain ⟨onc, Kc, ec, hbud⟩ := budget_split ctr
  obtain ⟨Co, eo, hOo⟩ := hO
  obtain ⟨Cv, ev, hv⟩ := (verdictMachine P.gamma εT).cls
  refine ⟨30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10, fun g hg => ?_⟩
  obtain ⟨Nc, hNc⟩ := width_unbounded s g onc
  obtain ⟨D, hprog, hDtc, hDN0, ⟨Ca, hCa⟩, hpadU⟩ := hU g ctr.program.program.tapeCount Nc
  obtain ⟨CM, hCM⟩ := gadgets_lin s g
  obtain ⟨Cq, hCq⟩ := qpoly s g 1
  obtain ⟨Ce, hCe⟩ := qpoly s g eo
  have hpad1 : ∀ N, N / 16 + 1 ≤ padOf Ca E0 Cq CM N := fun N => by unfold padOf; omega
  obtain ⟨Fs, hrejFs, haccFs, Cs, ons, hFs⟩ := hpadU (padOf Ca E0 Cq CM) (2 + Ca * (2 + 2 * (Cq + 1)) + 10 * CM)
    (E0 + 2) hpad1 (padOf_le Ca E0 Cq CM)
  obtain ⟨Bh, onh, hhot⟩ := hot_bound s g D.tc (Outer.apad s.mw (g.sv s) + 1)
  obtain ⟨A, onA, hA⟩ := fp_pe Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev
    (E0 * (E0 + 2 + 1)) ⟨Cs, ons, hFs⟩ (PE.of_all (C := CM) (fun N => by rw [pow_one]; exact hCM N))
    (PE.of_all (C := Ce) (fun N => by rw [pow_one]; exact hCe N))
  refine ⟨D, hprog, hDtc.symm, vmapFacts D _ _, padOf Ca E0 Cq CM,
    fun N => Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N,
    hotOf s g D.tc, A + 42, Bh, _, Outer.apad s.mw (g.sv s) + 1, hpad1, ?_, ?_,
    guessEnvelope4 s P g ctr budget hbud4, hg, le_rfl, ⟨onA, fun N hN => ?_⟩, ⟨onh, hhot⟩⟩
  · intro N x bits Bo hN hdec
    have hq : onc ≤ width s g N := hNc N (hDN0.trans hN)
    obtain ⟨hca, -⟩ : auxN s P g x Bo + gadgets s g N ≤ Ca * (N + 1) ^ E0 ∧ True :=
      ⟨hCa N x bits (padOf Ca E0 Cq CM N) Bo hN (hpad1 N) hdec, trivial⟩
    have hq1 : width s g N + 1 ≤ Cq * (N + 1) := by simpa using hCq N
    have hphys : N / 16 + 2 + auxN s P g x Bo * (2 + 2 * (N / 16) * (width s g N + 2)) + 10 * gadgets s g N ≤
        padOf Ca E0 Cq CM N := by
      unfold padOf
      have h1 : auxN s P g x Bo * (2 + 2 * (N / 16) * (width s g N + 2)) ≤
          Ca * (N + 1) ^ E0 * (2 + 2 * (N / 16) * (Cq * (N + 1) + 1)) :=
        Nat.mul_le_mul (by omega) (by
          have : 2 * (N / 16) * (width s g N + 2) ≤ 2 * (N / 16) * (Cq * (N + 1) + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega)
      have h2 := hCM N
      omega
    exact accept_fit ctr hD ω εT D (verdictMachine P.gamma εT) hCF hRF Fs onc Kc ec Co eo Cv ev hbud hOo hv x bits
      (padOf Ca E0 Cq CM N) Bo hq hdec (hpad1 N) hphys (haccFs N x bits Bo hN hdec)
  · intro N x bits
    have h := hrejFs N x bits
    show rejectCost D x bits (padOf Ca E0 Cq CM N) + 10 ≤
      Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N
    unfold Fpf
    omega
  · have h := hA N hN
    have h1 : 1 ≤ (N + 1) ^ (30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10) := Nat.one_le_pow _ _ (by omega)
    show Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N + 40 + 2 ≤
      (A + 42) * (N + 1) ^ (30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10) + hotOf s g D.tc N
    rw [Nat.add_mul]
    omega


noncomputable section

theorem workerSupply_of4
    (hrest : ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (budget : ℕ → ℕ) (εT ω : ℚ)
      (hD : Counter.DenOK ctr), Counter.OutOK ctr → (∃ q1 : ℕ, ∀ q, q1 ≤ q → budget q ≤ q ^ 4) → 0 < ω →
      ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 →
        ∃ D : SetupData s P g, (∃ prog : WMX (nsW D) nrW, SetupSpec D prog) ∧
          ctr.program.program.tapeCount = D.tc ∧
          VmapFacts D (verdictMachine P.gamma εT) ∧
          WeakWorkerRest s P g ctr hD budget εT ω D (verdictMachine P.gamma εT)) :
    WorkerSupplyWire := by
  intro s P B1 B2 ctr budget εT ω hb hω
  obtain ⟨d0, hd0⟩ := hrest s P B1 B2 ctr budget εT ω (Counter.denOK ctr) (Counter.outOK ctr) hb hω
  refine ⟨d0, fun g hg => ?_⟩
  obtain ⟨D, ⟨prog, hprog⟩, hct, ⟨vmap, hinj, hin, hL, hbl⟩, padF, F, hot, A, B, a, sigma, hpad, hacc, hrej, henv, ha,
    hsig, hsplitF, hhot⟩ := hd0 g hg
  exact WeakWorker_of s P g ctr (Counter.denOK ctr) budget εT ω D prog hct (verdictMachine P.gamma εT) vmap padF F hot
    A B a sigma hprog (termLoop_ideal D ctr hct ω) (loopExit_vi D ctr ω (Counter.denOK ctr)) hinj hin hL hbl hpad hacc
    hrej henv ha hsig hsplitF hhot

end

/-- **The weak machine for the wire measure**, from the set-up. -/
theorem workerSupply4 (hSU : Setup.SetupSupply) : WorkerSupplyWire :=
  workerSupply_of4 (hrest_of4 WorkerBounds.circuitSizeFit WorkerBounds.rowSizeFit hSU)

end NearQuarticWires.Worker4.WorkerArith
