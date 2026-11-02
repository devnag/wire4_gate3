import Proof.Quartic.StagePullback.RowWordFunction

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: actual original
child field widths and the complete affine output width are quadratic
in the original dimension, with fixed explicit constants. -/
theorem RowRequest.heightBounds (r : RowRequest) :
    r.Lin ≤ 9 * (r.parameters.n + 2) ^ 2 ∧ r.Lout ≤ 16 * (r.parameters.n + 2) ^ 2 := by
  let V := r.parameters.n + 2
  have hV : 1 ≤ V := by dsimp [V]; omega
  have h1 : 1 ≤ V ^ 2 := Nat.one_le_pow _ _ hV
  have h2 : (r.parameters.n + 1) ^ 2 ≤ V ^ 2 :=
    Nat.pow_le_pow_left (by dsimp [V]; omega) 2
  have hLin : r.Lin ≤ 9 * V ^ 2 := by nlinarith only [r.Lin_le, h1, h2]
  have hn : r.parameters.n ≤ V ^ 2 :=
    (show r.parameters.n ≤ V by dsimp [V]; omega).trans (Nat.le_self_pow (by decide) V)
  have hLout : r.Lout ≤ 16 * V ^ 2 := by unfold RowRequest.Lout; nlinarith only [hLin, hn, h1]
  exact ⟨hLin, hLout⟩

/-- `prop:time`, paper/paper.tex: the complete
original-source row execution, including every physical input and output
field, has an explicit cubic source-language clock. -/
theorem RowRequest.sourceClock_cubic (r : RowRequest) :
    r.sourceClock ≤ 20000 * (r.parameters.n + 2) ^ 3 := by
  let V := r.parameters.n + 2
  have hV : 1 ≤ V := by dsimp [V]; omega
  have h23 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV (by decide)
  have h13 : V ≤ V ^ 3 := Nat.le_self_pow (by decide) V
  have h03 : 1 ≤ V ^ 3 := Nat.one_le_pow _ _ hV
  have hN : r.parameters.n ≤ V := by dsimp [V]; omega
  have hW : NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.parameters ≤ V :=
    (NativeRows.nativeWidth_le r.parameters).trans hN
  have hh := r.heightBounds
  have hLin : r.Lin ≤ 9 * V ^ 2 := hh.1
  have hLout : r.Lout ≤ 16 * V ^ 2 := hh.2
  have hNL : r.parameters.n * r.Lin ≤ 9 * V ^ 3 := by
    calc
      _ ≤ V * (9 * V ^ 2) := Nat.mul_le_mul hN hLin
      _ = _ := by ring
  have hWL : NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.parameters * r.Lout ≤ 16 * V ^ 3 := by
    calc
      _ ≤ V * (16 * V ^ 2) := Nat.mul_le_mul hW hLout
      _ = _ := by ring
  have hN2 : r.parameters.n ^ 2 ≤ V ^ 3 := (Nat.pow_le_pow_left hN 2).trans h23
  have hN3 := hN.trans h13
  have hW3 := hW.trans h13
  have hLin3 := hLin.trans (Nat.mul_le_mul_left 9 h23)
  have hLout3 := hLout.trans (Nat.mul_le_mul_left 16 h23)
  change r.sourceClock ≤ 20000 * V ^ 3
  unfold RowRequest.sourceClock
  nlinarith only [hNL, hWL, hN2, hN3, hW3, hLin3, hLout3, h03]

/-- `lem:print`, paper/paper.tex: original fixed
signed fields occupy precisely their source binary width, with no
precomputed coefficient cache or extra row encoding. -/
theorem RowRequest.body_length (r : RowRequest) : r.body.length = (r.parameters.n + 1) * r.Lin := by
  have hh : ∀ zs : List ℤ,
      (zs.flatMap fun z => binary r.Lin (NearCubicGates.Close.WordPrograms.SInt.encS z)).length =
        zs.length * r.Lin := by
    intro zs
    induction zs with
    | nil => simp
    | cons z zs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        NearCubicWires.RepairOrdinary.SignedSortKey.binary_length, ih]
      ring
  simpa only [RowRequest.body, List.length_append, List.length_ofFn, List.length_cons, List.length_nil,
    Nat.zero_add] using hh (List.ofFn r.child.weight ++ [r.child.target])

/-- `prop:time`, paper/paper.tex: the full original
row request has a fixed cubic binary input-length bound. -/
theorem RowRequest.word_length_cubic (r : RowRequest) :
    r.word.length ≤ 10000 * (r.parameters.n + 2) ^ 3 := by
  have hhead : ∀ vs : List ℕ, (vs.flatMap natWord).length ≤ StageGamma.readFieldsCost vs := by
    intro vs
    induction vs with
    | nil => simp [StageGamma.readFieldsCost]
    | cons v vs ih =>
      simp only [List.flatMap_cons, List.length_append, natWord_length, StageGamma.readFieldsCost]
      omega
  have hh := (hhead r.fields).trans (rowFields_cost r)
  let V := r.parameters.n + 2
  have hV : 1 ≤ V := by dsimp [V]; omega
  have h23 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right hV (by decide)
  have h03 : 1 ≤ V ^ 3 := Nat.one_le_pow _ _ hV
  have hLin : r.Lin ≤ 9 * V ^ 2 := r.heightBounds.1
  have hLout : r.Lout ≤ 16 * V ^ 3 := r.heightBounds.2.trans (Nat.mul_le_mul_left 16 h23)
  have hbody : (r.parameters.n + 1) * r.Lin ≤ 9 * V ^ 3 := by
    calc
      _ ≤ V * (9 * V ^ 2) := Nat.mul_le_mul (by dsimp [V]; omega) hLin
      _ = _ := by ring
  change r.word.length ≤ 10000 * V ^ 3
  simp only [RowRequest.word, List.length_append, List.length_cons, List.length_nil, r.body_length]
  nlinarith only [hh, hLout, hbody, h03]

end NearQuarticWires.StagePullback
