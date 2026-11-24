import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly
import UnforcedLeray.Short.PartI.Tasks.SeedUniqueness

/-!
# Part III-a, task `PartIII-a:T21/c5/2` decomposition (`Sub/PartIII-a_T21_c5_2.lean`, SP 2866-2918, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2918 and
2991-2995 (`eq:short-causal-ampl-moving`).

## Mathematical structure and proved reductions

For the periodized moving frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed
kernel `κ` (`IsSeedKernels κ`) and a planar reference `P` (`IsPlanarReference P`):

1. **Decomposition of `amplDirectMat` into heat/dilation and Euler direct errors (proved here)**:
   * `movDirectHeat κ ν r i j` pairs `movLamDualHeat κ ν r i` with `perE κ d(r) j`, and
     `directHeatErr κ P ν r i j = movDirectHeat κ ν r i j - δ_{i,j} (modeKappa P i / θ(r))` isolates
     the subleading `κ_i / θ(r)` diagonal coming from the planar pairing `⟨λ_i, D e_j⟩ = δ_{i,j} κ_i`
     and the periodization identity `θ⁻¹ D(P_d e_j) - ∂_z(P_d e_j) = θ⁻¹ P_d(D e_j)`.
   * `movDirectEuler κ tr r i j` pairs the linearised Euler adjoint with `perE κ d(r) j`, and
     `directEulerErr κ P tr r i j = movDirectEuler κ tr r i j - δ_{i,j} modeEigen P i` isolates
     the leading eigenvalue diagonal `λ_i δ_{i,j}`.
   * `perLam_pairing_perE_eq_modeEigen`: by the exact biorthogonality `Λ E = I₂` on the moving cell
     (`F.dual`), the pairing `∫_{movingCell} (modeEigen P i * perLam κ d(r) i) * perE κ d(r) j`
     equals `if i = j then modeEigen P i else 0`.
   * `directEulerErr_eq_integral_eulerSub`: combines `perLam_pairing_perE_eq_modeEigen` with
     `seedModeEigen P.eigenvalue i = modeEigen P i` to express `directEulerErr κ P tr r i j` as the
     moving-cell pairing of `movLamDualEulerSub κ P.eigenvalue tr r i` with `perE κ d(r) j`.
   * `norm_directEulerErr_le_of_xNorm`: uses weighted Cauchy-Schwarz (`xNorm_pairing_bound`) and
     `F.E_bdd` (`xNorm d(r) m (perE κ d(r) j) ≤ ENNReal.ofReal K`) to bound
     `‖directEulerErr κ P tr r i j‖ ≤ B * max K 0` from any bound
     `xNorm d(r) (-m) (movLamDualEulerSub κ P.eigenvalue tr r i) ≤ ENNReal.ofReal B`.
   * `amplDirectMat_eq_add` and `norm_amplDirectMat_le`: proves that
     `amplDirectMat κ P F tr r i j = directHeatErr κ P ν r i j + directEulerErr κ P tr r i j` and
     bounds `‖amplDirectMat κ P F tr r i j‖` by the sum of their norms.

2. **Analytical leaves for the `O(ν³ / θ(r))` direct error**:
   * `DirectHeatError κ` (`PartIII-a:T21/c5/2/1`): the periodization tail and Gram-inverse derivative
     in `directHeatErr` are `O(1 / d(r)²) = O(ν³ / clockTheta ν r)` (by `inv_cellLen_sq_eq_nu_cube_div_theta`).
   * `DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`): after subtracting `modeEigen P i * perLam κ d(r) i`,
     the linearised Euler adjoint `movLamDualEulerSub κ P.eigenvalue tr r i` is bounded in
     `X_{-m, d(r)}` by `C_e * ν ^ 3 / clockTheta ν r` (combining the Gram-inverse error `O(d⁻²)`, the
     cylinder Biot-Savart tail `O(d⁻²)`, and the rescaled BUC train error `O(ν³ e^{-b₂ θ/ν³})`).
   * `amplDirectError_of`: assembles `AmplDirectError κ` (`PartIII-a:T21/c5/2`) from
     `DirectHeatError κ` (`PartIII-a:T21/c5/2/1`) and `DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`)
     with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Heat/dilation and Euler direct pairings and error matrices on `perE` -/

/-- Heat/dilation + age-derivative pairing on the periodized growing mode `perE κ d(r) j`
(SP 2905-2912, 2991-2995). -/
def movDirectHeat (κ : PlanarFrameKernels) (ν r : ℝ) (i j : Fin 2) : ℂ :=
  ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
    movLamDualHeat κ ν r i y * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- Linearised Euler (drift + nonlocal Biot-Savart) pairing on the periodized growing mode
`perE κ d(r) j` (SP 2905-2918, 2991-2995). -/
def movDirectEuler (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i j : Fin 2) : ℂ :=
  ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
    ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y) *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- Heat/dilation direct error entry after subtracting the subleading diagonal
`δ_{i,j} (modeKappa P i / θ(r))` (SP 2991-2995). -/
def directHeatErr (κ : PlanarFrameKernels) (P : PlanarData) (ν r : ℝ) (i j : Fin 2) : ℂ :=
  movDirectHeat κ ν r i j -
    if i = j then modeKappa P i / (clockTheta ν r : ℂ) else 0

/-- Linearised Euler direct error entry after subtracting the leading eigenvalue diagonal
`δ_{i,j} modeEigen P i` (SP 2991-2995). -/
def directEulerErr (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i j : Fin 2) : ℂ :=
  movDirectEuler κ tr r i j -
    if i = j then modeEigen P i else 0

/-! ## Analytical leaf specifications for `AmplDirectError` (`PartIII-a:T21/c5/2`) -/

/-- **Leaf 1 (`PartIII-a:T21/c5/2/1`, `DirectHeatError`, SP 2893, 2905-2912, 2991-2995)**:
By the termwise periodization identity `θ⁻¹ D(P_d e_j) - ∂_z(P_d e_j) = θ⁻¹ P_d(D e_j)`, the planar
subleading pairing `⟨λ_i, D e_j⟩ = δ_{i,j} κ_i`, the periodized tail `O(d⁻²) = O(ν³ / θ(r))`, and
the Gram-inverse derivative `(G⁻¹)_z = O(θ⁻¹ d⁻²)`, `movLamDualHeat κ ν r i` belongs to
`X_{-m, d(r)}` and `‖directHeatErr κ P ν r i j‖ ≤ C_h * ν ^ 3 / clockTheta ν r`.
Composed by task `PartIII-a:T21/c5/2` via `amplDirectError_of`. -/
def DirectHeatError (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ C_h b_h : ℝ, 0 ≤ C_h ∧ 1 ≤ b_h ∧
    ∀ b : ℝ, b_h ≤ b →
      ∃ ν_h : ℝ, 0 < ν_h ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_h →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ i j : Fin 2,
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) ∧
          ‖directHeatErr κ P ν r i j‖ ≤ C_h * ν ^ 3 / clockTheta ν r

/-- **Leaf 2 (`PartIII-a:T21/c5/2/2`, `DirectEulerSubBound`, SP 2866-2889, 2905-2918, 2991-2995)**:
For a planar reference `P` (`IsPlanarReference P`), after subtracting
`modeEigen P i * perLam κ d(r) i` (using planar seed uniqueness `PartI.isSeedXG_gaussianGrowingMode`
and planar duality `L_0^* λ_i = λ_i λ_i`), the residual Euler adjoint
`movLamDualEulerSub κ P.eigenvalue tr r i` (combining the Gram-inverse error `G⁻¹ - I = O(d⁻²)`, the
cylinder Biot-Savart tail `O(d⁻²)`, and the rescaled BUC train error `O(ν³ e^{-b₂ θ/ν³})`) belongs
to `X_{-m, d(r)}` with norm bounded by `C_e * ν ^ 3 / clockTheta ν r`.
Composed by task `PartIII-a:T21/c5/2` via `amplDirectError_of`. -/
def DirectEulerSubBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ C_e b_e : ℝ, 0 ≤ C_e ∧ 1 ≤ b_e ∧
    ∀ b : ℝ, b_e ≤ b →
      ∃ ν_e : ℝ, 0 < ν_e ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_e →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ i : Fin 2,
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2 (B0579.cellMeasure d (-m)) ∧
          xNorm d (-m) (movLamDualEulerSub κ P.eigenvalue tr r i) ≤
            ENNReal.ofReal (C_e * ν ^ 3 / clockTheta ν r)

namespace DirectErrorSub

open ComplCouplingSub

/-! ## Biorthogonality cancellation of `modeEigen P i` and Cauchy-Schwarz reduction -/

theorem seedModeEigen_eq_modeEigen (P : PlanarData) (i : Fin 2) :
    seedModeEigen P.eigenvalue i = modeEigen P i := rfl

/-- Exact biorthogonality `<perLam κ d(r) i, perE κ d(r) j> = δ_{i,j}` on the moving cell implies
that `<modeEigen P i * perLam κ d(r) i, perE κ d(r) j> = if i = j then modeEigen P i else 0`. -/
theorem perLam_pairing_perE_eq_modeEigen (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hF : PerFrameFacts κ ν m b K) (i j : Fin 2) :
    (∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
      (modeEigen P i * perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y) *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y) =
      if i = j then modeEigen P i else 0 := by
  have hdual := (periodizedFrame κ ν m b K hν hF).dual r hr hbr i j
  change (∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
      perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y *
        perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y) =
    if i = j then 1 else 0 at hdual
  simp_rw [mul_assoc]
  rw [integral_const_mul, hdual]
  split_ifs <;> ring

/-- Using `perLam_pairing_perE_eq_modeEigen`, the Euler direct error `directEulerErr κ P tr r i j`
equals the cell pairing of `movLamDualEulerSub κ P.eigenvalue tr r i` with `perE κ d(r) j`. -/
theorem directEulerErr_eq_integral_eulerSub (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2)
    (hEuler_mem : MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    directEulerErr κ P tr r i j =
      ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
        movLamDualEulerSub κ P.eigenvalue tr r i y *
          perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y := by
  set F := periodizedFrame κ ν m b K hν hF
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hE_mem : MemLp (perE κ d j) 2 (B0579.cellMeasure d m) :=
    memLp_frame_E F hr hbr j
  have hSub_int : IntegrableOn
      (fun y => movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    (xNorm_pairing_bound hEuler_mem hE_mem).1
  have hLam_int : IntegrableOn
      (fun y => (modeEigen P i * perLam κ d i y) * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) := by
    simp_rw [mul_assoc]
    exact (integrableOn_perLam_mul κ hm hd i hE_mem).const_mul (modeEigen P i)
  have heq : (fun y =>
      ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y) * perE κ d j y) =
      fun y => movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y +
        (modeEigen P i * perLam κ d i y) * perE κ d j y := by
    funext y
    unfold movLamDualEulerSub
    rw [seedModeEigen_eq_modeEigen]
    ring
  unfold directEulerErr movDirectEuler
  rw [heq, integral_add hSub_int hLam_int,
    perLam_pairing_perE_eq_modeEigen κ P hν hr hbr hF i j, add_sub_cancel_right]

/-- Weighted Cauchy-Schwarz bound on `‖directEulerErr κ P tr r i j‖` from an `X_{-m, d(r)}` bound
on `movLamDualEulerSub κ P.eigenvalue tr r i`. -/
theorem norm_directEulerErr_le_of_xNorm (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r B : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hB : 0 ≤ B) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2)
    (hEuler_mem : MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_bdd : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
      (movLamDualEulerSub κ P.eigenvalue tr r i) ≤ ENNReal.ofReal B) :
    ‖directEulerErr κ P tr r i j‖ ≤ B * max K 0 := by
  set F := periodizedFrame κ ν m b K hν hF
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hE_mem : MemLp (perE κ d j) 2 (B0579.cellMeasure d m) :=
    memLp_frame_E F hr hbr j
  have hE_bdd : xNorm d m (perE κ d j) ≤ ENNReal.ofReal (max K 0) :=
    (F.E_bdd r hr hbr j).trans (ENNReal.ofReal_le_ofReal (le_max_left K 0))
  rw [directEulerErr_eq_integral_eulerSub κ P hm hν hr hbr hd hF tr i j hEuler_mem]
  have hcs := (xNorm_pairing_bound hEuler_mem hE_mem).2
  have hprod : ENNReal.ofReal ‖∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
      movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y‖ ≤
      ENNReal.ofReal (B * max K 0) := by
    calc ENNReal.ofReal ‖∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
          movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y‖
        ≤ xNorm d (-m) (movLamDualEulerSub κ P.eigenvalue tr r i) * xNorm d m (perE κ d j) := hcs
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max K 0) := mul_le_mul' hEuler_bdd hE_bdd
      _ = ENNReal.ofReal (B * max K 0) := (ENNReal.ofReal_mul hB).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (le_max_right K 0))).1 hprod

/-! ## Decomposition of `movH0` and `amplDirectMat` on `F.E r j` -/

theorem movH0_perE_eq_heat_add_euler (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    movH0 κ tr r i ((periodizedFrame κ ν m b K hν hF).E r j) =
      movDirectHeat κ ν r i j + movDirectEuler κ tr r i j := by
  set F := periodizedFrame κ ν m b K hν hF
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hE_mem : MemLp (perE κ d j) 2 (B0579.cellMeasure d m) :=
    memLp_frame_E F hr hbr j
  have hHeat_int : IntegrableOn (fun y => movLamDualHeat κ ν r i y * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    (xNorm_pairing_bound hHeat_mem hE_mem).1
  have hSub_int : IntegrableOn
      (fun y => movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) :=
    (xNorm_pairing_bound hEuler_mem hE_mem).1
  have hLam_int : IntegrableOn
      (fun y => (modeEigen P i * perLam κ d i y) * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) := by
    simp_rw [mul_assoc]
    exact (integrableOn_perLam_mul κ hm hd i hE_mem).const_mul (modeEigen P i)
  have hEuler_int : IntegrableOn
      (fun y => ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y) * perE κ d j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) := by
    have heq : (fun y =>
        ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
          movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y) * perE κ d j y) =
        fun y => movLamDualEulerSub κ P.eigenvalue tr r i y * perE κ d j y +
          (modeEigen P i * perLam κ d i y) * perE κ d j y := by
      funext y
      unfold movLamDualEulerSub
      rw [seedModeEigen_eq_modeEigen]
      ring
    rw [heq]
    exact hSub_int.add hLam_int
  have hsum : (fun y => movLamDual κ tr r i y * perE κ d j y) =
      fun y => movLamDualHeat κ ν r i y * perE κ d j y +
        ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
          movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y) * perE κ d j y := by
    funext y
    rw [movLamDual_eq_heat_add_euler]
    ring
  change movH0 κ tr r i (perE κ d j) = movDirectHeat κ ν r i j + movDirectEuler κ tr r i j
  rw [movH0_eq_integral_movLamDual, hsum, integral_add hHeat_int hEuler_int]
  rfl

/-- Exact algebraic decomposition of `amplDirectMat`:
`amplDirectMat κ P F tr r i j = directHeatErr κ P ν r i j + directEulerErr κ P tr r i j`. -/
theorem amplDirectMat_eq_add (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    amplDirectMat κ P (periodizedFrame κ ν m b K hν hF) tr r i j =
      directHeatErr κ P ν r i j + directEulerErr κ P tr r i j := by
  unfold amplDirectMat directHeatErr directEulerErr modeDiag
  rw [movH0_perE_eq_heat_add_euler κ P hm hν hr hbr hd hF tr i j hHeat_mem hEuler_mem]
  split_ifs <;> ring

theorem norm_amplDirectMat_le (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K r : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i j : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ P.eigenvalue tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν hF) tr r i j‖ ≤
      ‖directHeatErr κ P ν r i j‖ + ‖directEulerErr κ P tr r i j‖ := by
  rw [amplDirectMat_eq_add κ P hm hν hr hbr hd hF tr i j hHeat_mem hEuler_mem]
  exact norm_add_le _ _

end DirectErrorSub

/-! ## Conditional assembly of `AmplDirectError` (`PartIII-a:T21/c5/2`) -/

open ComplCouplingSub DirectErrorSub in
/-- Conditional proof of `AmplDirectError κ` (`PartIII-a:T21/c5/2`) from `DirectHeatError κ`
(`PartIII-a:T21/c5/2/1`) and `DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`). -/
theorem amplDirectError_of (κ : PlanarFrameKernels)
    (hHeat : DirectHeatError κ) (hEuler : DirectEulerSubBound κ) :
    AmplDirectError κ := by
  intro hκ P hP m hm K
  obtain ⟨C_h, b_h, hCh, hbh, Hb_h⟩ := hHeat hκ P hP m hm
  obtain ⟨C_e, b_e, hCe, hbe, Hb_e⟩ := hEuler hκ P hP m hm
  have hK0 : 0 ≤ max K 0 := le_max_right K 0
  refine ⟨2 * (C_h + C_e * max K 0), max b_h b_e, by positivity,
    le_trans hbh (le_max_left _ _), ?_⟩
  intro b hb
  obtain ⟨ν_h, hν_h, Hν_h⟩ := Hb_h b (le_trans (le_max_left _ _) hb)
  obtain ⟨ν_e, hν_e, Hν_e⟩ := Hb_e b (le_trans (le_max_right _ _) hb)
  refine ⟨min (min ν_h ν_e) 1, by positivity, ?_⟩
  intro ν hν hF tr htr r hr hbr j
  have hν0 : 0 < ν := hν.1
  have hν_le_h : ν ≤ ν_h := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hν_le_e : ν ≤ ν_e := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν_le_1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hb1 : 1 ≤ b := le_trans hbh (le_trans (le_max_left _ _) hb)
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    one_le_cellLen_of_theta hν0 hν_le_1 hr (hb1.trans hbr)
  have hθ_pos : 0 < clockTheta ν r := theta_pos hν0 hr
  have hmode : ∀ i : Fin 2,
      ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν0 hF) tr r i j‖ ≤
        (C_h + C_e * max K 0) * ν ^ 3 / clockTheta ν r := by
    intro i
    obtain ⟨hHm, hHb⟩ := Hν_h ν ⟨hν0, hν_le_h⟩ r hr hbr i j
    obtain ⟨hEm, hEb⟩ := Hν_e ν ⟨hν0, hν_le_e⟩ tr htr r hr hbr i
    have htri := norm_amplDirectMat_le κ P hm hν0 hr hbr hd hF tr i j hHm hEm
    have hB_nn : 0 ≤ C_e * ν ^ 3 / clockTheta ν r := by positivity
    have hE_err := norm_directEulerErr_le_of_xNorm κ P hm hν0 hr hbr hd hB_nn hF tr i j hEm hEb
    calc ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν0 hF) tr r i j‖
        ≤ ‖directHeatErr κ P ν r i j‖ + ‖directEulerErr κ P tr r i j‖ := htri
      _ ≤ C_h * ν ^ 3 / clockTheta ν r + (C_e * ν ^ 3 / clockTheta ν r) * max K 0 :=
          add_le_add hHb hE_err
      _ = (C_h + C_e * max K 0) * ν ^ 3 / clockTheta ν r := by ring
  rw [Fin.sum_univ_two]
  calc ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν0 hF) tr r 0 j‖ +
        ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν0 hF) tr r 1 j‖
      ≤ (C_h + C_e * max K 0) * ν ^ 3 / clockTheta ν r +
          (C_h + C_e * max K 0) * ν ^ 3 / clockTheta ν r :=
        add_le_add (hmode 0) (hmode 1)
    _ = 2 * (C_h + C_e * max K 0) * ν ^ 3 / clockTheta ν r := by ring

end UnforcedLeray.Short.IIIa

end
