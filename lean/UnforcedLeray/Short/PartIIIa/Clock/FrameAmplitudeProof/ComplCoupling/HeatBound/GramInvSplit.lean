import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecay
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet

/-!
# Part III-a, task `PartIII-a:T21/c5/3/1/2`: product-rule split of `perLam = G(d)⁻¹ perLam0` (`PerGramInvHeatSplit`)

Source of record: `the November 2 reference manuscript` (SP), lines 2901-2912 and
2990-2997 (`eq:short-causal-ampl-moving`).

## Proved results in this file

1. **Cubic off-diagonal cross bound and termwise differentiation of `perGram κ d`
   (`gram_pt_three`, `exp_neg_sq_mul_cube_le`, `gramDerivCross_bound`, `hasDerivAt_gramTerm`,
   `hasDerivAt_perGram`, `norm_perGramDeriv_le`)**:
   Using translation invariance `gramTerm κ d i j k = ∫ z, κ.lamP i (z.1 - k d, z.2) * κ.e j z`,
   differentiates `gramTerm` under the integral sign with respect to `d` and sums termwise over
   `k : ℤ` using the `O(|y|⁻³)` decay of `∂₁(κ.lamP i)` from `SeedLamPJet2Decay κ`, proving
   `HasDerivAt (fun d' => perGram κ d' i j) (perGramDeriv κ d i j) d` with
   `‖perGramDeriv κ d i j‖ ≤ C_G / d ^ 3`.
2. **Differentiation of the `2 × 2` Gram inverse `(perGram κ d)⁻¹` and moving cell length `d(r)`
   (`hasDerivAt_perGram_inv_and_bound`, `hasDerivAt_cellLen_clockA`,
   `hasDerivWithinAt_perGram_inv_clockA`)**:
   Differentiates `(perGram κ d)⁻¹` via `Matrix.inv_def` and `Matrix.adjugate_fin_two` for large `d`,
   and composes with `r ↦ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)` to obtain the moving-time derivative
   `gDz j` bounded by `C_g * (1 / clockTheta ν r)`.
3. **Product rule for `ladDt`, linearity of `ladLapCx`, and moving split of `movLamDualHeat`
   (`ladLapCx_sum_fin2`, `ladDt_physFrameLam_eq`, `movLamDualHeat_split_of`,
   `perGramInvHeatSplit_of`)**:
   Differentiates `physFrameLam κ ν r i x = ∑ j, (perGram κ d)⁻¹ i j * physFrameLam0 κ ν r j x`
   in time (`ladDt`) and space (`ladLapCx`) and proves `PerGramInvHeatSplit κ` from
   `SeedLamPJet2Decay κ`.
4. **Unconditional split (`perGramInvHeatSplit`)**: the jet decay `SeedLamPJet2Decay κ` holds for
   every `κ` (`seedLamPJet2Decay_all`, `PartIII-a:T21/c5/3/1/1/1`, in `SeedJet.lean`), so
   `perGramInvHeatSplit_of` gives `PerGramInvHeatSplit κ` outright.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplCouplingHeat

/-! ## 1. Cubic cross-integral bound and differentiation of `perGram κ d` -/

/-- Pointwise bound `‖pdCx 0 L y‖ ≤ 2 * |C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 3` from the weighted
first-derivative bound `(1 + ‖y‖) * ‖fderiv ℝ L y‖ ≤ C * ((1 + |y.1| + |y.2|)⁻¹) ^ 2`. -/
theorem norm_pdCx_zero_le_inv_cube {L : ℝ × ℝ → ℂ} {C : ℝ}
    (h1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (y : ℝ × ℝ) :
    ‖pdCx 0 L y‖ ≤ 2 * |C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 3 := by
  have hy1 : |y.1| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le y
  have hy2 : |y.2| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le y
  have hnorm_le : 1 + |y.1| + |y.2| ≤ 2 * (1 + ‖y‖) := by linarith [norm_nonneg y]
  have hpos2 : 0 < 1 + |y.1| + |y.2| := by positivity
  have hpd : ‖pdCx 0 L y‖ ≤ ‖fderiv ℝ L y‖ := by
    unfold pdCx
    have hdir : ‖B0579.dir 0‖ = 1 := by simp [B0579.dir]
    simpa [hdir] using (fderiv ℝ L y).le_opNorm (B0579.dir 0)
  have h1_abs : (1 + ‖y‖) * ‖pdCx 0 L y‖ ≤ |C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 2 := by
    calc (1 + ‖y‖) * ‖pdCx 0 L y‖ ≤ (1 + ‖y‖) * ‖fderiv ℝ L y‖ :=
          mul_le_mul_of_nonneg_left hpd (by positivity)
      _ ≤ C * ((1 + |y.1| + |y.2|)⁻¹) ^ 2 := h1 y
      _ ≤ |C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc ‖pdCx 0 L y‖
      = ((1 + |y.1| + |y.2|) * ‖pdCx 0 L y‖) * (1 + |y.1| + |y.2|)⁻¹ := by
        rw [mul_right_comm, mul_inv_cancel₀ hpos2.ne', one_mul]
    _ ≤ (2 * ((1 + ‖y‖) * ‖pdCx 0 L y‖)) * (1 + |y.1| + |y.2|)⁻¹ :=
        mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (pdCx 0 L y)]) (by positivity)
    _ ≤ (2 * (|C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 2)) * (1 + |y.1| + |y.2|)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * |C| * ((1 + |y.1| + |y.2|)⁻¹) ^ 3 := by ring

/-- Pointwise splitting of `(1 + |y₁| + |y₂|)⁻¹ ^ 3` against the shifted Gaussian. -/
theorem gram_pt_three (a y1 y2 : ℝ) :
    (1 + |y1| + |y2|)⁻¹ ^ 3 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) ≤
      8 / (1 + |a|) ^ 3 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := by
  have hE8 : 0 ≤ Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) := (Real.exp_pos _).le
  have hE16 : 0 ≤ Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := (Real.exp_pos _).le
  have hEa : 0 ≤ Real.exp (-a ^ 2 / (4 * 16)) := (Real.exp_pos _).le
  rcases le_total |a| (2 * (|y1| + |y2|)) with h | h
  · have h1 : (1 + |a|) / 2 ≤ 1 + |y1| + |y2| := by linarith
    have hpos : 0 < (1 + |a|) / 2 := by positivity
    have h2 : (1 + |y1| + |y2|)⁻¹ ^ 3 ≤ 8 / (1 + |a|) ^ 3 := by
      have hcb := pow_le_pow_left₀ hpos.le h1 3
      calc (1 + |y1| + |y2|)⁻¹ ^ 3 = 1 / (1 + |y1| + |y2|) ^ 3 := by rw [inv_pow, one_div]
        _ ≤ 1 / ((1 + |a|) / 2) ^ 3 := one_div_le_one_div_of_le (by positivity) hcb
        _ = 8 / (1 + |a|) ^ 3 := by field_simp; norm_num
    have hm := mul_le_mul_of_nonneg_right h2 hE8
    have hnn : 0 ≤ Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) :=
      mul_nonneg hEa hE16
    linarith
  · have hz : |a| / 2 ≤ |y1 + a| := by
      have hA : |a| ≤ |y1 + a| + |y1| := by
        calc |a| = |(y1 + a) - y1| := by congr 1; ring
          _ ≤ |y1 + a| + |y1| := abs_sub _ _
      have h1 : |y1| ≤ |a| / 2 := by linarith [abs_nonneg y2]
      linarith
    have hsq : a ^ 2 / 4 ≤ (y1 + a) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hz 2
      have hsa : (|a| / 2) ^ 2 = a ^ 2 / 4 := by rw [div_pow, sq_abs]; ring
      have hsy : |y1 + a| ^ 2 = (y1 + a) ^ 2 := sq_abs _
      linarith
    have hexp : Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) ≤
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg y2]
    have hP : (1 + |y1| + |y2|)⁻¹ ^ 3 ≤ 1 := by
      have h1' : 1 ≤ 1 + |y1| + |y2| := by linarith [abs_nonneg y1, abs_nonneg y2]
      exact pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ h1')
    have hm := mul_le_mul_of_nonneg_right hP hE8
    have hnn : 0 ≤ 8 / (1 + |a|) ^ 3 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) := by
      positivity
    linarith

/-- The Gaussian weight `e^{-a²/64}` against `(1 + |a|)³`. -/
theorem exp_neg_sq_mul_cube_le (a : ℝ) :
    Real.exp (-a ^ 2 / (4 * 16)) * (1 + |a|) ^ 3 ≤ 65536 := by
  have h1 := Real.add_one_le_exp (a ^ 2 / 128)
  have h1_sq : (a ^ 2 / 128 + 1) ^ 2 ≤ Real.exp (a ^ 2 / (4 * 16)) := by
    calc (a ^ 2 / 128 + 1) ^ 2 ≤ Real.exp (a ^ 2 / 128) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = Real.exp (a ^ 2 / 128 + a ^ 2 / 128) := by rw [sq, ← Real.exp_add]
      _ = Real.exp (a ^ 2 / (4 * 16)) := by congr 1; ring
  have hEF : Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (a ^ 2 / (4 * 16)) = 1 := by
    rw [← Real.exp_add, show -a ^ 2 / (4 * 16) + a ^ 2 / (4 * 16) = 0 by ring, Real.exp_zero]
  have hE : 0 < Real.exp (-a ^ 2 / (4 * 16)) := Real.exp_pos _
  have hpoly : (1 + |a|) ^ 3 ≤ 65536 * (a ^ 2 / 128 + 1) ^ 2 := by
    have hnonneg : 0 ≤ 4 * (|a| ^ 2 - |a|) ^ 2 + 7 * |a| ^ 3 +
        1017 * (|a| - 1) ^ 2 + 2031 * |a| + 64518 := by positivity
    have hid : 65536 * (a ^ 2 / 128 + 1) ^ 2 - (1 + |a|) ^ 3 =
        4 * (|a| ^ 2 - |a|) ^ 2 + 7 * |a| ^ 3 +
          1017 * (|a| - 1) ^ 2 + 2031 * |a| + 64518 := by
      rw [← sq_abs a]
      ring
    linarith
  have hq : (1 + |a|) ^ 3 ≤ 65536 * Real.exp (a ^ 2 / (4 * 16)) :=
    hpoly.trans (mul_le_mul_of_nonneg_left h1_sq (by norm_num))
  calc Real.exp (-a ^ 2 / (4 * 16)) * (1 + |a|) ^ 3
      ≤ Real.exp (-a ^ 2 / (4 * 16)) * (65536 * Real.exp (a ^ 2 / (4 * 16))) :=
        mul_le_mul_of_nonneg_left hq hE.le
    _ = 65536 := by linear_combination 65536 * hEF

/-- Uniform cubic decay `‖∫ ∂₁(κ.lamP i) y * κ.e j (y.1 + a, y.2) dy‖ ≤ K₃ / (1 + |a|) ^ 3`. -/
theorem gramDerivCross_bound (κ : PlanarFrameKernels) {C₁ : ℝ}
    (h1 : ∀ (i : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP i) z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    ∃ K₃ : ℝ, 0 ≤ K₃ ∧ ∀ (i j : Fin 2) (a : ℝ),
      ‖∫ y : ℝ × ℝ, pdCx 0 (κ.lamP i) y * κ.e j (y.1 + a, y.2)‖ ≤ K₃ / (1 + |a|) ^ 3 := by
  obtain ⟨C2, hC2⟩ := κ.e_decay
  refine ⟨2 * |C₁| * |C2| * (1048640 * Real.pi), by positivity, fun i j a => ?_⟩
  have hA : 0 ≤ 2 * |C₁| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖pdCx 0 (κ.lamP i) y * κ.e j (y.1 + a, y.2)‖ ≤
      (2 * |C₁| * |C2|) * (8 / (1 + |a|) ^ 3 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have hp1 : ‖pdCx 0 (κ.lamP i) y‖ ≤ 2 * |C₁| * ((1 + |y.1| + |y.2|)⁻¹) ^ 3 :=
      norm_pdCx_zero_le_inv_cube (h1 i) y
    have hp2 : ‖κ.e j (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hC2 j (y.1 + a, y.2)
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖pdCx 0 (κ.lamP i) y‖ * ‖κ.e j (y.1 + a, y.2)‖
        ≤ (2 * |C₁| * (1 + |y.1| + |y.2|)⁻¹ ^ 3) *
            (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul hp1 hp2 (norm_nonneg _) (by positivity)
      _ = (2 * |C₁| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 3 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (2 * |C₁| * |C2|) * (8 / (1 + |a|) ^ 3 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
          Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        mul_le_mul_of_nonneg_left (gram_pt_three a y.1 y.2) hA
  have G8 := integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (2 * |C₁| * |C2|) *
      (8 / (1 + |a|) ^ 3 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (8 / (1 + |a|) ^ 3)).add
      (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hE := exp_neg_sq_mul_cube_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 65536 / (1 + |a|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ‖∫ y : ℝ × ℝ, pdCx 0 (κ.lamP i) y * κ.e j (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (2 * |C₁| * |C2|) *
          (8 / (1 + |a|) ^ 3 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
    _ = (2 * |C₁| * |C2|) * (8 / (1 + |a|) ^ 3 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_shift_gauss (c := a) (t := 2) (by norm_num),
          integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (2 * |C₁| * |C2|) * (8 / (1 + |a|) ^ 3 * (4 * Real.pi * 2) +
          65536 / (1 + |a|) ^ 3 * (4 * Real.pi * 4)) := by
        gcongr
    _ = 2 * |C₁| * |C2| * (1048640 * Real.pi) / (1 + |a|) ^ 3 := by ring

/-- `d`-derivative of the `k`-th cross integral `gramTerm κ d i j k`. -/
def gramTermDeriv (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) : ℂ :=
  (-(k : ℝ)) • ∫ y : ℝ × ℝ, pdCx 0 (κ.lamP i) y * κ.e j (y.1 + (k : ℝ) * d, y.2)

/-- Translation identity `gramTerm κ d i j k = ∫ z, κ.lamP i (z.1 - k d, z.2) * κ.e j z`. -/
theorem gramTerm_eq_shift_lamP (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) :
    gramTerm κ d i j k =
      ∫ z : ℝ × ℝ, κ.lamP i (z.1 - (k : ℝ) * d, z.2) * κ.e j z := by
  unfold gramTerm
  have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2)) ((k : ℝ) * d, 0)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have h1 : z - ((k : ℝ) * d, 0) = (z.1 - (k : ℝ) * d, z.2) := by ext <;> simp
  have h2 : ((z.1 - (k : ℝ) * d, z.2).1 + (k : ℝ) * d, (z.1 - (k : ℝ) * d, z.2).2) = z := by
    ext <;> simp [sub_add_cancel]
  rw [h1, h2]

/-- Translation identity for `gramTermDeriv κ d i j k`. -/
theorem gramTermDeriv_eq_shift_lamP (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) :
    gramTermDeriv κ d i j k =
      ∫ z : ℝ × ℝ, (-(k : ℝ)) • (pdCx 0 (κ.lamP i) (z.1 - (k : ℝ) * d, z.2) * κ.e j z) := by
  unfold gramTermDeriv
  rw [← integral_smul]
  have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => (-(k : ℝ)) • (pdCx 0 (κ.lamP i) y * κ.e j (y.1 + (k : ℝ) * d, y.2)))
    ((k : ℝ) * d, 0)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have h1 : z - ((k : ℝ) * d, 0) = (z.1 - (k : ℝ) * d, z.2) := by ext <;> simp
  have h2 : ((z.1 - (k : ℝ) * d, z.2).1 + (k : ℝ) * d, (z.1 - (k : ℝ) * d, z.2).2) = z := by
    ext <;> simp [sub_add_cancel]
  rw [h1, h2]

/-- Differentiating `d ↦ gramTerm κ d i j k` under the integral sign. -/
theorem hasDerivAt_gramTerm (κ : PlanarFrameKernels) (i j : Fin 2)
    (hCD : ContDiff ℝ 2 (κ.lamP i)) {C₁ : ℝ}
    (h1 : ∀ z : ℝ × ℝ,
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP i) z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2)
    (k : ℤ) (d : ℝ) :
    HasDerivAt (fun d' => gramTerm κ d' i j k) (gramTermDeriv κ d i j k) d := by
  obtain ⟨C₀, hC₀⟩ := κ.lamP_decay
  obtain ⟨C₂, hC₂⟩ := κ.e_decay
  set F : ℝ → ℝ × ℝ → ℂ := fun d' z => κ.lamP i (z.1 - (k : ℝ) * d', z.2) * κ.e j z
  set F' : ℝ → ℝ × ℝ → ℂ := fun d' z =>
    (-(k : ℝ)) • (pdCx 0 (κ.lamP i) (z.1 - (k : ℝ) * d', z.2) * κ.e j z)
  set bound : ℝ × ℝ → ℝ := fun z =>
    |(k : ℝ)| * (2 * |C₁|) * |C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))
  have hLd : Differentiable ℝ (κ.lamP i) := hCD.differentiable (by norm_num)
  have hpd_cont : Continuous (pdCx 0 (κ.lamP i)) := by
    have heq : pdCx 0 (κ.lamP i) = fun w => fderiv ℝ (κ.lamP i) w (B0579.dir 0) := rfl
    rw [heq]
    exact (hCD.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hF_cont : ∀ d' : ℝ, Continuous (F d') := fun d' => by
    refine ((κ.lamP_cont i).comp ?_).mul (κ.e_cont j)
    exact (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hF'_cont : ∀ d' : ℝ, Continuous (F' d') := fun d' => by
    refine Continuous.const_smul ?_ (-(k : ℝ))
    refine (hpd_cont.comp ?_).mul (κ.e_cont j)
    exact (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hG8 : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))) :=
    Gaussian.integrable_gauss_plane (a := 2) (by norm_num)
  have hF_int : Integrable (F d) volume := by
    refine Integrable.mono' (hG8.const_mul (|C₀| * |C₂|)) (hF_cont d).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    have hL_le : ‖κ.lamP i (z.1 - (k : ℝ) * d, z.2)‖ ≤ |C₀| := by
      have hw := hC₀ i (z.1 - (k : ℝ) * d, z.2)
      have hinv : ((1 + |(z.1 - (k : ℝ) * d, z.2).1| + |(z.1 - (k : ℝ) * d, z.2).2|)⁻¹) ^ 2 ≤ 1 := by
        have h1' : 1 ≤ 1 + |(z.1 - (k : ℝ) * d, z.2).1| + |(z.1 - (k : ℝ) * d, z.2).2| := by
          linarith [abs_nonneg (z.1 - (k : ℝ) * d), abs_nonneg z.2]
        exact pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ h1')
      calc ‖κ.lamP i (z.1 - (k : ℝ) * d, z.2)‖
          ≤ |C₀| * ((1 + |(z.1 - (k : ℝ) * d, z.2).1| + |(z.1 - (k : ℝ) * d, z.2).2|)⁻¹) ^ 2 :=
            hw.trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) (by positivity))
        _ ≤ |C₀| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg C₀)
        _ = |C₀| := mul_one _
    have he_le : ‖κ.e j z‖ ≤ |C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by
      have he := hC₂ j z
      have hh : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) =
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by norm_num
      rw [hh] at he
      exact he.trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) (Real.exp_pos _).le)
    calc ‖κ.lamP i (z.1 - (k : ℝ) * d, z.2)‖ * ‖κ.e j z‖
        ≤ |C₀| * (|C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))) :=
          mul_le_mul hL_le he_le (norm_nonneg _) (abs_nonneg C₀)
      _ = |C₀| * |C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by ring
  have hbound_int : Integrable bound volume :=
    hG8.const_mul (|(k : ℝ)| * (2 * |C₁|) * |C₂|)
  have h_bound : ∀ᵐ z ∂volume, ∀ d' ∈ (Set.univ : Set ℝ), ‖F' d' z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall fun z d' _ => ?_
    simp only [F', bound, norm_smul, Real.norm_eq_abs, abs_neg, norm_mul]
    have hpd_le : ‖pdCx 0 (κ.lamP i) (z.1 - (k : ℝ) * d', z.2)‖ ≤ 2 * |C₁| := by
      have hw := norm_pdCx_zero_le_inv_cube h1 (z.1 - (k : ℝ) * d', z.2)
      have hinv : ((1 + |(z.1 - (k : ℝ) * d', z.2).1| + |(z.1 - (k : ℝ) * d', z.2).2|)⁻¹) ^ 3 ≤ 1 := by
        have h1' : 1 ≤ 1 + |(z.1 - (k : ℝ) * d', z.2).1| + |(z.1 - (k : ℝ) * d', z.2).2| := by
          linarith [abs_nonneg (z.1 - (k : ℝ) * d'), abs_nonneg z.2]
        exact pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ h1')
      calc ‖pdCx 0 (κ.lamP i) (z.1 - (k : ℝ) * d', z.2)‖
          ≤ 2 * |C₁| * ((1 + |(z.1 - (k : ℝ) * d', z.2).1| + |(z.1 - (k : ℝ) * d', z.2).2|)⁻¹) ^ 3 := hw
        _ ≤ 2 * |C₁| * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 2 * |C₁| := mul_one _
    have he_le : ‖κ.e j z‖ ≤ |C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by
      have he := hC₂ j z
      have hh : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) =
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by norm_num
      rw [hh] at he
      exact he.trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) (Real.exp_pos _).le)
    calc |(k : ℝ)| * (‖pdCx 0 (κ.lamP i) (z.1 - (k : ℝ) * d', z.2)‖ * ‖κ.e j z‖)
        ≤ |(k : ℝ)| * ((2 * |C₁|) * (|C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpd_le he_le (norm_nonneg _) (by positivity)) (abs_nonneg _)
      _ = |(k : ℝ)| * (2 * |C₁|) * |C₂| * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by ring
  have h_diff : ∀ᵐ z ∂volume, ∀ d' ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun d'' => F d'' z) (F' d' z) d' := by
    refine Filter.Eventually.of_forall fun z d' _ => ?_
    have hin : HasDerivAt (fun d'' : ℝ => ((z.1 - (k : ℝ) * d'', z.2) : ℝ × ℝ))
        ((-((k : ℝ) * 1), (0 : ℝ))) d' :=
      (((hasDerivAt_id d').const_mul (k : ℝ)).const_sub z.1).prodMk (hasDerivAt_const d' z.2)
    have hcomp := (hLd (z.1 - (k : ℝ) * d', z.2)).hasFDerivAt.comp_hasDerivAt d' hin
    have hmul := hcomp.mul_const (κ.e j z)
    refine hmul.congr_deriv ?_
    have hvec : ((-((k : ℝ) * 1), (0 : ℝ)) : ℝ × ℝ) = (-(k : ℝ)) • B0579.dir 0 := by
      ext <;> simp [B0579.dir]
    rw [hvec, ContinuousLinearMap.map_smul]
    simp only [F', pdCx, smul_mul_assoc]
  have hkey := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    Filter.univ_mem
    (Filter.Eventually.of_forall fun d' => (hF_cont d').aestronglyMeasurable)
    hF_int (hF'_cont d).aestronglyMeasurable h_bound hbound_int h_diff).2
  have hfun : (fun d' => ∫ a : ℝ × ℝ, F d' a) = fun d' => gramTerm κ d' i j k := by
    funext d'
    exact (gramTerm_eq_shift_lamP κ d' i j k).symm
  rw [← hfun, gramTermDeriv_eq_shift_lamP]
  exact hkey

/-- Derivative of `d ↦ perGram κ d i j`. -/
def perGramDeriv (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) : ℂ :=
  ∑' k : ℤ, gramTermDeriv κ d i j k

/-- Bound on `gramTermDeriv κ d' i j k` for `d' ≥ d / 2 > 0`:
`‖gramTermDeriv κ d' i j k‖ ≤ (8 * K₃ / d ^ 3) * (1 / (k : ℝ) ^ 2)`. -/
theorem norm_gramTermDeriv_le_of_ge {κ : PlanarFrameKernels} {i j : Fin 2} {K₃ d d' : ℝ}
    (hK₃0 : 0 ≤ K₃) (hd : 0 < d) (hd' : d / 2 ≤ d')
    (hK₃ : ∀ a : ℝ,
      ‖∫ y : ℝ × ℝ, pdCx 0 (κ.lamP i) y * κ.e j (y.1 + a, y.2)‖ ≤ K₃ / (1 + |a|) ^ 3)
    (k : ℤ) :
    ‖gramTermDeriv κ d' i j k‖ ≤ (8 * K₃ / d ^ 3) * (1 / (k : ℝ) ^ 2) := by
  by_cases hk : k = 0
  · subst hk
    simp [gramTermDeriv]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk_pos : 0 < |(k : ℝ)| := abs_pos.2 hkR
    have hd'_pos : 0 < d' := by linarith
    have hlow : |(k : ℝ)| * (d / 2) ≤ 1 + |(k : ℝ) * d'| := by
      rw [abs_mul, abs_of_pos hd'_pos]
      have := mul_le_mul_of_nonneg_left hd' hk_pos.le
      linarith
    have hcb : (|(k : ℝ)| * (d / 2)) ^ 3 ≤ (1 + |(k : ℝ) * d'|) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hlow 3
    have hpos_cb : 0 < (|(k : ℝ)| * (d / 2)) ^ 3 := by positivity
    unfold gramTermDeriv
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    calc |(k : ℝ)| * ‖∫ y : ℝ × ℝ, pdCx 0 (κ.lamP i) y * κ.e j (y.1 + (k : ℝ) * d', y.2)‖
        ≤ |(k : ℝ)| * (K₃ / (1 + |(k : ℝ) * d'|) ^ 3) :=
          mul_le_mul_of_nonneg_left (hK₃ ((k : ℝ) * d')) hk_pos.le
      _ ≤ |(k : ℝ)| * (K₃ / (|(k : ℝ)| * (d / 2)) ^ 3) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hK₃0 hpos_cb hcb) hk_pos.le
      _ = (8 * K₃ / d ^ 3) * (1 / |(k : ℝ)| ^ 2) := by
          have hd_ne : d ≠ 0 := hd.ne'
          have hkabs_ne : |(k : ℝ)| ≠ 0 := hk_pos.ne'
          field_simp
          ring
      _ = (8 * K₃ / d ^ 3) * (1 / (k : ℝ) ^ 2) := by rw [sq_abs]

/-- Termwise differentiation of `d ↦ perGram κ d i j` for `d > 0` and `O(d⁻³)` bound on
`perGramDeriv κ d i j`. -/
theorem hasDerivAt_perGram_and_bound (κ : PlanarFrameKernels)
    (hCD : ∀ i : Fin 2, ContDiff ℝ 2 (κ.lamP i)) {C₁ : ℝ}
    (h1 : ∀ (i : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP i) z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    ∃ C_G : ℝ, 0 ≤ C_G ∧ ∀ {d : ℝ}, 0 < d → ∀ i j : Fin 2,
      HasDerivAt (fun d' => perGram κ d' i j) (perGramDeriv κ d i j) d ∧
      ‖perGramDeriv κ d i j‖ ≤ C_G / d ^ 3 := by
  obtain ⟨K₃, hK₃0, hK₃⟩ := gramDerivCross_bound κ h1
  have hS : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hS_nonneg : 0 ≤ ∑' k : ℤ, 1 / (k : ℝ) ^ 2 :=
    tsum_nonneg fun k => by positivity
  refine ⟨8 * K₃ * ∑' k : ℤ, 1 / (k : ℝ) ^ 2, by positivity, fun {d} hd i j => ?_⟩
  have hpt : d ∈ Ioo (d / 2) (2 * d) := ⟨by linarith, by linarith⟩
  have hu : Summable (fun k : ℤ => (8 * K₃ / d ^ 3) * (1 / (k : ℝ) ^ 2)) :=
    hS.mul_left (8 * K₃ / d ^ 3)
  have hsum0 : Summable (fun k : ℤ => gramTerm κ d i j k) :=
    (perGramUnfold κ d hd i j).1
  have hder_tsum := hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : ℤ) d' => gramTerm κ d' i j k)
    (g' := fun (k : ℤ) d' => gramTermDeriv κ d' i j k)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun k d' _ => hasDerivAt_gramTerm κ i j (hCD i) (h1 i) k d')
    (fun k d' hd' => norm_gramTermDeriv_le_of_ge hK₃0 hd hd'.1.le (hK₃ i j) k)
    hpt hsum0 hpt
  have hev : (fun d' => ∑' k : ℤ, gramTerm κ d' i j k) =ᶠ[𝓝 d] (fun d' => perGram κ d' i j) := by
    filter_upwards [lt_mem_nhds hd] with d' hd'
    exact ((perGramUnfold κ d' hd' i j).2).symm
  have hder : HasDerivAt (fun d' => perGram κ d' i j) (perGramDeriv κ d i j) d :=
    hder_tsum.congr_of_eventuallyEq hev.symm
  have hnorm_sum : Summable (fun k : ℤ => ‖gramTermDeriv κ d i j k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_gramTermDeriv_le_of_ge hK₃0 hd (by linarith) (hK₃ i j) k) hu
  have hbound : ‖perGramDeriv κ d i j‖ ≤ (8 * K₃ * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) / d ^ 3 := by
    unfold perGramDeriv
    calc ‖∑' k : ℤ, gramTermDeriv κ d i j k‖
        ≤ ∑' k : ℤ, ‖gramTermDeriv κ d i j k‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' k : ℤ, (8 * K₃ / d ^ 3) * (1 / (k : ℝ) ^ 2) :=
          hnorm_sum.tsum_le_tsum
            (fun k => norm_gramTermDeriv_le_of_ge hK₃0 hd (by linarith) (hK₃ i j) k) hu
      _ = (8 * K₃ / d ^ 3) * ∑' k : ℤ, 1 / (k : ℝ) ^ 2 := tsum_mul_left
      _ = (8 * K₃ * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) / d ^ 3 := by ring
  exact ⟨hder, hbound⟩

/-! ## 2. Differentiating `(perGram κ d)⁻¹` and composing with `cellLen (ν ^ (-2 : ℝ)) (clockA ν r)` -/

/-- For a `2 × 2` matrix-valued curve `G : ℝ → Matrix (Fin 2) (Fin 2) ℂ` that is within `1 / 4` of
the identity at `d` and entrywise differentiable at `d` with `‖G' i j‖ ≤ B`, the inverse entries
`d' ↦ (G d')⁻¹ i j` are differentiable at `d` with derivative bounded by `25 * B`. -/
theorem hasDerivAt_matrix_inv_fin2 {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {G' : Matrix (Fin 2) (Fin 2) ℂ} {d B : ℝ} (hB0 : 0 ≤ B)
    (hnear : ∀ i j : Fin 2, ‖G d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hder : ∀ i j : Fin 2, HasDerivAt (fun d' => G d' i j) (G' i j) d)
    (hb : ∀ i j : Fin 2, ‖G' i j‖ ≤ B) (i j : Fin 2) :
    ∃ g' : ℂ, HasDerivAt (fun d' => (G d')⁻¹ i j) g' d ∧ ‖g'‖ ≤ 27 * B := by
  have h00 := hnear 0 0
  have h11 := hnear 1 1
  have h01 := hnear 0 1
  have h10 := hnear 1 0
  simp only [ite_true, ite_false, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, sub_zero,
    one_ne_zero] at h00 h11 h01 h10
  have ha : 3 / 4 ≤ ‖G d 0 0‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G d 0 0)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hd_low : 3 / 4 ≤ ‖G d 1 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G d 1 1)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have ha' : ‖G d 0 0‖ ≤ 5 / 4 := by
    have := norm_sub_norm_le (G d 0 0) 1
    rw [norm_one] at this
    linarith
  have hd' : ‖G d 1 1‖ ≤ 5 / 4 := by
    have := norm_sub_norm_le (G d 1 1) 1
    rw [norm_one] at this
    linarith
  have h01' : ‖G d 0 1‖ ≤ 5 / 4 := by linarith
  have h10' : ‖G d 1 0‖ ≤ 5 / 4 := by linarith
  have hdet_low : 1 / 2 ≤ ‖(G d).det‖ := by
    rw [Matrix.det_fin_two]
    have h1 := norm_sub_norm_le (G d 0 0 * G d 1 1) (G d 0 1 * G d 1 0)
    rw [norm_mul, norm_mul] at h1
    nlinarith [norm_nonneg (G d 0 1), norm_nonneg (G d 1 0),
      mul_le_mul ha hd_low (by norm_num) (norm_nonneg _),
      mul_le_mul h01 h10 (norm_nonneg _) (by norm_num)]
  have hdet_ne : (G d).det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet_low
    linarith
  have hinv_le : ‖((G d).det)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  set det' : ℂ :=
    (G' 0 0 * G d 1 1 + G d 0 0 * G' 1 1) - (G' 0 1 * G d 1 0 + G d 0 1 * G' 1 0)
  have hdet_der : HasDerivAt (fun d' => (G d').det) det' d := by
    have hfun : (fun d' => (G d').det) =
        fun d' => G d' 0 0 * G d' 1 1 - G d' 0 1 * G d' 1 0 := by
      funext d'
      exact Matrix.det_fin_two (G d')
    rw [hfun]
    exact ((hder 0 0).mul (hder 1 1)).sub ((hder 0 1).mul (hder 1 0))
  have hdet'_le : ‖det'‖ ≤ 5 * B := by
    have h1 : ‖G' 0 0 * G d 1 1‖ ≤ B * (5 / 4) := by
      rw [norm_mul]; exact mul_le_mul (hb 0 0) hd' (norm_nonneg _) hB0
    have h2 : ‖G d 0 0 * G' 1 1‖ ≤ (5 / 4) * B := by
      rw [norm_mul]; exact mul_le_mul ha' (hb 1 1) (norm_nonneg _) (by positivity)
    have h3 : ‖G' 0 1 * G d 1 0‖ ≤ B * (5 / 4) := by
      rw [norm_mul]; exact mul_le_mul (hb 0 1) h10' (norm_nonneg _) hB0
    have h4 : ‖G d 0 1 * G' 1 0‖ ≤ (5 / 4) * B := by
      rw [norm_mul]; exact mul_le_mul h01' (hb 1 0) (norm_nonneg _) (by positivity)
    calc ‖det'‖
        ≤ ‖G' 0 0 * G d 1 1 + G d 0 0 * G' 1 1‖ + ‖G' 0 1 * G d 1 0 + G d 0 1 * G' 1 0‖ :=
          norm_sub_le _ _
      _ ≤ (‖G' 0 0 * G d 1 1‖ + ‖G d 0 0 * G' 1 1‖) +
          (‖G' 0 1 * G d 1 0‖ + ‖G d 0 1 * G' 1 0‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ 5 * B := by linarith
  have hinv_der : HasDerivAt (fun d' => ((G d').det)⁻¹) (-det' / ((G d).det) ^ 2) d :=
    hdet_der.inv hdet_ne
  have hinv'_le : ‖-det' / ((G d).det) ^ 2‖ ≤ 20 * B := by
    have hdiv : -det' / ((G d).det) ^ 2 = -det' * (((G d).det)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    rw [hdiv, norm_mul, norm_neg, norm_pow]
    have hsq : ‖((G d).det)⁻¹‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg ((G d).det)⁻¹]
    nlinarith [norm_nonneg det', norm_nonneg (((G d).det)⁻¹)]
  have hprod_bound : ∀ {u : ℝ → ℂ} {u' : ℂ},
      HasDerivAt u u' d → ‖u d‖ ≤ 5 / 4 → ‖u'‖ ≤ B →
      ∃ g' : ℂ, HasDerivAt (fun d' => ((G d').det)⁻¹ * u d') g' d ∧ ‖g'‖ ≤ 27 * B := by
    intro u u' hu hu0 hu'
    refine ⟨(-det' / ((G d).det) ^ 2) * u d + ((G d).det)⁻¹ * u', hinv_der.mul hu, ?_⟩
    have hp1 : ‖(-det' / ((G d).det) ^ 2) * u d‖ ≤ (20 * B) * (5 / 4) := by
      rw [norm_mul]; exact mul_le_mul hinv'_le hu0 (norm_nonneg _) (by positivity)
    have hp2 : ‖((G d).det)⁻¹ * u'‖ ≤ 2 * B := by
      rw [norm_mul]; exact mul_le_mul hinv_le hu' (norm_nonneg _) (by positivity)
    calc ‖(-det' / ((G d).det) ^ 2) * u d + ((G d).det)⁻¹ * u'‖
        ≤ ‖(-det' / ((G d).det) ^ 2) * u d‖ + ‖((G d).det)⁻¹ * u'‖ := norm_add_le _ _
      _ ≤ 27 * B := by linarith
  fin_cases i <;> fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · have hfun : (fun d' => (G d')⁻¹ 0 0) = fun d' => ((G d').det)⁻¹ * G d' 1 1 := by
      funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
    rw [hfun]; exact hprod_bound (hder 1 1) hd' (hb 1 1)
  · have hfun : (fun d' => (G d')⁻¹ 0 1) = fun d' => ((G d').det)⁻¹ * (-G d' 0 1) := by
      funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
    rw [hfun]; exact hprod_bound (hder 0 1).neg (by rw [norm_neg]; exact h01')
      (by rw [norm_neg]; exact hb 0 1)
  · have hfun : (fun d' => (G d')⁻¹ 1 0) = fun d' => ((G d').det)⁻¹ * (-G d' 1 0) := by
      funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
    rw [hfun]; exact hprod_bound (hder 1 0).neg (by rw [norm_neg]; exact h10')
      (by rw [norm_neg]; exact hb 1 0)
  · have hfun : (fun d' => (G d')⁻¹ 1 1) = fun d' => ((G d').det)⁻¹ * G d' 0 0 := by
      funext d'; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; simp
    rw [hfun]; exact hprod_bound (hder 0 0) ha' (hb 0 0)

/-- Derivative of `s ↦ cellLen c (clockA ν s)` at `s = r`:
`d'(r) = -(ν / (2 * clockA ν r)) * cellLen c (clockA ν r)`. -/
theorem hasDerivAt_cellLen_clockA (c : ℝ) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (fun s => cellLen c (clockA ν s))
      (-(ν / (2 * clockA ν r)) * cellLen c (clockA ν r)) r := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  have hclock : HasDerivAt (clockA ν) ν r := by
    unfold clockA
    simpa using ((hasDerivAt_id r).const_mul ν).const_add 1
  have hsqrt : HasDerivAt (fun s => Real.sqrt (clockA ν s))
      (ν / (2 * Real.sqrt (clockA ν r))) r :=
    hclock.sqrt ha.ne'
  have hinv := hsqrt.inv hsa.ne'
  have hmul := hinv.const_mul c
  have hfun : (fun s => cellLen c (clockA ν s)) = fun s => c * (Real.sqrt (clockA ν s))⁻¹ := by
    funext s
    unfold cellLen
    ring
  rw [hfun]
  refine hmul.congr_deriv ?_
  unfold cellLen
  have hsq : Real.sqrt (clockA ν r) ^ 2 = clockA ν r := Real.sq_sqrt ha.le
  have ha_ne : clockA ν r ≠ 0 := ha.ne'
  have hsa_ne : Real.sqrt (clockA ν r) ≠ 0 := hsa.ne'
  field_simp
  rw [hsq]

/-- Composing `(perGram κ d)⁻¹` with `s ↦ cellLen (ν ^ (-2 : ℝ)) (clockA ν s)`: for `d ≥ D_g`,
gives `HasDerivWithinAt` on `Ici r` and the moving-time derivative `gDz j` bounded by
`C_g * (1 / clockTheta ν r)`. -/
theorem hasDerivWithinAt_perGram_inv_clockA (κ : PlanarFrameKernels)
    (hCD : ∀ i : Fin 2, ContDiff ℝ 2 (κ.lamP i)) {C₁ : ℝ}
    (h1 : ∀ (i : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP i) z‖ ≤ C₁ * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    ∃ C_g D_g : ℝ, 0 ≤ C_g ∧ 1 ≤ D_g ∧
      ∀ {ν r : ℝ}, 0 < ν → 0 ≤ r →
        let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
        D_g ≤ d →
        ∀ i : Fin 2, ∃ G_inv' : Fin 2 → ℂ,
          (∀ j : Fin 2,
            HasDerivWithinAt
              (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
              (G_inv' j) (Ici r) r) ∧
          (∀ j : Fin 2,
            ‖(((clockA ν r) ^ 2 : ℝ) : ℂ) * G_inv' j‖ ≤ C_g * (1 / clockTheta ν r)) := by
  obtain ⟨D₀, hD₀⟩ :=
    perGramNear_of κ (perGramUnfold κ) (perGramTail κ) (1 / 4) (by norm_num)
  obtain ⟨C_G, hC_G0, hG_der⟩ := hasDerivAt_perGram_and_bound κ hCD h1
  set D_g : ℝ := max D₀ 1
  have hD_g1 : 1 ≤ D_g := le_max_right _ _
  refine ⟨(27 / 2) * C_G, D_g, by positivity, hD_g1, fun {ν r} hν hr hd i => ?_⟩
  set d : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd1 : 1 ≤ d := le_trans hD_g1 hd
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hd_D0 : D₀ ≤ d := le_trans (le_max_left _ _) hd
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hd_pow : d ≤ d ^ 3 := by nlinarith [sq_nonneg (d - 1)]
  have hB : ∀ p q : Fin 2, ‖perGramDeriv κ d p q‖ ≤ C_G / d := by
    intro p q
    refine (hG_der hd0 p q).2.trans ?_
    exact div_le_div_of_nonneg_left hC_G0 hd0 hd_pow
  have hinv_ex : ∀ j : Fin 2, ∃ g' : ℂ,
      HasDerivAt (fun d' => (perGram κ d')⁻¹ i j) g' d ∧ ‖g'‖ ≤ 27 * (C_G / d) :=
    fun j => hasDerivAt_matrix_inv_fin2 (by positivity) (hD₀ d hd_D0)
      (fun p q => (hG_der hd0 p q).1) hB i j
  choose g' hg'_der hg'_norm using hinv_ex
  have hcell_der := hasDerivAt_cellLen_clockA (ν ^ (-2 : ℝ)) hν hr
  refine ⟨fun j => (-(ν / (2 * clockA ν r)) * d) • g' j, fun j => ?_, fun j => ?_⟩
  · exact ((hg'_der j).scomp r hcell_der).hasDerivWithinAt
  · dsimp only
    rw [Complex.real_smul, ← mul_assoc, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ha 2),
      neg_mul, abs_neg, abs_of_pos (by positivity : 0 < ν / (2 * clockA ν r) * d)]
    have hscalar : (clockA ν r) ^ 2 * (ν / (2 * clockA ν r) * d) =
        (d / 2) * (1 / clockTheta ν r) := by
      unfold clockTheta
      have ha_ne : clockA ν r ≠ 0 := ha.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
    rw [hscalar]
    have hθ_pos : 0 < 1 / clockTheta ν r := by
      unfold clockTheta; positivity
    calc (d / 2) * (1 / clockTheta ν r) * ‖g' j‖
        ≤ (d / 2) * (1 / clockTheta ν r) * (27 * (C_G / d)) :=
          mul_le_mul_of_nonneg_left (hg'_norm j) (by positivity)
      _ = (27 / 2) * C_G * (1 / clockTheta ν r) := by
          have hd_ne : d ≠ 0 := hd0.ne'
          field_simp

/-! ## 3. Linearity of `ladLapCx`, product rule for `ladDt`, and assembly of `PerGramInvHeatSplit` -/

/-- `pdCx k` is linear on differentiable planar fields. -/
theorem pdCx_linear_comb (k : Fin 2) {f₀ f₁ : ℝ × ℝ → ℂ}
    (hf₀ : Differentiable ℝ f₀) (hf₁ : Differentiable ℝ f₁) (c₀ c₁ : ℂ) (x : ℝ × ℝ) :
    pdCx k (fun z => c₀ * f₀ z + c₁ * f₁ z) x =
      c₀ * pdCx k f₀ x + c₁ * pdCx k f₁ x := by
  unfold pdCx
  have hF : HasFDerivAt (fun z => c₀ * f₀ z + c₁ * f₁ z)
      (c₀ • fderiv ℝ f₀ x + c₁ • fderiv ℝ f₁ x) x :=
    ((hf₀ x).hasFDerivAt.const_mul c₀).add ((hf₁ x).hasFDerivAt.const_mul c₁)
  rw [hF.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- `pdCx k` of a `C²` field is differentiable. -/
theorem differentiable_pdCx (k : Fin 2) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (pdCx k f) := by
  have h1 : ContDiff ℝ 1 (pdCx k f) := by
    unfold pdCx
    exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h1.differentiable (by norm_num)

/-- `ladLapCx` is linear on `Fin 2` linear combinations of `C²` planar fields. -/
theorem ladLapCx_sum_fin2 {f : Fin 2 → ℝ × ℝ → ℂ} (hf : ∀ j : Fin 2, ContDiff ℝ 2 (f j))
    (c : Fin 2 → ℂ) (x : ℝ × ℝ) :
    ladLapCx (fun z => ∑ j : Fin 2, c j * f j z) x =
      ∑ j : Fin 2, c j * ladLapCx (f j) x := by
  simp only [Fin.sum_univ_two]
  have hd0 : Differentiable ℝ (f 0) := (hf 0).differentiable (by norm_num)
  have hd1 : Differentiable ℝ (f 1) := (hf 1).differentiable (by norm_num)
  have hpd1 : ∀ k : Fin 2,
      pdCx k (fun z => c 0 * f 0 z + c 1 * f 1 z) =
        fun z => c 0 * pdCx k (f 0) z + c 1 * pdCx k (f 1) z :=
    fun k => funext (pdCx_linear_comb k hd0 hd1 (c 0) (c 1))
  unfold ladLapCx
  rw [hpd1 0, hpd1 1,
    pdCx_linear_comb 0 (differentiable_pdCx 0 (hf 0)) (differentiable_pdCx 0 (hf 1)) (c 0) (c 1) x,
    pdCx_linear_comb 1 (differentiable_pdCx 1 (hf 0)) (differentiable_pdCx 1 (hf 1)) (c 0) (c 1) x]
  ring

/-- Product rule for `ladDt (fun s x' => physFrameLam κ ν s i x') r x`. -/
theorem ladDt_physFrameLam_eq (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2)
    (hCD : ∀ j : Fin 2, ContDiff ℝ 2 (κ.lamP j)) {C : ℝ}
    (h0 : ∀ (j : Fin 2) (z : ℝ × ℝ), ‖κ.lamP j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ (j : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {G_inv' : Fin 2 → ℂ}
    (hG_der : ∀ j : Fin 2,
      HasDerivWithinAt
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
        (G_inv' j) (Ici r) r)
    (x : ℝ × ℝ) :
    ladDt (fun s x' => physFrameLam κ ν s i x') r x =
      ∑ j : Fin 2,
        ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j *
            ladDt (fun s x' => physFrameLam0 κ ν s j x') r x +
          G_inv' j * physFrameLam0 κ ν r j x) := by
  have hterm : ∀ j : Fin 2,
      HasDerivWithinAt
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j *
          physFrameLam0 κ ν s j x)
        ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j *
            ladDt (fun s x' => physFrameLam0 κ ν s j x') r x +
          G_inv' j * physFrameLam0 κ ν r j x)
        (Ici r) r := by
    intro j
    have hLd : Differentiable ℝ (κ.lamP j) := (hCD j).differentiable (by norm_num)
    have hLam0 := hasDerivWithinAt_physFrameLam0 κ hν hr j hLd (h0 j) (h1 j) x
    rw [← ladDt_physFrameLam0_eq κ hν hr j hLd (h0 j) (h1 j) x] at hLam0
    have hmul := (hG_der j).mul hLam0
    refine hmul.congr_deriv (by ring)
  have hsum := (hterm 0).add (hterm 1)
  have hcongr : (fun s => physFrameLam κ ν s i x) =
      fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i 0 * physFrameLam0 κ ν s 0 x +
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i 1 * physFrameLam0 κ ν s 1 x := by
    funext s
    rw [physFrameLam_eq_sum_perGram_inv, Fin.sum_univ_two]
  unfold ladDt
  rw [hcongr, Fin.sum_univ_two]
  exact hsum.derivWithin (uniqueDiffWithinAt_Ici r)

/-- Moving pullback split of `movLamDualHeat κ ν r i y` given `G_inv'`. -/
theorem movLamDualHeat_split_of (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2)
    (hCD : ∀ j : Fin 2, ContDiff ℝ 2 (κ.lamP j)) {C : ℝ}
    (h0 : ∀ (j : Fin 2) (z : ℝ × ℝ), ‖κ.lamP j z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h1 : ∀ (j : Fin 2) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    (h2 : ∀ (j : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ 2 (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {G_inv' : Fin 2 → ℂ}
    (hG_der : ∀ j : Fin 2,
      HasDerivWithinAt
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
        (G_inv' j) (Ici r) r)
    (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movLamDualHeat κ ν r i y =
      ∑ j : Fin 2,
        ((perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y +
          ((((clockA ν r) ^ 2 : ℝ) : ℂ) * G_inv' j) * perLam0 κ d j y) := by
  intro d
  set a : ℝ := clockA ν r
  set x : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have ha1 : 1 ≤ a := one_le_clockA hν.le hr
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ha_ne : a ≠ 0 := ha.ne'
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa_ne : Real.sqrt a ≠ 0 := hsa.ne'
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν (-2)).ne'
  have hLam0_CD : ∀ j : Fin 2, ContDiff ℝ 2 (physFrameLam0 κ ν r j) := by
    intro j
    have heq : physFrameLam0 κ ν r j = perSum (ν ^ (-2 : ℝ)) (physAdj a (κ.lamP j)) :=
      funext (physFrameLam0_eq_perSum_physAdj κ hν hr j)
    rw [heq]
    exact contDiff_perSum_physAdj (hCD j) hc ha (h0 j) (h1 j) (h2 j)
  have hDt := ladDt_physFrameLam_eq κ hν hr i hCD h0 h1 hG_der x
  have hLap : ladLapCx (physFrameLam κ ν r i) x =
      ∑ j : Fin 2, (perGram κ d)⁻¹ i j * ladLapCx (physFrameLam0 κ ν r j) x := by
    have heq : physFrameLam κ ν r i =
        fun z => ∑ j : Fin 2, (perGram κ d)⁻¹ i j * physFrameLam0 κ ν r j z :=
      funext (physFrameLam_eq_sum_perGram_inv κ ν r i)
    rw [heq]
    exact ladLapCx_sum_fin2 hLam0_CD (fun j => (perGram κ d)⁻¹ i j) x
  have hLam0_eval : ∀ j : Fin 2, physFrameLam0 κ ν r j x = ((a : ℝ) : ℂ) * perLam0 κ d j y := by
    intro j
    unfold physFrameLam0 physAdj
    congr 2
    ext
    · exact mul_div_cancel_left₀ y.1 hsa_ne
    · exact mul_div_cancel_left₀ y.2 hsa_ne
  unfold movLamDualHeat physLamDualHeat movLam0DualHeat movingPhi
  dsimp only
  change (((a ^ (2 : ℝ) : ℝ) : ℂ) *
    (((a⁻¹ : ℝ) : ℂ) *
      (ladDt (fun r' x' => physFrameLam κ ν r' i x') r x +
        (ν : ℂ) * ladLapCx (physFrameLam κ ν r i) x))) = _
  rw [hDt, hLap, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    hLam0_eval 0, hLam0_eval 1, Real.rpow_two]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha_ne
  push_cast
  have hinv_a : (a : ℂ)⁻¹ * (a : ℂ) = 1 := inv_mul_cancel₀ haC
  linear_combination
    (((a : ℂ) ^ 2 * G_inv' 0 * perLam0 κ d 0 y + (a : ℂ) ^ 2 * G_inv' 1 * perLam0 κ d 1 y) *
      hinv_a)

/-- Conditional proof of `PerGramInvHeatSplit κ` (`PartIII-a:T21/c5/3/1/2`) from
`SeedLamPJet2Decay κ`. -/
theorem perGramInvHeatSplit_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet2Decay κ) :
    PerGramInvHeatSplit κ := by
  intro hκ
  obtain ⟨hCD, C, _hC0, h0, h1, h2⟩ := seedLamP_jet2_bounds_of κ hJet hκ
  obtain ⟨C_g, D_g, hC_g0, hD_g1, hG⟩ := hasDerivWithinAt_perGram_inv_clockA κ hCD h1
  refine ⟨C_g, D_g, hC_g0, hD_g1, fun {ν r} hν hr hd i => ?_⟩
  obtain ⟨G_inv', hG_der, hG_bound⟩ := hG hν hr hd i
  have ht : ∀ j : Fin 2,
      (∀ z : ℝ × ℝ, ‖κ.lamP j z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP j) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (κ.lamP j) z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ))) :=
    fun j => translate_jet2_bounds (h0 j) (h1 j) (h2 j)
  refine ⟨fun j => (((clockA ν r) ^ 2 : ℝ) : ℂ) * G_inv' j, hG_bound, fun y => ?_⟩
  exact movLamDualHeat_split_of κ hν hr i hCD
    (fun j => (ht j).1) (fun j => (ht j).2.1) (fun j => (ht j).2.2) hG_der y

end ComplCouplingHeat

/-- Top-level conditional proof of `PerGramInvHeatSplit κ` (`PartIII-a:T21/c5/3/1/2`) from
`SeedLamPJet2Decay κ`. -/
theorem perGramInvHeatSplit_of (κ : PlanarFrameKernels) (hJet : SeedLamPJet2Decay κ) :
    PerGramInvHeatSplit κ :=
  ComplCouplingHeat.perGramInvHeatSplit_of κ hJet

/-- **`PartIII-a:T21/c5/3/1/2`** (SP 2901-2912, 2990-2997): differentiating
`physFrameLam = G(d(r))⁻¹ physFrameLam0` splits `movLamDualHeat κ ν r i` into the Gram-normalised
sum of `movLam0DualHeat κ ν r j` plus `gDz j * perLam0 κ d j` with `‖gDz j‖ ≤ C_g / clockTheta ν r`.
The jet decay input is `seedLamPJet2Decay_all`. -/
theorem perGramInvHeatSplit (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PerGramInvHeatSplit κ :=
  perGramInvHeatSplit_of κ (seedLamPJet2Decay_all κ)

end UnforcedLeray.Short.IIIa
