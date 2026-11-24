import UnforcedLeray.Cons.C08PhysicalMode
import UnforcedLeray.Loc.Hyp.ModeIdentification.Slices
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Units.B0005.Bridge.Weak

/-!
# Interface I10, part 2: integrability of the coupling pairing `τ ↦ weakCoupling V b ψ τ`

Helper for `Short/Interface/Leaf2_Integrability.lean` (task `Interface:I10`, the last clause of
`ModeSolutionIntegrability`). For a continuous background `V` with `‖V‖ ≤ C` and `b ∈ 𝒴_{2,div}`,
and a similarity test `ψ`, the phase function `τ ↦ weakCoupling V b ψ τ` is integrable on `ℝ`.

* Bound: at almost every phase, `|weakCoupling(τ)| ≤ ∑_j ‖col_j(τ)‖₂ ‖∂_jψ(τ)‖₂` (Cauchy–Schwarz
  in `L²`, the projection has norm at most one), with `‖col_j(τ)‖₂ ≤ 2C‖b(τ)‖₂`
  (`norm_toL2_symTensorColumns_le`), and `‖∂_jψ(τ)‖₂ ≤ M_j`, vanishing for `τ ∉ [-R, R]`
  (`exists_slice_bound`, `slice_norm_le_zero`). The majorant `τ ↦ 2CM ‖b(τ)‖₂ 1_{[-R,R]}(τ)` is
  integrable by periodicity of `b` (`ModeId.Y2.integrableOn`).
* Measurability: the projected test paths `τ ↦ 𝔓∂_jψ(τ)` have jointly measurable representatives
  (`exists_joint_projection`), so `τ ↦ ∫_y ⟨col_j(τ, y), F_j(τ, y)⟩ dy` is measurable by Fubini
  (`AEStronglyMeasurable.integral_prod_right'`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.Interface.Leaf2_Integrability

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-! ## 1. Bounds for the columns of `U ⊗ w + w ⊗ U` -/

/-- Pointwise: the column `j` of `U ⊗ w + w ⊗ U` is at most `2C` times `|w|`. -/
theorem norm_symTensorColumns_le {u v : SpatialField} {C : ℝ} (hu : ∀ y, ‖u y‖ ≤ C)
    (j : Fin 3) (y : Space) :
    ‖symTensorColumns u v j y‖ ≤ 2 * C * ‖v y‖ := by
  show ‖(v y) j • u y + (u y) j • v y‖ ≤ 2 * C * ‖v y‖
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have h1 : ‖(v y) j‖ ≤ ‖v y‖ := PiLp.norm_apply_le (v y) j
  have h2 : ‖(u y) j‖ ≤ C := (PiLp.norm_apply_le (u y) j).trans (hu y)
  have h3 : ‖(v y) j‖ * ‖u y‖ ≤ ‖v y‖ * C :=
    mul_le_mul h1 (hu y) (norm_nonneg _) (norm_nonneg _)
  have h4 : ‖(u y) j‖ * ‖v y‖ ≤ C * ‖v y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  nlinarith

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem norm_sq_toL2 {f : SpatialField} (hf : MemLp f 2 volume) :
    ‖toL2 f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 := by
  have hT : toL2 f = hf.toLp f := by
    unfold toL2
    rw [dif_pos hf]
  rw [hT, ← real_inner_self_eq_norm_sq (hf.toLp f), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

/-- The columns of `U ⊗ w + w ⊗ U` have `L²` norm at most `2C` times that of `w`. -/
theorem norm_toL2_symTensorColumns_le {u v : SpatialField} {C : ℝ} (hu : Continuous u)
    (hC : ∀ y, ‖u y‖ ≤ C) (hv : MemLp v 2 volume) (j : Fin 3) :
    ‖toL2 (symTensorColumns u v j)‖ ≤ 2 * C * ‖toL2 v‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hcol : MemLp (symTensorColumns u v j) 2 volume := columnsL2_symTensor hu hC hv j
  have hint : ∫ y, ‖symTensorColumns u v j y‖ ^ 2 ≤ ∫ y, (2 * C) ^ 2 * ‖v y‖ ^ 2 := by
    refine integral_mono hcol.norm.integrable_sq ((hv.norm.integrable_sq).const_mul _)
      (fun y => ?_)
    have h := norm_symTensorColumns_le (v := v) hC j y
    calc ‖symTensorColumns u v j y‖ ^ 2 ≤ (2 * C * ‖v y‖) ^ 2 := by gcongr
      _ = (2 * C) ^ 2 * ‖v y‖ ^ 2 := by ring
  have e : (2 * C * ‖toL2 v‖) ^ 2 = ∫ y, (2 * C) ^ 2 * ‖v y‖ ^ 2 := by
    rw [integral_const_mul, mul_pow, norm_sq_toL2 hv]
  have hsq : ‖toL2 (symTensorColumns u v j)‖ ^ 2 ≤ (2 * C * ‖toL2 v‖) ^ 2 := by
    rw [norm_sq_toL2 hcol, e]
    exact hint
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hC0) (norm_nonneg _)) two_ne_zero).mp hsq

/-! ## 2. A uniform `L²` bound for functions supported in a ball -/

/-- An `L²` bound for a function vanishing off a closed ball and bounded by `η`. -/
theorem eLpNorm_two_le_of_ball (g : Space → Space) (R η : ℝ)
    (hsupp : ∀ y, R < ‖y‖ → g y = 0) (hb : ∀ y, ‖g y‖ ≤ η) :
    eLpNorm g 2 volume ≤
      volume (closedBall (0 : Space) R) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal η := by
  have hind : (closedBall (0 : Space) R).indicator g = g := by
    funext y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · simp [hy]
    · have : R < ‖y‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hy
      simp [hy, hsupp y this]
  rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (closedBall (0 : Space) R)) (p := 2)
    (f := g) (C := η) (ae_restrict_of_forall_mem measurableSet_closedBall fun y _ => hb y)
  simpa [Measure.restrict_apply_univ] using h

/-- The `L²` norm of a function vanishing off a closed ball and bounded by `η`. -/
theorem norm_toL2_le_of_ball (g : Space → Space) (R η : ℝ)
    (hsupp : ∀ y, R < ‖y‖ → g y = 0) (hb : ∀ y, ‖g y‖ ≤ η) :
    ‖toL2 g‖ ≤ (volume (closedBall (0 : Space) R) ^ (2 : ℝ≥0∞).toReal⁻¹ *
      ENNReal.ofReal η).toReal := by
  by_cases hg : MemLp g 2 volume
  · have hT : toL2 g = hg.toLp g := by
      unfold toL2
      rw [dif_pos hg]
    have hfin : volume (closedBall (0 : Space) R) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal η ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
          measure_closedBall_lt_top.ne)
        ENNReal.ofReal_ne_top
    rw [hT, Lp.norm_toLp]
    exact ENNReal.toReal_mono hfin (eLpNorm_two_le_of_ball g R η hsupp hb)
  · have hT : toL2 g = 0 := by
      unfold toL2
      rw [dif_neg hg]
    rw [hT, norm_zero]
    exact ENNReal.toReal_nonneg

/-! ## 3. A jointly measurable representative of a projected `L²` path -/

/-- Joint representative: for a square integrable `D` on `ℝ × ℝ³`, the phase path of the Leray
projections of the slices `D(τ, ·)` has a jointly strongly measurable representative. -/
theorem exists_joint_projection {D : ℝ × Space → Space}
    (hD : MemLp D 2 (volume : Measure (ℝ × Space))) :
    ∃ F : ℝ × Space → Space, StronglyMeasurable F ∧
      ∀ᵐ τ : ℝ, (fun y => F (τ, y)) =ᵐ[volume]
        (UnforcedLeray.Leray.projection (toL2 (fun y => D (τ, y))) : Space → Space) := by
  have hD' : MemLp D 2 ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact hD
  obtain ⟨hpm, -⟩ := BochnerTime.stronglyMeasurable_toPath_Lq (q := 2)
    (ν := (volume : Measure ℝ)) (μ := (volume : Measure Space)) hD'
  set u : ℝ → L2Space := fun t => UnforcedLeray.Leray.projection
    (BochnerTime.toPathLq 2 volume D t) with hudef
  have hu : AEStronglyMeasurable u volume :=
    UnforcedLeray.Leray.projection.continuous.comp_aestronglyMeasurable hpm
  obtain ⟨F, hFm, hF⟩ :=
    Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hu.stronglyMeasurable_mk
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hu.ae_eq_mk] with t ht
  have h1 := hF t
  rw [← ht] at h1
  exact h1

/-! ## 4. The derivative slices `∂_jψ(τ, ·)` of a similarity test -/

/-- The slice derivative is the `j`-th partial of the spacetime test. -/
theorem testPartial_slice_eq {ψ : SpaceTime → Space} (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3)
    (τ : ℝ) (y : Space) :
    Blueprint.testPartial (Blueprint.slice ψ τ) j y =
      UnforcedLeray.PhaseSpace.dy j ψ (τ, y) := by
  show fderiv ℝ (fun y' => ψ (τ, y')) y (coordinateVector j) =
    fderiv ℝ ψ (τ, y) (0, coordinateVector j)
  rw [B0005.fderiv_slice_space (hψ.differentiable (by simp) (τ, y))]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The `j`-th spacetime derivative of a similarity test is continuous and compactly supported. -/
theorem dy_continuous_hasCompactSupport {ψ : SpaceTime → Space}
    (hψ : Blueprint.IsSimilarityTest ψ) (j : Fin 3) :
    Continuous (UnforcedLeray.PhaseSpace.dy j ψ) ∧
      HasCompactSupport (UnforcedLeray.PhaseSpace.dy j ψ) :=
  ⟨(B0005.contDiff_dy' hψ.smooth j).continuous,
    hψ.compact.fderiv_apply ℝ (0, coordinateVector j)⟩

/-- The `j`-th spacetime derivative of a similarity test vanishes outside a ball, uniformly. -/
theorem dy_bounded_support {ψ : SpaceTime → Space} (hψ : Blueprint.IsSimilarityTest ψ)
    (j : Fin 3) :
    ∃ R : ℝ, ∀ τ y, R < ‖y‖ → UnforcedLeray.PhaseSpace.dy j ψ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ :=
    ((B0005.IsSimilarityTest.isPhaseTest hψ).fderiv_apply (0, coordinateVector j)).bounded_support
  exact ⟨R, fun τ y hy => hR τ y hy⟩

/-- A uniform bound on the `L²` norms of the derivative slices `∂_jψ(τ, ·)`. -/
theorem exists_slice_bound {ψ : SpaceTime → Space} (hψ : Blueprint.IsSimilarityTest ψ)
    (j : Fin 3) :
    ∃ M : ℝ, ∀ τ, ‖toL2 (Blueprint.testPartial (Blueprint.slice ψ τ) j)‖ ≤ M := by
  obtain ⟨η, hη⟩ := (dy_continuous_hasCompactSupport hψ j).1.bounded_above_of_compact_support
    (dy_continuous_hasCompactSupport hψ j).2
  obtain ⟨R, hR⟩ := dy_bounded_support hψ j
  refine ⟨(volume (closedBall (0 : Space) R) ^ (2 : ℝ≥0∞).toReal⁻¹ *
    ENNReal.ofReal η).toReal, fun τ => ?_⟩
  have hfun : Blueprint.testPartial (Blueprint.slice ψ τ) j =
      fun y => UnforcedLeray.PhaseSpace.dy j ψ (τ, y) := by
    funext y
    exact testPartial_slice_eq hψ.smooth j τ y
  rw [hfun]
  exact norm_toL2_le_of_ball _ R η (fun y hy => hR τ y hy) (fun y => hη (τ, y))

/-- Outside the phase window the derivative slice vanishes, so its `L²` norm is zero. -/
theorem slice_norm_le_zero {ψ : SpaceTime → Space} (hψ : Blueprint.IsSimilarityTest ψ) {R : ℝ}
    (hRT : UnforcedLeray.PhaseTrace.TimeSupp (-R) R ψ) (j : Fin 3) {τ : ℝ}
    (hτ : τ ∉ Icc (-R) R) :
    ‖toL2 (Blueprint.testPartial (Blueprint.slice ψ τ) j)‖ ≤ 0 := by
  have hfun : Blueprint.testPartial (Blueprint.slice ψ τ) j = fun _ => (0 : Space) := by
    funext y
    rw [testPartial_slice_eq hψ.smooth j τ y]
    exact B0005.timeSupp_dy hRT j τ y hτ
  rw [hfun]
  have h := norm_toL2_le_of_ball (fun _ : Space => (0 : Space)) 0 0 (fun _ _ => rfl)
    (fun y => by simp)
  simpa using h

/-! ## 5. The Leray pairing and the integrability of the coupling -/

/-- The Leray pairing is bounded by the sum of the products of the `L²` norms. -/
theorem norm_lerayDivPairing_le (col : Fin 3 → SpatialField) (φ : Space → Space) :
    ‖lerayDivPairing col φ‖ ≤ ∑ j : Fin 3, ‖toL2 (col j)‖ * ‖toL2 (Blueprint.testPartial φ j)‖ := by
  unfold lerayDivPairing
  rw [norm_neg, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (UnforcedLeray.Leray.norm_projection_apply_le _) (norm_nonneg _)

end UnforcedLeray.Short.Interface.Leaf2_Integrability
