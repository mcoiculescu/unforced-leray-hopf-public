import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2
import UnforcedLeray.Lib.HeatCylinder.SmoothBounds
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part III-a, `PartIII-a:T21/3/2/2/org`: the Gaussian smoothing `P_θ ψ` of a cylinder test

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the
weighted heat semigroup `S₀` and its divergence response `S` on the cylinder `C_c`, tested by the
dual heat flow of a cylinder test).

`cylHeatSmooth c θ ψ` is the cylinder heat flow `e^{θΔ} ψ` of a test `ψ` on `C_c`: since `ψ` is
represented by its `c`-periodic lift, this is the planar Gaussian convolution
`x ↦ ∫_{ℝ²} G_θ(w) ψ(x - w) dw` with B0284's kernel `heatKernel2 θ` (the same kernel as in the
response `S(θ) = -e^{θΔ} div`, `B0296.heatDiv`). For `θ ≤ 0` it returns `ψ`.

Gaussian convolution does not preserve the bounded `η`-support of `IsCylTest`; the smoothed test is
smooth, `c`-periodic and has every partial-derivative word globally bounded (`IsCylSmoothBdd`).
This file proves the spatial statements: bounds, linearity, `∂_j P_θ = P_θ ∂_j`,
`P_θ Δ = Δ P_θ`, periodicity, smoothness, `IsCylSmoothBdd`, and the symmetry of mixed partials of
smooth functions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.B0284 (heatKernel2)

/-- The cylinder heat flow `P_θ ψ = e^{θΔ} ψ` of a (periodic lift of a) cylinder test, for
`θ > 0` the planar Gaussian convolution with `heatKernel2 θ`; `P_θ ψ = ψ` for `θ ≤ 0`
(source lines 2819-2836). The period `c` is not used: the lift of `ψ` is already `c`-periodic. -/
def cylHeatSmooth (_c θ : ℝ) (ψ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun x => if 0 < θ then ∫ w : ℝ × ℝ, heatKernel2 θ w * ψ (x - w) else ψ x

theorem cylHeatSmooth_apply_of_pos {c θ : ℝ} (hθ : 0 < θ) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    cylHeatSmooth c θ ψ x = ∫ w : ℝ × ℝ, heatKernel2 θ w * ψ (x - w) := by
  simp [cylHeatSmooth, hθ]

theorem cylHeatSmooth_eq_of_pos {c θ : ℝ} (hθ : 0 < θ) (ψ : ℝ × ℝ → ℝ) :
    cylHeatSmooth c θ ψ = fun x => ∫ w : ℝ × ℝ, heatKernel2 θ w * ψ (x - w) := by
  funext x
  exact cylHeatSmooth_apply_of_pos hθ ψ x

theorem cylHeatSmooth_of_nonpos {c θ : ℝ} (hθ : θ ≤ 0) (ψ : ℝ × ℝ → ℝ) :
    cylHeatSmooth c θ ψ = ψ := by
  funext x
  simp [cylHeatSmooth, not_lt.mpr hθ]

/-- `P_0 ψ = ψ`. -/
theorem cylHeatSmooth_zero (c : ℝ) (ψ : ℝ × ℝ → ℝ) : cylHeatSmooth c 0 ψ = ψ :=
  cylHeatSmooth_of_nonpos le_rfl ψ

/-! ### Elementary bounds -/

theorem continuous_heatKernel2' (θ : ℝ) : Continuous (heatKernel2 θ) := by
  unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  fun_prop

theorem isCylSmooth_of_isCylTest {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    UnforcedLeray.Sob.IsCylSmooth c ψ := by
  refine ⟨hψ.smooth, fun z => ?_, hψ.band⟩
  have hz : z + ((c, 0) : ℝ × ℝ) = (z.1 + c, z.2) := by ext <;> simp
  rw [hz]
  exact hψ.periodic z

/-- A cylinder test is globally bounded (`c > 0`). -/
theorem cylTest_exists_bound {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |ψ x| ≤ M := by
  obtain ⟨M, hM, h⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hc (isCylSmooth_of_isCylTest hψ)
  exact ⟨M, hM, fun x => by simpa [Real.norm_eq_abs] using h x⟩

/-- The derivative of a cylinder test is globally bounded (`c > 0`). -/
theorem cylTest_exists_fderiv_bound {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ ψ x‖ ≤ M :=
  UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth hc
    (isCylSmooth_of_isCylTest hψ)

theorem integrable_heatKernel2_mul {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (x : ℝ × ℝ) :
    Integrable (fun w : ℝ × ℝ => heatKernel2 θ w * g (x - w)) := by
  refine ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M).mono' ?_ ?_
  · exact ((continuous_heatKernel2' θ).mul
      (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [] with w
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)

/-- The Gaussian smoothing is a sup-norm contraction. -/
theorem abs_cylHeatSmooth_le {c θ : ℝ} {g : ℝ × ℝ → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (x : ℝ × ℝ) : |cylHeatSmooth c θ g x| ≤ M := by
  by_cases hθ : 0 < θ
  · rw [cylHeatSmooth_apply_of_pos hθ]
    have h := norm_integral_le_of_norm_le
      ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M)
      (Eventually.of_forall fun w => by
        show ‖heatKernel2 θ w * g (x - w)‖ ≤ heatKernel2 θ w * M
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
        exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w))
    rw [integral_mul_const, UnforcedLeray.B0284.integral_heatKernel2 hθ, one_mul,
      Real.norm_eq_abs] at h
    exact h
  · rw [cylHeatSmooth_of_nonpos (not_lt.mp hθ)]
    exact hM x

theorem cylHeatSmooth_add {c θ : ℝ} {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {Mf Mg : ℝ} (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg) :
    cylHeatSmooth c θ (fun x => f x + g x) =
      fun x => cylHeatSmooth c θ f x + cylHeatSmooth c θ g x := by
  funext x
  by_cases hθ : 0 < θ
  · rw [cylHeatSmooth_apply_of_pos hθ, cylHeatSmooth_apply_of_pos hθ,
      cylHeatSmooth_apply_of_pos hθ, ← integral_add (integrable_heatKernel2_mul hθ hf hMf x)
        (integrable_heatKernel2_mul hθ hg hMg x)]
    congr 1
    funext w
    ring
  · simp only [cylHeatSmooth_of_nonpos (not_lt.mp hθ)]

/-- `P_θ` preserves `c`-periodicity in `q`. -/
theorem cylHeatSmooth_periodic {c θ : ℝ} {ψ : ℝ × ℝ → ℝ}
    (hψ : ∀ x : ℝ × ℝ, ψ (x.1 + c, x.2) = ψ x) (x : ℝ × ℝ) :
    cylHeatSmooth c θ ψ (x.1 + c, x.2) = cylHeatSmooth c θ ψ x := by
  by_cases hθ : 0 < θ
  · rw [cylHeatSmooth_apply_of_pos hθ, cylHeatSmooth_apply_of_pos hθ]
    congr 1
    funext w
    have hw : ((x.1 + c, x.2) : ℝ × ℝ) - w = ((x - w).1 + c, (x - w).2) := by
      ext <;> simp <;> ring
    rw [hw, hψ]
  · simp only [cylHeatSmooth_of_nonpos (not_lt.mp hθ)]
    exact hψ x

/-! ### Spatial derivatives -/

/-- Fréchet differentiation under the scalar Gaussian convolution. -/
theorem hasFDerivAt_gaussConv {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {M₀ M₁ : ℝ} (hM₀ : ∀ x, |g x| ≤ M₀) (hM₁ : ∀ x, ‖fderiv ℝ g x‖ ≤ M₁) (z : ℝ × ℝ) :
    HasFDerivAt (fun x => ∫ w : ℝ × ℝ, heatKernel2 θ w * g (x - w))
      (∫ w : ℝ × ℝ, heatKernel2 θ w • fderiv ℝ g (z - w)) z := by
  let F : ℝ × ℝ → ℝ × ℝ → ℝ := fun z' w => heatKernel2 θ w * g (z' - w)
  let F' : ℝ × ℝ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z' w =>
    heatKernel2 θ w • fderiv ℝ g (z' - w)
  have hkernel : Integrable (heatKernel2 θ) := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hK := continuous_heatKernel2' θ
  have hFmeas : ∀ᶠ z' : ℝ × ℝ in 𝓝 z, AEStronglyMeasurable (F z') volume :=
    Eventually.of_forall fun z' =>
      (hK.mul (hg.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hFint : Integrable (F z) volume := integrable_heatKernel2_mul hθ hg.continuous hM₀ z
  have hFprimeMeas : AEStronglyMeasurable (F' z) volume := by
    have hder : Continuous (fun w : ℝ × ℝ => fderiv ℝ g (z - w)) :=
      (hg.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
    exact (hK.smul hder).aestronglyMeasurable
  have hbound : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ z' ∈ Metric.ball z 1,
      ‖F' z' w‖ ≤ heatKernel2 θ w * M₁ := by
    filter_upwards [] with w
    intro z' _
    show ‖heatKernel2 θ w • fderiv ℝ g (z' - w)‖ ≤ heatKernel2 θ w * M₁
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (hM₁ _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hdiff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ z' ∈ Metric.ball z 1,
      HasFDerivAt (F · w) (F' z' w) z' := by
    filter_upwards [] with w
    intro z' _
    have hinput : HasFDerivAt (fun y : ℝ × ℝ => y - w)
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)) z' := (hasFDerivAt_id z').sub_const w
    have hgd : HasFDerivAt g (fderiv ℝ g (z' - w)) (z' - w) :=
      ((hg.differentiable one_ne_zero) (z' - w)).hasFDerivAt
    have hcomp := (hgd.comp z' hinput).const_mul (heatKernel2 θ w)
    simpa [F, F'] using hcomp
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball z 1) (x₀ := z) (μ := (volume : Measure (ℝ × ℝ)))
    (F := F) (F' := F') (bound := fun w => heatKernel2 θ w * M₁)
    (Metric.ball_mem_nhds z one_pos) hFmeas hFint hFprimeMeas hbound
    (hkernel.mul_const M₁) hdiff
  exact hparam

/-- `∂_j P_θ g = P_θ ∂_j g` pointwise, for `g` with bounded first derivatives (`θ > 0`). -/
theorem pd_gaussConv {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {M₀ M₁ : ℝ} (hM₀ : ∀ x, |g x| ≤ M₀) (hM₁ : ∀ x, ‖fderiv ℝ g x‖ ≤ M₁) (j : Fin 2)
    (z : ℝ × ℝ) :
    B0579.pd j (fun x => ∫ w : ℝ × ℝ, heatKernel2 θ w * g (x - w)) z =
      ∫ w : ℝ × ℝ, heatKernel2 θ w * B0579.pd j g (z - w) := by
  have hfd := hasFDerivAt_gaussConv hθ hg hM₀ hM₁ z
  have hK := continuous_heatKernel2' θ
  have hJint : Integrable (fun w : ℝ × ℝ => heatKernel2 θ w • fderiv ℝ g (z - w)) := by
    refine ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M₁).mono' ?_ ?_
    · exact (hK.smul ((hg.continuous_fderiv one_ne_zero).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    · filter_upwards [] with w
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
      exact mul_le_mul_of_nonneg_left (hM₁ _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  simp only [B0579.pd]
  rw [hfd.fderiv, ContinuousLinearMap.integral_apply hJint]
  rfl

/-- `∂_j P_θ ψ = P_θ ∂_j ψ` for a cylinder test `ψ` (every `θ`). -/
theorem pd_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) (j : Fin 2) :
    B0579.pd j (cylHeatSmooth c θ ψ) = cylHeatSmooth c θ (B0579.pd j ψ) := by
  by_cases hθ : 0 < θ
  · obtain ⟨M₀, _, hM₀⟩ := cylTest_exists_bound hc hψ
    obtain ⟨M₁, _, hM₁⟩ := cylTest_exists_fderiv_bound hc hψ
    funext z
    rw [cylHeatSmooth_eq_of_pos hθ ψ, cylHeatSmooth_apply_of_pos hθ]
    exact pd_gaussConv hθ (hψ.smooth.of_le (by simp)) hM₀ hM₁ j z
  · simp only [cylHeatSmooth_of_nonpos (not_lt.mp hθ)]

theorem differentiable_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : Differentiable ℝ (cylHeatSmooth c θ ψ) := by
  by_cases hθ : 0 < θ
  · obtain ⟨M₀, _, hM₀⟩ := cylTest_exists_bound hc hψ
    obtain ⟨M₁, _, hM₁⟩ := cylTest_exists_fderiv_bound hc hψ
    rw [cylHeatSmooth_eq_of_pos hθ ψ]
    exact fun z => (hasFDerivAt_gaussConv hθ (hψ.smooth.of_le (by simp)) hM₀ hM₁ z).differentiableAt
  · rw [cylHeatSmooth_of_nonpos (not_lt.mp hθ)]
    exact hψ.differentiable

theorem continuous_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : Continuous (cylHeatSmooth c θ ψ) :=
  (differentiable_cylHeatSmooth hc hψ).continuous

/-- `P_θ Δ ψ = Δ P_θ ψ` for a cylinder test `ψ`. -/
theorem cylHeatSmooth_lapP {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : cylHeatSmooth c θ (lapP ψ) = lapP (cylHeatSmooth c θ ψ) := by
  have h0 := (hψ.pd 0).pd 0
  have h1 := (hψ.pd 1).pd 1
  obtain ⟨M₀, _, hM₀⟩ := cylTest_exists_bound hc h0
  obtain ⟨M₁, _, hM₁⟩ := cylTest_exists_bound hc h1
  have hlap : lapP ψ = fun x => B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x := rfl
  rw [hlap, cylHeatSmooth_add h0.continuous h1.continuous hM₀ hM₁]
  funext x
  simp only [lapP]
  rw [pd_cylHeatSmooth hc hψ 0, pd_cylHeatSmooth hc (hψ.pd 0) 0, pd_cylHeatSmooth hc hψ 1,
    pd_cylHeatSmooth hc (hψ.pd 1) 1]

/-- Every derivative of a function on the plane in terms of its two partials. -/
theorem fderiv_eq_pd (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    fderiv ℝ f x = B0579.pd 0 f x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      B0579.pd 1 f x • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨a, b⟩ := v
  have hv : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp [B0579.pd, B0579.dir]
  ring

/-- `P_θ ψ` is smooth. -/
theorem contDiff_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : ContDiff ℝ ∞ (cylHeatSmooth c θ ψ) := by
  have key : ∀ n : ℕ, ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ContDiff ℝ n (cylHeatSmooth c θ ψ) := by
    intro n
    induction n with
    | zero =>
        intro ψ hψ
        exact contDiff_zero.2 (continuous_cylHeatSmooth hc hψ)
    | succ n ih =>
        intro ψ hψ
        rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
        refine ⟨differentiable_cylHeatSmooth hc hψ, fun h => absurd h (by simp), ?_⟩
        have hfd : fderiv ℝ (cylHeatSmooth c θ ψ) = fun x =>
            cylHeatSmooth c θ (B0579.pd 0 ψ) x • ContinuousLinearMap.fst ℝ ℝ ℝ +
              cylHeatSmooth c θ (B0579.pd 1 ψ) x • ContinuousLinearMap.snd ℝ ℝ ℝ := by
          funext x
          rw [fderiv_eq_pd, pd_cylHeatSmooth hc hψ 0, pd_cylHeatSmooth hc hψ 1]
        rw [hfd]
        exact ((ih _ (hψ.pd 0)).smul contDiff_const).add ((ih _ (hψ.pd 1)).smul contDiff_const)
  exact contDiff_infty.2 fun n => key n ψ hψ

/-! ### Derivative words and the regularity class of `P_θ ψ` -/

/-- The partial-derivative word `∂_{j₁} ⋯ ∂_{j_k} φ`. -/
def pdWord : List (Fin 2) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], φ => φ
  | j :: js, φ => B0579.pd j (pdWord js φ)

theorem cylTest_pdWord {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∀ js : List (Fin 2), B0579.IsCylTest c (pdWord js ψ)
  | [] => hψ
  | j :: js => (cylTest_pdWord hψ js).pd j

theorem pdWord_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    ∀ js : List (Fin 2), pdWord js (cylHeatSmooth c θ ψ) = cylHeatSmooth c θ (pdWord js ψ)
  | [] => rfl
  | j :: js => by
      show B0579.pd j (pdWord js (cylHeatSmooth c θ ψ)) = _
      rw [pdWord_cylHeatSmooth hc hψ js, pd_cylHeatSmooth hc (cylTest_pdWord hψ js) j]
      rfl

/-- The regularity class of the smoothed tests: smooth, `c`-periodic in `q`, and every
partial-derivative word globally bounded. Unlike `B0579.IsCylTest` it has no bounded
`η`-support (Gaussian convolution of a nonzero test is never `η`-compactly supported). -/
structure IsCylSmoothBdd (c : ℝ) (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x
  bdd : ∀ js : List (Fin 2), ∃ M : ℝ, ∀ x, |pdWord js φ x| ≤ M

/-- The smoothed test `P_θ ψ` of a cylinder test lies in `IsCylSmoothBdd` (every `θ`). -/
theorem isCylSmoothBdd_cylHeatSmooth {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : IsCylSmoothBdd c (cylHeatSmooth c θ ψ) where
  smooth := contDiff_cylHeatSmooth hc hψ
  periodic := cylHeatSmooth_periodic hψ.periodic
  bdd js := by
    obtain ⟨M, _, hM⟩ := cylTest_exists_bound hc (cylTest_pdWord hψ js)
    refine ⟨M, fun x => ?_⟩
    rw [pdWord_cylHeatSmooth hc hψ js]
    exact abs_cylHeatSmooth_le hM x

/-- A cylinder test lies in `IsCylSmoothBdd`. -/
theorem IsCylTest.isCylSmoothBdd {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) : IsCylSmoothBdd c ψ := by
  simpa [cylHeatSmooth_zero] using isCylSmoothBdd_cylHeatSmooth (θ := 0) hc hψ

/-- Uniform-in-age bound for the derivative words of `P_θ ψ`. -/
theorem exists_bound_pdWord_cylHeatSmooth {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) (js : List (Fin 2)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ x, |pdWord js (cylHeatSmooth c θ ψ) x| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := cylTest_exists_bound hc (cylTest_pdWord hψ js)
  refine ⟨M, hM0, fun θ x => ?_⟩
  rw [pdWord_cylHeatSmooth hc hψ js]
  exact abs_cylHeatSmooth_le hM x

/-! ### Symmetry of mixed partials -/

theorem pd_pd_eq_fderiv_fderiv {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd i (B0579.pd j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir i) (B0579.dir j) := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ f y (B0579.dir j)) x (B0579.dir i) = _
  rw [fderiv_clm_apply (hdf x) (differentiableAt_const _)]
  simp

/-- `∂_i ∂_j f = ∂_j ∂_i f` for a `C²` function. -/
theorem pd_comm {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) :
    B0579.pd i (B0579.pd j f) = B0579.pd j (B0579.pd i f) := by
  funext x
  rw [pd_pd_eq_fderiv_fderiv hf, pd_pd_eq_fderiv_fderiv hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem pd_add' {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  simp only [B0579.pd]
  rw [fderiv_fun_add (hf x) (hg x)]
  rfl

/-- `∂_i Δ φ = Δ ∂_i φ` for a cylinder test. -/
theorem pd_lapP {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (i : Fin 2) :
    B0579.pd i (lapP φ) = lapP (B0579.pd i φ) := by
  have h2 : ∀ {g : ℝ × ℝ → ℝ}, B0579.IsCylTest c g → ContDiff ℝ 2 g :=
    fun hg => hg.smooth.of_le (by simp)
  funext x
  have hlap : lapP φ = fun y => B0579.pd 0 (B0579.pd 0 φ) y + B0579.pd 1 (B0579.pd 1 φ) y := rfl
  rw [hlap, pd_add' ((hφ.pd 0).pd 0).differentiable ((hφ.pd 1).pd 1).differentiable]
  simp only [lapP]
  rw [pd_comm (h2 (hφ.pd 0)) i 0, pd_comm (h2 hφ) i 0, pd_comm (h2 (hφ.pd 1)) i 1,
    pd_comm (h2 hφ) i 1]

/-- The Laplacian of a cylinder test is a cylinder test. -/
theorem cylTest_lapP {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (lapP φ) :=
  cylTest_add' ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)

end UnforcedLeray.Short.IIIa.Exist
