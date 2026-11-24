import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.IBP
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Part III-a, `PartIII-a:T21/3/2/2/org`: the age dependence of `P_θ ψ`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

For a cylinder test `ψ`:
* `∂_θ P_θ ψ = Δ P_θ ψ` for `θ > 0` (B0284's kernel solves the heat equation,
  `heatKernel2AgeDerivative`, plus two Gaussian integrations by parts);
* the parabolic rescaling `P_θ g(x) = ∫ G_1(v) g(x - √θ v) dv`, valid for every `θ` (for `θ ≤ 0`
  both sides are `g x`), which gives joint continuity of `(θ, x) ↦ P_θ g(x)` on `ℝ × ℝ²`;
* the Duhamel identity `P_θ φ = φ + ∫_0^θ P_η Δφ dη` (`θ ≥ 0`), also for first derivatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.B0284 (heatKernel2)

/-! ### Age derivative -/

/-- Differentiation of the scalar Gaussian convolution in its positive age. -/
theorem hasDerivAt_gaussConv_age {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |g x| ≤ M) (z : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => ∫ w : ℝ × ℝ, heatKernel2 s w * g (z - w))
      (∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * g (z - w)) θ := by
  let F : ℝ → ℝ × ℝ → ℝ := fun s w => heatKernel2 s w * g (z - w)
  let F' : ℝ → ℝ × ℝ → ℝ := fun s w =>
    UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * g (z - w)
  have hball : Set.Ioo (θ / 2) (2 * θ) ∈ 𝓝 θ := Ioo_mem_nhds (by linarith) (by linarith)
  have hwide : Integrable
      (fun w : ℝ × ℝ => (1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) :=
    UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2 (by positivity)
  have hFmeas : ∀ᶠ s : ℝ in 𝓝 θ, AEStronglyMeasurable (F s) volume :=
    Eventually.of_forall fun s =>
      ((continuous_heatKernel2' s).mul
        (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hFint : Integrable (F θ) volume := integrable_heatKernel2_mul hθ hg hM z
  have hFprimeMeas : AEStronglyMeasurable (F' θ) volume := by
    have hk : Measurable (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ) := by
      unfold UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative UnforcedLeray.B0284.heatKernel2
        UnforcedLeray.B0191.heatKernel
      fun_prop
    exact (hk.mul (hg.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hbound : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Set.Ioo (θ / 2) (2 * θ),
      ‖F' s w‖ ≤ 4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by
    filter_upwards [] with w
    intro s hs
    have hlocal := UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local
      (θ₀ := θ) hθ hs.1 hs.2 w
    show ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * g (z - w)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * |g (z - w)|
        ≤ |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * M :=
          mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
      _ ≤ (4 * (θ⁻¹ ^ 2 + 2 / θ) * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w)) * M :=
          mul_le_mul_of_nonneg_right hlocal hM0
      _ = 4 * (θ⁻¹ ^ 2 + 2 / θ) * M * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by
          ring
  have hdiff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ s ∈ Set.Ioo (θ / 2) (2 * θ),
      HasDerivAt (F · w) (F' s w) s := by
    filter_upwards [] with w
    intro s hs
    have hpos : 0 < s := lt_trans (by positivity) hs.1
    exact (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hpos w).mul_const (g (z - w))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ × ℝ))) (F := F) (F' := F')
    (bound := fun w => 4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
      ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w))
    hball hFmeas hFint hFprimeMeas hbound (hwide.const_mul _) hdiff
  exact hparam.2

/-- `∂_θ P_θ ψ = Δ P_θ ψ` for `θ > 0` (source lines 2819-2836). -/
theorem hasDerivAt_cylHeatSmooth_age {c θ : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) (hθ : 0 < θ) (x : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => cylHeatSmooth c s ψ x) (lapP (cylHeatSmooth c θ ψ) x) θ := by
  obtain ⟨M, hM0, hM⟩ := cylTest_exists_bound hc hψ
  have h := hasDerivAt_gaussConv_age hθ hψ.continuous hM0 hM x
  have hibp := integral_ageDeriv_mul_comp_sub hθ hc hψ x
  have hlap : lapP (cylHeatSmooth c θ ψ) x =
      ∫ w : ℝ × ℝ, heatKernel2 θ w * lapP ψ (x - w) := by
    rw [← cylHeatSmooth_lapP hc hψ, cylHeatSmooth_apply_of_pos hθ]
  rw [hlap, ← hibp]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hθ] with s hs
  exact cylHeatSmooth_apply_of_pos hs ψ x

/-! ### Parabolic rescaling and joint continuity -/

theorem heatKernel2_smul_sqrt {θ : ℝ} (hθ : 0 < θ) (v : ℝ × ℝ) :
    heatKernel2 θ (Real.sqrt θ • v) = (Real.sqrt θ)⁻¹ ^ 2 * heatKernel2 1 v := by
  have hb : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have hbne : Real.sqrt θ ≠ 0 := hb.ne'
  have hq : UnforcedLeray.B0191.heatKernel 1 θ (Real.sqrt θ * v.1) =
      (Real.sqrt θ)⁻¹ * UnforcedLeray.B0191.heatKernel 1 1 v.1 := by
    rw [UnforcedLeray.B0191.heatKernel_selfSimilar 1 hθ]
    simp only [UnforcedLeray.B0191.profile]
    congr 1
    simp [hbne]
  have hη : UnforcedLeray.B0191.heatKernel 1 θ (Real.sqrt θ * v.2) =
      (Real.sqrt θ)⁻¹ * UnforcedLeray.B0191.heatKernel 1 1 v.2 := by
    rw [UnforcedLeray.B0191.heatKernel_selfSimilar 1 hθ]
    simp only [UnforcedLeray.B0191.profile]
    congr 1
    simp [hbne]
  change UnforcedLeray.B0191.heatKernel 1 θ (Real.sqrt θ * v.1) *
    UnforcedLeray.B0191.heatKernel 1 θ (Real.sqrt θ * v.2) = _
  rw [hq, hη]
  dsimp [UnforcedLeray.B0284.heatKernel2]
  ring

/-- Parabolic rescaling of the Gaussian convolution to unit age. -/
theorem gaussConv_eq_unit {θ : ℝ} (hθ : 0 < θ) (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, heatKernel2 θ w * g (x - w) =
      ∫ v : ℝ × ℝ, heatKernel2 1 v * g (x - Real.sqrt θ • v) := by
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hker : ∀ v : ℝ × ℝ, heatKernel2 θ (Real.sqrt θ • v) * g (x - Real.sqrt θ • v) =
      θ⁻¹ * (heatKernel2 1 v * g (x - Real.sqrt θ • v)) := by
    intro v
    rw [heatKernel2_smul_sqrt hθ, inv_pow, hsq]
    ring
  have h := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (fun w => heatKernel2 θ w * g (x - w)) (Real.sqrt θ)
  simp only [hker, hfin, hsq, integral_const_mul, smul_eq_mul] at h
  rw [abs_of_pos (inv_pos.mpr hθ)] at h
  exact (mul_left_cancel₀ (inv_ne_zero hθ.ne') h).symm

/-- The unit-age representation `P_θ g(x) = ∫ G_1(v) g(x - √θ v) dv`, for every `θ`. -/
theorem cylHeatSmooth_eq_unit {c θ : ℝ} (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    cylHeatSmooth c θ g x = ∫ v : ℝ × ℝ, heatKernel2 1 v * g (x - Real.sqrt θ • v) := by
  by_cases hθ : 0 < θ
  · rw [cylHeatSmooth_apply_of_pos hθ, gaussConv_eq_unit hθ]
  · rw [cylHeatSmooth_of_nonpos (not_lt.mp hθ), Real.sqrt_eq_zero'.mpr (not_lt.mp hθ)]
    simp only [zero_smul, sub_zero]
    rw [integral_mul_const, UnforcedLeray.B0284.integral_heatKernel2 one_pos, one_mul]

/-- `(θ, x) ↦ P_θ g(x)` is jointly continuous on `ℝ × ℝ²` for bounded continuous `g`. -/
theorem continuous_cylHeatSmooth_joint {c : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => cylHeatSmooth c p.1 g p.2) := by
  have hfun : (fun p : ℝ × (ℝ × ℝ) => cylHeatSmooth c p.1 g p.2) =
      fun p => ∫ v : ℝ × ℝ, heatKernel2 1 v * g (p.2 - Real.sqrt p.1 • v) := by
    funext p
    exact cylHeatSmooth_eq_unit g p.2
  rw [hfun]
  have hK := continuous_heatKernel2' 1
  refine continuous_of_dominated (bound := fun v => heatKernel2 1 v * M) ?_ ?_ ?_ ?_
  · intro p
    exact (hK.mul (hg.comp (continuous_const.sub
      (continuous_id.const_smul (Real.sqrt p.1))))).aestronglyMeasurable
  · intro p
    filter_upwards [] with v
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg one_pos v)]
    exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.B0284.heatKernel2_nonneg one_pos v)
  · exact (UnforcedLeray.B0284.integrable_heatKernel2 one_pos).mul_const M
  · filter_upwards [] with v
    exact continuous_const.mul (hg.comp (continuous_snd.sub
      ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const)))

/-- Joint continuity of `(θ, x) ↦ P_θ ψ(x)` for a cylinder test. -/
theorem continuous_cylHeatSmooth_joint_test {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => cylHeatSmooth c p.1 ψ p.2) := by
  obtain ⟨M, _, hM⟩ := cylTest_exists_bound hc hψ
  exact continuous_cylHeatSmooth_joint hψ.continuous hM

/-- Joint continuity of `(θ, x) ↦ ∂_i P_θ ψ(x)` on `ℝ × ℝ²` (in particular on `[0,1] × K`). -/
theorem continuous_pd_cylHeatSmooth_joint {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) (i : Fin 2) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => B0579.pd i (cylHeatSmooth c p.1 ψ) p.2) := by
  have hfun : (fun p : ℝ × (ℝ × ℝ) => B0579.pd i (cylHeatSmooth c p.1 ψ) p.2) =
      fun p => cylHeatSmooth c p.1 (B0579.pd i ψ) p.2 := by
    funext p
    rw [pd_cylHeatSmooth hc hψ i]
  rw [hfun]
  exact continuous_cylHeatSmooth_joint_test hc (hψ.pd i)

/-- Joint continuity of `(θ, x) ↦ Δ P_θ ψ(x)`. -/
theorem continuous_lapP_cylHeatSmooth_joint {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => lapP (cylHeatSmooth c p.1 ψ) p.2) := by
  have hfun : (fun p : ℝ × (ℝ × ℝ) => lapP (cylHeatSmooth c p.1 ψ) p.2) =
      fun p => cylHeatSmooth c p.1 (lapP ψ) p.2 := by
    funext p
    rw [cylHeatSmooth_lapP hc hψ]
  rw [hfun]
  exact continuous_cylHeatSmooth_joint_test hc (cylTest_lapP hψ)

/-! ### The Duhamel identity of the smoothed tests -/

/-- `P_θ φ = φ + ∫_0^θ P_η Δφ dη` pointwise, for a cylinder test `φ` and `θ ≥ 0`. -/
theorem cylHeatSmooth_duhamel {c θ : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (hθ : 0 ≤ θ) (x : ℝ × ℝ) :
    cylHeatSmooth c θ φ x = φ x + ∫ η in (0 : ℝ)..θ, cylHeatSmooth c η (lapP φ) x := by
  have hjoint := continuous_cylHeatSmooth_joint_test hc hφ
  have hjointL := continuous_cylHeatSmooth_joint_test hc (cylTest_lapP hφ)
  have hcont : Continuous (fun s : ℝ => cylHeatSmooth c s φ x) :=
    hjoint.comp (continuous_id.prodMk continuous_const)
  have hcontL : Continuous (fun s : ℝ => cylHeatSmooth c s (lapP φ) x) :=
    hjointL.comp (continuous_id.prodMk continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ hcont.continuousOn
    (fun s hs => by
      have h := hasDerivAt_cylHeatSmooth_age hc hφ hs.1 x
      rwa [← cylHeatSmooth_lapP hc hφ] at h)
    (hcontL.intervalIntegrable 0 θ)
  rw [hFTC, cylHeatSmooth_zero]
  ring

/-- The Duhamel identity for the first derivatives:
`∂_i P_θ φ = ∂_i φ + ∫_0^θ P_η Δ∂_i φ dη` (`θ ≥ 0`). -/
theorem pd_cylHeatSmooth_duhamel {c θ : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (hθ : 0 ≤ θ) (i : Fin 2) (x : ℝ × ℝ) :
    B0579.pd i (cylHeatSmooth c θ φ) x =
      B0579.pd i φ x + ∫ η in (0 : ℝ)..θ, B0579.pd i (cylHeatSmooth c η (lapP φ)) x := by
  rw [pd_cylHeatSmooth hc hφ i, cylHeatSmooth_duhamel hc (hφ.pd i) hθ x, ← pd_lapP hφ i]
  congr 1
  refine intervalIntegral.integral_congr fun η _ => ?_
  rw [pd_cylHeatSmooth hc (cylTest_lapP hφ) i]

end UnforcedLeray.Short.IIIa.Exist
