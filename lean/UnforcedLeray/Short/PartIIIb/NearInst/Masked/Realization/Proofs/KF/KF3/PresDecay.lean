import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresGrad
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresSmooth
import UnforcedLeray.Analysis.Pressure.Spatial
import UnforcedLeray.Analysis.Pressure.NewtonKernel

/-!
# `kf3PresDecay : KF3PresDecay` (source 3602-3606, 117-120)

Route: the Newtonian kernel satisfies `|∂_jN(w)| ≤ (4π)⁻¹|w|⁻²`. For a function `h` bounded by `B`
and vanishing off `closedBall 0 r`, the convolution `∂_jN ⋆ h` is bounded by `K B (1+|x|)⁻²`
(far region `|x| ≥ R`: the kernel is `≲ |x|⁻²` on the support; near region `|x| < R`: a
translated integrable majorant).  The bounds `B` are uniform in the phase `τ` by periodicity and
compactness.  `lerayPres` is a sum of three such convolutions (`kf3PresDecay` uses the definition
directly), and `∇ₓp` is given by `KF3PresGrad` as a sum of such convolutions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Polynomial form of the Newtonian-gradient kernel bound. -/
theorem kf3d_kernel_le (j : Fin 3) (w : Space) :
    ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j w‖ ≤
      (4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹ := by
  have h := UnforcedLeray.PressureAnalysis.norm_newtonGradientKernel_le j w
  rw [Real.rpow_neg (norm_nonneg w), Real.rpow_two] at h
  exact h

/-- The local majorant `|∂_jN| 1_{closedBall 0 ρ}`. -/
def kf3dG (j : Fin 3) (ρ : ℝ) (w : Space) : ℝ :=
  (Metric.closedBall (0 : Space) ρ).indicator
    (fun v => ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j v‖) w

theorem kf3dG_nonneg (j : Fin 3) (ρ : ℝ) (w : Space) : 0 ≤ kf3dG j ρ w :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) w

theorem kf3dG_of_le (j : Fin 3) {ρ : ℝ} {w : Space} (hw : ‖w‖ ≤ ρ) :
    kf3dG j ρ w = ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j w‖ := by
  unfold kf3dG
  exact Set.indicator_of_mem (mem_closedBall_zero_iff.2 hw) _

theorem kf3dG_integrable (j : Fin 3) (ρ : ℝ) : Integrable (kf3dG j ρ) := by
  unfold kf3dG
  have hK : IntegrableOn (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
      (Metric.closedBall (0 : Space) ρ) :=
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable j).integrableOn_isCompact
      (isCompact_closedBall 0 ρ)
  exact (integrable_indicator_iff measurableSet_closedBall).mpr hK.norm

/-- **Newtonian convolution bound.**  For `r ≥ 0` there is one constant `K ≥ 0` such that every
bounded continuous `h` vanishing off `closedBall 0 r` satisfies
`|∂_jN ⋆ h (x)| ≤ K B (1+|x|)⁻²`, `B` a bound for `|h|`. -/
theorem kf3d_newton_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3) (B : ℝ) (h : Space → ℝ), Continuous h →
      (∀ z, |h z| ≤ B) → (∀ z, r < ‖z‖ → h z = 0) → ∀ x : Space,
      |UnforcedLeray.PressureAnalysis.newtonComponent j h x| ≤ K * B / (1 + ‖x‖) ^ 2 := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max (2 * r) 1 := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R + r := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (Metric.closedBall (0 : Space) r)).toReal :=
    ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hR2 : 2 * r ≤ R := by rw [hRdef]; exact le_max_left _ _
  have hV0 : 0 ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
  have hI0 : ∀ j : Fin 3, 0 ≤ ∫ w, kf3dG j ρ w :=
    fun j => integral_nonneg (fun w => kf3dG_nonneg j ρ w)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ j : Fin 3, ∫ w, kf3dG j ρ w := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun j _ => hI0 j)
  have hIS : ∀ j : Fin 3, (∫ w, kf3dG j ρ w) ≤ S := fun j => by
    rw [hSdef]; exact Finset.single_le_sum (fun k _ => hI0 k) (Finset.mem_univ j)
  refine ⟨(4 * Real.pi)⁻¹ * 16 * V + (1 + R) ^ 2 * S, ?_, ?_⟩
  · have h1 : 0 ≤ (4 * Real.pi)⁻¹ * 16 * V :=
      mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hV0
    have h2 : 0 ≤ (1 + R) ^ 2 * S := mul_nonneg (by positivity) hS0
    linarith
  intro j B h hc hB hsupp x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hposK : 0 ≤ (4 * Real.pi)⁻¹ * 16 * V * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hV0) hB0
  unfold UnforcedLeray.PressureAnalysis.newtonComponent
  rw [le_div_iff₀ (by positivity), ← Real.norm_eq_abs]
  rcases lt_or_ge ‖x‖ R with hx | hx
  · -- near region: translated integrable majorant
    have hmaj : ∀ y : Space,
        ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y) * h y‖ ≤
          B * kf3dG j ρ (x - y) := by
      intro y
      rw [norm_mul]
      by_cases hy : ‖y‖ ≤ r
      · have hxy : ‖x - y‖ ≤ ρ := by
          have := norm_sub_le x y
          rw [hρdef]; linarith
        have h1 : ‖h y‖ ≤ B := by rw [Real.norm_eq_abs]; exact hB y
        rw [kf3dG_of_le j hxy]
        calc ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y)‖ * ‖h y‖
            ≤ ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y)‖ * B :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = B * ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y)‖ := by ring
      · have hgt : r < ‖y‖ := lt_of_not_ge hy
        rw [hsupp y hgt, norm_zero, mul_zero]
        exact mul_nonneg hB0 (kf3dG_nonneg j ρ _)
    have hmi : Integrable (fun y : Space => B * kf3dG j ρ (x - y)) :=
      ((kf3dG_integrable j ρ).comp_sub_left x).const_mul B
    have hnear := norm_integral_le_of_norm_le hmi (ae_of_all _ hmaj)
    have hsub : ∫ y : Space, kf3dG j ρ (x - y) = ∫ w : Space, kf3dG j ρ w :=
      integral_sub_left_eq_self (kf3dG j ρ) volume x
    rw [integral_const_mul, hsub] at hnear
    have hA : ‖∫ y : Space, UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y) * h y‖
        ≤ B * S := hnear.trans (mul_le_mul_of_nonneg_left (hIS j) hB0)
    have hsq : (1 + ‖x‖) ^ 2 ≤ (1 + R) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hx.le) (by linarith [norm_nonneg x] : (0:ℝ) ≤ 2 + R + ‖x‖)]
    have hnn : 0 ≤ (1 + ‖x‖) ^ 2 := by positivity
    calc ‖∫ y : Space, UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y) * h y‖
          * (1 + ‖x‖) ^ 2 ≤ (B * S) * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_right hA hnn
      _ ≤ (B * S) * (1 + R) ^ 2 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hB0 hS0)
      _ ≤ ((4 * Real.pi)⁻¹ * 16 * V + (1 + R) ^ 2 * S) * B := by nlinarith [hposK]
  · -- far region: the kernel is `≲ |x|⁻²` on the support of `h`
    have ha1 : 1 ≤ ‖x‖ := le_trans hR1 hx
    have hxr : 2 * r ≤ ‖x‖ := le_trans hR2 hx
    have hcb : ∀ y : Space, ‖y‖ ≤ r →
        ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y)‖ ≤
          (4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) := by
      intro y hy
      have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le x y
        linarith
      have hpos : 0 < ‖x‖ / 2 := by linarith
      have hsq2 : (‖x‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith
      have h1 : (‖x - y‖ ^ 2)⁻¹ ≤ ((‖x‖ / 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq2
      have h2 : ((‖x‖ / 2) ^ 2)⁻¹ ≤ 16 / (1 + ‖x‖) ^ 2 := by
        rw [div_pow, inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) (by linarith : (0:ℝ) ≤ 3 * ‖x‖ + 1)]
      calc ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y)‖
          ≤ (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹ := kf3d_kernel_le j (x - y)
        _ ≤ (4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    have hmaj : ∀ y : Space,
        ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y) * h y‖ ≤
          (Metric.closedBall (0 : Space) r).indicator
            (fun _ : Space => (4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) * B) y := by
      intro y
      rw [norm_mul]
      by_cases hy : ‖y‖ ≤ r
      · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hy)]
        have h1 : ‖h y‖ ≤ B := by rw [Real.norm_eq_abs]; exact hB y
        exact mul_le_mul (hcb y hy) h1 (norm_nonneg _) (by positivity)
      · have h0 : y ∉ Metric.closedBall (0 : Space) r := fun hm => hy (mem_closedBall_zero_iff.1 hm)
        rw [hsupp y (lt_of_not_ge hy), norm_zero, mul_zero, Set.indicator_of_notMem h0]
    have hΦ : Integrable ((Metric.closedBall (0 : Space) r).indicator
        (fun _ : Space => (4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) * B)) :=
      (integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (measure_closedBall_lt_top (μ := volume)).ne)
    have hfar := norm_integral_le_of_norm_le hΦ (ae_of_all _ hmaj)
    rw [integral_indicator_const _ measurableSet_closedBall, measureReal_def, smul_eq_mul,
      ← hVdef] at hfar
    have he : (4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) * B * (1 + ‖x‖) ^ 2
        = (4 * Real.pi)⁻¹ * 16 * B := by
      have hne : (1 + ‖x‖) ≠ 0 := by positivity
      field_simp
    have hnn : 0 ≤ (1 + ‖x‖) ^ 2 := by positivity
    have hSB : 0 ≤ (1 + R) ^ 2 * S * B := mul_nonneg (mul_nonneg (by positivity) hS0) hB0
    calc ‖∫ y : Space, UnforcedLeray.PressureAnalysis.newtonGradientKernel j (x - y) * h y‖
          * (1 + ‖x‖) ^ 2 ≤ (V * ((4 * Real.pi)⁻¹ * (16 / (1 + ‖x‖) ^ 2) * B)) * (1 + ‖x‖) ^ 2 :=
            mul_le_mul_of_nonneg_right hfar hnn
      _ = V * ((4 * Real.pi)⁻¹ * 16 * B) := by rw [← he]; ring
      _ ≤ ((4 * Real.pi)⁻¹ * 16 * V + (1 + R) ^ 2 * S) * B := by nlinarith [hSB]


/-- A vector of `EuclideanSpace` is bounded by the sum of the absolute values of its entries. -/
theorem kf3d_norm_le_sum_abs (v : Space) : ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |v i|)
    (fun i _ => abs_nonneg _)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- Uniform bound for one continuous, `P`-periodic in `τ`, spatially supported function. -/
theorem kf3d_uniform_one {P r : ℝ} (hP : 0 < P) (F : Space × ℝ → ℝ) (hc : Continuous F)
    (hper : ∀ (x : Space) (τ : ℝ), F (x, τ + P) = F (x, τ))
    (hsupp : ∀ (x : Space) (τ : ℝ), r < ‖x‖ → F (x, τ) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Space) (τ : ℝ), |F (x, τ)| ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : Space) r ×ˢ Icc (0 : ℝ) P) :=
    (isCompact_closedBall (0 : Space) r).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x τ => ?_⟩
  obtain ⟨τ', hτ', hEq⟩ :=
    (show Function.Periodic (fun t => F (x, t)) P from fun t => hper x t).exists_mem_Ico₀ hP τ
  have hEq' : F (x, τ) = F (x, τ') := hEq
  by_cases hx : ‖x‖ ≤ r
  · have hmem : (x, τ') ∈ Metric.closedBall (0 : Space) r ×ˢ Icc (0 : ℝ) P :=
      ⟨mem_closedBall_zero_iff.2 hx, ⟨hτ'.1, hτ'.2.le⟩⟩
    have h1 := hC (x, τ') hmem
    rw [hEq', ← Real.norm_eq_abs]
    exact h1.trans (le_max_left _ _)
  · have hx' : r < ‖x‖ := lt_of_not_ge hx
    rw [hsupp x τ hx', abs_zero]
    exact le_max_right _ _

/-- Uniform bound for a finite family. -/
theorem kf3d_uniform {ι : Type} [Fintype ι] {P r : ℝ} (hP : 0 < P) (F : ι → Space × ℝ → ℝ)
    (hc : ∀ a, Continuous (F a))
    (hper : ∀ a (x : Space) (τ : ℝ), F a (x, τ + P) = F a (x, τ))
    (hsupp : ∀ a (x : Space) (τ : ℝ), r < ‖x‖ → F a (x, τ) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a (x : Space) (τ : ℝ), |F a (x, τ)| ≤ B := by
  have h1 : ∀ a, ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Space) (τ : ℝ), |F a (x, τ)| ≤ B :=
    fun a => kf3d_uniform_one hP (F a) (hc a) (hper a) (hsupp a)
  choose B hB0 hB using h1
  refine ⟨∑ a, B a, Finset.sum_nonneg (fun a _ => hB0 a), fun a x τ => ?_⟩
  exact (hB a x τ).trans (Finset.single_le_sum (fun b _ => hB0 b) (Finset.mem_univ a))

/-- The slice derivative of a far-supported `cartDiv` vanishes outside the support ball. -/
theorem kf3d_slice_far (P : ℝ) (M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hM : IsOuterTest P M)
    (r : ℝ) (hr : ∀ y : Space × ℝ, M y ≠ 0 → ‖y.1‖ ≤ r) (x : Space) (τ : ℝ) (hx : r < ‖x‖)
    (i j : Fin 3) :
    fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) x (UnforcedLeray.coordinateVector i) = 0 := by
  have hev : (fun x' : Space => cartDiv M (x', τ) j) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt (continuous_const (y := r)) continuous_norm :
      IsOpen {x'' : Space | r < ‖x''‖}).mem_nhds hx] with x' hx''
    exact kf3g_cartDiv_far P M hM r hr x' τ hx'' j
  rw [hev.fderiv_eq]
  simp

/-- The components of `cartDiv M` are smooth in `(x, τ)`. -/
theorem kf3d_hG {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hM : IsOuterTest P M)
    (j : Fin 3) : ContDiff ℝ ∞ (fun q : Space × ℝ => cartDiv M (q.1, q.2) j) := by
  have h1 : ContDiff ℝ ∞ (fun y : Space × ℝ => (y.2, y.1)) := contDiff_snd.prodMk contDiff_fst
  exact (kf3p_phi_smooth P M hM j).comp h1

/-- The slice derivative in `x` as a function of `(x, τ)`. -/
theorem kf3d_grad_eq {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hM : IsOuterTest P M)
    (i j : Fin 3) (q : Space × ℝ) :
    fderiv ℝ (fun x' : Space => cartDiv M (x', q.2) j) q.1 (UnforcedLeray.coordinateVector i) =
      fderiv ℝ (fun y : Space × ℝ => cartDiv M (y.1, y.2) j) q
        (UnforcedLeray.coordinateVector i, 0) :=
  kf3g_slice_fderiv (fun y : Space × ℝ => cartDiv M (y.1, y.2) j) (kf3d_hG hM j) q.1 q.2 _

/-- Continuity of the slice derivatives jointly in `(x, τ)`. -/
theorem kf3d_gradF_cont {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hM : IsOuterTest P M)
    (ij : Fin 3 × Fin 3) :
    Continuous (fun q : Space × ℝ =>
      fderiv ℝ (fun x' : Space => cartDiv M (x', q.2) ij.2) q.1
        (UnforcedLeray.coordinateVector ij.1)) := by
  have hc1 : Continuous (fun q : Space × ℝ =>
      fderiv ℝ (fun y : Space × ℝ => cartDiv M (y.1, y.2) ij.2) q
        (UnforcedLeray.coordinateVector ij.1, 0)) :=
    ((kf3d_hG hM ij.2).continuous_fderiv (by simp)).clm_apply continuous_const
  exact hc1.congr (fun q => (kf3d_grad_eq hM ij.1 ij.2 q).symm)

/-- **Leaf: decay of the Leray pressure and its gradient** (source 3602-3606). -/
theorem kf3PresDecay : KF3PresDecay := by
  intro P M hP hM
  obtain ⟨r, hr⟩ := hM.bounded
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = max r 0 := ⟨_, rfl⟩
  have hr0 : 0 ≤ r₀ := by rw [hr₀]; exact le_max_right _ _
  have hrr : ∀ x : Space, r₀ < ‖x‖ → r < ‖x‖ := fun x hx => by
    rw [hr₀] at hx; exact lt_of_le_of_lt (le_max_left r 0) hx
  obtain ⟨K, hK0, hN⟩ := kf3d_newton_bound r₀ hr0
  obtain ⟨Bp, hBp0, hBp⟩ := kf3d_uniform (ι := Fin 3) (r := r₀) hP
    (fun j q => cartDiv M (q.1, q.2) j)
    (fun j => (kf3d_hG hM j).continuous)
    (fun j x τ => by simp only [cartDiv_periodic hM.periodic])
    (fun j x τ hx => kf3g_cartDiv_far P M hM r hr x τ (hrr x hx) j)
  obtain ⟨Bg, hBg0, hBg⟩ := kf3d_uniform (ι := Fin 3 × Fin 3) (r := r₀) hP
    (fun ij q => fderiv ℝ (fun x' : Space => cartDiv M (x', q.2) ij.2) q.1
        (UnforcedLeray.coordinateVector ij.1))
    (fun ij => kf3d_gradF_cont hM ij)
    (fun ij x τ => by simp only [cartDiv_periodic hM.periodic])
    (fun ij x τ hx => kf3d_slice_far P M hM r hr x τ (hrr x hx) ij.1 ij.2)
  refine ⟨9 * K * Bg + 3 * K * Bp, ?_⟩
  rintro ⟨x, τ⟩
  dsimp only
  have ha0 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
  -- pressure: sum of three Newtonian convolutions
  have hpres : |lerayPres M (x, τ)| ≤ 3 * (K * Bp / (1 + ‖x‖) ^ 2) := by
    have hl : lerayPres M (x, τ) =
        ∑ i : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent i
          (fun z => cartDiv M (z, τ) i) x := rfl
    rw [hl]
    calc |∑ i : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent i
          (fun z => cartDiv M (z, τ) i) x|
        ≤ ∑ i : Fin 3, |UnforcedLeray.PressureAnalysis.newtonComponent i
          (fun z => cartDiv M (z, τ) i) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, K * Bp / (1 + ‖x‖) ^ 2 := Finset.sum_le_sum (fun i _ =>
          hN i Bp (fun z => cartDiv M (z, τ) i)
            ((kf3d_hG hM i).continuous.comp (continuous_id.prodMk continuous_const))
            (fun z => hBp i z τ)
            (fun z hz => kf3g_cartDiv_far P M hM r hr z τ (hrr z hz) i) x)
      _ = 3 * (K * Bp / (1 + ‖x‖) ^ 2) := by simp [Finset.sum_const] <;> ring
  -- gradient: each component is a sum of three Newtonian convolutions
  have hgrad_comp : ∀ i : Fin 3,
      |UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i| ≤ 3 * (K * Bg / (1 + ‖x‖) ^ 2) := by
    intro i
    rw [kf3PresGrad P M hM x τ i]
    calc |∑ j : Fin 3, UnforcedLeray.PressureAnalysis.newtonComponent j
          (fun z => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i)) x|
        ≤ ∑ j : Fin 3, |UnforcedLeray.PressureAnalysis.newtonComponent j
          (fun z => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
            (UnforcedLeray.coordinateVector i)) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, K * Bg / (1 + ‖x‖) ^ 2 := Finset.sum_le_sum (fun j _ =>
          hN j Bg (fun z => fderiv ℝ (fun x' : Space => cartDiv M (x', τ) j) z
              (UnforcedLeray.coordinateVector i))
            ((kf3d_gradF_cont hM (i, j)).comp (continuous_id.prodMk continuous_const))
            (fun z => hBg (i, j) z τ)
            (fun z hz => kf3d_slice_far P M hM r hr z τ (hrr z hz) i j) x)
      _ = 3 * (K * Bg / (1 + ‖x‖) ^ 2) := by simp [Finset.sum_const] <;> ring
  have hgrad : ‖UnforcedLeray.B0226.gradX (lerayPres M) (x, τ)‖ ≤ 9 * (K * Bg / (1 + ‖x‖) ^ 2) := by
    calc ‖UnforcedLeray.B0226.gradX (lerayPres M) (x, τ)‖
        ≤ ∑ i : Fin 3, |UnforcedLeray.B0226.gradX (lerayPres M) (x, τ) i| :=
          kf3d_norm_le_sum_abs _
      _ ≤ ∑ i : Fin 3, 3 * (K * Bg / (1 + ‖x‖) ^ 2) := Finset.sum_le_sum (fun i _ => hgrad_comp i)
      _ = 9 * (K * Bg / (1 + ‖x‖) ^ 2) := by simp [Finset.sum_const] <;> ring
  -- comparison of the powers of `1 + |x|`
  have hKB : 0 ≤ K * Bp := mul_nonneg hK0 hBp0
  have hKBg : 0 ≤ K * Bg := mul_nonneg hK0 hBg0
  have h1 : K * Bp / (1 + ‖x‖) ^ 2 ≤ K * Bp / (1 + ‖x‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hKB ha0) (norm_nonneg x)]
  have hsplit1 : (9 * K * Bg + 3 * K * Bp) / (1 + ‖x‖) =
      3 * (K * Bp / (1 + ‖x‖)) + 9 * (K * Bg) / (1 + ‖x‖) := by ring
  have hnn1 : 0 ≤ 9 * (K * Bg) / (1 + ‖x‖) := div_nonneg (by linarith) ha0
  have hpres' : |lerayPres M (x, τ)| ≤ (9 * K * Bg + 3 * K * Bp) / (1 + ‖x‖) := by
    rw [hsplit1]; linarith
  have hsplit2 : (9 * K * Bg + 3 * K * Bp) / (1 + ‖x‖) ^ 2 =
      9 * (K * Bg / (1 + ‖x‖) ^ 2) + 3 * (K * Bp) / (1 + ‖x‖) ^ 2 := by ring
  have hnn2 : 0 ≤ 3 * (K * Bp) / (1 + ‖x‖) ^ 2 := div_nonneg (by linarith) (by positivity)
  have hgrad' : ‖UnforcedLeray.B0226.gradX (lerayPres M) (x, τ)‖ ≤
      (9 * K * Bg + 3 * K * Bp) / (1 + ‖x‖) ^ 2 := by
    rw [hsplit2]; linarith
  exact ⟨hpres', hgrad'⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
