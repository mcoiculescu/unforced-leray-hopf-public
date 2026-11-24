import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.TailFDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.HeatGConvFDeriv
import UnforcedLeray.Analysis.Pressure.NewtonIdentity
import UnforcedLeray.Analysis.Pressure.NewtonKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `kf3HeatNewtonGrad : KF3HeatNewtonGrad` (source 3597-3601, 3609-3611)

For `θ > 0`, `∫ G_θ(x - y) ∂_jN(y) dy = ∂_j∫_θ^∞G_a(x) da`, where `∂_jN(y) = ∫_0^∞ ∂_jG_b(y) db`
for `y ≠ 0` (`PressureAnalysis.integral_fderiv_heatKernel_time`).

Route: Fubini on `ℝ³ × (0,∞)` for `(y, b) ↦ G_θ(x - y) ∂_jG_b(y)`, whose absolute integral is
`∫ G_θ(x - y) |∂_jN(y)| dy < ∞`.  The inner `y`-integral is `∂_jG_{θ+b}(x)`
(`kf3HeatGConvFDeriv`), and the shift `b ↦ θ + b` maps `(0,∞)` onto `(θ,∞)`.  The tail derivative
is `kf3TailFDeriv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

/-- Continuity of the heat kernel in space, for fixed time. -/
theorem kf3hn_heatG_continuous (a : ℝ) : Continuous (heatG a) :=
  (kf3hc_smooth a).continuous

/-- The heat kernel is nonnegative for positive time. -/
theorem kf3hn_heatG_nonneg {a : ℝ} (ha : 0 < a) (z : Space) : 0 ≤ heatG a z := by
  rw [heatG_eq_heatKernel]
  exact UnforcedLeray.Heat.kernel_nonneg ha z

/-- Uniform bound on the heat kernel for positive time. -/
theorem kf3hn_heatG_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 < a → ∀ z : Space,
    |heatG a z| ≤ C * a ^ (-(3/2:ℝ)) := by
  obtain ⟨C0, hC0, hC0b⟩ := heatGBound 0
  refine ⟨C0, hC0, fun a ha z => ?_⟩
  have hz : ‖iteratedFDeriv ℝ 0 (heatG a) z‖ = ‖heatG a z‖ := norm_iteratedFDeriv_zero
  have h := hC0b a ha z
  have e : -(3 + ((0:ℕ):ℝ)) / 2 = -(3/2:ℝ) := by norm_num
  rw [e] at h
  have hexp : Real.exp (-‖z‖ ^ 2 / (8 * a)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
    positivity
  have hpos : 0 ≤ C0 * a ^ (-(3/2:ℝ)) := mul_nonneg hC0 (Real.rpow_nonneg ha.le _)
  calc |heatG a z| = ‖heatG a z‖ := (Real.norm_eq_abs _).symm
    _ = ‖iteratedFDeriv ℝ 0 (heatG a) z‖ := hz.symm
    _ ≤ C0 * a ^ (-(3/2:ℝ)) * Real.exp (-‖z‖ ^ 2 / (8 * a)) := h
    _ ≤ C0 * a ^ (-(3/2:ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp hpos
    _ = C0 * a ^ (-(3/2:ℝ)) := mul_one _

/-- A bounded measurable `h` that is integrable, times a function `g` that is integrable on the
closed unit ball and bounded by `C` outside it, is integrable. -/
theorem kf3hn_integrable_mul {h g : Space → ℝ} (hh : Measurable h) (hhI : Integrable h)
    {M : ℝ} (hM : ∀ y, |h y| ≤ M) (hg : Measurable g)
    (hgI : IntegrableOn g (Metric.closedBall (0 : Space) 1)) {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ y : Space, 1 < ‖y‖ → |g y| ≤ C) :
    Integrable (fun y => h y * g y) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hu : Integrable (fun y : Space =>
      M * ‖(Metric.closedBall (0 : Space) 1).indicator g y‖ + C * |h y|) := by
    refine Integrable.add ?_ ?_
    · exact (hgI.integrable_indicator measurableSet_closedBall).norm.const_mul M
    · exact hhI.abs.const_mul C
  refine Integrable.mono' hu (hh.mul hg).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
  by_cases hy : ‖y‖ ≤ 1
  · have hmem : y ∈ Metric.closedBall (0 : Space) 1 := by
      rw [mem_closedBall_zero_iff]
      exact hy
    rw [indicator_of_mem hmem]
    have h2 : 0 ≤ C * |h y| := mul_nonneg hC (abs_nonneg _)
    calc ‖h y * g y‖ = |h y| * ‖g y‖ := by rw [norm_mul, Real.norm_eq_abs]
      _ ≤ M * ‖g y‖ := mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
      _ ≤ M * ‖g y‖ + C * |h y| := le_add_of_nonneg_right h2
  · have hy' : 1 < ‖y‖ := lt_of_not_ge hy
    have hnot : y ∉ Metric.closedBall (0 : Space) 1 := by
      rw [mem_closedBall_zero_iff]
      exact not_le.mpr hy'
    rw [indicator_of_notMem hnot, norm_zero, mul_zero, zero_add]
    calc ‖h y * g y‖ = |h y| * |g y| := by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |h y| * C := mul_le_mul_of_nonneg_left (hgC y hy') (abs_nonneg _)
      _ = C * |h y| := mul_comm _ _

/-- The Fubini integrand `(y, b) ↦ G_θ(x - y) ∂_jG_b(y)`. -/
def kf3hnF (θ : ℝ) (x : Space) (j : Fin 3) (y : Space) (b : ℝ) : ℝ :=
  heatG θ (x - y) * fderiv ℝ (heatG b) y (UnforcedLeray.coordinateVector j)

/-- **Leaf: the heat flow of the Newtonian gradient** (source 3597-3601, 3609-3611). -/
theorem kf3HeatNewtonGrad : KF3HeatNewtonGrad := by
  intro θ hθ x j
  obtain ⟨C0, hC0, hC0b⟩ := kf3hn_heatG_bound
  -- measurability and integrability of the heat kernel translate
  have hGmeas : Measurable (fun y : Space => heatG θ (x - y)) :=
    ((kf3hn_heatG_continuous θ).comp (continuous_const.sub continuous_id)).measurable
  have hGint : Integrable (fun y : Space => heatG θ (x - y)) :=
    (kf3hc_integrable hθ).comp_sub_left x
  have hGb : ∀ y : Space, |heatG θ (x - y)| ≤ C0 * θ ^ (-(3/2:ℝ)) :=
    fun y => hC0b θ hθ (x - y)
  -- the Newtonian gradient kernel
  have hKmeas : Measurable (UnforcedLeray.PressureAnalysis.newtonGradientKernel j) :=
    UnforcedLeray.PressureAnalysis.newtonGradientKernel_measurable j
  have hKloc : IntegrableOn (UnforcedLeray.PressureAnalysis.newtonGradientKernel j)
      (Metric.closedBall (0 : Space) 1) :=
    (UnforcedLeray.PressureAnalysis.newtonGradientKernel_locallyIntegrable j).integrableOn_isCompact
      (isCompact_closedBall 0 1)
  have hKbd : ∀ y : Space, 1 < ‖y‖ →
      |UnforcedLeray.PressureAnalysis.newtonGradientKernel j y| ≤ (4 * Real.pi)⁻¹ := by
    intro y hy
    calc |UnforcedLeray.PressureAnalysis.newtonGradientKernel j y|
        = ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j y‖ := (Real.norm_eq_abs _).symm
      _ ≤ (4 * Real.pi)⁻¹ * ‖y‖ ^ (-2 : ℝ) :=
          UnforcedLeray.PressureAnalysis.norm_newtonGradientKernel_le j y
      _ ≤ (4 * Real.pi)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hy.le (by norm_num)) (by positivity)
      _ = (4 * Real.pi)⁻¹ := mul_one _
  have hC : (0:ℝ) ≤ (4 * Real.pi)⁻¹ := by positivity
  -- integrability of the kernel against the heat kernel
  have hK_int : Integrable (fun y : Space =>
      heatG θ (x - y) * UnforcedLeray.PressureAnalysis.newtonGradientKernel j y) :=
    kf3hn_integrable_mul hGmeas hGint hGb hKmeas hKloc hC hKbd
  have hKn_int : Integrable (fun y : Space =>
      heatG θ (x - y) * ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j y‖) := by
    refine kf3hn_integrable_mul hGmeas hGint hGb hKmeas.norm hKloc.norm hC ?_
    intro y hy
    simpa [abs_norm] using hKbd y hy
  -- the time integral of the derivative of the heat kernel is the Newtonian gradient
  have hT : ∀ y : Space, y ≠ 0 →
      ∫ b in Ioi (0:ℝ), fderiv ℝ (heatG b) y (UnforcedLeray.coordinateVector j) =
        UnforcedLeray.PressureAnalysis.newtonGradientKernel j y := by
    intro y hy
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.PressureAnalysis.integral_fderiv_heatKernel_time hy j
  have hTn : ∀ y : Space, y ≠ 0 →
      ∫ b in Ioi (0:ℝ), ‖fderiv ℝ (heatG b) y (UnforcedLeray.coordinateVector j)‖ =
        ‖UnforcedLeray.PressureAnalysis.newtonGradientKernel j y‖ := by
    intro y hy
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.PressureAnalysis.integral_norm_fderiv_heatKernel_time hy j
  have hS : ∀ y : Space, y ≠ 0 →
      IntegrableOn (fun b => fderiv ℝ (heatG b) y (UnforcedLeray.coordinateVector j)) (Ioi 0) := by
    intro y hy
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.PressureAnalysis.fderiv_heatKernel_integrable_time hy j
  -- joint measurability of the Fubini integrand
  have hmeasF : Measurable (fun p : Space × ℝ => kf3hnF θ x j p.1 p.2) := by
    have h1 : Measurable (fun p : Space × ℝ => heatG θ (x - p.1)) :=
      hGmeas.comp measurable_fst
    have h2 : Measurable (fun p : Space × ℝ =>
        fderiv ℝ (heatG p.2) p.1 (UnforcedLeray.coordinateVector j)) := by
      have e : (fun p : Space × ℝ => fderiv ℝ (heatG p.2) p.1 (UnforcedLeray.coordinateVector j)) =
          fun p : Space × ℝ =>
            fderiv ℝ (UnforcedLeray.Heat.kernel p.2) p.1 (UnforcedLeray.coordinateVector j) := by
        funext p
        rw [heatG_eq_heatKernel]
      rw [e]
      exact UnforcedLeray.PressureAnalysis.fderiv_heatKernel_joint_measurable j
    exact h1.mul h2
  -- integrability on the product
  have hFint : Integrable (fun p : Space × ℝ => kf3hnF θ x j p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeasF.aestronglyMeasurable]
    constructor
    · filter_upwards [Measure.ae_ne (volume : Measure Space) (0 : Space)] with y hy
      exact (hS y hy).const_mul (heatG θ (x - y))
    · refine hKn_int.congr ?_
      filter_upwards [Measure.ae_ne (volume : Measure Space) (0 : Space)] with y hy
      have hnorm : ∫ b in Ioi (0:ℝ), ‖kf3hnF θ x j y b‖ =
          heatG θ (x - y) * ∫ b in Ioi (0:ℝ),
            ‖fderiv ℝ (heatG b) y (UnforcedLeray.coordinateVector j)‖ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun b hb => ?_)
        simp only [kf3hnF]
        rw [norm_mul, Real.norm_of_nonneg (kf3hn_heatG_nonneg hθ _)]
      rw [hnorm, hTn y hy]
  -- Fubini
  have hswap := integral_integral_swap (μ := volume) (ν := volume.restrict (Ioi (0:ℝ)))
    (f := kf3hnF θ x j) hFint
  -- left side
  have hL : ∫ y : Space, ∫ b in Ioi (0:ℝ), kf3hnF θ x j y b =
      ∫ y : Space, heatG θ (x - y) * UnforcedLeray.PressureAnalysis.newtonGradientKernel j y := by
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne (volume : Measure Space) (0 : Space)] with y hy
    simp only [kf3hnF]
    rw [integral_const_mul, hT y hy]
  -- right side: the heat semigroup on the derivative
  have hR : ∫ b in Ioi (0:ℝ), ∫ y : Space, kf3hnF θ x j y b =
      ∫ b in Ioi (0:ℝ), fderiv ℝ (heatG (θ + b)) x (UnforcedLeray.coordinateVector j) :=
    setIntegral_congr_fun measurableSet_Ioi (fun b hb =>
      kf3HeatGConvFDeriv θ b hθ (Set.mem_Ioi.mp hb) x j)
  -- shift of the time variable
  have hImg : (fun b : ℝ => θ + b) '' Ioi (0:ℝ) = Ioi θ := by
    rw [Set.image_const_add_Ioi, add_zero]
  have hShift : ∫ b in Ioi (0:ℝ), fderiv ℝ (heatG (θ + b)) x (UnforcedLeray.coordinateVector j) =
      ∫ a in Ioi θ, fderiv ℝ (heatG a) x (UnforcedLeray.coordinateVector j) := by
    have h := integral_image_eq_integral_abs_deriv_smul (f := fun b : ℝ => θ + b)
      (f' := fun _ => (1:ℝ)) (s := Ioi (0:ℝ)) measurableSet_Ioi
      (fun b _ => (hasDerivAt_id' b).const_add θ |>.hasDerivWithinAt)
      (fun a _ b _ hab => by simpa using hab)
      (fun a => fderiv ℝ (heatG a) x (UnforcedLeray.coordinateVector j))
    rw [hImg] at h
    simp only [abs_one, one_smul] at h
    exact h.symm
  -- conclusion
  refine ⟨hK_int, ?_⟩
  rw [kf3TailFDeriv θ hθ x j]
  calc ∫ y : Space, heatG θ (x - y) * UnforcedLeray.PressureAnalysis.newtonGradientKernel j y
      = ∫ y : Space, ∫ b in Ioi (0:ℝ), kf3hnF θ x j y b := hL.symm
    _ = ∫ b in Ioi (0:ℝ), ∫ y : Space, kf3hnF θ x j y b := hswap
    _ = ∫ b in Ioi (0:ℝ), fderiv ℝ (heatG (θ + b)) x (UnforcedLeray.coordinateVector j) := hR
    _ = ∫ a in Ioi θ, fderiv ℝ (heatG a) x (UnforcedLeray.coordinateVector j) := hShift

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
