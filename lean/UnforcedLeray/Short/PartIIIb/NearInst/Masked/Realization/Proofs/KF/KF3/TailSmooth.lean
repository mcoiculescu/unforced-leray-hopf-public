import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# `kf3TailSmooth : KF3TailSmooth` (source 3597-3601)

For `θ > 0`, `heatTail θ = ∫_θ^∞ G_a da` is `C^∞` on all of `ℝ³` (the origin included).

Route (real variable, to avoid vector-valued measurability): `heatTail θ x = S θ 0 ‖x‖²` with
`S θ k r = ∫_{(θ,∞)} ((-(4a)⁻¹)^k (4πa)^{-3/2}) e^{-r/(4a)} da`.  Each `S θ k` is differentiable
with derivative `S θ (k+1)` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated on
`|r| ≤ R` by a constant times `(4πa)^{-3/2}`), so `S θ 0` is `C^n` for every `n` by induction on
`n` (`contDiff_succ_iff_deriv`), and `‖·‖²` is smooth (`contDiff_norm_sq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

/-- The scalar profile `S θ k r = ∫_{(θ,∞)} ((-(4a)⁻¹)^k (4πa)^{-3/2}) e^{-r/(4a)} da`. -/
def kf3tsF (θ : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ∫ a in Ioi θ, ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))

theorem kf3ts_bound_integrable (θ : ℝ) (hθ : 0 < θ) (C : ℝ) :
    IntegrableOn (fun a : ℝ => C * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) (Ioi θ) := by
  have h1 : IntegrableOn (fun a : ℝ => (4 * Real.pi) ^ (-3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ)) (Ioi θ) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) hθ).const_mul _
  have h2 : IntegrableOn (fun a : ℝ => C * ((4 * Real.pi) ^ (-3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ))) (Ioi θ) :=
    h1.const_mul C
  refine h2.congr_fun (fun a ha => ?_) measurableSet_Ioi
  have ha0 : 0 < a := lt_trans hθ ha
  show C * ((4 * Real.pi) ^ (-3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ)) = C * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)
  rw [Real.mul_rpow (x := 4 * Real.pi) (y := a) (by positivity) ha0.le]

theorem kf3ts_hd (a c r : ℝ) :
    HasDerivAt (fun r => c * Real.exp (-r / (4 * a))) (c * (Real.exp (-r / (4 * a)) * (-1 / (4 * a)))) r := by
  have h := (((hasDerivAt_id r).neg).div_const (4 * a)).exp.const_mul c
  exact h

theorem kf3ts_dom (θ R : ℝ) (hθ : 0 < θ) (hR : 0 ≤ R) (k j : ℕ) (hj : j ≤ k + 1)
    (a r : ℝ) (ha : θ < a) (hr : |r| ≤ R) :
    ‖((-(4 * a)⁻¹) ^ j * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))‖ ≤
      ((1 + (4 * θ)⁻¹) ^ (k + 1) * Real.exp (R / (4 * θ))) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
  have ha0 : 0 < a := lt_trans hθ ha
  have hP : 0 ≤ (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hE : 0 < Real.exp (-r / (4 * a)) := Real.exp_pos _
  have hL : (4 * a)⁻¹ ≤ (4 * θ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hM : 1 ≤ 1 + (4 * θ)⁻¹ := by
    have : 0 ≤ (4 * θ)⁻¹ := by positivity
    linarith
  have hpow : ‖(-(4 * a)⁻¹) ^ j‖ ≤ (1 + (4 * θ)⁻¹) ^ (k + 1) := by
    rw [norm_pow, norm_neg, Real.norm_of_nonneg (by positivity)]
    calc ((4 * a)⁻¹) ^ j ≤ (1 + (4 * θ)⁻¹) ^ j :=
          pow_le_pow_left₀ (by positivity) (by linarith) j
      _ ≤ (1 + (4 * θ)⁻¹) ^ (k + 1) := pow_le_pow_right₀ hM hj
  have hexp : Real.exp (-r / (4 * a)) ≤ Real.exp (R / (4 * θ)) := by
    apply Real.exp_le_exp.2
    have h1 : -r ≤ R := le_trans (neg_le_abs r) hr
    have h2 : -r / (4 * a) ≤ R / (4 * a) := div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : R / (4 * a) ≤ R / (4 * θ) := div_le_div_of_nonneg_left hR (by positivity) (by linarith)
    linarith
  calc ‖((-(4 * a)⁻¹) ^ j * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))‖
      = ‖(-(4 * a)⁻¹) ^ j‖ * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (-r / (4 * a)) := by
        rw [norm_mul, norm_mul, Real.norm_of_nonneg hP, Real.norm_of_nonneg hE.le]
    _ ≤ (1 + (4 * θ)⁻¹) ^ (k + 1) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) * Real.exp (R / (4 * θ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpow hP) hexp hE.le (by positivity)
    _ = ((1 + (4 * θ)⁻¹) ^ (k + 1) * Real.exp (R / (4 * θ))) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
        ring

/-- **Differentiation of the scalar profile**: `∂_r S θ k = S θ (k+1)`. -/
theorem kf3ts_hasDeriv (θ : ℝ) (hθ : 0 < θ) (k : ℕ) (r0 : ℝ) :
    HasDerivAt (kf3tsF θ k) (kf3tsF θ (k + 1) r0) r0 := by
  set R : ℝ := |r0| + 1 with hRdef
  have hR : 0 ≤ R := by positivity
  have hbdInt := kf3ts_bound_integrable θ hθ ((1 + (4 * θ)⁻¹) ^ (k + 1) * Real.exp (R / (4 * θ)))
  have hmeasF : ∀ r : ℝ, Measurable (fun a : ℝ =>
      ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))) :=
    fun r => by fun_prop
  have hmeasF' : ∀ r : ℝ, Measurable (fun a : ℝ =>
      ((-(4 * a)⁻¹) ^ (k + 1) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))) :=
    fun r => by fun_prop
  have hF_int : Integrable (fun a : ℝ =>
      ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r0 / (4 * a)))
      (volume.restrict (Ioi θ)) := by
    refine Integrable.mono' hbdInt (hmeasF r0).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha => ?_)
    exact kf3ts_dom θ R hθ hR k k (Nat.le_succ k) a r0 ha (by rw [hRdef]; linarith [le_abs_self r0])
  have h_bound : ∀ᵐ a ∂(volume.restrict (Ioi θ)), ∀ r ∈ Metric.ball r0 1,
      ‖((-(4 * a)⁻¹) ^ (k + 1) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))‖ ≤
        ((1 + (4 * θ)⁻¹) ^ (k + 1) * Real.exp (R / (4 * θ))) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha r hr => ?_)
    have hr' : |r| ≤ R := by
      have h := Metric.mem_ball.1 hr
      rw [Real.dist_eq] at h
      rw [hRdef]
      linarith [abs_sub_abs_le_abs_sub r r0]
    exact kf3ts_dom θ R hθ hR k (k + 1) le_rfl a r ha hr'
  have h_diff : ∀ᵐ a ∂(volume.restrict (Ioi θ)), ∀ r ∈ Metric.ball r0 1,
      HasDerivAt (fun r : ℝ =>
        ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a)))
        (((-(4 * a)⁻¹) ^ (k + 1) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a))) r := by
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun a ha r _ => ?_)
    have h := kf3ts_hd a ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) r
    convert h using 1
    ring
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi θ))
    (F := fun r a => ((-(4 * a)⁻¹) ^ k * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a)))
    (F' := fun r a => ((-(4 * a)⁻¹) ^ (k + 1) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ)) * Real.exp (-r / (4 * a)))
    (x₀ := r0)
    (bound := fun a : ℝ => ((1 + (4 * θ)⁻¹) ^ (k + 1) * Real.exp (R / (4 * θ))) * (4 * Real.pi * a) ^ (-3 / 2 : ℝ))
    (s := Metric.ball r0 1) (Metric.ball_mem_nhds r0 one_pos)
    (Filter.Eventually.of_forall (fun r => (hmeasF r).aestronglyMeasurable))
    hF_int (hmeasF' r0).aestronglyMeasurable h_bound hbdInt h_diff
  unfold kf3tsF
  exact hd

theorem kf3ts_contDiff (θ : ℝ) (hθ : 0 < θ) (n : ℕ) : ∀ k : ℕ, ContDiff ℝ n (kf3tsF θ k) := by
  induction n with
  | zero =>
    intro k
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 (fun r => (kf3ts_hasDeriv θ hθ k r).continuousAt)
  | succ n ih =>
    intro k
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_deriv.2 ⟨fun r => (kf3ts_hasDeriv θ hθ k r).differentiableAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · have hder : deriv (kf3tsF θ k) = kf3tsF θ (k + 1) :=
        funext (fun r => (kf3ts_hasDeriv θ hθ k r).deriv)
      rw [hder]
      exact ih (k + 1)

/-- **Leaf: the heat tail is smooth for positive time** (source 3597-3601). -/
theorem kf3TailSmooth : KF3TailSmooth := by
  intro θ hθ
  have hfun : heatTail θ = fun x : Space => kf3tsF θ 0 (‖x‖ ^ 2) := by
    funext x
    unfold heatTail heatG kf3tsF
    simp only [pow_zero, one_mul]
  rw [hfun]
  exact (contDiff_infty.2 (fun n => kf3ts_contDiff θ hθ n 0)).comp (contDiff_norm_sq ℝ)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
