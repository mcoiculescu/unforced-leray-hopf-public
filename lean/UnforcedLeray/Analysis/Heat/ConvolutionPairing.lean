import UnforcedLeray.Analysis.Heat.ConvolutionL2
import UnforcedLeray.Analysis.Heat.Translation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual Hilbert pairings of whole-space convolution

The scalar integrand needed to test convolution against an L² field is jointly
integrable. This is proved using the L¹ kernel and both squared L² field norms.
Fubini then gives the genuine pairing identity, with the sharp outer absolute
bound from the isometry of translations and Hilbert Cauchy--Schwarz.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

/-- The actual scalar product integrand, with output coordinate first. -/
def convolutionPairingIntegrand (k : Space → ℝ) (f g : L2Space)
    (z : Space × Space) : ℝ :=
  k z.2 * inner ℝ (f (z.1 - z.2)) (g z.1)

/-- Joint measurability follows from the concrete Haar translation map. -/
theorem convolutionPairing_aestronglyMeasurable {k : Space → ℝ}
    (hk : Integrable k volume) (f g : L2Space) :
    AEStronglyMeasurable (convolutionPairingIntegrand k f g)
      ((volume : Measure Space).prod volume) := by
  have h : AEStronglyMeasurable
      (fun z : Space × Space => inner ℝ (k z.2 • f (z.1-z.2)) (g z.1))
      ((volume : Measure Space).prod volume) :=
    (convolution_joint_aestronglyMeasurable hk.aestronglyMeasurable
      (Lp.aestronglyMeasurable f)).inner (Lp.aestronglyMeasurable g).comp_fst
  apply h.congr
  filter_upwards [] with z
  simp only [convolutionPairingIntegrand, real_inner_smul_left]

/-- The kernel-inner-product expression is genuinely integrable on R³×R³. -/
theorem convolutionPairing_integrable {k : Space → ℝ}
    (hk : Integrable k volume) (f g : L2Space) :
    Integrable (convolutionPairingIntegrand k f g)
      ((volume : Measure Space).prod volume) := by
  have hf2 : Integrable (fun x : Space => ‖f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg2 : Integrable (fun x : Space => ‖g x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hfirst : Integrable (fun z : Space × Space => ‖k z.2‖ * ‖f (z.1-z.2)‖ ^ 2)
      ((volume : Measure Space).prod volume) :=
    hk.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf2
  have hsecond := hg2.mul_prod hk.norm
  apply (hfirst.fun_add hsecond).mono' (convolutionPairing_aestronglyMeasurable hk f g)
  filter_upwards [] with z
  change ‖k z.2 * inner ℝ (f (z.1-z.2)) (g z.1)‖ ≤
    ‖k z.2‖ * ‖f (z.1-z.2)‖ ^ 2 + ‖g z.1‖ ^ 2 * ‖k z.2‖
  rw [norm_mul]
  have hb : ‖f (z.1-z.2)‖ * ‖g z.1‖ ≤ ‖f (z.1-z.2)‖ ^ 2 + ‖g z.1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f (z.1-z.2)‖ - ‖g z.1‖),
      mul_nonneg (norm_nonneg (f (z.1-z.2))) (norm_nonneg (g z.1))]
  calc
    ‖k z.2‖ * ‖inner ℝ (f (z.1-z.2)) (g z.1)‖ ≤
        ‖k z.2‖ * (‖f (z.1-z.2)‖ * ‖g z.1‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖k z.2‖ * (‖f (z.1-z.2)‖ ^ 2 + ‖g z.1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

/-- The integral of a translated pointwise pairing equals the actual Hilbert pairing. -/
theorem inner_translation_eq_integral (y : Space) (f g : L2Space) :
    inner ℝ (translation y f) g = ∫ x : Space, inner ℝ (f (x-y)) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translation_ae y f] with x hx
  rw [hx]

/-- The outer pairing integral is integrable, including signed kernels. -/
theorem convolutionPairing_outer_integrable {k : Space → ℝ}
    (hk : Integrable k volume) (f g : L2Space) :
    Integrable (fun y : Space => k y * (∫ x : Space, inner ℝ (f (x-y)) (g x))) volume := by
  simpa only [convolutionPairingIntegrand, integral_const_mul] using
    (convolutionPairing_integrable hk f g).integral_prod_right

/-- A sharp absolute-integral estimate for the outer pairing. -/
theorem convolutionPairing_outer_norm_bound {k : Space → ℝ}
    (hk : Integrable k volume) (f g : L2Space) :
    (∫ y : Space, ‖k y * (∫ x : Space, inner ℝ (f (x-y)) (g x))‖) ≤
      (∫ y : Space, ‖k y‖) * ‖f‖ * ‖g‖ := by
  have hpoint (y : Space) :
      ‖k y * (∫ x : Space, inner ℝ (f (x-y)) (g x))‖ ≤ ‖k y‖ * (‖f‖ * ‖g‖) := by
    rw [norm_mul, ← inner_translation_eq_integral]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [norm_translation] using norm_inner_le_norm (translation y f) g)
      (norm_nonneg _)
  calc
    _ ≤ ∫ y : Space, ‖k y‖ * (‖f‖ * ‖g‖) :=
      integral_mono (convolutionPairing_outer_integrable hk f g).norm
        (hk.norm.mul_const _) hpoint
    _ = _ := by rw [integral_mul_const]; ring

/-- Fubini identifies the actual L² convolution operator with the translation pairing. -/
theorem inner_convolutionOperator_eq_integral {k : Space → ℝ}
    (hk : Integrable k volume) (f g : L2Space) :
    inner ℝ (convolutionOperator k hk f) g =
      ∫ y : Space, k y * (∫ x : Space, inner ℝ (f (x-y)) (g x)) := by
  rw [L2.inner_def]
  calc
    (∫ x : Space, inner ℝ ((convolutionOperator k hk f) x) (g x)) =
        ∫ x : Space, inner ℝ (convolution k f x) (g x) := by
      apply integral_congr_ae
      filter_upwards [convolutionToL2_rep k hk f] with x hx
      simp only [convolutionOperator_apply, hx]
    _ = ∫ x : Space, ∫ y : Space, k y * inner ℝ (f (x-y)) (g x) := by
      apply integral_congr_ae
      filter_upwards [ae_integrable_convolution hk (Lp.memLp f)] with x hx
      change inner ℝ (∫ y : Space, k y • f (x-y)) (g x) = _
      calc
        _ = inner ℝ (g x) (∫ y : Space, k y • f (x-y)) := real_inner_comm _ _
        _ = ∫ y : Space, inner ℝ (g x) (k y • f (x-y)) := (integral_inner hx (g x)).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [real_inner_smul_right, real_inner_comm (g x) (f (x-y))]
    _ = ∫ y : Space, ∫ x : Space, k y * inner ℝ (f (x-y)) (g x) :=
      integral_integral_swap (convolutionPairing_integrable hk f g)
    _ = _ := by simp only [integral_const_mul]

end UnforcedLeray.Heat
