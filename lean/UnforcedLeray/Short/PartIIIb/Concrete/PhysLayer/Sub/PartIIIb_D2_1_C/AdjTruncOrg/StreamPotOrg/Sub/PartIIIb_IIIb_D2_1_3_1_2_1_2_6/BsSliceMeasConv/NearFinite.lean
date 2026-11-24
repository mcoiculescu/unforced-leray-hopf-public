import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HedbergFar
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSDefined
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Almost everywhere finiteness of the near part of `rieszT`

Source `the November 2 reference manuscript` (stream potential, `L² * |w|⁻² → L⁶`).
For `G` measurable with `∫ G² < ∞`, the near part `∫_{B(y,1)} G(z) k(y-z) dz` is finite for a.e. `y`
(Tonelli on `B(0,n) × ℝ³`, using `∫_{B(0,1)} k < ∞`), and the far part is finite for every `y`
by `hedbergFar`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma bsmc_bsK2_measurable : Measurable bsK2 := by
  unfold bsK2
  exact Measurable.ennreal_ofReal (measurable_const.mul (measurable_norm.pow_const 2).inv)

lemma bsmc_ball_iff (y z : Space) : z ∈ ball y (1:ℝ) ↔ y - z ∈ ball (0:Space) (1:ℝ) := by
  rw [mem_ball, dist_eq_norm, mem_ball_zero_iff, norm_sub_rev]

/-- `∫_{B(0,1)} k < ∞` for the kernel `k = bsK2` (`|w|⁻²` is integrable on `B(0,1)` in `ℝ³`). -/
lemma bsmc_kernel_integral_lt_top : ∫⁻ w in ball (0:Space) 1, bsK2 w < ⊤ := by
  have hint : IntegrableOn (fun w : Space => (4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹) (ball (0:Space) 1) := by
    refine integrableOn_ball_of_norm_le_rpow (f := fun w : Space => (4 * Real.pi)⁻¹ * (‖w‖ ^ 2)⁻¹)
      (C := (4 * Real.pi)⁻¹) (α := 2) (r := 1) ?_ ?_ ?_ ?_
    · rw [finrank_space_three]; norm_num
    · rw [finrank_space_three]; norm_num
    · refine ae_of_all _ (fun x => le_of_eq ?_)
      show ‖(4 * Real.pi)⁻¹ * (‖x‖ ^ 2)⁻¹‖ = (4 * Real.pi)⁻¹ * ‖x‖ ^ (-(2:ℝ))
      rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (4 * Real.pi)⁻¹ * (‖x‖ ^ 2)⁻¹),
        Real.rpow_neg (norm_nonneg x), Real.rpow_two]
    · exact (measurable_const.mul (measurable_norm.pow_const 2).inv).aestronglyMeasurable
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun w => by positivity))).mp hint.2
  unfold bsK2
  exact hfin

/-- `x ≤ x² + 1` in `ℝ≥0∞`. -/
lemma bsmc_le_sq_add_one (x : ℝ≥0∞) : x ≤ x ^ 2 + 1 := by
  rcases le_total x 1 with h | h
  · exact h.trans (le_add_of_nonneg_left (by positivity))
  · exact (le_self_pow₀ h two_ne_zero).trans le_self_add

/-- Integrand of the near part as a function of `(y, z)`: `G(z) k(y - z)` when `z ∈ B(y,1)`. -/
def bsmcH (G : Space → ℝ≥0∞) (p : Space × Space) : ℝ≥0∞ :=
  {q : Space × Space | q.2 ∈ ball q.1 (1:ℝ)}.indicator (fun q => G q.2 * bsK2 (q.1 - q.2)) p

lemma bsmcH_measurable (G : Space → ℝ≥0∞) (hG : Measurable G) : Measurable (bsmcH G) := by
  unfold bsmcH
  refine Measurable.indicator ?_ ?_
  · exact (hG.comp measurable_snd).mul (bsmc_bsK2_measurable.comp (measurable_fst.sub measurable_snd))
  · show MeasurableSet {q : Space × Space | dist q.2 q.1 < (1:ℝ)}
    exact measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const

lemma bsmcH_lintegral_eq (G : Space → ℝ≥0∞) (y : Space) :
    ∫⁻ z in ball y (1:ℝ), G z * bsK2 (y - z) = ∫⁻ z, bsmcH G (y, z) := by
  classical
  rw [← lintegral_indicator measurableSet_ball]
  try rfl

lemma bsmcH_lintegral_y_eq (G : Space → ℝ≥0∞) (z : Space) :
    ∫⁻ y, bsmcH G (y, z) = G z * ∫⁻ w in ball (0:Space) 1, bsK2 w := by
  classical
  have hrepr : (fun y : Space => bsmcH G (y, z)) =
      fun y => (ball (0:Space) (1:ℝ)).indicator (fun w => G z * bsK2 w) (y - z) := by
    funext y
    unfold bsmcH
    by_cases h : z ∈ ball y (1:ℝ)
    · have h' := (bsmc_ball_iff y z).mp h
      simp only [Set.indicator_apply, Set.mem_setOf_eq, h, h', if_true]
    · have h' : y - z ∉ ball (0:Space) (1:ℝ) := fun h'' => h ((bsmc_ball_iff y z).mpr h'')
      simp only [Set.indicator_apply, Set.mem_setOf_eq, h, h', if_false]
  rw [hrepr]
  rw [lintegral_sub_right_eq_self ((ball (0:Space) (1:ℝ)).indicator (fun w => G z * bsK2 w)) z]
  rw [lintegral_indicator measurableSet_ball]
  rw [lintegral_const_mul _ bsmc_bsK2_measurable]

lemma bsmcH_lintegral_z_le (G : Space → ℝ≥0∞) (hG : Measurable G) (n : ℕ) (z : Space) :
    ∫⁻ y in ball (0:Space) n, bsmcH G (y, z)
      ≤ (ball (0:Space) ((n:ℝ) + 1)).indicator
          (fun z => G z * ∫⁻ w in ball (0:Space) 1, bsK2 w) z := by
  classical
  by_cases hz : z ∈ ball (0:Space) ((n:ℝ) + 1)
  · rw [Set.indicator_apply, if_pos hz]
    calc ∫⁻ y in ball (0:Space) n, bsmcH G (y, z) ≤ ∫⁻ y, bsmcH G (y, z) :=
          setLIntegral_le_lintegral _ _
      _ = G z * ∫⁻ w in ball (0:Space) 1, bsK2 w := bsmcH_lintegral_y_eq G z
  · rw [Set.indicator_apply, if_neg hz]
    have hzero : ∀ᵐ y ∂(volume.restrict (ball (0:Space) n)), bsmcH G (y, z) = 0 := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hnot : ¬ (z ∈ ball y (1:ℝ)) := by
        intro hmem
        rw [mem_ball, dist_eq_norm] at hmem
        rw [mem_ball_zero_iff] at hy
        rw [mem_ball_zero_iff] at hz
        have htri : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
          have := norm_add_le (z - y) y
          rwa [sub_add_cancel] at this
        exact hz (by linarith)
      unfold bsmcH
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hnot, if_false]
    exact le_of_eq (by rw [lintegral_congr_ae hzero, lintegral_zero])

lemma bsmcH_lintegral_bound (G : Space → ℝ≥0∞) (hG : Measurable G) (n : ℕ) :
    ∫⁻ z, ∫⁻ y in ball (0:Space) n, bsmcH G (y, z)
      ≤ (∫⁻ z in ball (0:Space) ((n:ℝ) + 1), G z) * ∫⁻ w in ball (0:Space) 1, bsK2 w := by
  calc ∫⁻ z, ∫⁻ y in ball (0:Space) n, bsmcH G (y, z)
      ≤ ∫⁻ z, (ball (0:Space) ((n:ℝ) + 1)).indicator
          (fun z => G z * ∫⁻ w in ball (0:Space) 1, bsK2 w) z :=
        lintegral_mono (fun z => bsmcH_lintegral_z_le G hG n z)
    _ = ∫⁻ z in ball (0:Space) ((n:ℝ) + 1), G z * ∫⁻ w in ball (0:Space) 1, bsK2 w :=
        lintegral_indicator measurableSet_ball _
    _ = (∫⁻ z in ball (0:Space) ((n:ℝ) + 1), G z) * ∫⁻ w in ball (0:Space) 1, bsK2 w :=
        lintegral_mul_const _ hG

lemma bsmc_lintegral_ball_lt_top (G : Space → ℝ≥0∞) (hG2 : ∫⁻ z, G z ^ 2 < ⊤) (r : ℝ) :
    ∫⁻ z in ball (0:Space) r, G z < ⊤ := by
  have h1 : ∫⁻ z in ball (0:Space) r, G z ≤ ∫⁻ z in ball (0:Space) r, (G z ^ 2 + 1) :=
    lintegral_mono fun z => bsmc_le_sq_add_one (G z)
  have h2 : ∫⁻ z in ball (0:Space) r, (G z ^ 2 + 1)
      = (∫⁻ z in ball (0:Space) r, G z ^ 2) + volume (ball (0:Space) r) := by
    rw [lintegral_add_right _ measurable_const, lintegral_one, Measure.restrict_apply_univ]
  have h3 : ∫⁻ z in ball (0:Space) r, G z ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hG2
  exact lt_of_le_of_lt (h1.trans (le_of_eq h2))
    (ENNReal.add_lt_top.mpr ⟨h3, measure_ball_lt_top⟩)

/-- Near part finite for almost every `y` (Tonelli on `B(0,n) × ℝ³`). -/
lemma bsmc_near_ae (G : Space → ℝ≥0∞) (hG : Measurable G) (hG2 : ∫⁻ z, G z ^ 2 < ⊤) :
    ∀ᵐ y : Space, ∫⁻ z in ball y (1:ℝ), G z * bsK2 (y - z) < ⊤ := by
  have hN : Measurable (fun y : Space => ∫⁻ z, bsmcH G (y, z)) :=
    (bsmcH_measurable G hG).lintegral_prod_right'
  have hfin : ∀ n : ℕ, ∫⁻ y in ball (0:Space) n, ∫⁻ z, bsmcH G (y, z) < ⊤ := by
    intro n
    have hswap := lintegral_lintegral_swap (μ := volume.restrict (ball (0:Space) n))
      (ν := volume) (f := fun y z => bsmcH G (y, z))
      (bsmcH_measurable G hG).aemeasurable
    rw [hswap]
    exact lt_of_le_of_lt (bsmcH_lintegral_bound G hG n)
      (ENNReal.mul_lt_top (bsmc_lintegral_ball_lt_top G hG2 _) bsmc_kernel_integral_lt_top)
  have hae : ∀ n : ℕ, ∀ᵐ y : Space, y ∈ ball (0:Space) n → ∫⁻ z, bsmcH G (y, z) < ⊤ := by
    intro n
    have h1 := ae_lt_top hN (hfin n).ne
    rw [ae_restrict_iff' measurableSet_ball] at h1
    exact h1
  have hall : ∀ᵐ y : Space, ∀ n : ℕ, y ∈ ball (0:Space) n → ∫⁻ z, bsmcH G (y, z) < ⊤ :=
    ae_all_iff.mpr hae
  filter_upwards [hall] with y hy
  obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
  have hyN : ∫⁻ z, bsmcH G (y, z) < ⊤ := hy n (mem_ball_zero_iff.mpr hn)
  rw [bsmcH_lintegral_eq]
  exact hyN

/-- A.e. finiteness of the Biot-Savart potential of a scalar `G` with `∫ G² < ∞`. -/
lemma bsmc_rieszT_ae (G : Space → ℝ≥0∞) (hG : Measurable G) (hG2 : ∫⁻ z, G z ^ 2 < ⊤) :
    ∀ᵐ y : Space, rieszT G y < ⊤ := by
  filter_upwards [bsmc_near_ae G hG hG2] with y hy
  have hfar := hedbergFar G hG y 1 one_pos
  have hfar_lt : (∫⁻ z, G z ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((4 * Real.pi * 1) ^ (-(1 / 2 : ℝ)))
      < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG2.ne) ENNReal.ofReal_lt_top
  have hsplit : rieszT G y
      = (∫⁻ z in ball y (1:ℝ), G z * bsK2 (y - z)) + ∫⁻ z in (ball y (1:ℝ))ᶜ, G z * bsK2 (y - z) :=
    (lintegral_add_compl (fun z => G z * bsK2 (y - z)) measurableSet_ball).symm
  rw [hsplit]
  exact ENNReal.add_lt_top.mpr ⟨hy, lt_of_le_of_lt hfar hfar_lt⟩

end UnforcedLeray.Short.PartIIIb.Concrete
