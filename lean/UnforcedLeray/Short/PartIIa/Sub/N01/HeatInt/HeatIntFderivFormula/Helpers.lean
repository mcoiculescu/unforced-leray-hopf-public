import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0223.Lift
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `PartII-a:N01/9/1/2/4/4` helpers for `HeatIntFderivFormula`

Generic facts about the cylinder heat `planeHeat` for an arbitrary normed space of values:
zero, a uniform bound, and the dilated form together with joint continuity in a parameter.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01.HIFD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem planeHeat_zero_fun (θ : ℝ) :
    UnforcedLeray.B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : E)) = fun _ => 0 := by
  by_cases h : 0 < θ
  · funext x
    rw [UnforcedLeray.B0224.planeHeat_of_pos h]
    simp
  · exact UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h) _

theorem planeHeat_norm_le {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → E} {B : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) (x : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ g x‖ ≤ B := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  have hint : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y * B) :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const B
  have hle : ∀ y : UnforcedLeray.Gaussian.Euc 2,
      ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y • g (x - UnforcedLeray.B0224.planeι y)‖
        ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y * B := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
    exact mul_le_mul_of_nonneg_left (hB _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
  refine (norm_integral_le_of_norm_le hint (ae_of_all _ hle)).trans (le_of_eq ?_)
  rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, one_mul]

/-- Dilation of the planar heat for any value space, for `θ > 0`. -/
theorem planeHeat_scale_eq_gen (θ : ℝ) (hθ : 0 < θ) (u : ℝ × ℝ → E) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u x = ∫ z : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z)) := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  have hs0 : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hs2 : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hc := MeasureTheory.Measure.integral_comp_smul (volume : Measure (UnforcedLeray.Gaussian.Euc 2))
    (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y))
    (Real.sqrt θ)
  rw [UnforcedLeray.Gaussian.finrank_euc] at hc
  have hpt : ∀ z : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ (Real.sqrt θ • z) •
          u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z))
        = (Real.sqrt θ ^ 2)⁻¹ • (UnforcedLeray.Gaussian.gaussKernel 2 1 z •
          u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z))) := by
    intro z
    have h1 := UnforcedLeray.Gaussian.gaussKernel_scale (d := 2) (lam := Real.sqrt θ) (θ := 1)
      hs0 one_pos z
    rw [mul_one, hs2] at h1
    have hpow : Real.sqrt θ ^ (-((2 : ℕ) : ℝ)) = (Real.sqrt θ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hs0.le]
      norm_num
    rw [h1, hpow, mul_smul]
  have h3 : (Real.sqrt θ ^ 2)⁻¹ • ∫ z : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 1 z • u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z))
      = (Real.sqrt θ ^ 2)⁻¹ • ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) := by
    calc (Real.sqrt θ ^ 2)⁻¹ • ∫ z : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 1 z • u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z))
        = ∫ z : UnforcedLeray.Gaussian.Euc 2, (Real.sqrt θ ^ 2)⁻¹ •
          (UnforcedLeray.Gaussian.gaussKernel 2 1 z • u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z))) :=
          (integral_smul _ _).symm
      _ = ∫ z : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ (Real.sqrt θ • z) •
            u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • z)) :=
          integral_congr_ae (ae_of_all _ fun z => (hpt z).symm)
      _ = |(Real.sqrt θ ^ 2)⁻¹| • ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) := hc
      _ = (Real.sqrt θ ^ 2)⁻¹ • ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) := by
          rw [abs_of_pos (inv_pos.2 (pow_pos hs0 2))]
  have hne : (Real.sqrt θ ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hs0.ne')
  exact (smul_right_injective _ hne h3).symm

/-- Dilated form of the planar heat for all `θ` (for `θ ≤ 0` it is `u` itself). -/
theorem planeHeat_eq_dilate_gen (θ : ℝ) (u : ℝ × ℝ → E) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u x = ∫ z : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        u (x - UnforcedLeray.B0224.planeι (Real.sqrt (max θ 0) • z)) := by
  rcases lt_or_ge 0 θ with h | h
  · rw [max_eq_left h.le]
    exact planeHeat_scale_eq_gen θ h u x
  · have h0 : Real.sqrt (max θ 0) = 0 := by rw [max_eq_right h, Real.sqrt_zero]
    rw [h0, UnforcedLeray.B0224.planeHeat_of_nonpos h u]
    simp only [zero_smul, map_zero, sub_zero]
    rw [integral_smul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) one_pos, one_smul]

/-- Joint continuity in the parameter `t` of `t ↦ planeHeat (θ t) (u t) x` for a jointly
continuous, uniformly bounded family of value fields. -/
theorem continuous_planeHeat_param {θ : ℝ → ℝ} (hθc : Continuous θ) {u : ℝ → ℝ × ℝ → E}
    (hjc : Continuous (fun p : ℝ × (ℝ × ℝ) => u p.1 p.2)) {M : ℝ} (hM : ∀ t w, ‖u t w‖ ≤ M)
    (x : ℝ × ℝ) :
    Continuous (fun t => UnforcedLeray.B0224.planeHeat (θ t) (u t) x) := by
  have hK : (fun t => UnforcedLeray.B0224.planeHeat (θ t) (u t) x) = fun t =>
      ∫ z : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        u t (x - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ t) 0) • z)) :=
    funext fun t => planeHeat_eq_dilate_gen (θ t) (u t) x
  rw [hK]
  have hG1nn : ∀ z : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 z :=
    fun z => UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z
  have hcomp : ∀ z : UnforcedLeray.Gaussian.Euc 2, Continuous fun t : ℝ =>
      u t (x - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ t) 0) • z)) := by
    intro z
    have h1 : Continuous fun t : ℝ => Real.sqrt (max (θ t) 0) • z :=
      (Real.continuous_sqrt.comp ((hθc).max continuous_const)).smul continuous_const
    have h2 : Continuous fun t : ℝ =>
        x - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ t) 0) • z) :=
      continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp h1)
    exact hjc.comp (continuous_id.prodMk h2)
  refine MeasureTheory.continuous_of_dominated
    (bound := fun z => UnforcedLeray.Gaussian.gaussKernel 2 1 z * M)
    (fun t => ?_) (fun t => ae_of_all _ fun z => ?_)
    ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const M)
    (ae_of_all _ fun z => ?_)
  · have hz : Continuous fun z : UnforcedLeray.Gaussian.Euc 2 =>
        u t (x - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ t) 0) • z)) := by
      have h1 : Continuous fun z : UnforcedLeray.Gaussian.Euc 2 =>
          Real.sqrt (max (θ t) 0) • z :=
        continuous_id.const_smul (Real.sqrt (max (θ t) 0))
      have h2 : Continuous fun z : UnforcedLeray.Gaussian.Euc 2 =>
          x - UnforcedLeray.B0224.planeι (Real.sqrt (max (θ t) 0) • z) :=
        continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp h1)
      exact (hjc.comp (continuous_const.prodMk h2))
    exact (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul hz |>.aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (hG1nn z)]
    exact mul_le_mul_of_nonneg_left (hM _ _) (hG1nn z)
  · exact continuous_const.smul (hcomp z)

end UnforcedLeray.Short.PartIIa.N01.HIFD
