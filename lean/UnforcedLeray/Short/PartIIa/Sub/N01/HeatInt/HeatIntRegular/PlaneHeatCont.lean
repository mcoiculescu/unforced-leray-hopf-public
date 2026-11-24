import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0223.Lift
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `PartII-a:N01/9/1/2/4/3` (helper): joint continuity of the planar heat

For a bounded, uniformly continuous `u`, the map `(θ, x) ↦ planeHeat θ u x` is continuous on
`ℝ × ℝ²`. The heat is written with the unit Gaussian after the dilation `y = √θ z`, so that
`θ ↦ planeHeat θ u x` is `∫ G₁(z) u(x - ι(√(max θ 0) z)) dz` for all `θ`, and continuity follows
from dominated convergence with the integrable bound `M G₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

/-- Dilation of the planar heat: for `θ > 0`, `planeHeat θ u x = ∫ G₁(z) u(x - ι(√θ z)) dz`. -/
theorem planeHeat_scale_eq (θ : ℝ) (hθ : 0 < θ) (u : ℝ × ℝ → UnforcedLeray.B0223.MeridC)
    (x : ℝ × ℝ) :
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

/-- The dilated form of the planar heat, valid for all `θ` (for `θ ≤ 0` it is `u` itself). -/
theorem planeHeat_eq_dilate (u : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (θ : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u x = ∫ z : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        u (x - UnforcedLeray.B0224.planeι (Real.sqrt (max θ 0) • z)) := by
  rcases lt_or_ge 0 θ with h | h
  · rw [max_eq_left h.le]
    exact planeHeat_scale_eq θ h u x
  · have h0 : Real.sqrt (max θ 0) = 0 := by rw [max_eq_right h, Real.sqrt_zero]
    rw [h0, UnforcedLeray.B0224.planeHeat_of_nonpos h u]
    simp only [zero_smul, map_zero, sub_zero]
    rw [integral_smul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) one_pos, one_smul]

theorem planeHeat_jointContinuous (u : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (hb : ∃ M : ℝ, ∀ x, ‖u x‖ ≤ M) (huc : UniformContinuous u) : Continuous (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat p.1 u p.2) := by
  obtain ⟨M, hM⟩ := hb
  have hcont : Continuous u := huc.continuous
  have hK : (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat p.1 u p.2) = fun p =>
      ∫ z : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 1 z •
        u (p.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max p.1 0) • z)) :=
    funext fun p => planeHeat_eq_dilate u p.1 p.2
  rw [hK]
  have hG1 : Continuous (UnforcedLeray.Gaussian.gaussKernel 2 1) :=
    UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1
  have hG1nn : ∀ z : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 z :=
    fun z => UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z
  refine MeasureTheory.continuous_of_dominated
    (bound := fun z => UnforcedLeray.Gaussian.gaussKernel 2 1 z * M)
    (fun p => ?_) (fun p => ae_of_all _ fun z => ?_)
    ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const M)
    (ae_of_all _ fun z => ?_)
  · exact (hG1.smul (hcont.comp (continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp
      (continuous_const_smul _))))).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (hG1nn z)]
    exact mul_le_mul_of_nonneg_left (hM _) (hG1nn z)
  · have h1 : Continuous fun p : ℝ × (ℝ × ℝ) => Real.sqrt (max p.1 0) • z :=
      (Real.continuous_sqrt.comp (continuous_fst.max continuous_const)).smul continuous_const
    have h2 : Continuous fun p : ℝ × (ℝ × ℝ) =>
        p.2 - UnforcedLeray.B0224.planeι (Real.sqrt (max p.1 0) • z) :=
      continuous_snd.sub (UnforcedLeray.B0224.continuous_planeι.comp h1)
    exact Continuous.smul (continuous_const (y := UnforcedLeray.Gaussian.gaussKernel 2 1 z)) (hcont.comp h2)

end UnforcedLeray.Short.PartIIa.N01
