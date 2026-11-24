import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.PlaneHeatCont

/-!
# `PartII-a:N01/9/1/2/4/6/2/3` (helper): continuity of the planar heat in a parameter

Source `the November 2 reference manuscript`
lines 3373-3383.  For a jointly continuous, bounded `G : ℝ × ℝ² → MeridC` and a continuous
`T : ℝ → ℝ`, the map `σ ↦ planeHeat (T σ) (G (σ, ·)) x` is continuous.  The dilated Gaussian form
`planeHeat_eq_dilate` puts the parameter inside the integrand, and dominated convergence with the
bound `G₁(z) K` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

theorem hgiPlaneHeatContSigma : UnforcedLeray.Short.PartIIa.N01.HGIPlaneHeatContSigma := by
  intro G K hGc hGK T hT x
  have hK : (fun σ : ℝ => UnforcedLeray.B0224.planeHeat (T σ) (fun w => G (σ, w)) x) =
      fun σ : ℝ => ∫ z : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 1 z •
          G (σ, x - UnforcedLeray.B0224.planeι (Real.sqrt (max (T σ) 0) • z)) :=
    funext fun σ => planeHeat_eq_dilate (fun w => G (σ, w)) (T σ) x
  rw [hK]
  have hG1nn : ∀ z : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 1 z :=
    fun z => UnforcedLeray.Gaussian.gaussKernel_nonneg one_pos z
  refine MeasureTheory.continuous_of_dominated
    (bound := fun z => UnforcedLeray.Gaussian.gaussKernel 2 1 z * K)
    (fun σ => ?_) (fun σ => ae_of_all _ fun z => ?_)
    ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const K)
    (ae_of_all _ fun z => ?_)
  · -- measurability in `z` for fixed `σ`
    exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul
      (hGc.comp (continuous_const.prodMk (continuous_const.sub
        (UnforcedLeray.B0224.continuous_planeι.comp (continuous_const_smul _)))))).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (hG1nn z)]
    exact mul_le_mul_of_nonneg_left (hGK _) (hG1nn z)
  · -- continuity in `σ` for fixed `z`
    have h1 : Continuous fun σ : ℝ => Real.sqrt (max (T σ) 0) • z :=
      (Real.continuous_sqrt.comp (hT.max continuous_const)).smul continuous_const
    have h2 : Continuous fun σ : ℝ =>
        (σ, x - UnforcedLeray.B0224.planeι (Real.sqrt (max (T σ) 0) • z)) :=
      continuous_id.prodMk (continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp h1))
    exact Continuous.smul (continuous_const (y := UnforcedLeray.Gaussian.gaussKernel 2 1 z))
      (hGc.comp h2)

end UnforcedLeray.Short.PartIIa.N01
