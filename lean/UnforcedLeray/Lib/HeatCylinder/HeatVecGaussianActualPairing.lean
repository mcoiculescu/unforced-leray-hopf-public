import UnforcedLeray.Lib.HeatCylinder.CenteredHeatProjectionConditional
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeComponents
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianConvolutionPairing

/-!
# Pairing identity for actual centered heat

On smooth periodic inputs, the centered quotient of the actual B0284 heat has the same pairings
as the actual Gaussian average of centered translations. The proof passes through the literal
Gaussian convolution field and the existing centered/normalized quotient maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (cellμ L2v)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)

private theorem isQPeriodic_cylSmooth_local {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) : IsQPeriodic c T := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact hT.periodic z

/-- Centered-to-normalized transport returns the normalized class of a smooth periodic field. -/
private theorem centeredVecToNormalized_cylSmooth {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hTm : MemLp T 2 (cellμ c)) :
    centeredVecToNormalizedCLM hc (hTm.toLp T) =
      (memLp_iterD_vec_cylSmooth_normalized hc hT []).toLp T := by
  let x := hTm.toLp T
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT []
  have hbase : centeredVecL2Rep x =ᵐ[cellμ c] T := by
    filter_upwards [centeredVecL2Rep_ae x, hTm.coeFn_toLp] with z hrep hTz
    exact hrep.trans hTz
  have hper := isQPeriodic_cylSmooth_local hT
  have hglobal : centeredVecL2PeriodicRep hc x =ᵐ[volume] T := by
    have hlift := centeredPerLift_congr_ae hc hbase
    have hself := centeredPerLift_eq_self_of_periodic hc hper
    filter_upwards [hlift] with z hz
    exact hz.trans (congrFun hself z)
  have hnorm : centeredVecL2PeriodicRep hc x =ᵐ[cellMeasure c] T := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hglobal)
  change (memLp_centeredVecL2PeriodicRep_normalized hc x).toLp
      (centeredVecL2PeriodicRep hc x) = hm.toLp T
  exact MemLp.toLp_congr (memLp_centeredVecL2PeriodicRep_normalized hc x) hm hnorm

/-- The actual centered heat and the centered Gaussian shift average agree when tested against
any smooth compact-axial periodic fields. -/
theorem inner_centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM_of_cylSmooth
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U)
    (hTm : MemLp T 2 (cellμ c)) (hUm : MemLp U 2 (cellμ c)) :
    inner ℝ (centeredHeatVecL2CLM hc θ (hTm.toLp T)) (hUm.toLp U) =
      inner ℝ (centeredGaussianShiftAverageCLM hc hθ (hTm.toLp T)) (hUm.toLp U) := by
  let hmN := memLp_iterD_vec_cylSmooth_normalized hc hT []
  let xin := hmN.toLp T
  have hin : centeredVecToNormalizedCLM hc (hTm.toLp T) = xin :=
    centeredVecToNormalized_cylSmooth hc hT hTm
  have hmeasure (c : ℝ) :
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = cellμ c := by
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ, cellμ]
  have hconvMem : MemLp (heatVecConvolution θ T) 2 (cellμ c) := by
    have hfield := memLp_heatVecH3Field hc hθ hT UnforcedLeray.Sob.Idx.zero
    rw [← hmeasure c]
    have hfieldEq : heatVecH3Field (c := c) (θ := θ) T
        UnforcedLeray.Sob.Idx.zero = heatVecConvolution θ T := by
      funext z
      rfl
    rw [hfieldEq] at hfield
    exact hfield
  have hout : centeredHeatVecL2CLM hc θ (hTm.toLp T) = hconvMem.toLp
      (heatVecConvolution θ T) := by
    change centeredVecOfNormalizedVec hc (heatVecL2CLM hc θ
      (centeredVecToNormalizedCLM hc (hTm.toLp T))) = _
    rw [hin]
    exact centeredVecOfNormalizedVec_heatVecL2CLM_iterD hc hθ hT
      UnforcedLeray.Sob.Idx.zero
  rw [hout]
  rw [UnforcedLeray.Cyl.inner_toLp_eq hconvMem hUm]
  exact (integral_heatVecConvolution_pairing_eq_centeredGaussianShiftAverageCLM
    hc hθ hT hU hTm hUm)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.inner_centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM_of_cylSmooth
