import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalRadialOscillator
import UnforcedLeray.Cons.C01ReferenceChoice.Oscillator

/-!
# Closed Gaussian action pairing on the actual growing mode

Identify the closed oscillator action of the right mode with its classical radial profile, then
use the existing Gaussian pairing formula to identify its adjoint pairing with `kapMode`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.Blueprint.Planar
open UnforcedLeray.ComplexODEC UnforcedLeray.Cons.C01
open MeasureTheory

namespace UnforcedLeray.Cons.G3b

/-- The closed oscillator pairing of the actual right mode with its normalized left mode is the
profile coefficient `kapMode`. -/
theorem closedD_pairing_rightMode_eq_kapMode {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) :
    inner ℂ (qdagMode hF)
      (B0094.D ⟨qMode hF, qMode_mem_Ddomain hF⟩) = kapMode c F := by
  obtain ⟨β₀, hβ₀ne, hMode⟩ := exists_mode_eq_regLog hF
  have hβ : ∀ t, F t = β₀ * regLog c t := fun t => (hMode t).1
  obtain ⟨hD, DF, hDact, df, hfield, hDFae⟩ :=
    PlanarSpectral.exists_Ddomain_of_gaussClass_profile_ae
      (PlanarSpectral.modeVort_ae_eq_modeBeta hβ)
      (PlanarSpectral.gaussClass_angularTwo_of_derivBound
        (contDiff_modeBeta hF.im_ne_zero β₀) (derivBound_modeBeta hF β₀))
      (PlanarSpectral.isAngularTwo_angularTwoField_radialSq (modeBeta c β₀))
      (memLp_modeVort_XG hF)
  have hqrep : (memLp_modeVort_XG hF).toLp (modeVort c F) = qMode hF := by
    apply Lp.ext
    filter_upwards [(memLp_modeVort_XG hF).coeFn_toLp,
      (memLp_of_memXG (memXG_modeVort hF)).coeFn_toLp] with r hr₁ hr₂
    exact hr₁.trans hr₂.symm
  let rawDomain : B0094.D.domain :=
    ⟨(memLp_modeVort_XG hF).toLp (modeVort c F), hD⟩
  let actualDomain : B0094.D.domain := ⟨qMode hF, qMode_mem_Ddomain hF⟩
  have hdomain : rawDomain = actualDomain := by
    apply Subtype.ext
    exact hqrep
  have hDactual : B0094.D actualDomain = DF := by
    calc
      B0094.D actualDomain = B0094.D rawDomain := by
        exact congrArg B0094.D hdomain.symm
      _ = DF := hDact
  have hgauss := PlanarSpectral.gaussianOperator_angularTwoField_radialSq
    (contDiff_modeBeta hF.im_ne_zero β₀)
  let radialD : Profile := fun r => (r : ℂ) ^ 2 *
    (4 * (r ^ 2 : ℝ) * deriv (deriv (modeBeta c β₀)) (r ^ 2) +
      ((r ^ 2 + 12 : ℝ) : ℂ) * deriv (modeBeta c β₀) (r ^ 2) +
      3 * modeBeta c β₀ (r ^ 2))
  have hprofile : B0010.angularTwoField df = B0010.angularTwoField radialD := by
    rw [hfield, hgauss]
  have hDFosc : (DF : ℝ → ℂ) =ᵐ[xGMeasure] oscillatorD (modeVort c F) := by
    filter_upwards [hDFae, B0012.ae_xG_pos] with r hrad hr
    have hfieldr := congrFun hprofile (r, 0)
    rw [B0010.angularTwoField_profile df hr,
      B0010.angularTwoField_profile radialD hr] at hfieldr
    have hpoint := oscillatorD_modeVort_eq_modeBeta_radial hF hβ hr
    exact hrad.trans (hfieldr.trans hpoint.symm)
  let hoscXG : MemXG (oscillatorD (modeVort c F)) :=
    UnforcedLeray.Cons.C01.Osc.memXG_oscillatorD_modeVort hF
  let hmOsc : MemLp (oscillatorD (modeVort c F)) 2 xGMeasure :=
    memLp_of_memXG hoscXG
  have hDrep : B0094.D actualDomain = hmOsc.toLp (oscillatorD (modeVort c F)) := by
    apply Lp.ext
    filter_upwards [hDFosc, hmOsc.coeFn_toLp] with r hrad hosc
    rw [hDactual]
    exact hrad.trans hosc.symm
  have hpair := congrArg (fun x : XG => inner ℂ (qdagMode hF) x) hDrep
  rw [hpair, kapMode, gaussianPairing_eq_inner
    (UnforcedLeray.Cons.C01.Osc.memXG_oscillatorD_modeVort hF) (memXG_adjointMode hF)]
  rfl

end UnforcedLeray.Cons.G3b
