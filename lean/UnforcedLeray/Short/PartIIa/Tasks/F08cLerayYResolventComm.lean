import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Short.PartIIa.Tasks.F08bLerayYPhaseTComm
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Lib.LerayC.Phase

/-!
# Part II-a, task `PartII-a:F08/3`: the Leray projection commutes with the body resolvent `R_μ`

Source `the November 2 reference manuscript` lines 1498-1500. The resolvent is the
Laplace integral `R_μ f = ∫₀^∞ e^{-μt} 𝒯_ν(t) f dt` (F01). Integrability of the integrand on
`(0, ∞)` is re-derived as in `bodyResolvent_exists_of` (`Sub/F01.lean`), using the unconditional
sharp decay `freeCSharpDecay_of normLiftExists_proof freeCPointwiseLe_proof`. Then the bounded
linear map `𝐏` commutes with the Bochner integral (`ContinuousLinearMap.integral_comp_comm`), and
pointwise in `t` it commutes with `𝒯_ν(t)` by `lerayYPhaseTComm_proof` (F08/2), with the scalar
`e^{-μt}` passing through `map_smul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`PartII-a:F08/3`** (source 1498-1500): the Leray projection commutes with the Laplace
integral `R_μ` of the phase semigroup `𝒯_ν`. -/
theorem lerayYResolventComm_proof : LerayYResolventComm := by
  intro r hr h1 h3 P hP ν hν μ hμ Rm hRm f
  have hq : r ≠ ⊤ := ne_top_of_lt h3
  have hdec : FreeCSharpDecay := freeCSharpDecay_of normLiftExists_proof freeCPointwiseLe_proof
  set a : ℝ := μ.re + gammaR r with ha
  have hnorm : ∀ t : ℝ, 0 ≤ t → ∀ g : Yq P r,
      ‖Complex.exp (-(μ * t)) • B0421.phaseT hq ν t g‖ ≤ Real.exp (-a * t) * ‖g‖ := by
    intro t ht g
    rw [norm_smul, Complex.norm_exp]
    have hre : (-(μ * (t : ℂ))).re = -(μ.re * t) := by simp
    rw [hre]
    have h2 : ‖B0421.phaseT hq ν t g‖ ≤ Real.exp (-B0418.gammaExp r * t) * ‖g‖ :=
      ((B0421.phaseT hq ν t).le_opNorm g).trans
        (mul_le_mul_of_nonneg_right
          ((B0421.norm_phaseT_le hq ν t).trans (hdec r hq ν t ht)) (norm_nonneg _))
    calc Real.exp (-(μ.re * t)) * ‖B0421.phaseT hq ν t g‖
        ≤ Real.exp (-(μ.re * t)) * (Real.exp (-B0418.gammaExp r * t) * ‖g‖) := by gcongr
      _ = Real.exp (-a * t) * ‖g‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [ha, gammaR, B0418.gammaExp]
        ring
  have hint : IntegrableOn
      (fun t : ℝ => Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f) (Ioi (0 : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f)
        (Ioi (0 : ℝ)) := by
      have hc1 : Continuous fun t : ℝ => Complex.exp (-(μ * (t : ℂ))) := by fun_prop
      exact hc1.continuousOn.smul
        ((B0421.continuousOn_phaseT hq hν.le f).mono Ioi_subset_Ici_self)
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine Integrable.mono' (hexp.mul_const ‖f‖) (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => hnorm t (le_of_lt ht) f)
  -- pointwise commutation of 𝐏 with the scalar-weighted phase operator
  have hcomm : ∀ t : ℝ,
      lerayY P r h1 hq (Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f) =
        Complex.exp (-(μ * t)) • B0421.phaseT hq ν t (lerayY P r h1 hq f) := by
    intro t
    rw [map_smul, lerayYPhaseTComm_proof r h1 hq P ν t f]
  -- 𝐏 commutes with the Bochner integral
  have hL : lerayY P r h1 hq (∫ t in Ioi (0 : ℝ),
      Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f) =
      ∫ t in Ioi (0 : ℝ),
        lerayY P r h1 hq (Complex.exp (-(μ * t)) • B0421.phaseT hq ν t f) :=
    (ContinuousLinearMap.integral_comp_comm (lerayY P r h1 hq) hint).symm
  rw [hRm f, hRm (lerayY P r h1 hq f), hL]
  exact integral_congr_ae (Eventually.of_forall fun t => hcomm t)

end UnforcedLeray.Short.PartIIa
