import UnforcedLeray.Short.PartI.Sub.PartI_S09_2
import UnforcedLeray.Lib.PlanarSectors.Green
import UnforcedLeray.Units.B0011
import UnforcedLeray.Cons.L2.CanonicalBranch.Bridge
import UnforcedLeray.Cons.C01ReferenceChoice.Adjoint

/-!
# Part I, task `PartI:S09/2/1` (`GreenTwoSmooth`): smoothness of `greenN 2`

Source: `the November 2 reference manuscript`
lines 606-609.

For `h` in `L²(xG)` and smooth on `(0,∞)`, `greenN 2 h = R h` on `(0,∞)`
(`B0011.R`, the explicit Green inverse `-(1/4)[r⁻² ∫₀^r s³h + r² ∫_r^∞ s⁻¹h]`).
The first integral is a primitive of the smooth function `s³h`, and the second is
a constant minus a primitive of `s⁻¹h`; both are smooth on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- A primitive `r ↦ ∫_a^r f` of a smooth `f` on `(0,∞)`, locally integrable from `a`,
is smooth on `(0,∞)`. -/
theorem greenTwo_contDiffOn_integral {f : ℝ → ℂ} {a : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hint : ∀ r ∈ Ioi (0 : ℝ), IntervalIntegrable f volume a r) :
    ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in a..r, f s) (Ioi 0) := by
  have hcont : ContinuousOn f (Ioi 0) := hf.continuousOn
  have hd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => ∫ s in a..u, f s) (f r) r :=
    fun r hr => intervalIntegral.integral_hasDerivAt_right (hint r hr)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi r hr)
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hr))
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (hd r hr).differentiableAt.differentiableWithinAt, ?_⟩
  exact hf.congr fun r hr => (hd r hr).deriv

theorem greenTwoSmooth_proof : GreenTwoSmooth := by
  intro h hh hs
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) :=
    hs.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hw : B0011.WProf h :=
    UnforcedLeray.Cons.C01.wprof_of_memXG (UnforcedLeray.Cons.G3b.memXG_of_memLp hm hh)
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  -- `r ↦ r⁻²` and `r ↦ r²` on `(0,∞)`
  have hsq : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ 2) (Ioi 0) := (hc.pow 2).contDiffOn
  have hinv2 : ContDiffOn ℝ ∞ (fun r : ℝ => ((r : ℂ) ^ 2)⁻¹) (Ioi 0) :=
    hsq.inv fun r hr => by
      have hr' : (0 : ℝ) < r := hr
      exact pow_ne_zero 2 (by exact_mod_cast hr'.ne')
  -- primitive of `s³ h`
  have hA : ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * h s) (Ioi 0) :=
    greenTwo_contDiffOn_integral ((hc.pow 3).contDiffOn.mul hs)
      (fun r hr => (hw.integrable_R_parts hr).1)
  -- primitive of `s⁻¹ h`
  have hinv : ContDiffOn ℝ ∞ (fun s : ℝ => (s : ℂ)⁻¹) (Ioi 0) :=
    hc.contDiffOn.inv fun s hs' => by
      have hs0 : (0 : ℝ) < s := hs'
      exact_mod_cast hs0.ne'
  have hg : ContDiffOn ℝ ∞ (fun s : ℝ => (s : ℂ)⁻¹ * h s) (Ioi 0) := hinv.mul hs
  have hC : ContDiffOn ℝ ∞ (fun r : ℝ => ∫ s in (1 : ℝ)..r, (s : ℂ)⁻¹ * h s) (Ioi 0) := by
    refine greenTwo_contDiffOn_integral hg (fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    have hmin : (0 : ℝ) < min 1 r := lt_min one_pos hr'
    have hI := (hw.integrable_R_parts hmin).2
    rw [intervalIntegrable_iff]
    exact hI.mono_set (fun x hx => (Set.mem_Ioc.mp hx).1)
  -- the closed form of `R h` on `(0,∞)`
  have hK : ContDiffOn ℝ ∞ (fun r : ℝ =>
      -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * h s) +
        (r : ℂ) ^ 2 * ((∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * h s) -
          ∫ s in (1 : ℝ)..r, (s : ℂ)⁻¹ * h s))) (Ioi 0) :=
    contDiffOn_const.mul
      ((hinv2.mul hA).add ((hsq.mul (contDiffOn_const.sub hC))))
  have hEq : ∀ r ∈ Ioi (0 : ℝ), B0011.R h r =
      -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * h s) +
        (r : ℂ) ^ 2 * ((∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * h s) -
          ∫ s in (1 : ℝ)..r, (s : ℂ)⁻¹ * h s)) := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have hB : (∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * h s) - (∫ s in Ioi r, (s : ℂ)⁻¹ * h s) =
        ∫ s in (1 : ℝ)..r, (s : ℂ)⁻¹ * h s :=
      intervalIntegral.integral_Ioi_sub_Ioi' (hw.integrable_R_parts zero_lt_one).2
        (hw.integrable_R_parts hr').2
    have hBr : (∫ s in Ioi r, (s : ℂ)⁻¹ * h s) =
        (∫ s in Ioi (1 : ℝ), (s : ℂ)⁻¹ * h s) - ∫ s in (1 : ℝ)..r, (s : ℂ)⁻¹ * h s := by
      linear_combination -hB
    rw [B0011.R, hBr]
  have hR : ContDiffOn ℝ ∞ (fun r : ℝ => B0011.R h r) (Ioi 0) :=
    hK.congr fun r hr => hEq r hr
  refine hR.congr fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  exact Planar.greenN_two_eq_R hw hr'

end UnforcedLeray.Short.PartI
