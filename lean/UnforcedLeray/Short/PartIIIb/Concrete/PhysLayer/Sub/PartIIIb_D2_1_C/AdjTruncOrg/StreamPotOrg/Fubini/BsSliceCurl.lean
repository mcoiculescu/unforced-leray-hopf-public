import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsPairIntegrable
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsDecayL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsFubiniSwap
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelCurlId
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsGradFieldSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsGradFieldDecay
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsGradField
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Slice curl identity (BSSliceCurl)

Source `the November 2 reference manuscript` lines 1351-1362 (`curl psi = Phi`).

For a solenoidal slice `f in L^2`, a smooth compactly supported `Theta`, and `A = bsCurlS Theta`:
`int A . bsSlice f = int f . (int K(y-z) x A(y) dy)` (`bsFubiniSwap`), the kernel identity
`int K(y-z) x curl Theta(y) dy = Theta(z) + G(z)` with `G(z) = int div Theta(y) K(y-z) dy`
(`bsKernelCurlId`), and `int f . G = 0` (`bsGradField`) with `h = bsDivS Theta`.
Integrability of `z |-> f(z) . Theta(z)` and `z |-> f(z) . G(z)` is by Cauchy-Schwarz type
bounds (`MemLp.integrable_mul`) using `bsGradFieldDecay` and `bsDecayL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

theorem bsSliceCurl : BSSliceCurl := by
  intro f hf hsol Θ hΘ hΘc
  have hDsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ Θ) :=
    (contDiff_infty_iff_fderiv.mp hΘ).2
  have hD : Continuous (fderiv ℝ Θ) := hDsm.continuous
  have hdir : ∀ v : Space, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ Θ y v) :=
    fun v => (ContinuousLinearMap.apply ℝ CVec3 v).contDiff.comp hDsm
  have hdotc : Continuous (fun p : CVec3 × CVec3 => dotL p.1 p.2) :=
    (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ).continuous₂
  -- continuity and compact support of the spatial curl
  have hA : Continuous (bsCurlS Θ) := by
    unfold bsCurlS
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact crossC_continuous'.comp
      (continuous_const.prodMk ((hdir (EuclideanSpace.single j (1 : ℝ))).continuous))
  have hc0 : ∀ c : CVec3, crossC c 0 = 0 := by
    intro c
    ext i
    fin_cases i <;> simp [crossC]
  have hAc : HasCompactSupport (bsCurlS Θ) :=
    (hΘc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Space →L[ℝ] CVec3 =>
        ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ)) (L (EuclideanSpace.single j (1 : ℝ))))
      (by simp [hc0])
  -- smoothness and compact support of the spatial divergence
  have hdivsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bsDivS Θ) := by
    unfold bsDivS
    refine ContDiff.sum (fun j _ => ?_)
    exact ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp
      (hdir (EuclideanSpace.single j (1 : ℝ)))
  have hdivc : HasCompactSupport (bsDivS Θ) :=
    (hΘc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Space →L[ℝ] CVec3 => ∑ j : Fin 3, (L (EuclideanSpace.single j (1 : ℝ))) j)
      (by simp)
  -- the swap
  have hsw := bsFubiniSwap (bsCurlS Θ) hA hAc f hf
  rw [hsw]
  -- the gradient field G(z) = int div Theta(y) K(y-z) dy is continuous
  obtain ⟨hgsm, hgeq⟩ := bsGradFieldSmooth (bsDivS Θ) hdivsm hdivc
  have hGc : Continuous (fun z : Space => ∫ y : Space, bsDivS Θ y • bsKernel (y - z)) := by
    have h1 := bsGradS_continuous hgsm
    convert h1 using 1
    funext z
    exact (hgeq z).symm
  -- integrability of z |-> f(z) . Theta(z)
  have hΘ2 : MemLp Θ 2 volume := hΘ.continuous.memLp_of_hasCompactSupport hΘc
  have hint_a : Integrable (fun z : Space => dotL (f z) (Θ z)) volume := by
    have hprod : Integrable (fun z : Space => ‖f z‖ * ‖Θ z‖) volume :=
      hf.norm.integrable_mul hΘ2.norm
    refine Integrable.mono' (hprod.const_mul ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖) ?_ ?_
    · exact hdotc.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => dotL a b)
        hf.aestronglyMeasurable hΘ.continuous.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      calc ‖dotL (f z) (Θ z)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖f z‖ * ‖Θ z‖ :=
            bsDotL_bound _ _
        _ = ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * (‖f z‖ * ‖Θ z‖) := by ring
  -- integrability of z |-> f(z) . G(z)
  have hG_int : Integrable
      (fun z : Space => dotL (f z) (∫ y : Space, bsDivS Θ y • bsKernel (y - z))) volume := by
    obtain ⟨C, hC⟩ := bsGradFieldDecay (bsDivS Θ) hdivsm hdivc
    have hdec : MemLp (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) 2 volume := bsDecayL2
    have hw : Integrable (fun z : Space => ‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) volume :=
      hf.norm.integrable_mul hdec
    refine Integrable.mono' (hw.const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C)) ?_ ?_
    · exact hdotc.comp_aestronglyMeasurable₂ (g := fun a b : CVec3 => dotL a b)
        hf.aestronglyMeasurable hGc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have hGz := (hC z).2
      calc ‖dotL (f z) (∫ y : Space, bsDivS Θ y • bsKernel (y - z))‖
          ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖f z‖ *
              ‖∫ y : Space, bsDivS Θ y • bsKernel (y - z)‖ := bsDotL_bound _ _
        _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖f z‖ * (C * (1 + ‖z‖ ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hGz (by positivity)
        _ = (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C) * (‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) := by ring
  -- pointwise kernel identity and splitting
  have hstep : ∀ z : Space,
      dotL (f z) (∫ y : Space, crossC (bsKernel (y - z)) (bsCurlS Θ y))
        = dotL (f z) (Θ z) + dotL (f z) (∫ y : Space, bsDivS Θ y • bsKernel (y - z)) := by
    intro z
    rw [bsKernelCurlId Θ hΘ hΘc z, map_add]
  simp only [hstep]
  rw [integral_add hint_a hG_int, bsGradField f hf hsol (bsDivS Θ) hdivsm hdivc, add_zero]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => bsDotL_comm _ _))

end UnforcedLeray.Short.PartIIIb.Concrete
