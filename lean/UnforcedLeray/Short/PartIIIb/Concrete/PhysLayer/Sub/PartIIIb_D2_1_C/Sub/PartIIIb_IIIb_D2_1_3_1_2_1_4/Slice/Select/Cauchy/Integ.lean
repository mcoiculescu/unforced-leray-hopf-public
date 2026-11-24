import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props

/-!
# Integrability helpers for the one-slice Laplacian identity (`Cauchy/`)

Shared by `LapDiff.lean`, `WeakDiff.lean`, `SliceEnergy.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

instance holderTriple_two_two : ENNReal.HolderTriple 2 2 1 := by
  have h := ENNReal.HolderTriple.of (2 : ENNReal) 2
  rwa [ENNReal.inv_two_add_inv_two, inv_one] at h

theorem vlap_contDiff {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (lapS θ) := by
  unfold lapS
  refine ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    (hθ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (h1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem vlap_cs {θ : Space → CVec3} (hθ : HasCompactSupport θ) : HasCompactSupport (lapS θ) := by
  have hg : ∀ j : Fin 3, HasCompactSupport (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => HasCompactSupport.fderiv_apply ℝ hθ (EuclideanSpace.single j (1 : ℝ))
  have hh : ∀ j : Fin 3, HasCompactSupport (fun y => fderiv ℝ
      (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => HasCompactSupport.fderiv_apply ℝ (hg j) (EuclideanSpace.single j (1 : ℝ))
  have hsum : lapS θ = ∑ j : Fin 3, (fun y => fderiv ℝ
      (fun z => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))) := by
    funext y
    simp only [lapS, Finset.sum_apply]
  rw [hsum]
  exact HasCompactSupport.finset_sum fun j _ => hh j

/-- Integrability of `∑ᵢ f(y)ᵢ ψᵢ(y)` for `f ∈ L²` and compactly supported continuous `ψᵢ`. -/
theorem integrable_sum_L2 {f : Space → CVec3} (hf : MemLp f 2 volume)
    (ψ : Fin 3 → Space → ℂ) (hψc : ∀ i, Continuous (ψ i)) (hψs : ∀ i, HasCompactSupport (ψ i)) :
    Integrable (fun y => ∑ i : Fin 3, f y i * ψ i y) volume := by
  have hcomp : ∀ i : Fin 3, MemLp (fun y => f y i) 2 volume := fun i =>
    hf.continuousLinearMap_comp (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  exact (hcomp i).integrable_mul ((hψc i).memLp_of_hasCompactSupport (p := 2) (hψs i))

theorem vcomp_cont {θ : Space → CVec3} (hθ : Continuous θ) (i : Fin 3) :
    Continuous (fun y => θ y i) :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hθ

theorem vcomp_cs {θ : Space → CVec3} (hθ : HasCompactSupport θ) (i : Fin 3) :
    HasCompactSupport (fun y => θ y i) :=
  hθ.comp_left (g := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)) (map_zero _)

end UnforcedLeray.Short.PartIIIb.Concrete
