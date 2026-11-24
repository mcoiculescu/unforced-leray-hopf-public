import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonInnerRot
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3

/-!
# `NewtonVEquiv`: rotation covariance of the zero-width Newton field (task `PartIII-b:C/srcL/7/6`)

Source of record: `the November 2 reference manuscript`, lines 4776-4782, 4917-4937.
For `x` with `5ν/6 < x₁² + x₂²`, `V_{μ,M}(R_θ x) = R_θ V_{μ,M}(x)`: the inner integral is rotation
covariant for each `t ∈ (0,1]` (`newtonInnerRot`), and the outer `t`-integral is linear, provided
the integrands `t ↦ newtonFam a t x` are integrable on `(0,1]` (`newtonFamMeas`, `newtonFamDom` at
order `0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The outer integrands `t ↦ newtonFam i t x` are integrable on `(0,1]` for `x` in the region. -/
theorem newtonFam_integrable_t (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (hc : 0 < c)
    (hν : 0 < ν) (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M)
    (x : Vec3) (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) (j : Fin 3) :
    Integrable (fun t : ℝ => newtonFam c ν μ χo M j t x) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨s, hs, g, hg, hb⟩ := newtonFamDom c ν μ χo M hc hν hμ hχ hM j 0 x hx
  have hmeas : AEStronglyMeasurable (fun t : ℝ => newtonFam c ν μ χo M j t x)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := (continuousMultilinearCurryFin0 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable
      (newtonFamMeas c ν μ χo M hc hν hμ hχ hM j 0 x hx)
    exact h.congr (Filter.Eventually.of_forall fun t => by simp)
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have h := hb t ht x (mem_of_mem_nhds hs)
  rw [norm_iteratedFDeriv_zero] at h
  exact h

theorem newtonVEquivariant : NewtonVEquivariant := by
  intro c ν μ χo M hc hν hμ hχ hM θ x hx
  have hpt : ∀ i : Fin 3, ∀ t ∈ Ioc (0 : ℝ) 1,
      newtonFam c ν μ χo M i t (rotAx θ x) =
        ∑ a : Fin 3, rotMat θ i a * newtonFam c ν μ χo M a t x := by
    intro i t ht
    simp only [newtonFam]
    rw [newtonInnerRot c ν χo M hc hν hχ hM θ t ht x hx i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  funext i
  simp only [rotAx_apply, newtonV_apply]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => hpt i t ht)]
  rw [integral_finsetSum Finset.univ (fun a _ => (newtonFam_integrable_t c ν μ χo M hc hν hμ hχ hM x hx a).const_mul _)]
  simp only [integral_const_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
