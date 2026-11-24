import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR.Integrable

/-!
# `PartII-b:T10/7/1/1/2/8`: `gl_pairLinL` (linearity of `pairF` in its first slot over phase tests)

Source of record: `the November 2 reference manuscript` lines 1912-1921.
Mirror of `gl_pairLinR`: the integrand `dotL (∑ a_k Φ_k x) (w x)` splits as `∑ a_k dotL (Φ_k x) (w x)`
and each summand is integrable on the phase cell (`integrable_dotL_phaseTest_Yr`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem gl_pairLinL : UnforcedLeray.Short.IIb.GLPairLinL := by
  intro P r Φ w a hP hr hΦ hw
  have : Fact (0 < P) := ⟨hP⟩
  have hI : ∀ k, Integrable (fun x => dotL (Φ k x) (w x)) (volume.restrict (phaseCell P)) :=
    fun k => integrable_dotL_phaseTest_Yr hP hr (hΦ k) hw
  have hEq : ∀ x : ℝ × Space, dotL (∑ k, a k • Φ k x) (w x) = ∑ k, a k * dotL (Φ k x) (w x) := by
    intro x
    simp [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hTot0 : Integrable (fun x => ∑ k, a k * dotL (Φ k x) (w x))
      (volume.restrict (phaseCell P)) :=
    integrable_finset_sum _ (fun k _ => (hI k).const_mul (a k))
  have hTot : Integrable (fun x => dotL (∑ k, a k • Φ k x) (w x))
      (volume.restrict (phaseCell P)) :=
    hTot0.congr (ae_of_all _ fun x => (hEq x).symm)
  have hsum : ∫ x, dotL (∑ k, a k • Φ k x) (w x) ∂(volume.restrict (phaseCell P)) =
      ∑ k, a k * ∫ x, dotL (Φ k x) (w x) ∂(volume.restrict (phaseCell P)) := by
    rw [integral_congr_ae (ae_of_all _ hEq), integral_finset_sum _ (fun k _ => (hI k).const_mul (a k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul]
  have hpk : ∀ k, pairF P (Φ k) w =
      P⁻¹ • ∫ x, dotL (Φ k x) (w x) ∂(volume.restrict (phaseCell P)) :=
    fun k => pairF_eq_restrictedProductIntegral (hI k)
  rw [pairF_eq_restrictedProductIntegral hTot, hsum]
  simp only [hpk]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Complex.real_smul]
  ring

end UnforcedLeray.Short.IIb
