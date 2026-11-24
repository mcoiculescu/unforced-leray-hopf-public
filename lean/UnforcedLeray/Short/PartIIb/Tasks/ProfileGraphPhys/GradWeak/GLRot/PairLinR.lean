import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR.Integrable

/-!
# `PartII-b:T10/7/1/1/2/7`: `gl_pairLinR` (linearity of `pairF` in its second slot over `Y_r`)

Source of record: `the November 2 reference manuscript` lines 1912-1921.
For a phase test `Φ` and fields `u_k ∈ Y_r` (`r > 1`), each `dotL (Φ x) (u_k x)` is integrable on the
phase cell (`integrable_dotL_phaseTest_Yr`), so the finite sum splits under the integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem gl_pairLinR : UnforcedLeray.Short.IIb.GLPairLinR := by
  intro P r Φ u a hP hr hΦ hu
  have hPos : (0 : ℝ) < P := hP
  have : Fact (0 < P) := ⟨hP⟩
  have hI : ∀ k, Integrable (fun x => dotL (Φ x) (u k x)) (volume.restrict (phaseCell P)) :=
    fun k => integrable_dotL_phaseTest_Yr hP hr hΦ (hu k)
  have hEq : ∀ x : ℝ × Space, dotL (Φ x) (∑ k, a k • u k x) = ∑ k, a k * dotL (Φ x) (u k x) := by
    intro x
    simp [map_sum, map_smul, smul_eq_mul]
  have hTot0 : Integrable (fun x => ∑ k, a k * dotL (Φ x) (u k x))
      (volume.restrict (phaseCell P)) :=
    integrable_finset_sum _ (fun k _ => (hI k).const_mul (a k))
  have hTot : Integrable (fun x => dotL (Φ x) (∑ k, a k • u k x))
      (volume.restrict (phaseCell P)) :=
    hTot0.congr (ae_of_all _ fun x => (hEq x).symm)
  have hsum : ∫ x, dotL (Φ x) (∑ k, a k • u k x) ∂(volume.restrict (phaseCell P)) =
      ∑ k, a k * ∫ x, dotL (Φ x) (u k x) ∂(volume.restrict (phaseCell P)) := by
    rw [integral_congr_ae (ae_of_all _ hEq), integral_finset_sum _ (fun k _ => (hI k).const_mul (a k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul]
  have hpk : ∀ k, pairF P Φ (u k) =
      P⁻¹ • ∫ x, dotL (Φ x) (u k x) ∂(volume.restrict (phaseCell P)) :=
    fun k => pairF_eq_restrictedProductIntegral (hI k)
  rw [pairF_eq_restrictedProductIntegral hTot, hsum]
  simp only [hpk]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Complex.real_smul]
  ring

end UnforcedLeray.Short.IIb
