import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackRealIdentity.AdjTest

/-!


Source `the November 2 reference manuscript`
lines 1431-1441 (reversed window, `θ = 1 - e^{-t}`, `x = e^{-t/2} y`).  Analogue of
`WinBack.real_identity` (`Tasks/F03cWindowBackEquation.lean`).  The weak second derivatives of
`u_c = adjWindowField χ τ₀ W c` are tested against `adjLapTest τ₀ a`
(`BackRealIdentity/AdjTest.lean`), whose chart values are `e^{3t/2} a` and `e^{5t/2} Δa`; the
weights `e^{-5t/2}` of the reversed chart cancel exactly on the window, where `χ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.Short.PartIIa.WinBack

theorem adjBackRealIdentity : AdjBackRealIdentity := by
  intro r _ hrt P _ w W hW χ hχ τ₀ ν c D2 hD2 a ha hsup
  have hφ : IsSTTest (adjLapTest τ₀ a : PS 3 → ℝ) := isSTTest_adjLapTest ha hsup
  have hMem : MemLp (adjWindowField χ τ₀ W c) r volume := adjWindowField_memLp hrt hW hχ τ₀ c
  have hMemD : MemLp (fun X => ∑ i, D2 c i i X) r volume :=
    memLp_finsetSum Finset.univ fun i _ => (hD2 i).1
  have hI1 : ∀ i, Integrable (fun X => adjWindowField χ τ₀ W c X *
      ((sD2 i i (adjLapTest τ₀ a) X : ℝ) : ℂ)) := fun i =>
    integrable_of_memLp_mul hMem
      (Complex.continuous_ofReal.comp ((hφ.dirD (sdir i)).dirD (sdir i)).continuous)
      (((hφ.dirD (sdir i)).dirD (sdir i)).2.comp_left Complex.ofReal_zero)
  have hI2 : ∀ i, Integrable (fun X => D2 c i i X * ((adjLapTest τ₀ a X : ℝ) : ℂ)) := fun i =>
    integrable_of_memLp_mul (hD2 i).1 (Complex.continuous_ofReal.comp hφ.continuous)
      (hφ.2.comp_left Complex.ofReal_zero)
  have hsum : ∫ X, adjWindowField χ τ₀ W c X * ((sLap (adjLapTest τ₀ a) X : ℝ) : ℂ) =
      ∫ X, (∑ i, D2 c i i X) * ((adjLapTest τ₀ a X : ℝ) : ℂ) := by
    have e1 : ∀ X, adjWindowField χ τ₀ W c X * ((sLap (adjLapTest τ₀ a) X : ℝ) : ℂ) =
        ∑ i, adjWindowField χ τ₀ W c X * ((sD2 i i (adjLapTest τ₀ a) X : ℝ) : ℂ) := by
      intro X
      simp only [sLap, Complex.ofReal_sum, Finset.mul_sum]
    have e2 : ∀ X, (∑ i, D2 c i i X) * ((adjLapTest τ₀ a X : ℝ) : ℂ) =
        ∑ i, D2 c i i X * ((adjLapTest τ₀ a X : ℝ) : ℂ) := by
      intro X
      simp only [Finset.sum_mul]
    simp_rw [e1, e2]
    rw [integral_finset_sum _ fun i _ => hI1 i, integral_finset_sum _ fun i _ => hI2 i]
    exact Finset.sum_congr rfl fun i _ => (hD2 i).2 _ hφ
  have hL := integral_adjField_sLap hχ τ₀ W c ha hsup
  have hR := integral_adjWindowLap_eq ν τ₀ (fun c X => ∑ i, D2 c i i X) c hsup
  have hshift1 : ∫ p : ℝ × Space, W p c * ((ν * sLap a p : ℝ) : ℂ) =
      (ν : ℂ) * ∫ p : ℝ × Space, W p c * ((sLap a p : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  rw [hshift1, ← hL, hsum]
  exact hR.symm

end UnforcedLeray.Short.PartIIa
