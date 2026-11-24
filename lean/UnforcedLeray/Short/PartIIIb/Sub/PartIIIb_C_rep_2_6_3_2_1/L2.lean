import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D

/-!
# `extIntPointDeriv` (`PartIII-b:C/rep/2/6/3/2/1/2`)

Source `the November 2 reference manuscript` lines 3603-3610, 4171-4200.
For `p = (s,z)` with `s ≠ τ`, the shifted integrand is eventually a finite sum of
`Kd(t-s)` (when `s < τ`) or eventually zero (when `s > τ`).  The `h`-derivative of `Kd` at
`h = τ - s > 0` exists by `gkerHasDerivH`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem extIntPointDeriv : ExtIntPointDeriv := by
  intro ν μ hν T τ y i ⟨s, z⟩ hp
  change s ≠ τ at hp
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have hpos : 0 < τ - s := sub_pos.mpr hlt
    have hKd : ∀ j k : Fin 3, HasDerivAt (fun h' => Kd ν μ h' y z i j k)
        (kdDh ν μ (τ - s) y z i j k) (τ - s) := by
      intro j k
      have h1 := gkerHasDerivH ν (μ : ℂ) hν (τ - s) hpos y z i j k
      have h2 := gkerHasDerivH ν ((μ : ℂ) + 1) hν (τ - s) hpos y z i j k
      exact (h1.sub h2).differentiableAt.hasDerivAt
    have hf : HasDerivAt (fun t => ∑ j : Fin 3, ∑ k : Fin 3,
        Kd ν μ (t - s) y z i j k * ((T s z j k : ℝ) : ℂ))
        (∑ j : Fin 3, ∑ k : Fin 3, kdDh ν μ (τ - s) y z i j k * ((T s z j k : ℝ) : ℂ)) τ := by
      apply HasDerivAt.fun_sum
      intro j _
      apply HasDerivAt.fun_sum
      intro k _
      exact ((hKd j k).comp_sub_const τ s).mul_const _
    have hcongr : (fun t => extInt T (Kd ν μ) t y i (s, z)) =ᶠ[nhds τ]
        fun t => ∑ j : Fin 3, ∑ k : Fin 3,
          Kd ν μ (t - s) y z i j k * ((T s z j k : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hlt] with t ht
      have hst : s ∈ Iio t := show s < t from ht
      simp only [extInt, Set.indicator_of_mem hst]
    have hval : extInt T (kdDh ν μ) τ y i (s, z) =
        ∑ j : Fin 3, ∑ k : Fin 3, kdDh ν μ (τ - s) y z i j k * ((T s z j k : ℝ) : ℂ) := by
      simp only [extInt, Set.indicator_of_mem (show s ∈ Iio τ from hlt)]
    rw [hval]
    exact hf.congr_of_eventuallyEq hcongr
  · have hcongr : (fun t => extInt T (Kd ν μ) t y i (s, z)) =ᶠ[nhds τ] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hgt] with t ht
      have hst : s ∉ Iio t := fun h => absurd (show s < t from h) (not_lt.mpr (le_of_lt ht))
      simp only [extInt, Set.indicator_of_notMem hst]
    have hval : extInt T (kdDh ν μ) τ y i (s, z) = 0 := by
      have hst : s ∉ Iio τ := fun h => absurd (show s < τ from h) (not_lt.mpr (le_of_lt hgt))
      simp only [extInt, Set.indicator_of_notMem hst]
    rw [hval]
    exact (hasDerivAt_const τ (0 : ℂ)).congr_of_eventuallyEq hcongr

end UnforcedLeray.Short.PartIIIb.Concrete
