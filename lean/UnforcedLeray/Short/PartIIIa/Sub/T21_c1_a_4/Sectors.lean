import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Of

/-!
# `PartIII-a:T21/c1/a/4/2`: the angular sectors of `q = h(r) e^{2 i theta}`

Source: `the November 2 reference manuscript` lines 593-601.
Proves `SeedSectors` (defined in `Of.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ComplexConjugate

namespace UnforcedLeray.Short.IIIa.SeedSectorsAux

/-- For `r > 0`, the sector `n` of `h(|x|) e^{2 i arg x}` is `h r` when `n = 2` and `0` otherwise. -/
lemma angularSector_seedPlanar (h : ℝ → ℂ) (n : ℤ) (r : ℝ) (hr : 0 < r) :
    UnforcedLeray.Planar.NUE.Polar.angularSector
        (UnforcedLeray.Short.PartI.seedPlanar h) n r =
      if n = 2 then h r else 0 := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hnorm : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  -- pointwise value of the integrand
  have hpt : ∀ θ : ℝ,
      UnforcedLeray.Short.PartI.seedPlanar h ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((n : ℂ) * θ * Complex.I)) =
        h r * Complex.exp (((2 - n : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
    intro θ
    have hdiv : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
        ((‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ : ℝ) : ℂ)
          = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hnorm θ]
      exact mul_div_cancel_left₀ _ hrC
    unfold UnforcedLeray.Short.PartI.seedPlanar UnforcedLeray.Planar.NUE.Ang.ofProfile
      UnforcedLeray.Planar.NUE.Ang.angPhase
    rw [hdiv, hnorm θ, zpow_ofNat, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold UnforcedLeray.Planar.NUE.Polar.angularSector
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  by_cases hn : n = 2
  · have one : ∀ θ : ℝ, Complex.exp (((2 - n : ℤ) : ℂ) * Complex.I * (θ : ℂ)) = 1 := by
      intro θ
      rw [hn]
      simp
    rw [if_pos hn]
    simp only [one, mul_one, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    push_cast
    field_simp
  · rw [if_neg hn]
    have h2 : (2 - n : ℤ) ≠ 0 := sub_ne_zero.2 (fun e => hn e.symm)
    have hc : ((2 - n : ℤ) : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.2 h2) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have key : Complex.exp (((2 - n : ℤ) : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show ((2 - n : ℤ) : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)
          = ((2 - n : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [key]
    simp

end UnforcedLeray.Short.IIIa.SeedSectorsAux

theorem seedSectors_proof : UnforcedLeray.Short.IIIa.SeedSectors := by
  unfold UnforcedLeray.Short.IIIa.SeedSectors
  intro h r hr
  have A := UnforcedLeray.Short.IIIa.SeedSectorsAux.angularSector_seedPlanar h 2 r hr
  have B := UnforcedLeray.Short.IIIa.SeedSectorsAux.angularSector_seedPlanar h (-2) r hr
  have C := UnforcedLeray.Planar.NUE.Ang.angularSector_conj
    (UnforcedLeray.Short.PartI.seedPlanar h) (-2) r
  have D := UnforcedLeray.Planar.NUE.Ang.angularSector_conj
    (UnforcedLeray.Short.PartI.seedPlanar h) 2 r
  norm_num at A B C D
  refine ⟨by rw [A], by rw [B], ?_, ?_⟩
  · rw [C, B]
    simp
  · rw [D, A]

