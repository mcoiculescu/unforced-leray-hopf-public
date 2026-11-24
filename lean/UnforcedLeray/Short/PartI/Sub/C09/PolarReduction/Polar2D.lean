import UnforcedLeray.Short.PartI.Sub.C09.PolarReduction.Radial
import UnforcedLeray.Units.B0010

/-!
# Helper for `polarReduction`: planar pairing with an angular-two function in polar coordinates

For `g` locally integrable on `(0, ∞)` and a continuous planar `M` vanishing on the polar
annulus complement of `[a, b]`,
`∫_{ℝ²} angularTwoField g · M = ∫_{(0,∞)} r g(r) (∫_{-π}^{π} e^{2iθ} M(r cos θ, r sin θ) dθ) dr`
(`polar_pairing`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PolarRed

/-- Integrability of `(r, θ) ↦ r g(r) m(r, θ)` on `(0, ∞) × (-π, π)`. -/
theorem integrableOn_polar (g : ℝ → ℂ) (hg : LocallyIntegrableOn g (Ioi 0)) (m : ℝ × ℝ → ℂ)
    (hm : Continuous m) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ p : ℝ × ℝ, 0 < p.1 → (p.1 < a ∨ b < p.1) → m p = 0) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 * g p.1) * m p) (Ioi 0 ×ˢ Ioo (-π) π)
      (volume.prod volume) := by
  have hK : IsCompact (Icc a b ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hg1 : IntegrableOn (fun r : ℝ => r * g r) (Icc a b) := by
    have h1 : IntegrableOn g (Icc a b) :=
      hg.integrableOn_compact_subset (fun r hr => lt_of_lt_of_le ha hr.1) isCompact_Icc
    exact IntegrableOn.continuousOn_mul Complex.continuous_ofReal.continuousOn h1 isCompact_Icc
  have hg2 : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-π) π) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hprod : Integrable (fun z : ℝ × ℝ => (z.1 * g z.1) * (1 : ℂ))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-π) π))) :=
    Integrable.mul_prod hg1 hg2
  have hKint : IntegrableOn (fun z : ℝ × ℝ => z.1 * g z.1) (Icc a b ×ˢ Icc (-π) π)
      (volume.prod volume) := by
    show Integrable _ ((volume.prod volume).restrict (Icc a b ×ˢ Icc (-π) π))
    rw [← Measure.prod_restrict]
    simpa using hprod
  have hKF : IntegrableOn (fun p : ℝ × ℝ => (p.1 * g p.1) * m p) (Icc a b ×ˢ Icc (-π) π)
      (volume.prod volume) :=
    hKint.mul_continuousOn hm.continuousOn hK
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := measurableSet_Ioi.prod measurableSet_Ioo
  refine hKF.of_forall_sdiff_eq_zero hS ?_
  intro x hx
  have hx1 : 0 < x.1 := hx.1.1
  have hnot : ¬ (x.1 ∈ Icc a b) := by
    intro h
    exact hx.2 ⟨h, Ioo_subset_Icc_self hx.1.2⟩
  have hlt : x.1 < a ∨ b < x.1 := by
    rcases lt_or_ge x.1 a with h | h
    · exact Or.inl h
    · rcases lt_or_ge b x.1 with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨h, h'⟩ hnot
  simp only [hzero x hx1 hlt, mul_zero]

/-- Polar form of the planar pairing `∫ angularTwoField g · M`. -/
theorem polar_pairing (g : ℝ → ℂ) (hg : LocallyIntegrableOn g (Ioi 0)) (M : ℝ × ℝ → ℂ)
    (hM : Continuous M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ r θ : ℝ, 0 < r → (r < a ∨ b < r) → M (pol r θ) = 0) :
    ∫ z, UnforcedLeray.B0010.angularTwoField g z * M z =
      ∫ r in Ioi (0 : ℝ), r * g r * ∫ θ in (-π)..π,
        Complex.exp (2 * Complex.I * (θ : ℂ)) * M (pol r θ) := by
  have hcont : Continuous (fun p : ℝ × ℝ => Complex.exp (2 * Complex.I * (p.2 : ℂ)) *
      M (pol p.1 p.2)) :=
    contDiff_expMode.continuous.mul (hM.comp contDiff_pol.continuous)
  have hint := integrableOn_polar g hg _ hcont ha hab (fun p hp1 hp2 => by
    simp only [hsupp p.1 p.2 hp1 hp2, mul_zero])
  rw [← integral_comp_polarCoord_symm]
  have key : EqOn (fun p : ℝ × ℝ =>
      p.1 • (UnforcedLeray.B0010.angularTwoField g (polarCoord.symm p) * M (polarCoord.symm p)))
      (fun p : ℝ × ℝ => (p.1 * g p.1) *
        (Complex.exp (2 * Complex.I * (p.2 : ℂ)) * M (pol p.1 p.2)))
      polarCoord.target := by
    intro p hp
    dsimp only
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have hsym : polarCoord.symm p = pol p.1 p.2 := by
      rw [polarCoord_symm_apply]
      rfl
    rw [hsym, show UnforcedLeray.B0010.angularTwoField g (pol p.1 p.2) =
        g p.1 * Complex.exp (2 * Complex.I * (p.2 : ℂ)) from
        UnforcedLeray.B0010.angularTwoField_polar g hp1 p.2]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target,
    Measure.volume_eq_prod, setIntegral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  simp only
  rw [integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

end UnforcedLeray.Short.PartI.PolarRed
