import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2_2

/-!
# `PhaseIntScale` (task `PartIII-b:C/near/pins/3/2/2/3`)

Source `the November 2 reference manuscript` 4139-4146 (dilation `x = ε y`).

`phaseInt P F = P⁻¹ ∫_{(0,P]} ∫_y F(t,y)`; the physical measure is `dx dτ` on one period, so
Fubini (`integral_prod_symm`) swaps to the `τ` outer order and the dilation `y ↦ ε⁻¹ y` in `ℝ³`
(`Measure.integral_comp_smul`, `|(ε⁻¹)^3|⁻¹ = ε^3`) gives the factor `ε^3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem phaseIntScale : PhaseIntScale := by
  intro p F hint
  have hε : 0 < p.ε := p.ε_pos
  have hmeas : UnforcedLeray.B0220.physMeasure p.ε p.c =
      (volume.restrict (univ : Set Space)).prod (volume.restrict (Ioc (0 : ℝ) (2 * p.ε * p.c))) := by
    unfold UnforcedLeray.B0220.physMeasure UnforcedLeray.B0220.physDomain
    rw [Measure.volume_eq_prod Space ℝ, Measure.prod_restrict]
  have hint' : Integrable (fun y : Space × ℝ => F (y.2, p.ε⁻¹ • y.1))
      ((volume.restrict (univ : Set Space)).prod (volume.restrict (Ioc (0 : ℝ) (2 * p.ε * p.c)))) := by
    rw [← hmeas]
    exact hint
  have hkey : ∀ t : ℝ, ∫ x : Space, F (t, p.ε⁻¹ • x) = (p.ε ^ 3) • ∫ y : Space, F (t, y) := by
    intro t
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space) (fun y : Space => F (t, y)) p.ε⁻¹
    rw [finrank_euclideanSpace_fin] at h
    rw [h, abs_of_pos (by positivity : (0 : ℝ) < ((p.ε⁻¹) ^ 3)⁻¹)]
    congr 1
    field_simp
  rw [hmeas, integral_prod_symm _ hint']
  simp only [Measure.restrict_univ]
  simp only [hkey]
  rw [integral_smul]
  unfold phaseInt
  rw [Complex.real_smul]
  have hεne : p.ε ≠ 0 := hε.ne'
  have hcne : p.c ≠ 0 := p.c_pos.ne'
  simp only [Complex.real_smul]
  push_cast
  field_simp

end UnforcedLeray.Short.PartIIIb.NearInst
