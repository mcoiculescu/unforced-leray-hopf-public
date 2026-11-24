import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A real vector `x` has vanishing complexification iff `x = 0`. -/
theorem realC_eq_zero_iff_D (x : Space) : B0412.realC x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have h1 := congrArg (fun v : CVec3 => v i) h
    simp only [B0412.realC_apply, PiLp.zero_apply, Complex.ofReal_eq_zero] at h1
    simpa using h1
  · rintro rfl
    ext i
    simp [B0412.realC_apply]

theorem fwuLiftInj {c γ ν ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) :
    FWULiftInj c γ ν ε := by
  intro d hd
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  -- the lift vanishes volume-a.e. on `ℝ × ℝ³`
  have hl0 : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), liftFun ε⁻¹ c (d : Chart → Merid) x = 0 := by
    filter_upwards [hd] with x hx
    have hx' : B0412.realC (Nv ε⁻¹ (perExt c (d : Chart → Merid)) x.1 x.2) = 0 := hx
    have hNv := (realC_eq_zero_iff_D _).1 hx'
    unfold liftFun
    rw [hNv, smul_zero]
  -- the period-averaged phase measure is absolutely continuous to volume
  have hac : phaseμ (2 * c / ε⁻¹) ≪ (volume : Measure (ℝ × Space)) := by
    have h1 : ((ENNReal.ofReal (2 * c / ε⁻¹))⁻¹ •
        (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * c / ε⁻¹))) ≪ (volume : Measure ℝ) :=
      Measure.smul_absolutelyContinuous.trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    unfold phaseμ
    rw [Measure.volume_eq_prod]
    exact Measure.AbsolutelyContinuous.prod h1 (Measure.absolutelyContinuous_of_le le_rfl)
  have hphase : liftFun ε⁻¹ c (d : Chart → Merid) =ᵐ[phaseμ (2 * c / ε⁻¹)] 0 := by
    have h := hac.ae_le hl0
    filter_upwards [h] with x hx
    simpa using hx
  have hmeas : Measurable (d : Chart → Merid) := (Lp.stronglyMeasurable d).measurable
  have h2 : eLpNorm (liftFun ε⁻¹ c (d : Chart → Merid)) 2 (phaseμ (2 * c / ε⁻¹)) = 0 := by
    rw [eLpNorm_congr_ae hphase, eLpNorm_zero]
  -- the weighted `L²` norm of the profile on the age cell vanishes
  have h3 : eLpNorm (d : Chart → Merid) 2 (ageμ c (-3 / 2)) = 0 := by
    have hh := eLpNorm_liftFun hR hc rfl hmeas
    rw [h2] at hh
    exact hh.symm
  have h4 : (d : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] 0 :=
    (eLpNorm_eq_zero_iff hmeas.aestronglyMeasurable two_ne_zero).1 h3
  -- the body measure is a density of `ageμ`, hence absolutely continuous to it
  have h5 : (d : Chart → Merid) =ᵐ[bodyMeasure c γ ν] 0 := by
    unfold bodyMeasure
    exact (withDensity_absolutelyContinuous (ageμ c (-3 / 2))
      (fun p => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2))).ae_le h4
  exact Lp.ext (h5.trans (Lp.coeFn_zero Merid 2 (bodyMeasure c γ ν)).symm)

end UnforcedLeray.Short.PartIIIb.Concrete
