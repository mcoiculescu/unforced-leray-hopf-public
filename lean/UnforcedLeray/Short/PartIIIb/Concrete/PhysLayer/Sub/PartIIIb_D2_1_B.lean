import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The complexification `realC` is isometric (enorm form). -/
theorem enorm_realC_B (x : Space) : ‖B0412.realC x‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  congr 1
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [B0412.realC_apply, Complex.norm_real]

theorem realC_continuous_B : Continuous (B0412.realC : Space → CVec3) := by
  unfold B0412.realC
  fun_prop

/-- Lower bound on the gain density: `g⁻¹ ≥ e^{-|γ|/ν}`. -/
theorem ginv_lower_B {γ ν : ℝ} (hν : 0 < ν) (p : Chart) :
    Real.exp (-(|γ| / ν)) ≤ ginv γ ν p := by
  have h1 := NearInst.gainFun_le (γ := γ) hν p
  rw [abs_of_pos (NearInst.gainFun_pos γ ν p)] at h1
  have h2 : ginv γ ν p = (NearInst.gainFun γ ν p)⁻¹ := rfl
  rw [h2, Real.exp_neg]
  exact inv_anti₀ (NearInst.gainFun_pos γ ν p) h1

theorem fwuLiftYr {c γ ν ε : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) :
    FWULiftYr c γ ν ε := by
  intro b
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have hc0 : c ≠ 0 := hc.ne'
  have hbm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hpm : Measurable (perExt c (b : Chart → Merid)) := measurable_perExt c hbm
  have hm : Measurable (velPhys ε⁻¹ c (b : Chart → Merid)) :=
    realC_continuous_B.measurable.comp (measurable_Nv ε⁻¹ hpm)
  refine ⟨?_, hm.aestronglyMeasurable, ?_⟩
  · -- periodicity in the phase
    refine Filter.Eventually.of_forall fun x => ?_
    have hper := congrFun (Nv_dss (R := ε⁻¹) (c := c) (P := 2 * c / ε⁻¹) hR0 rfl
      (perExt_periodic hc0 (b : Chart → Merid)) x.1) x.2
    show B0412.realC (Nv ε⁻¹ (perExt c (b : Chart → Merid)) (x.1 + 2 * ε * c) x.2) =
      B0412.realC (Nv ε⁻¹ (perExt c (b : Chart → Merid)) x.1 x.2)
    rw [hP, hper]
  · -- finiteness of the phase-normalized `L²` norm
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    have hF : Measurable (fun x : ℝ × Space => ‖velPhys ε⁻¹ c (b : Chart → Merid) x‖ₑ ^ (2 : ℝ)) :=
      (hm.enorm).pow_const _
    have hI : ENNReal.ofReal (2 * ε * c)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y, ‖velPhys ε⁻¹ c (b : Chart → Merid) (t, y)‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, ‖velPhys ε⁻¹ c (b : Chart → Merid) x‖ₑ ^ (2 : ℝ) ∂phaseμ (2 * ε * c) := by
      rw [ENNReal.ofReal_inv_of_pos hP0, lintegral_phaseμ _ hF]
    rw [hI]
    have hF' : (fun x : ℝ × Space => ‖velPhys ε⁻¹ c (b : Chart → Merid) x‖ₑ ^ (2 : ℝ)) =
        fun x => ‖Nv ε⁻¹ (perExt c (b : Chart → Merid)) x.1 x.2‖ₑ ^ (2 : ℝ) := by
      funext x
      simp only [velPhys]
      rw [enorm_realC_B]
    rw [hF', lintegral_phaseμ_Nv hR hc hP (by norm_num : (0 : ℝ) < 2) hpm
      (perExt_periodic hc0 (b : Chart → Merid))]
    rw [show ((2 : ℝ) / 2 - 5 / 2) = -3 / 2 by norm_num]
    have hae : ∫⁻ p, ‖perExt c (b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) =
        ∫⁻ p, ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [perExt_ae_eq hc (-3 / 2) (b : Chart → Merid)] with p hp
      rw [hp]
    rw [hae]
    -- the body measure has finite `L²` integral
    have hbody : ∫⁻ p, ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν < ⊤ := by
      have h2 : eLpNorm (b : Chart → Merid) 2 (bodyMeasure c γ ν) < ⊤ :=
        (Lp.memLp b).eLpNorm_lt_top
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num)
        (by norm_num) h2
      simpa using this
    have hdens : ∫⁻ p, ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure c γ ν =
        ∫⁻ p, (ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ))
          ∂ageμ c (-3 / 2) := by
      unfold bodyMeasure
      refine lintegral_withDensity_eq_lintegral_mul _ ?_ (hbm.enorm.pow_const _)
      exact (ENNReal.measurable_ofReal.comp
        ((measurable_const.mul ((NearInst.gainFun_measurable γ ν).inv.pow_const 2))))
    rw [hdens] at hbody
    -- the density is bounded below by a positive constant
    set m : ℝ≥0∞ := ENNReal.ofReal (Real.pi * Real.exp (-(|γ| / ν)) ^ 2) with hmdef
    have hm0 : m ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hmtop : m ≠ ⊤ := ENNReal.ofReal_ne_top
    have hle : ∀ p : Chart, m ≤ ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
      intro p
      apply ENNReal.ofReal_le_ofReal
      have hexp : Real.exp (-(|γ| / ν)) ^ 2 ≤ ginv γ ν p ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le (ginv_lower_B hν p) 2
      exact mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
    have hfin : ∫⁻ p, ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) < ⊤ := by
      calc ∫⁻ p, ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)
          = ∫⁻ p, m⁻¹ * (m * ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
            refine lintegral_congr fun p => ?_
            rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
        _ ≤ ∫⁻ p, m⁻¹ * (ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) *
              ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
            refine lintegral_mono fun p => ?_
            gcongr <;> exact hle p
        _ = m⁻¹ * ∫⁻ p, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) *
              ‖(b : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
            rw [lintegral_const_mul]
            exact (ENNReal.measurable_ofReal.comp
              (measurable_const.mul ((NearInst.gainFun_measurable γ ν).inv.pow_const 2))).mul
              (hbm.enorm.pow_const _)
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 (by positivity)))
            hbody
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne

end UnforcedLeray.Short.PartIIIb.Concrete
