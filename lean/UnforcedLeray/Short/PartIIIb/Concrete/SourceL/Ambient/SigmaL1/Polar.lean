import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_4

/-!
# `PlanePolar` (source 4924-4927 and the `σ_M` integral)

Polar coordinates on `ℝ²` and the substitution `u = (r²)⁻¹` give
`∫_{ℝ²} ρ⁻¹ H(ρ⁻²) dx' = π ∫_0^∞ u^{-3/2} H(u) du` for `H ≥ 0` a.e. measurable.
The measurable case is proved first, then the a.e. case through a measurable modification and the
polar-coordinate null-set lemma `polar_null`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The integrand of `PlanePolar`: `ρ⁻¹ H(ρ⁻²)` with `ρ² = x₁² + x₂²`, as an extended real. -/
def polarF (H : ℝ → ℝ) (x' : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹))

lemma sq_add_polar_symm (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
  ring

lemma rpow_inv_sq_neg32 {r : ℝ} (hr : 0 < r) :
    ((r ^ 2)⁻¹) ^ (-(3 / 2 : ℝ)) = r ^ (3 : ℕ) := by
  have h2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  rw [Real.inv_rpow h2, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
  rw [show ((2 : ℕ) : ℝ) * -(3 / 2 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le,
    Real.rpow_natCast, inv_inv]

/-- Pointwise: the polar integrand at a point `symm (r, θ)` with `r > 0`. -/
lemma polarF_symm_mul (H : ℝ → ℝ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    ENNReal.ofReal p.1 * polarF H (polarCoord.symm p) =
      ENNReal.ofReal (H ((p.1 ^ 2)⁻¹)) := by
  have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
  rw [hsymm]
  unfold polarF
  dsimp only
  have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    have h := Real.sin_sq_add_cos_sq p.2
    rw [sq_add_polar_symm, h, mul_one]
  rw [hsq, Real.sqrt_sq hp.le, ← ENNReal.ofReal_mul hp.le]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

/-- The change of variables `u = (r²)⁻¹` on `(0, ∞)`. -/
theorem polar_change' (H : ℝ → ℝ) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u) =
      ENNReal.ofReal 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (H ((r ^ 2)⁻¹)) := by
  have hinj : InjOn (fun r : ℝ => (r ^ 2)⁻¹) (Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have h1 : (a ^ 2)⁻¹ = (b ^ 2)⁻¹ := hab
    have h2 : a ^ 2 = b ^ 2 := inv_injective h1
    exact (pow_left_inj₀ ha'.le hb'.le two_ne_zero).1 h2
  have himg : (fun r : ℝ => (r ^ 2)⁻¹) '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact inv_pos.2 (pow_pos (show (0 : ℝ) < r from hr) 2)
    · intro hu
      have hu' : 0 < u := hu
      refine ⟨Real.sqrt u⁻¹, Real.sqrt_pos.2 (inv_pos.2 hu'), ?_⟩
      show ((Real.sqrt u⁻¹) ^ 2)⁻¹ = u
      rw [Real.sq_sqrt (inv_nonneg.2 hu'.le), inv_inv]
  have hderiv : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => (r ^ 2)⁻¹) (-(2 * r) / (r ^ 2) ^ 2) (Ioi 0) r := by
    intro r hr
    have hr' : r ≠ 0 := ne_of_gt hr
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    exact (h2.inv (pow_ne_zero 2 hr')).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun r : ℝ => (r ^ 2)⁻¹)
    (f' := fun r : ℝ => -(2 * r) / (r ^ 2) ^ 2) measurableSet_Ioi hderiv hinj
    (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u))
  rw [himg] at key
  have hpt : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (|-(2 * r) / (r ^ 2) ^ 2|) *
      ENNReal.ofReal ((((r ^ 2)⁻¹) ^ (-(3 / 2 : ℝ))) * H ((r ^ 2)⁻¹)) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal 2 * ENNReal.ofReal (H ((r ^ 2)⁻¹)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have habs : |-(2 * r) / (r ^ 2) ^ 2| = 2 * r / (r ^ 2) ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * r),
        abs_of_pos (by positivity : (0 : ℝ) < (r ^ 2) ^ 2)]
    rw [rpow_inv_sq_neg32 hr0, habs,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * r / (r ^ 2) ^ 2 by positivity),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    field_simp <;> ring
  calc ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u)
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (|-(2 * r) / (r ^ 2) ^ 2|) *
          ENNReal.ofReal ((((r ^ 2)⁻¹) ^ (-(3 / 2 : ℝ))) * H ((r ^ 2)⁻¹)) := key
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal 2 * ENNReal.ofReal (H ((r ^ 2)⁻¹)) := hpt
    _ = ENNReal.ofReal 2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (H ((r ^ 2)⁻¹)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The measurable case of `PlanePolar`. -/
theorem polar_meas (H : ℝ → ℝ) (hH0 : ∀ u, 0 ≤ H u) (hH : Measurable H) :
    ∫⁻ x' : ℝ × ℝ, polarF H x' =
      ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u) := by
  have hA : ∫⁻ x' : ℝ × ℝ, polarF H x' =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal (H ((p.1 ^ 2)⁻¹)) := by
    calc ∫⁻ x' : ℝ × ℝ, polarF H x'
        = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • polarF H (polarCoord.symm p) :=
          (lintegral_comp_polarCoord_symm _).symm
      _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal (H ((p.1 ^ 2)⁻¹)) := by
          refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
          rw [smul_eq_mul]
          exact polarF_symm_mul H p hp.1
  have hm1 : Measurable (fun r : ℝ => ENNReal.ofReal (H ((r ^ 2)⁻¹))) :=
    (hH.comp ((measurable_id.pow_const 2).inv)).ennreal_ofReal
  have hC : ∫⁻ p in polarCoord.target, ENNReal.ofReal (H ((p.1 ^ 2)⁻¹)) =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (H ((r ^ 2)⁻¹))) *
        ENNReal.ofReal (Real.pi - -Real.pi) := by
    have htgt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
    have hm2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (H ((p.1 ^ 2)⁻¹))) :=
      hm1.comp measurable_fst
    rw [htgt, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
      lintegral_prod _ hm2.aemeasurable]
    simp only [setLIntegral_const, Real.volume_Ioo]
    rw [lintegral_mul_const _ hm1]
  have hsub : ENNReal.ofReal (Real.pi - -Real.pi) =
      ENNReal.ofReal 2 * ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hA, hC, polar_change', hsub]
  ring

/-- Null-set lemma: the preimage under `x' ↦ (x'₁² + x'₂²)⁻¹` of a null measurable set is null
(on the punctured plane), by the polar-coordinate identity applied to the indicator. -/
theorem polar_null {t : Set ℝ} (ht : MeasurableSet t) (ht0 : volume t = 0) :
    ∀ᵐ x' : ℝ × ℝ, ¬ (0 < x'.1 ^ 2 + x'.2 ^ 2 ∧ (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ t) := by
  set H : ℝ → ℝ := t.indicator (fun _ => (1 : ℝ)) with hHdef
  have hH0 : ∀ u, 0 ≤ H u := fun u => Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hHm : Measurable H := measurable_const.indicator ht
  have hmeas0 : (volume.restrict (Ioi (0 : ℝ))) t = 0 := by
    rw [Measure.restrict_apply ht]
    exact measure_mono_null inter_subset_left ht0
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), u ∉ t := by
    rw [ae_iff]
    simpa using hmeas0
  have hzero : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u) = 0 := by
    have hfz : (fun u : ℝ => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun _ => (0 : ENNReal)) :=
      hae.mono fun u hu => by simp [hHdef, Set.indicator_of_notMem hu]
    rw [lintegral_congr_ae hfz, lintegral_zero]
  have h0 : ∫⁻ x' : ℝ × ℝ, polarF H x' = 0 := by
    rw [polar_meas H hH0 hHm, hzero, mul_zero]
  have hpm : Measurable (polarF H) := by
    unfold polarF
    apply Measurable.ennreal_ofReal
    apply Measurable.mul
    · exact (Real.continuous_sqrt.measurable.comp
        (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)))).inv
    · exact hHm.comp (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).inv)
  have hae0 : polarF H =ᵐ[volume] (0 : ℝ × ℝ → ENNReal) :=
    (lintegral_eq_zero_iff hpm).1 h0
  filter_upwards [hae0] with x' hx
  rintro ⟨hs, hmem⟩
  have hH1 : H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) = 1 := by
    rw [hHdef, Set.indicator_of_mem hmem]
  have hpos : 0 < (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * 1 :=
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 hs)) one_pos
  have hx' : polarF H x' = 0 := hx
  unfold polarF at hx'
  rw [hH1, ENNReal.ofReal_eq_zero] at hx'
  linarith

/-- `PlanePolar`. -/
theorem planePolar : PlanePolar := by
  intro H hH0 hHm
  set G : ℝ → ℝ := fun u => max (hHm.mk H u) 0 with hG
  have hGm : Measurable G := (hHm.measurable_mk).max measurable_const
  have hG0 : ∀ u, 0 ≤ G u := fun u => le_max_right _ _
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), H u = hHm.mk H u := hHm.ae_eq_mk
  have hae' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (0 : ℝ) → H u = G u := by
    have h := (ae_restrict_iff' measurableSet_Ioi).1 hae
    filter_upwards [h] with u hu hu0
    have h1 : H u = hHm.mk H u := hu hu0
    have h2 : 0 ≤ hHm.mk H u := h1 ▸ hH0 u
    show H u = max (hHm.mk H u) 0
    rw [max_eq_left h2]
    exact h1
  obtain ⟨t, hsubt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae')
  have hnull := polar_null htm ht0
  have hcongr : ∀ᵐ x' : ℝ × ℝ, polarF H x' = polarF G x' := by
    filter_upwards [hnull] with x' hx
    by_cases hs : x'.1 ^ 2 + x'.2 ^ 2 = 0
    · unfold polarF
      rw [hs]
      simp
    · have hpos : 0 < x'.1 ^ 2 + x'.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      have hnt : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∉ t := fun h => hx ⟨hpos, h⟩
      have hHG : H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) = G ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
        by_contra hc
        exact hnt (hsubt (fun h => hc (h (inv_pos.2 hpos))))
      unfold polarF
      rw [hHG]
  have hHG' : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), H u = G u :=
    (ae_restrict_iff' measurableSet_Ioi).2 hae'
  calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          H ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹))
      = ∫⁻ x' : ℝ × ℝ, polarF G x' := lintegral_congr_ae hcongr
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * G u) :=
        polar_meas G hG0 hGm
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * H u) := by
        congr 1
        exact lintegral_congr_ae (hHG'.mono fun u hu => by simp only [hu])

end UnforcedLeray.Short.PartIIIb.Concrete
