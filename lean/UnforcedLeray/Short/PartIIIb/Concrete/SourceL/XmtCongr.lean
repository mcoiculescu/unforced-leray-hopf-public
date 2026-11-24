import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Null sets of `ℝ` pull back to null sets of `ℝ²` under `x' ↦ (x'₁² + x'₂²)⁻¹`
(polar coordinates; the radial map `u ↦ (√u)⁻¹` is differentiable on `(0,∞)`). -/
theorem vol_preimage_radius_sq_null (N : Set ℝ) (hN : volume N = 0) :
    volume {x' : ℝ × ℝ | (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ N} = 0 := by
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  set S' : Set (ℝ × ℝ) := {x' | (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ N'} with hS'
  have hS'm : MeasurableSet S' := by
    have : Measurable (fun x' : ℝ × ℝ => (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by fun_prop
    exact this hN'm
  refine measure_mono_null (fun x hx => hNN' hx) ?_
  · show volume S' = 0
    set A : Set ℝ := {r | 0 < r ∧ (r ^ 2)⁻¹ ∈ N'} with hA
    have hA0 : volume A = 0 := by
      have himg : volume ((fun u : ℝ => (Real.sqrt u)⁻¹) '' (N' ∩ Ioi 0)) = 0 := by
        apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
        · intro u hu
          have hu0 : u ≠ 0 := ne_of_gt hu.2
          exact ((Real.hasDerivAt_sqrt hu0).differentiableAt.inv
            (Real.sqrt_ne_zero'.mpr hu.2)).differentiableWithinAt
        · exact measure_mono_null inter_subset_left hN'0
      refine measure_mono_null ?_ himg
      rintro r ⟨hr, hrN⟩
      refine ⟨(r ^ 2)⁻¹, ⟨hrN, inv_pos.mpr (pow_pos hr 2)⟩, ?_⟩
      show (Real.sqrt ((r ^ 2)⁻¹))⁻¹ = r
      rw [Real.sqrt_inv, Real.sqrt_sq hr.le, inv_inv]
    have hAu : volume (A ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, hA0, zero_mul]
    have key := lintegral_comp_polarCoord_symm (Set.indicator S' (fun _ => (1 : ℝ≥0∞)))
    have hone : ∫⁻ p : ℝ × ℝ, S'.indicator (fun _ => (1 : ℝ≥0∞)) p = volume S' := by
      rw [lintegral_indicator_const hS'm, one_mul]
    rw [hone] at key
    rw [← key]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have h1 : ∀ᵐ p ∂(volume.restrict polarCoord.target), p ∈ polarCoord.target :=
      ae_restrict_mem polarCoord.open_target.measurableSet
    have h2 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ A ×ˢ (univ : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp hAu
    filter_upwards [h1, ae_restrict_of_ae h2] with p hp hpA
    have hp1 : 0 < p.1 := hp.1
    have hnot : polarCoord.symm p ∉ S' := by
      intro hmem
      apply hpA
      refine ⟨⟨hp1, ?_⟩, mem_univ _⟩
      have hmem' : ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)⁻¹ ∈ N' := hmem
      have hsq : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        nlinarith [Real.sin_sq_add_cos_sq p.2]
      rwa [hsq] at hmem'
    rw [Set.indicator_of_notMem hnot]
    simp

/-- The phase mean depends only on the a.e. class of `M` on the old region, for a.e. `u`. -/
theorem ae_phaseMean_congr (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M M' : Chart → Mat3) (h : M =ᵐ[oldMeasure c ν] M') :
    ∀ᵐ u ∂(volume : Measure ℝ), phaseMean c ν χo M u = phaseMean c ν χo M' u := by
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  have h1 := Measure.ae_ae_of_ae_prod h
  have h2 : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (6 / 5 / ν) →
      ∀ᵐ x ∂(Cyl.avgμ c), M (u, x) = M' (u, x) := by
    exact (ae_restrict_iff' measurableSet_Ioi).mp h1
  filter_upwards [h2] with u hu
  by_cases hu' : u ∈ Ioi (6 / 5 / ν)
  · funext i j
    unfold phaseMean
    split_ifs with hij
    · rfl
    · congr 1
      exact integral_congr_ae (by filter_upwards [hu hu'] with x hx; rw [hx])
  · funext i j
    have hle : ν * u ≤ 6 / 5 := by
      have : u ≤ 6 / 5 / ν := not_lt.mp hu'
      rw [le_div_iff₀ hν] at this
      linarith
    unfold phaseMean
    simp [hχo.zero _ hle]

theorem xmtCongr : XmtCongr := by
  intro c ν ε μ χo χy hχo hν M M' h
  have hu := ae_phaseMean_congr c ν χo hχo hν M M' h
  have hx : ∀ᵐ x' ∂(volume : Measure (ℝ × ℝ)), sigmaM c ν χo M x' = sigmaM c ν χo M' x' := by
    rw [ae_iff] at hu ⊢
    have := vol_preimage_radius_sq_null _ hu
    refine measure_mono_null (fun x' hx' => ?_) this
    show ¬ phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ =
      phaseMean c ν χo M' (x'.1 ^ 2 + x'.2 ^ 2)⁻¹
    intro hh
    apply hx'
    unfold sigmaM
    rw [hh]
  have hV : ∀ μ, newtonV c ν μ χo M = newtonV c ν μ χo M' := by
    intro μ
    funext x i
    unfold newtonV
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hx] with x' hx'
    rw [hx']
  unfold Xmt youngW
  rw [hV μ, hV (μ + 1)]

end UnforcedLeray.Short.PartIIIb.Concrete
