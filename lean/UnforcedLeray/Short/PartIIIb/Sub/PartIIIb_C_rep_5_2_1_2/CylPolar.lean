import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2

/-!
# `PartIII-b:C/rep/5/2/1/2`: cylindrical coordinates `CylPolar`

Source `the November 2 reference manuscript` 2683-2689, step (ii):
for a measurable axisymmetric `Φ ≥ 0` on `Space = EuclideanSpace ℝ (Fin 3)`,
`∫ Φ dy = ∫_{r>0} ∫_z 2πr Φ(r,0,z) dr dz`.
Proof: a volume-preserving equivalence `Space ≃ ℝ × (ℝ × ℝ)`, `y ↦ (y 2, (y 0, y 1))`; Fubini in
the first coordinate; polar coordinates on `ℝ²` (`lintegral_comp_polarCoord_symm`), where axisymmetry
makes the integrand depend on the radius only, and integration over the angle gives `2π`; then
Tonelli to swap `z` and `r`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(z, (x, y)) ↦ (x, y, z) ∈ Space`. -/
def cylQ (p : ℝ × (ℝ × ℝ)) : Space := WithLp.toLp 2 ![p.2.1, p.2.2, p.1]

/-- The measurable equivalence `Space ≃ ℝ × (ℝ × ℝ)`, `y ↦ (y 2, (y 0, y 1))`. -/
def cylE : Space ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))

lemma cylQ_cylE (y : Space) : cylQ (cylE y) = y := by
  ext i
  fin_cases i <;> simp [cylQ, cylE] <;> rfl

lemma mp_cylE : MeasurePreserving cylE volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow) volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact h3.comp (h2.comp h1)

lemma measurable_cylQ : Measurable cylQ := by
  unfold cylQ
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun i => ?_))
  fin_cases i <;> simp <;> fun_prop

lemma measurable_line (z : ℝ) :
    Measurable (fun r : ℝ => (WithLp.toLp 2 ![r, 0, z] : Space)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun i => ?_))
  fin_cases i <;> simp <;> fun_prop

lemma measurable_pair :
    Measurable (fun p : ℝ × ℝ => (WithLp.toLp 2 ![p.2, 0, p.1] : Space)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_pi_lambda _ (fun i => ?_))
  fin_cases i <;> simp <;> fun_prop

/-- Cylindrical coordinates (step (ii)), the statement `CylPolar`. -/
theorem cylPolar : CylPolar := by
  intro Φ hΦ hax
  have hΦQ : Measurable (fun p : ℝ × (ℝ × ℝ) => Φ (cylQ p)) := hΦ.comp measurable_cylQ
  -- transfer to `ℝ × (ℝ × ℝ)`
  have step1 : ∫⁻ y, Φ y = ∫⁻ p : ℝ × (ℝ × ℝ), Φ (cylQ p) := by
    calc ∫⁻ y, Φ y = ∫⁻ y, Φ (cylQ (cylE y)) := by
          congr 1
          funext y
          rw [cylQ_cylE]
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), Φ (cylQ p) := mp_cylE.lintegral_comp hΦQ
  -- Fubini in the `z` coordinate
  have step2 : ∫⁻ p : ℝ × (ℝ × ℝ), Φ (cylQ p) =
      ∫⁻ z : ℝ, ∫⁻ q : ℝ × ℝ, Φ (WithLp.toLp 2 ![q.1, q.2, z]) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ hΦQ.aemeasurable
  -- polar coordinates in the plane, for fixed `z`
  have step3 : ∀ z : ℝ, ∫⁻ q : ℝ × ℝ, Φ (WithLp.toLp 2 ![q.1, q.2, z]) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.pi * r) * Φ (WithLp.toLp 2 ![r, 0, z]) := by
    intro z
    have hpol : ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • Φ (WithLp.toLp 2 ![(polarCoord.symm p).1, (polarCoord.symm p).2, z])
          = ∫⁻ q : ℝ × ℝ, Φ (WithLp.toLp 2 ![q.1, q.2, z]) :=
      lintegral_comp_polarCoord_symm (fun q : ℝ × ℝ => Φ (WithLp.toLp 2 ![q.1, q.2, z]))
    rw [← hpol]
    rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl]
    have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 • Φ (WithLp.toLp 2 ![(polarCoord.symm p).1, (polarCoord.symm p).2, z])
          = ENNReal.ofReal p.1 * Φ (WithLp.toLp 2 ![p.1, 0, z]) := by
      intro p hp
      have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
      rw [smul_eq_mul]
      congr 1
      apply hax (WithLp.toLp 2 ![p.1, 0, z])
        (WithLp.toLp 2 ![(polarCoord.symm p).1, (polarCoord.symm p).2, z])
      · simp [hsymm]
      · simp [hsymm]
        linear_combination (p.1 ^ 2) * Real.sin_sq_add_cos_sq p.2
    rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt]
    have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * Φ (WithLp.toLp 2 ![p.1, 0, z])) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul
        (hΦ.comp ((measurable_line z).comp measurable_fst))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    ring
  have hmeas2 : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (2 * Real.pi * p.2) * Φ (WithLp.toLp 2 ![p.2, 0, p.1])) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_snd)).mul
      (hΦ.comp measurable_pair)
  calc ∫⁻ y, Φ y = ∫⁻ p : ℝ × (ℝ × ℝ), Φ (cylQ p) := step1
    _ = ∫⁻ z : ℝ, ∫⁻ q : ℝ × ℝ, Φ (WithLp.toLp 2 ![q.1, q.2, z]) := step2
    _ = ∫⁻ z : ℝ, ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.pi * r) * Φ (WithLp.toLp 2 ![r, 0, z]) :=
        lintegral_congr step3
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal (2 * Real.pi * r) * Φ (WithLp.toLp 2 ![r, 0, z]) :=
        lintegral_lintegral_swap hmeas2.aemeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
