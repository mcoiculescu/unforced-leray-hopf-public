import UnforcedLeray.Lib.EvolutionFamilies.Dyson

/-!
# Fubini on the time triangle (INF08 T8.2, T8.8, auxiliary)

The exchange `∫_s^t ∫_s^q G(q,r) dr dq = ∫_s^t ∫_r^t G(q,r) dq dr` for a bounded integrand that is
a.e. strongly measurable on the lower triangle `{r < q}` of `(s,t] × (s,t]`
(`integral_triangle_swap`), and the measurability of the iterated Duhamel integrands
`(q,r) ↦ L(τ,q) A(q) V(q,r) A(r) W(r)` built from evolution families and strongly measurable
interactions (`aestronglyMeasurable_iterated`). Used for the right Duhamel identity
(`paper/main.tex`, lines 1597, 1617; B0104) and the variation-of-constants formulas of INF08 T8.8
("Mathlib Fubini on the triangle", scoping note §5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The lower triangle `{(q,r) | r < q}`. -/
def lowerTri : Set (ℝ × ℝ) := {p | p.2 < p.1}

theorem measurableSet_lowerTri : MeasurableSet lowerTri :=
  measurableSet_lt measurable_snd measurable_fst

/-- The measure `(vol|_{(s,t]} ⊗ vol|_{(s,t]})|_{r < q}` on which the iterated integrands live. -/
abbrev triMeasure (s t : ℝ) : Measure (ℝ × ℝ) :=
  ((volume.restrict (Ioc s t)).prod (volume.restrict (Ioc s t))).restrict lowerTri

theorem triMeasure_eq (s t : ℝ) :
    triMeasure s t = (volume.prod volume).restrict (lowerTri ∩ Ioc s t ×ˢ Ioc s t) := by
  rw [triMeasure, Measure.prod_restrict, Measure.restrict_restrict measurableSet_lowerTri]

omit [NormedSpace ℂ X] in
/-- A function continuous on `{s ≤ r ≤ q ≤ t}` (`p = (q,r)`) is a.e. strongly measurable for
`triMeasure s t`. -/
theorem aestronglyMeasurable_triMeasure_of_continuousOn {s t : ℝ} {f : ℝ × ℝ → X}
    (hf : ContinuousOn f {p | s ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t}) :
    AEStronglyMeasurable f (triMeasure s t) := by
  rw [triMeasure_eq]
  refine (hf.mono ?_).aestronglyMeasurable
    (measurableSet_lowerTri.inter (measurableSet_Ioc.prod measurableSet_Ioc))
  rintro p ⟨hp, h1, h2⟩
  exact ⟨h2.1.le, le_of_lt hp, h1.2⟩

/-- A function of the outer variable `q` measurable on `(s,t]` is measurable for
`triMeasure s t`. -/
theorem aestronglyMeasurable_triMeasure_fst {Y : Type*} [TopologicalSpace Y] {s t : ℝ}
    {f : ℝ → Y} (hf : AEStronglyMeasurable f (volume.restrict (Ioc s t))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1) (triMeasure s t) :=
  (hf.comp_fst (ν := volume.restrict (Ioc s t))).restrict

/-- A function of the inner variable `r` measurable on `(s,t]` is measurable for
`triMeasure s t`. -/
theorem aestronglyMeasurable_triMeasure_snd {Y : Type*} [TopologicalSpace Y] {s t : ℝ}
    {f : ℝ → Y} (hf : AEStronglyMeasurable f (volume.restrict (Ioc s t))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (triMeasure s t) :=
  (hf.comp_snd (μ := volume.restrict (Ioc s t))).restrict

variable [CompleteSpace X]

/-- **Fubini on the triangle**: `∫_s^t ∫_s^q G(q,r) dr dq = ∫_s^t ∫_r^t G(q,r) dq dr` for `G`
bounded on `s < r < q ≤ t` and a.e. strongly measurable for `triMeasure s t`. -/
theorem integral_triangle_swap {s t K : ℝ} (hst : s ≤ t) {G : ℝ → ℝ → X}
    (hG : AEStronglyMeasurable (Function.uncurry G) (triMeasure s t))
    (hK : ∀ q r, s < r → r < q → q ≤ t → ‖G q r‖ ≤ K) :
    ∫ q in s..t, (∫ r in s..q, G q r) = ∫ r in s..t, (∫ q in r..t, G q r) := by
  set μ : Measure ℝ := volume.restrict (Ioc s t) with hμ
  set f : ℝ → ℝ → X := fun q r => lowerTri.indicator (Function.uncurry G) (q, r) with hf_def
  have hfun : Function.uncurry f = lowerTri.indicator (Function.uncurry G) := by
    ext p; rfl
  have hf : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [hfun]
    refine Integrable.of_bound ((aestronglyMeasurable_indicator_iff measurableSet_lowerTri).mpr hG)
      (max K 0) ?_
    rw [hμ, Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    by_cases hpS : p ∈ lowerTri
    · rw [indicator_of_mem hpS]
      exact (hK p.1 p.2 hp.2.1 hpS hp.1.2).trans (le_max_left _ _)
    · rw [indicator_of_notMem hpS, norm_zero]
      exact le_max_right _ _
  have hswap := integral_integral_swap hf
  have hL : ∫ q in s..t, (∫ r in s..q, G q r) = ∫ q, ∫ r, f q r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    have hfq : (fun r => f q r) = (Iio q).indicator (G q) := by
      ext r
      simp only [hf_def, lowerTri, indicator_apply, mem_ofPred_eq, mem_Iio,
        Function.uncurry_apply_pair]
    have hset : Ioc s t ∩ Iio q = Ioo s q := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, h3.le.trans hq.2⟩, h3⟩
    rw [intervalIntegral.integral_of_le hq.1.le, integral_Ioc_eq_integral_Ioo, hfq,
      setIntegral_indicator measurableSet_Iio, hset]
  have hR : ∫ r in s..t, (∫ q in r..t, G q r) = ∫ r, ∫ q, f q r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hfr : (fun q => f q r) = (Ioi r).indicator (fun q => G q r) := by
      ext q
      simp only [hf_def, lowerTri, indicator_apply, mem_ofPred_eq, mem_Ioi,
        Function.uncurry_apply_pair]
    have hset : Ioc s t ∩ Ioi r = Ioc r t := by
      ext q
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hr.1.trans h1, h2⟩, h1⟩
    rw [intervalIntegral.integral_of_le hr.2, hfr, setIntegral_indicator measurableSet_Ioi, hset]
  rw [hL, hswap, hR]

namespace EvolutionFamily

variable {a b : ℝ}

omit [CompleteSpace X] in
/-- **Measurability of iterated Duhamel integrands.** For evolution families `L`, `V`, a strongly
measurable interaction `A` and a strongly measurable `W`, the function
`(q,r) ↦ L(τ,q) A(q) V(q,r) A'(r) W(r)` is a.e. strongly measurable for `triMeasure s τ`. -/
theorem aestronglyMeasurable_iterated (L V : EvolutionFamily X a b) (A A' : BoundedPert X a b)
    {s τ : ℝ} (hs : a ≤ s) (hτ : τ ≤ b) {W : ℝ → X}
    (hW : AEStronglyMeasurable W (volume.restrict (Ioc s τ))) :
    AEStronglyMeasurable
      (Function.uncurry fun q r => L.U τ q (A.A q (V.U q r (A'.A r (W r))))) (triMeasure s τ) := by
  have hsub : Ioc s τ ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs hτ)
  have hv : AEStronglyMeasurable (fun r => A'.A r (W r)) (volume.restrict (Ioc s τ)) :=
    aestronglyMeasurable_clm_apply
      (fun v => (A'.meas v).mono_measure (Measure.restrict_mono hsub le_rfl)) hW
  have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => V.U p.1 p.2 (A'.A p.2 (W p.2)))
      (triMeasure s τ) := by
    refine aestronglyMeasurable_clm_apply (L := fun p : ℝ × ℝ => V.U p.1 p.2) (fun e => ?_)
      (aestronglyMeasurable_triMeasure_snd hv)
    refine aestronglyMeasurable_triMeasure_of_continuousOn ?_
    exact (V.U_cont e).comp continuous_swap.continuousOn
      fun p hp => ⟨hs.trans hp.1, hp.2.1, hp.2.2.trans hτ⟩
  have hAw : AEStronglyMeasurable (fun p : ℝ × ℝ => A.A p.1 (V.U p.1 p.2 (A'.A p.2 (W p.2))))
      (triMeasure s τ) :=
    aestronglyMeasurable_clm_apply (L := fun p : ℝ × ℝ => A.A p.1)
      (fun e => aestronglyMeasurable_triMeasure_fst
        ((A.meas e).mono_measure (Measure.restrict_mono hsub le_rfl))) hw
  exact aestronglyMeasurable_clm_apply (L := fun p : ℝ × ℝ => L.U τ p.1)
    (fun e => aestronglyMeasurable_triMeasure_fst (((L.continuousOn_snd hτ e).mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl))).aestronglyMeasurable
      measurableSet_Ioc)) hAw

omit [CompleteSpace X] in
/-- The bound of the iterated integrand. -/
theorem norm_iterated_le (L V : EvolutionFamily X a b) (A A' : BoundedPert X a b)
    {s τ q r : ℝ} (hs : a ≤ s) (hτ : τ ≤ b) (hr : s ≤ r) (hrq : r ≤ q) (hq : q ≤ τ) (w : X) :
    ‖L.U τ q (A.A q (V.U q r (A'.A r w)))‖ ≤ L.M * A.C * (V.M * (A'.C * ‖w‖)) := by
  calc ‖L.U τ q (A.A q (V.U q r (A'.A r w)))‖ ≤ L.M * A.C * ‖V.U q r (A'.A r w)‖ :=
        L.norm_integrand_le A hs hτ ⟨hr.trans hrq, hq⟩ _
    _ ≤ L.M * A.C * (V.M * (A'.C * ‖w‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg L.M_nonneg A.C_nonneg)
        refine (V.norm_apply_le (hs.trans hr) hrq (hq.trans hτ) _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ V.M_nonneg
        exact ((A'.A r).le_opNorm w).trans (mul_le_mul_of_nonneg_right
          (A'.norm_le ⟨hs.trans hr, hrq.trans (hq.trans hτ)⟩) (norm_nonneg _))

end EvolutionFamily

end UnforcedLeray.Evolution
