import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# Phase functions lifted to the line (block 2F, INF14 T6 support)

For `f ∈ L^q(ℝ/Pℤ; X)` with the normalised Haar measure (decision D2; the space `Y_q` of
tex 7313–7317 when `X = L^q(ℝ³; ℂ³)`), the lift `t ↦ f(t mod P)` is a.e. strongly measurable
on `ℝ`, interval integrable on every bounded interval, and its norm integrates over any period
to at most `P ‖f‖_{Y_q}` (Hölder on a probability space). Conversely, a continuous function on
the circle that agrees a.e. on one period with the lift of `f` represents `f`.

These are the measure-theoretic facts behind "integrate over at most one period" and
"Hölder's inequality gives (free-stress-4)" (tex 7628–7630, unit B0434).

Status: infrastructure for `Lib/PhaseTrace.lean`; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.PhaseTrace

variable {P : ℝ} [hP : Fact (0 < P)]

omit hP in
theorem periodic_coe : Function.Periodic (fun x : ℝ => (x : AddCircle P)) P :=
  fun x => AddCircle.coe_add_period P x

omit hP in
theorem coe_add_int_mul (t : ℝ) (k : ℤ) : ((t + k * P : ℝ) : AddCircle P) = (t : AddCircle P) :=
  (periodic_coe.int_mul k) t

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem aestronglyMeasurable_volume (f : Lp X q (AddCircle.haarAddCircle (T := P))) :
    AEStronglyMeasurable (f : AddCircle P → X) volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact (Lp.aestronglyMeasurable f).smul_measure _

/-- The lift `t ↦ f(t mod P)` is a.e. strongly measurable on `ℝ`. -/
theorem aestronglyMeasurable_comp_mk (f : Lp X q (AddCircle.haarAddCircle (T := P))) :
    AEStronglyMeasurable (fun t : ℝ => f (t : AddCircle P)) volume := by
  have h : ∀ k : ℤ, AEStronglyMeasurable (fun t : ℝ => f (t : AddCircle P))
      (volume.restrict (Ioc (0 + k • P) (0 + (k + 1) • P))) := by
    intro k
    have hmp := AddCircle.measurePreserving_mk P (0 + k • P)
    have e : (0 + (k + 1) • P) = (0 + k • P) + P := by rw [add_smul, one_smul]; ring
    rw [e]
    exact (aestronglyMeasurable_volume f).comp_measurePreserving hmp
  rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_add_zsmul hP.out 0]
  exact aestronglyMeasurable_iUnion_iff.mpr h

theorem integrable_volume (f : Lp X q (AddCircle.haarAddCircle (T := P))) :
    Integrable (f : AddCircle P → X) volume := by
  have h1 : Integrable (f : AddCircle P → X) AddCircle.haarAddCircle :=
    (Lp.memLp f).integrable Fact.out
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  exact h1.smul_measure ENNReal.ofReal_ne_top

theorem integrableOn_comp_mk_Ioc (f : Lp X q (AddCircle.haarAddCircle (T := P))) (t : ℝ) :
    IntegrableOn (fun s : ℝ => f (s : AddCircle P)) (Ioc t (t + P)) volume :=
  ((AddCircle.measurePreserving_mk P t).integrable_comp (aestronglyMeasurable_volume f)).mpr
    (integrable_volume f)

omit hP [NormedAddCommGroup X] [NormedSpace ℝ X] [Fact (1 ≤ q)] in
theorem periodic_comp_mk (f : AddCircle P → X) :
    Function.Periodic (fun s : ℝ => f (s : AddCircle P)) P := fun s => by
  simp only [AddCircle.coe_add_period]

/-- The lift is interval integrable on every bounded interval. -/
theorem intervalIntegrable_comp_mk (f : Lp X q (AddCircle.haarAddCircle (T := P))) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => f (s : AddCircle P)) volume a b := by
  refine (periodic_comp_mk (f : AddCircle P → X)).intervalIntegrable (t := 0) hP.out.ne' ?_ a b
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 0 + P by linarith [hP.out])).mpr
    (integrableOn_comp_mk_Ioc f 0)

theorem integrableOn_comp_mk (f : Lp X q (AddCircle.haarAddCircle (T := P))) {a b : ℝ} :
    IntegrableOn (fun s : ℝ => f (s : AddCircle P)) (Ioo a b) volume := by
  rcases le_or_gt a b with hab | hab
  · exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      (intervalIntegrable_comp_mk f a b))
  · rw [Ioo_eq_empty_of_le hab.le]; exact integrableOn_empty

/-- **One period of the norm**: `∫_s^{s+P} ‖f(r)‖ dr ≤ P ‖f‖` (normalised measure, `q ≥ 1`). -/
theorem intervalIntegral_norm_comp_mk_le (f : Lp X q (AddCircle.haarAddCircle (T := P)))
    (s : ℝ) : ∫ r in s..s + P, ‖f (r : AddCircle P)‖ ≤ P * ‖f‖ := by
  rw [AddCircle.intervalIntegral_preimage P s (fun x => ‖f x‖),
    AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hP.out.le, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ hP.out.le
  calc ∫ x, ‖f x‖ ∂AddCircle.haarAddCircle
      = (eLpNorm f 1 AddCircle.haarAddCircle).toReal := by
        rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
          eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm f q AddCircle.haarAddCircle).toReal :=
        ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
          (eLpNorm_le_eLpNorm_of_exponent_le Fact.out (Lp.aestronglyMeasurable f))
    _ = ‖f‖ := (Lp.norm_def f).symm

/-- A continuous function on the circle that agrees a.e. on one period with the lift of `f`
agrees with `f` almost everywhere for the Haar measure. -/
theorem ae_eq_of_ae_eq_comp_mk {g : AddCircle P → X} (hg : Continuous g)
    (f : Lp X q (AddCircle.haarAddCircle (T := P)))
    (h : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) (0 + P))), g (t : AddCircle P) = f (t : AddCircle P)) :
    g =ᵐ[AddCircle.haarAddCircle] f := by
  set f' := (Lp.aestronglyMeasurable f).mk (f : AddCircle P → X) with hf'def
  have hf' : (f : AddCircle P → X) =ᵐ[AddCircle.haarAddCircle] f' :=
    (Lp.aestronglyMeasurable f).ae_eq_mk
  have hf'v : (f : AddCircle P → X) =ᵐ[volume] f' := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure hf' _
  have hmp := AddCircle.measurePreserving_mk P 0
  have h2 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) (0 + P))), g (t : AddCircle P) = f' (t : AddCircle P) := by
    filter_upwards [h, hmp.quasiMeasurePreserving.ae_eq_comp hf'v] with t h1 h2
    rw [h1]
    exact h2
  have hmeas : MeasurableSet {x | g x = f' x} :=
    hg.stronglyMeasurable.measurableSet_eq_fun (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have h3 : ∀ᵐ x ∂(volume : Measure (AddCircle P)), g x = f' x := by
    rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable hmeas]
    exact h2
  have h4 : ∀ᵐ x ∂AddCircle.haarAddCircle, g x = f' x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at h3
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP.out).ne').mp h3
  filter_upwards [h4, hf'] with x a b
  rw [a, b]

end UnforcedLeray.PhaseTrace
