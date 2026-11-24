import UnforcedLeray.Cons.C08PhysicalMode.Free

/-!
# C08-reg, part 1: the similarity chart `(t, y) ↦ (e^t, e^{t/2} y)`

`paper/main.tex` lines 7479–7500 (blueprint unit B0424, `eq:free-stress-13`,
`eq:free-stress-14`): the fixed-window estimate puts `v(t, x) = e^{-t/2} w(τ₀ + t, e^{-t/2} x)`
and `θ = e^t`, so that a similarity solution becomes a heat solution in `(θ, x)`. Composing the
two substitutions, a point `(t, y)` of similarity variables corresponds to the point
`(θ, x) = (e^t, e^{t/2} y)` of heat variables. This file proves the change of variables for that
chart (with the center `τ₀ = 0`; the windows are recentred in `FreeLaplacianRegularity.lean`).

* `simE z = (e^{z.1}, e^{z.1/2} z.2)`, with left inverse `simG X = (log X.1, e^{-log X.1/2} X.2)`;
  `simE` is a measurable embedding with range the half-space `posHalf = {θ > 0}`.
* `map_simE`: the image of `e^{5t/2} dt dy` (`simMeasure`) under `simE` is Lebesgue measure on
  `posHalf` (the Jacobian `e^t · (e^{t/2})³`).
* `integral_eq_of_vanish`, `integrable_of_vanish`: `∫_{ℝ × ℝ³} f = ∫ e^{5t/2} f ∘ simE` for `f`
  vanishing on `θ ≤ 0`, and integrability transfers.
* `push f`: the function `f ∘ simG` on `θ > 0`, extended by zero; `push f ∘ simE = f` and
  `push f ∈ L²` when `f ∈ L²(e^{5t/2} dt dy)` (`memLp_push`).
* On a time slab `[a, b] × ℝ³` the weight `e^{5t/2}` is bounded above and below, so `L²` for
  `simMeasure` and for Lebesgue measure agree there (`memLp_simMeasure_of_slab`,
  `memLp_slab_of_simMeasure`).
* `IsY2.memLp_slab`: a periodic `𝒴₂` field is square integrable on every slab `[a, b] × ℝ³`.

No junk values: `simG` uses `log` only on `θ > 0`; `push f` is defined to be `0` on `θ ≤ 0`.

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.L2.FreeLapReg

open UnforcedLeray.Blueprint

/-! ## The chart -/

/-- The chart `(t, y) ↦ (θ, x) = (e^t, e^{t/2} y)` from similarity to heat variables (tex
7484–7497, B0424, with `τ₀ = 0`). -/
def simE (z : SpaceTime) : SpaceTime := (Real.exp z.1, Real.exp (z.1 / 2) • z.2)

/-- The inverse chart `(θ, x) ↦ (log θ, θ^{-1/2} x)`, meaningful for `θ > 0`. -/
def simG (X : SpaceTime) : SpaceTime := (Real.log X.1, Real.exp (-(Real.log X.1 / 2)) • X.2)

/-- The half-space `{θ > 0}` of heat variables. -/
def posHalf : Set SpaceTime := Ioi (0 : ℝ) ×ˢ univ

/-- The Jacobian `e^{5t/2}` of `simE`. -/
def dens (z : SpaceTime) : ℝ≥0 := ⟨Real.exp (5 / 2 * z.1), (Real.exp_pos _).le⟩

/-- The measure `e^{5t/2} dt dy` on similarity variables. -/
def simMeasure : Measure SpaceTime := volume.withDensity fun z => (dens z : ℝ≥0∞)

theorem measurableSet_posHalf : MeasurableSet posHalf :=
  measurableSet_Ioi.prod MeasurableSet.univ

theorem continuous_simE : Continuous simE := by
  unfold simE
  fun_prop

theorem measurable_simG : Measurable simG := by
  unfold simG
  refine (Real.measurable_log.comp measurable_fst).prodMk ?_
  exact (Real.measurable_exp.comp ((Real.measurable_log.comp measurable_fst).div_const 2).neg).smul
    measurable_snd

theorem simE_fst (z : SpaceTime) : (simE z).1 = Real.exp z.1 := rfl

theorem simE_fst_pos (z : SpaceTime) : 0 < (simE z).1 := Real.exp_pos _

theorem simG_simE (z : SpaceTime) : simG (simE z) = z := by
  obtain ⟨t, y⟩ := z
  simp only [simE, simG, Real.log_exp, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    one_smul]

theorem simE_simG {X : SpaceTime} (hX : 0 < X.1) : simE (simG X) = X := by
  obtain ⟨θ, x⟩ := X
  simp only [simE, simG, Real.exp_log hX, smul_smul, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_smul]

theorem range_simE : range simE = posHalf := by
  ext X
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨simE_fst_pos z, mem_univ _⟩
  · intro hX
    exact ⟨simG X, simE_simG hX.1⟩

theorem measurableEmbedding_simE : MeasurableEmbedding simE :=
  MeasurableEmbedding.of_measurable_inverse continuous_simE.measurable
    (by rw [range_simE]; exact measurableSet_posHalf) measurable_simG simG_simE

theorem measurable_dens : Measurable dens :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).subtype_mk

theorem coe_dens (z : SpaceTime) : (dens z : ℝ) = Real.exp (5 / 2 * z.1) := rfl

theorem ennreal_dens (z : SpaceTime) :
    (dens z : ℝ≥0∞) = ENNReal.ofReal (Real.exp (5 / 2 * z.1)) := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_dens]

/-! ## The change of variables -/

/-- Spatial dilation: `∫ f = r³ ∫ f(r y) dy` for `r > 0`. -/
theorem lintegral_space_eq_smul (f : Space → ℝ≥0∞) (hf : Measurable f) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, f x = ENNReal.ofReal (r ^ 3) * ∫⁻ y, f (r • y) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure Space) hr.ne'
  rw [finrank_euclideanSpace_fin] at hmap
  have h1 : ∫⁻ y, f (r • y) = ∫⁻ x, f x ∂(Measure.map (r • ·) volume) :=
    (lintegral_map hf (measurable_const_smul r)).symm
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

theorem exp_five_halves (t : ℝ) :
    Real.exp t * Real.exp (t / 2) ^ 3 = Real.exp (5 / 2 * t) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The change of variables** for nonnegative functions:
`∫_{θ > 0} g(θ, x) dθ dx = ∫ e^{5t/2} g(e^t, e^{t/2} y) dt dy`. -/
theorem lintegral_posHalf (g : SpaceTime → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ X in posHalf, g X = ∫⁻ z, (dens z : ℝ≥0∞) * g (simE z) := by
  have hprod : (volume : Measure SpaceTime).restrict posHalf =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Space) := by
    rw [posHalf, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hH : Measurable fun θ : ℝ => ∫⁻ x, g (θ, x) := hg.lintegral_prod_right'
  rw [hprod, lintegral_prod _ hg.aemeasurable, ← Real.range_exp, ← image_univ,
    lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
      (fun θ => ∫⁻ x, g (θ, x)), Measure.restrict_univ]
  have hm : Measurable fun z : SpaceTime => (dens z : ℝ≥0∞) * g (simE z) :=
    measurable_dens.coe_nnreal_ennreal.mul (hg.comp continuous_simE.measurable)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun t => ?_
  have hgt : Measurable fun x : Space => g (Real.exp t, x) := hg.comp measurable_prodMk_left
  rw [lintegral_space_eq_smul _ hgt (Real.exp_pos (t / 2)), abs_of_pos (Real.exp_pos t),
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos t).le, exp_five_halves,
    ← lintegral_const_mul _ (f := fun y => g (Real.exp t, Real.exp (t / 2) • y))
      (hgt.comp (measurable_const_smul _))]
  refine lintegral_congr fun y => ?_
  rw [ennreal_dens]
  rfl

/-- **The image measure**: `simE` carries `e^{5t/2} dt dy` to Lebesgue measure on `θ > 0`. -/
theorem map_simE : Measure.map simE simMeasure = volume.restrict posHalf := by
  ext A hA
  have hpre : MeasurableSet (simE ⁻¹' A) := continuous_simE.measurable hA
  rw [Measure.map_apply continuous_simE.measurable hA, simMeasure, withDensity_apply _ hpre,
    ← lintegral_indicator_one (μ := volume.restrict posHalf) hA,
    lintegral_posHalf (A.indicator 1) (measurable_one.indicator hA), ← lintegral_indicator hpre]
  refine lintegral_congr fun z => ?_
  by_cases h : simE z ∈ A
  · rw [Set.indicator_of_mem (show z ∈ simE ⁻¹' A from h), Set.indicator_of_mem h]
    simp
  · rw [Set.indicator_of_notMem (show z ∉ simE ⁻¹' A from h), Set.indicator_of_notMem h]
    simp

theorem integral_posHalf (f : SpaceTime → ℝ) :
    ∫ X in posHalf, f X = ∫ z, Real.exp (5 / 2 * z.1) * f (simE z) := by
  rw [← map_simE, measurableEmbedding_simE.integral_map, simMeasure,
    integral_withDensity_eq_integral_smul measurable_dens]
  rfl

theorem notMem_posHalf {X : SpaceTime} (hX : X ∉ posHalf) : X.1 ≤ 0 := by
  by_contra h
  exact hX ⟨lt_of_not_ge h, mem_univ _⟩

/-- **Change of variables for integrals** of functions vanishing on `θ ≤ 0`. -/
theorem integral_eq_of_vanish {f : SpaceTime → ℝ} (hf : ∀ X : SpaceTime, X.1 ≤ 0 → f X = 0) :
    ∫ X, f X = ∫ z, Real.exp (5 / 2 * z.1) * f (simE z) := by
  rw [← integral_posHalf, setIntegral_eq_integral_of_forall_compl_eq_zero]
  exact fun X hX => hf X (notMem_posHalf hX)

theorem indicator_eq_of_vanish {E : Type*} [Zero E] {f : SpaceTime → E}
    (hf : ∀ X : SpaceTime, X.1 ≤ 0 → f X = 0) : posHalf.indicator f = f := by
  funext X
  by_cases hX : X ∈ posHalf
  · rw [Set.indicator_of_mem hX]
  · rw [Set.indicator_of_notMem hX, hf X (notMem_posHalf hX)]

/-- **Integrability transfers** for functions vanishing on `θ ≤ 0`. -/
theorem integrable_of_vanish {f : SpaceTime → ℝ} (hf : ∀ X : SpaceTime, X.1 ≤ 0 → f X = 0)
    (hi : Integrable f) : Integrable (fun z => Real.exp (5 / 2 * z.1) * f (simE z)) := by
  rw [← indicator_eq_of_vanish hf, integrable_indicator_iff measurableSet_posHalf,
    IntegrableOn, ← map_simE, measurableEmbedding_simE.integrable_map_iff, simMeasure,
    integrable_withDensity_iff_integrable_smul measurable_dens] at hi
  exact hi

/-! ## Functions on the half-space -/

/-- `f ∘ simG` on `θ > 0`, extended by zero to `θ ≤ 0`. -/
def push (f : SpaceTime → ℝ) (X : SpaceTime) : ℝ := if 0 < X.1 then f (simG X) else 0

theorem push_simE (f : SpaceTime → ℝ) (z : SpaceTime) : push f (simE z) = f z := by
  simp only [push, simE_fst_pos z, ↓reduceIte, simG_simE]

theorem push_of_nonpos (f : SpaceTime → ℝ) {X : SpaceTime} (hX : X.1 ≤ 0) : push f X = 0 := by
  simp only [push, not_lt.mpr hX, ↓reduceIte]

theorem push_eq_indicator (f : SpaceTime → ℝ) : push f = posHalf.indicator (f ∘ simG) := by
  funext X
  by_cases hX : 0 < X.1
  · rw [Set.indicator_of_mem (show X ∈ posHalf from ⟨hX, mem_univ _⟩)]
    simp only [push, hX, ↓reduceIte, Function.comp]
  · rw [Set.indicator_of_notMem (fun h => hX h.1)]
    simp only [push, hX, ↓reduceIte]

theorem memLp_push {f : SpaceTime → ℝ} (hf : MemLp f 2 simMeasure) : MemLp (push f) 2 volume := by
  rw [push_eq_indicator, memLp_indicator_iff_restrict measurableSet_posHalf, ← map_simE,
    measurableEmbedding_simE.memLp_map_measure_iff]
  have e : (f ∘ simG) ∘ simE = f := funext fun z => by simp only [Function.comp, simG_simE]
  rw [e]
  exact hf

theorem memLp_comp_simE {F : SpaceTime → ℝ} (hF : MemLp F 2 volume) :
    MemLp (F ∘ simE) 2 simMeasure := by
  rw [← measurableEmbedding_simE.memLp_map_measure_iff, map_simE]
  exact hF.restrict _

/-! ## Slabs -/

/-- The time slab `[a, b] × ℝ³`. -/
def slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab a b) :=
  measurableSet_Icc.prod MeasurableSet.univ

theorem simMeasure_restrict_le (a b : ℝ) :
    simMeasure.restrict (slab a b) ≤
      ENNReal.ofReal (Real.exp (5 / 2 * b)) • volume.restrict (slab a b) := by
  rw [simMeasure, restrict_withDensity (measurableSet_slab a b), ← withDensity_const]
  refine withDensity_mono ?_
  refine (ae_restrict_iff' (measurableSet_slab a b)).mpr (Eventually.of_forall fun z hz => ?_)
  show (dens z : ℝ≥0∞) ≤ _
  rw [ennreal_dens]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hz.1.2]))

theorem volume_restrict_le (a b : ℝ) :
    volume.restrict (slab a b) ≤
      ENNReal.ofReal (Real.exp (-(5 / 2 * a))) • simMeasure.restrict (slab a b) := by
  rw [simMeasure, restrict_withDensity (measurableSet_slab a b),
    ← withDensity_smul _ measurable_dens.coe_nnreal_ennreal]
  conv_lhs => rw [← withDensity_one (μ := volume.restrict (slab a b))]
  refine withDensity_mono ?_
  refine (ae_restrict_iff' (measurableSet_slab a b)).mpr (Eventually.of_forall fun z hz => ?_)
  simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul, ennreal_dens]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith [hz.1.1]))

theorem memLp_simMeasure_of_slab {f : SpaceTime → ℝ} {a b : ℝ}
    (hf : MemLp f 2 (volume.restrict (slab a b))) (h0 : ∀ z, z ∉ slab a b → f z = 0) :
    MemLp f 2 simMeasure := by
  have e : (slab a b).indicator f = f := by
    funext z
    by_cases hz : z ∈ slab a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, h0 z hz]
  rw [← e, memLp_indicator_iff_restrict (measurableSet_slab a b)]
  exact MemLp.of_measure_le_smul ENNReal.ofReal_ne_top (simMeasure_restrict_le a b) hf

theorem memLp_slab_of_simMeasure {f : SpaceTime → ℝ} (hf : MemLp f 2 simMeasure) (a b : ℝ) :
    MemLp f 2 (volume.restrict (slab a b)) :=
  MemLp.of_measure_le_smul ENNReal.ofReal_ne_top (volume_restrict_le a b) (hf.restrict _)

/-! ## Time shifts -/

/-- The time shift `(t, y) ↦ (t + c, y)` as a measurable equivalence. -/
def timeShift (c : ℝ) : SpaceTime ≃ᵐ SpaceTime where
  toFun z := (z.1 + c, z.2)
  invFun z := (z.1 - c, z.2)
  left_inv z := by simp
  right_inv z := by simp
  measurable_toFun := (measurable_fst.add_const c).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub_const c).prodMk measurable_snd

theorem timeShift_apply (c : ℝ) (z : SpaceTime) : timeShift c z = (z.1 + c, z.2) := rfl

theorem measurePreserving_timeShift (c : ℝ) :
    MeasurePreserving (timeShift c) volume volume := by
  have e : ⇑(timeShift c) = Prod.map (fun t : ℝ => t + c) id := rfl
  rw [e, Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume c).prod (MeasurePreserving.id volume)

theorem integral_timeShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SpaceTime → E) (c : ℝ) : ∫ z : SpaceTime, g (z.1 + c, z.2) = ∫ z, g z :=
  (measurePreserving_timeShift c).integral_comp' g

/-! ## Periodic `𝒴₂` fields on slabs -/

theorem memLp_restrict_union {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hfm : AEStronglyMeasurable f μ) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h1 : MemLp f 2 (μ.restrict s))
    (h2 : MemLp f 2 (μ.restrict t)) : MemLp f 2 (μ.restrict (s ∪ t)) := by
  rw [← memLp_indicator_iff_restrict (hs.union ht)]
  rw [← memLp_indicator_iff_restrict hs] at h1
  rw [← memLp_indicator_iff_restrict ht] at h2
  refine (h1.norm.add h2.norm).of_le (hfm.indicator (hs.union ht)) (Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ ‖s.indicator f x‖ + ‖t.indicator f x‖ := by positivity
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg hn]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem (Set.mem_union_left t hxs), Set.indicator_of_mem hxs]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · by_cases hxt : x ∈ t
    · rw [Set.indicator_of_mem (Set.mem_union_right s hxt), Set.indicator_of_mem hxt]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · rw [Set.indicator_of_notMem (fun h : x ∈ s ∪ t => h.elim hxs hxt), norm_zero]
      exact hn

section Periodic

variable {P : ℝ} {f : ℝ → SpatialField}

/-- The period slab translated by `k` periods. -/
theorem memLp_period_shift (hf : B0005.IsY2 P f) (k : ℤ) :
    MemLp (fun z : SpaceTime => f z.1 z.2) 2
      (volume.restrict (Ioc (k * P) (k * P + P) ×ˢ (univ : Set Space))) := by
  have hpre : (timeShift (-(k * P))) ⁻¹' periodSlab P =
      Ioc (k * P) (k * P + P) ×ˢ (univ : Set Space) := by
    ext z
    simp only [periodSlab, mem_preimage, mem_prod, mem_Ioc, mem_univ, and_true, timeShift_apply]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hmp : MeasurePreserving (timeShift (-(k * P)))
      (volume.restrict (Ioc (k * P) (k * P + P) ×ˢ (univ : Set Space)))
      (volume.restrict (periodSlab P)) := by
    have := (measurePreserving_timeShift (-(k * P))).restrict_preimage (s := periodSlab P)
      (measurableSet_Ioc.prod MeasurableSet.univ)
    rwa [hpre] at this
  have h := hf.memL2.comp_measurePreserving hmp
  have e : (fun z : SpaceTime => f z.1 z.2) ∘ (timeShift (-(k * P))) =
      fun z : SpaceTime => f z.1 z.2 := by
    funext z
    simp only [Function.comp, timeShift_apply]
    rw [← sub_eq_add_neg, (hf.periodic.int_mul k).sub_eq]
  rwa [e] at h

theorem memLp_Ioc_mul (hf : B0005.IsY2 P f) (m : ℤ) :
    ∀ n : ℤ, m ≤ n → MemLp (fun z : SpaceTime => f z.1 z.2) 2
      (volume.restrict (Ioc (m * P) (n * P) ×ˢ (univ : Set Space))) := by
  intro n hn
  induction n, hn using Int.le_induction with
  | base => simp
  | succ n hmn ih =>
    by_cases hP : P ≤ 0
    · have hemp : Ioc (m * P) (((n + 1 : ℤ) : ℝ) * P) ⊆ Ioc (m * P) (n * P) ∪
          Ioc (n * P) (n * P + P) := by
        intro x hx
        left
        refine ⟨hx.1, hx.2.trans ?_⟩
        push_cast
        nlinarith
      refine MemLp.mono_measure (Measure.restrict_mono (Set.prod_mono hemp le_rfl) le_rfl) ?_
      rw [union_prod]
      exact memLp_restrict_union hf.measurable (measurableSet_Ioc.prod MeasurableSet.univ)
        (measurableSet_Ioc.prod MeasurableSet.univ) ih (memLp_period_shift hf n)
    · have hsplit : Ioc (m * P) (((n + 1 : ℤ) : ℝ) * P) =
          Ioc (m * P) (n * P) ∪ Ioc (n * P) (n * P + P) := by
        push_cast
        rw [add_mul, one_mul, Ioc_union_Ioc_eq_Ioc]
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (le_of_not_ge hP)
        · linarith [le_of_not_ge hP]
      rw [hsplit, union_prod]
      exact memLp_restrict_union hf.measurable (measurableSet_Ioc.prod MeasurableSet.univ)
        (measurableSet_Ioc.prod MeasurableSet.univ) ih (memLp_period_shift hf n)

/-- **A periodic `𝒴₂` field is square integrable on every slab** `[a, b] × ℝ³`. -/
theorem IsY2.memLp_slab (hP : 0 < P) (hf : B0005.IsY2 P f) (a b : ℝ) :
    MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (slab a b)) := by
  obtain ⟨m, hm⟩ := exists_int_lt (a / P)
  obtain ⟨n, hn⟩ := exists_int_gt (b / P)
  by_cases hab : a ≤ b
  · have hmn : m ≤ n := by
      have : a / P ≤ b / P := div_le_div_of_nonneg_right hab hP.le
      exact_mod_cast ((hm.trans_le this).trans hn).le
    refine MemLp.mono_measure (Measure.restrict_mono (Set.prod_mono ?_ le_rfl) le_rfl)
      (memLp_Ioc_mul hf m n hmn)
    intro x hx
    constructor
    · have := (lt_div_iff₀ hP).mp (hm.trans_le (div_le_div_of_nonneg_right hx.1 hP.le))
      linarith
    · have := (div_lt_iff₀ hP).mp ((div_le_div_of_nonneg_right hx.2 hP.le).trans_lt hn)
      linarith
  · have : slab a b = ∅ := by
      ext z
      simp only [slab, mem_prod, mem_Icc, mem_univ, and_true, mem_empty_iff_false, iff_false,
        not_and]
      intro h1 h2
      exact hab (h1.trans h2)
    rw [this]
    simp

end Periodic

end UnforcedLeray.Cons.L2.FreeLapReg
