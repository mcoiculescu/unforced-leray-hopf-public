import UnforcedLeray.Units.B0220.ChangeOfVariables

/-!
# B0220 helper: the meridional frame, the lifts `U = a b`, `F = a³ g` and their `L²` identities

Blueprint unit B0220 (label `eq:st18-t00113`), `paper/main.tex` lines 3279–3314.

A `c`-periodic profile `b` lifts to `U(x,τ) = a b(s,q,η)` and a source `g` to
`F(x,τ) = a³ g(s,q,η)` (tex lines 3290–3293); for meridional vector fields the components of
`b` are taken in `(e_r, e_z)` (tex lines 3294–3295). Over one `τ` period and the full azimuth
(tex lines 3295–3304)
`‖U‖² = 2πε² ∫ s^{-3/2}|b|² ds dq dη` and `‖F‖² = 2πε² ∫ s^{1/2}|g|² ds dq dη`.

We give both readings of the lift formula: `liftU`, `liftF` lift a profile with values in any
normed space `E` componentwise, and `fieldU`, `fieldF` lift a meridional profile
`b = (b_r, b_z)` to the physical vector field `a (b_r e_r + b_z e_z)`. The identities are stated
for the lower Lebesgue integral of `‖·‖ₑ²`, so they hold (possibly as `∞ = ∞`) for every
measurable `c`-periodic profile, with no integrability assumption.

On the axis `r = 0` the Lean values `a = 0⁻¹ = 0` and `e_r = 0` are junk; the axis is a null
set (`volume_axis`), and the lifts vanish there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.B0220

/-- Meridional components `(b_r, b_z)` of a profile (tex lines 3294–3295). -/
abbrev Merid := EuclideanSpace ℝ (Fin 2)

/-- The radial unit vector `e_r = (cos φ, sin φ, 0)`; on the axis its Lean value is `0`. -/
def unitR (x : Space) : Space :=
  (x 0 / radius x) • EuclideanSpace.single 0 1 + (x 1 / radius x) • EuclideanSpace.single 1 1

/-- The axial unit vector `e_z`. -/
def unitZ : Space := EuclideanSpace.single 2 1

/-- The meridional frame `(v_r, v_z) ↦ v_r e_r + v_z e_z` (tex line 3295). -/
def frame (x : Space) : Merid →ₗ[ℝ] Space where
  toFun v := v 0 • unitR x + v 1 • unitZ
  map_add' u v := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' r v := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

theorem frame_apply (x : Space) (v : Merid) : frame x v = v 0 • unitR x + v 1 • unitZ := rfl

theorem norm_frame {x : Space} (hx : radius x ≠ 0) (v : Merid) : ‖frame x v‖ = ‖v‖ := by
  have hr2 : radius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [frame_apply, unitR, unitZ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, add_zero,
    zero_add]
  field_simp
  linear_combination (-(v 0 ^ 2)) * hr2

theorem measurable_unitR : Measurable unitR := by
  have h0 : Measurable fun x : Space => x 0 := (PiLp.continuous_apply 2 _ 0).measurable
  have h1 : Measurable fun x : Space => x 1 := (PiLp.continuous_apply 2 _ 1).measurable
  exact ((h0.div measurable_radius).smul_const _).add ((h1.div measurable_radius).smul_const _)

theorem measurable_frame_uncurry {α : Type*} [MeasurableSpace α] {X : α → Space}
    (hX : Measurable X) : Measurable fun p : α × Merid => frame (X p.1) p.2 := by
  have h0 : Measurable fun p : α × Merid => p.2 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).measurable.comp measurable_snd
  have h1 : Measurable fun p : α × Merid => p.2 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).measurable.comp measurable_snd
  simp only [frame_apply]
  exact (h0.smul (measurable_unitR.comp (hX.comp measurable_fst))).add (h1.smul_const _)

/-! ### Elementary chart identities -/

theorem liftA_nonneg (x : Space) : 0 ≤ liftA x := inv_nonneg.2 (Real.sqrt_nonneg _)

theorem liftA_sq (x : Space) : liftA x ^ 2 = ageS x := by
  simp only [liftA, ageS, inv_pow]

theorem liftA_eq_zero {x : Space} (hx : radius x = 0) : liftA x = 0 := by
  simp [liftA, hx]

theorem chart_fst (ε : ℝ) (y : Space × ℝ) : (chart ε y).1 = liftA y.1 ^ 2 :=
  (liftA_sq y.1).symm

/-- One `τ` period `2εc` shifts `q` by one cell `c` (tex lines 3289–3290). -/
theorem chart_add_period {ε : ℝ} (hε : ε ≠ 0) (c : ℝ) (x : Space) (τ : ℝ) :
    chart ε (x, τ + 2 * ε * c) =
      ((chart ε (x, τ)).1, (chart ε (x, τ)).2.1 + c, (chart ε (x, τ)).2.2) := by
  simp only [chart, cellQ, Prod.mk.injEq, true_and, and_true]
  field_simp
  ring

/-! ### The lifts (tex lines 3290–3293) -/

section Lifts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lift `U(x,τ) = a b(s,q,η)` of a profile, componentwise (tex line 3292). -/
def liftU (ε : ℝ) (b : Profile → E) (y : Space × ℝ) : E := liftA y.1 • b (chart ε y)

/-- The source lift `F(x,τ) = a³ g(s,q,η)`, componentwise (tex line 3292). -/
def liftF (ε : ℝ) (g : Profile → E) (y : Space × ℝ) : E := liftA y.1 ^ 3 • g (chart ε y)

/-- The meridional lift `U = a (b_r e_r + b_z e_z)` (tex lines 3292–3295). -/
def fieldU (ε : ℝ) (b : Profile → Merid) (y : Space × ℝ) : Space :=
  liftA y.1 • frame y.1 (b (chart ε y))

/-- The meridional source lift `F = a³ (g_r e_r + g_z e_z)` (tex lines 3292–3295). -/
def fieldF (ε : ℝ) (g : Profile → Merid) (y : Space × ℝ) : Space :=
  liftA y.1 ^ 3 • frame y.1 (g (chart ε y))

/-- `F = a³ g = a (s g)`: the source lift is the lift of `M_s g = s g`. -/
theorem liftF_eq_liftU (ε : ℝ) (g : Profile → E) :
    liftF ε g = liftU ε (fun p => p.1 • g p) := by
  funext y
  simp only [liftF, liftU, chart_fst, smul_smul]
  ring_nf

theorem fieldF_eq_fieldU (ε : ℝ) (g : Profile → Merid) :
    fieldF ε g = fieldU ε (fun p => p.1 • g p) := by
  funext y
  simp only [fieldF, fieldU, chart_fst, map_smul, smul_smul]
  ring_nf

/-- A `c`-periodic profile lifts to a `τ`-periodic field of period `2εc` (tex lines 3289–3290). -/
theorem liftU_periodic {ε c : ℝ} (hε : ε ≠ 0) {b : Profile → E} (hb : QPeriodic c b)
    (x : Space) (τ : ℝ) : liftU ε b (x, τ + 2 * ε * c) = liftU ε b (x, τ) := by
  rw [liftU, liftU, chart_add_period hε c x τ, hb (chart ε (x, τ))]

theorem liftF_periodic {ε c : ℝ} (hε : ε ≠ 0) {g : Profile → E} (hg : QPeriodic c g)
    (x : Space) (τ : ℝ) : liftF ε g (x, τ + 2 * ε * c) = liftF ε g (x, τ) := by
  rw [liftF, liftF, chart_add_period hε c x τ, hg (chart ε (x, τ))]

theorem fieldU_periodic {ε c : ℝ} (hε : ε ≠ 0) {b : Profile → Merid} (hb : QPeriodic c b)
    (x : Space) (τ : ℝ) : fieldU ε b (x, τ + 2 * ε * c) = fieldU ε b (x, τ) := by
  rw [fieldU, fieldU, chart_add_period hε c x τ, hb (chart ε (x, τ))]

theorem fieldF_periodic {ε c : ℝ} (hε : ε ≠ 0) {g : Profile → Merid} (hg : QPeriodic c g)
    (x : Space) (τ : ℝ) : fieldF ε g (x, τ + 2 * ε * c) = fieldF ε g (x, τ) := by
  rw [fieldF, fieldF, chart_add_period hε c x τ, hg (chart ε (x, τ))]

/-! ### Pointwise norms: `|U| = a|b|`, `|F| = a³|g|` -/

theorem norm_liftU (ε : ℝ) (b : Profile → E) (y : Space × ℝ) :
    ‖liftU ε b y‖ = liftA y.1 * ‖b (chart ε y)‖ := by
  rw [liftU, norm_smul, Real.norm_of_nonneg (liftA_nonneg _)]

theorem norm_fieldU (ε : ℝ) (b : Profile → Merid) (y : Space × ℝ) :
    ‖fieldU ε b y‖ = liftA y.1 * ‖b (chart ε y)‖ := by
  rw [fieldU, norm_smul, Real.norm_of_nonneg (liftA_nonneg _)]
  by_cases hx : radius y.1 = 0
  · simp [liftA_eq_zero hx]
  · rw [norm_frame hx]

/-- The pointwise identity behind the `L²` identities: `‖a w‖ₑ² = a² ‖w‖ₑ²`. -/
theorem enorm_sq_of_norm {V : Type*} [NormedAddCommGroup V] {a t : ℝ} (ha : 0 ≤ a) {v : V}
    (hv : ‖v‖ = a * t) :
    ‖v‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ENNReal.ofReal t ^ 2 := by
  rw [← ofReal_norm, hv, ENNReal.ofReal_mul ha, mul_pow, ENNReal.ofReal_pow ha]

theorem enorm_liftU_sq (ε : ℝ) (b : Profile → E) (y : Space × ℝ) :
    ‖liftU ε b y‖ₑ ^ 2 = ENNReal.ofReal (liftA y.1 ^ 2) * ‖b (chart ε y)‖ₑ ^ 2 := by
  rw [enorm_sq_of_norm (v := liftU ε b y) (liftA_nonneg _) (norm_liftU ε b y), ofReal_norm]

theorem enorm_fieldU_sq (ε : ℝ) (b : Profile → Merid) (y : Space × ℝ) :
    ‖fieldU ε b y‖ₑ ^ 2 = ENNReal.ofReal (liftA y.1 ^ 2) * ‖b (chart ε y)‖ₑ ^ 2 := by
  rw [enorm_sq_of_norm (v := fieldU ε b y) (liftA_nonneg _) (norm_fieldU ε b y), ofReal_norm]

/-- The source density `s² |g|²`, so that `|F|² = a² s² |g|²`. -/
def sourceDensity {V : Type*} [NormedAddCommGroup V] (g : Profile → V) (p : Profile) : ℝ≥0∞ :=
  ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2

theorem enorm_smul_fst_sq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Profile → V) (p : Profile) (hp : 0 ≤ p.1) :
    ‖p.1 • g p‖ₑ ^ 2 = sourceDensity g p := by
  rw [sourceDensity, enorm_sq_of_norm (v := p.1 • g p) hp
    (by rw [norm_smul, Real.norm_of_nonneg hp]), ofReal_norm]

theorem enorm_liftF_sq (ε : ℝ) (g : Profile → E) (y : Space × ℝ) :
    ‖liftF ε g y‖ₑ ^ 2 = ENNReal.ofReal (liftA y.1 ^ 2) * sourceDensity g (chart ε y) := by
  rw [liftF_eq_liftU, enorm_liftU_sq, enorm_smul_fst_sq _ _ (by
    rw [chart_fst]; positivity)]

theorem enorm_fieldF_sq (ε : ℝ) (g : Profile → Merid) (y : Space × ℝ) :
    ‖fieldF ε g y‖ₑ ^ 2 = ENNReal.ofReal (liftA y.1 ^ 2) * sourceDensity g (chart ε y) := by
  rw [fieldF_eq_fieldU, enorm_fieldU_sq, enorm_smul_fst_sq _ _ (by
    rw [chart_fst]; positivity)]

/-! ### The `L²` identities (tex lines 3295–3304) -/

variable [MeasurableSpace E] [OpensMeasurableSpace E]

theorem qPeriodic_enorm_sq {V : Type*} [NormedAddCommGroup V] {c : ℝ} {b : Profile → V}
    (hb : QPeriodic c b) : QPeriodic c fun p => ‖b p‖ₑ ^ 2 := fun p => by
  simp only [hb p]

/-- `s^{-3/2} · s² = s^{1/2}` for `s > 0`. -/
theorem weight_mul_sq {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal (s ^ 2) =
      ENNReal.ofReal (s ^ (1 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two, ← Real.rpow_add hs]
  norm_num

/-- `‖U‖²_{L²(dx dτ)} = 2πε² ∫ s^{-3/2} |b|² ds dq dη` over one `τ` period, the full azimuth
and one `q`-cell (tex lines 3295–3300), componentwise reading. -/
theorem lintegral_liftU {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : Profile → E)
    (hb : Measurable b) (hper : QPeriodic c b) :
    ∫⁻ y, ‖liftU ε b y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖b p‖ₑ ^ 2 := by
  simp_rw [enorm_liftU_sq]
  exact lintegral_chart hε hc (fun p => ‖b p‖ₑ ^ 2) (hb.enorm.pow_const 2)
    (qPeriodic_enorm_sq hper)

/-- `‖U‖²_{L²(dx dτ)} = 2πε² ∫ s^{-3/2} |b|² ds dq dη` for the meridional field
`U = a (b_r e_r + b_z e_z)` (tex lines 3294–3300). -/
theorem lintegral_fieldU {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : Profile → Merid)
    (hb : Measurable b) (hper : QPeriodic c b) :
    ∫⁻ y, ‖fieldU ε b y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖b p‖ₑ ^ 2 := by
  simp_rw [enorm_fieldU_sq]
  exact lintegral_chart hε hc (fun p => ‖b p‖ₑ ^ 2) (hb.enorm.pow_const 2)
    (qPeriodic_enorm_sq hper)

theorem measurable_sourceDensity {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    [OpensMeasurableSpace V] {g : Profile → V} (hg : Measurable g) :
    Measurable (sourceDensity g) :=
  (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2)).mul (hg.enorm.pow_const 2)

theorem qPeriodic_sourceDensity {V : Type*} [NormedAddCommGroup V] {c : ℝ} {g : Profile → V}
    (hg : QPeriodic c g) : QPeriodic c (sourceDensity g) := fun p => by
  simp only [sourceDensity, hg p]

/-- The source side of the identities: `∫ s^{-3/2} s² |g|² = ∫ s^{1/2} |g|²` on the cell. -/
theorem setLIntegral_cell_source {V : Type*} [NormedAddCommGroup V] (c : ℝ)
    (g : Profile → V) :
    ∫⁻ p in cell c, weightH p * sourceDensity g p =
      ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ)) * ‖g p‖ₑ ^ 2 := by
  refine setLIntegral_congr_fun (measurableSet_cell c) (fun p hp => ?_)
  have hs : 0 < p.1 := hp.1
  rw [weightH, sourceDensity, ← mul_assoc, weight_mul_sq hs]

/-- `‖F‖²_{L²(dx dτ)} = 2πε² ∫ s^{1/2} |g|² ds dq dη` (tex lines 3301–3303), componentwise
reading. -/
theorem lintegral_liftF {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (g : Profile → E)
    (hg : Measurable g) (hper : QPeriodic c g) :
    ∫⁻ y, ‖liftF ε g y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ)) * ‖g p‖ₑ ^ 2 := by
  simp_rw [enorm_liftF_sq]
  rw [lintegral_chart hε hc _ (measurable_sourceDensity hg) (qPeriodic_sourceDensity hper),
    setLIntegral_cell_source]

/-- `‖F‖²_{L²(dx dτ)} = 2πε² ∫ s^{1/2} |g|² ds dq dη` for the meridional source field
`F = a³ (g_r e_r + g_z e_z)` (tex lines 3294–3303). -/
theorem lintegral_fieldF {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (g : Profile → Merid)
    (hg : Measurable g) (hper : QPeriodic c g) :
    ∫⁻ y, ‖fieldF ε g y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ)) * ‖g p‖ₑ ^ 2 := by
  simp_rw [enorm_fieldF_sq]
  rw [lintegral_chart hε hc _ (measurable_sourceDensity hg) (qPeriodic_sourceDensity hper),
    setLIntegral_cell_source]

end Lifts

end UnforcedLeray.B0220
