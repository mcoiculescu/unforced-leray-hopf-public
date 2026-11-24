import UnforcedLeray.Units.B0223.Dilation
import UnforcedLeray.Units.B0220

/-!
# B0223 helper: the complex lifts `J_ε : H → L²(dx dτ)` onto periodic fields

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3341–3368, using the lift
of B0220 (`eq:st18-t00113`, tex lines 3279–3314; `Units/B0220.lean`).

The resolvent `R_ε(μ)` is "conjugated to `H` by `J_ε`" (tex lines 3355–3366). Since `μ` is
complex, we need the complexified lift. B0220's `J` maps real meridional profiles into real
fields on `ℝ³ × (0, 2εc]`; here the same formulas are taken with complex coefficients and with
values in the `τ`-periodic space `X E P`, `P = 2εc` (the cell `(0, P]` and the circle `ℝ/Pℤ`
are identified by `AddCircle.equivIoc`, a measure-preserving map, `mp_toCell`):

* scalar: `liftSc b (x, τ) = (√(2π) ε)⁻¹ a b(s, q, η)`, `b ∈ H = L²(s^{-3/2} ds dq dη; E)`;
* meridional: `liftVec b (x, τ) = (√(2π) ε)⁻¹ a (b_r e_r + b_z e_z)`,
  `b ∈ L²(s^{-3/2} ds dq dη; ℂ²)`, values in `ℂ³` (Cartesian components).

Both are complex linear isometries (the change of variables is B0220's
`map_cellChart_jDensity`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open UnforcedLeray.B0220

namespace UnforcedLeray.B0223

variable {P : ℝ} [Fact (0 < P)]

/-! ### One period of `τ` and the circle -/

/-- The representative in `(0, P]` of a phase: `(x, τ mod P) ↦ (x, τ)`. -/
def toCell (P : ℝ) [Fact (0 < P)] (z : PSpace P) : Space × ℝ :=
  (z.1, ((AddCircle.measurableEquivIoc P 0 z.2 : Ioc (0 : ℝ) (0 + P)) : ℝ))

theorem measurable_toCell : Measurable (toCell P) :=
  measurable_fst.prodMk (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc P 0).measurable.comp measurable_snd))

/-- The identification of the circle with one period `(0, P]` is measure preserving:
`L²(ℝ³ × ℝ/Pℤ) = L²(ℝ³ × (0, P])` (tex lines 3294–3301). -/
theorem mp_toCell :
    MeasurePreserving (toCell P) volume
      ((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 P)) := by
  have h2 : MeasurePreserving
      (fun θ : AddCircle P => ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ))
      volume ((volume : Measure ℝ).restrict (Ioc 0 (0 + P))) :=
    (measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc P)
  have h3 := (MeasurePreserving.id (volume : Measure Space)).prod h2
  have hm : (volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 P) =
      (volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioc 0 (0 + P))) := by
    rw [zero_add, show (volume : Measure (Space × ℝ)) = (volume : Measure Space).prod volume
      from rfl, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm]
  exact h3

variable {ε c : ℝ}

theorem physMeasure_eq (hP : P = 2 * ε * c) :
    physMeasure ε c = (volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 P) := by
  rw [hP]; rfl

/-- The pushforward identity of the lift on the periodic space. -/
theorem map_liftDensity (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    ((volume : Measure (PSpace P)).withDensity
        fun z => ENNReal.ofReal ((jConst ε * liftA z.1) ^ 2)).map
      (fun z => cellChart ε c (toCell P z)) = measureH c := by
  rw [← map_cellChart_jDensity hε hc]
  have hmp := mp_toCell (P := P)
  rw [← physMeasure_eq hP] at hmp
  set D : Space × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((jConst ε * liftA y.1) ^ 2) with hD
  have hDm : Measurable D :=
    ENNReal.measurable_ofReal.comp
      (((measurable_liftA.comp measurable_fst).const_mul _).pow_const 2)
  ext A hA
  have hpre : MeasurableSet (cellChart ε c ⁻¹' A) := measurable_cellChart ε c hA
  have hT : Measurable fun z : PSpace P => cellChart ε c (toCell P z) :=
    (measurable_cellChart ε c).comp measurable_toCell
  rw [Measure.map_apply hT hA, Measure.map_apply (measurable_cellChart ε c) hA,
    withDensity_apply _ (hT hA), withDensity_apply _ hpre, ← lintegral_indicator (hT hA),
    ← lintegral_indicator hpre, ← hmp.lintegral_comp (hDm.indicator hpre)]
  refine lintegral_congr fun z => ?_
  simp only [Set.indicator, Set.mem_preimage, hD]
  rfl

/-! ### The scalar lift -/

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The scalar lift `b ↦ (√(2π) ε)⁻¹ a b(s, q, η)` as a weighted composition into the periodic
space. -/
def liftScWC (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    WeightedComp (volume : Measure (PSpace P)) (measureH c) E E where
  T z := cellChart ε c (toCell P z)
  L z := (jConst ε * liftA z.1) • LinearMap.id
  ρ z := jConst ε * liftA z.1
  measurable_T := (measurable_cellChart ε c).comp measurable_toCell
  measurable_ρ := (measurable_liftA.comp measurable_fst).const_mul _
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact (((measurable_liftA.comp measurable_fst).const_mul _).comp measurable_fst).smul
      measurable_snd
  nonneg_ρ z := mul_nonneg (jConst_nonneg hε) (liftA_nonneg _)
  norm_L z v := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (jConst_nonneg hε) (liftA_nonneg _))]
  map_eq := map_liftDensity hε hc hP

theorem liftScWC_smul (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (z : PSpace P) (k : ℂ)
    (v : E) : (liftScWC (E := E) hε hc hP).L z (k • v) = k • (liftScWC hε hc hP).L z v := by
  simp only [liftScWC, LinearMap.smul_apply, LinearMap.id_apply]
  exact smul_comm _ _ _

/-- **The complex scalar lift `J_ε : H → L²(dx dτ)`** (tex lines 3289–3311, complexified),
onto `τ`-periodic fields of period `P = 2εc`; a complex linear isometry. -/
def liftSc (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) : HSpace c E →ₗᵢ[ℂ] X E P :=
  wcToLIC (liftScWC hε hc hP) (liftScWC_smul hε hc hP)

/-- `J_ε b (x, τ) = (√(2π) ε)⁻¹ a b(s, q, η)`, with `q` reduced to the cell `(0, c]` (the
`c`-periodic extension of `b`, B0220 `periodize`) and `τ` represented in `(0, P]`. -/
theorem coeFn_liftSc (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (b : HSpace c E) :
    (liftSc hε hc hP b : PSpace P → E) =ᵐ[volume]
      fun z => (√(2 * Real.pi) * ε)⁻¹ • liftU ε (periodize c (b : Profile → E)) (toCell P z) := by
  filter_upwards [(liftScWC hε hc hP).coeFn_toLI b] with z hz
  rw [liftSc, wcToLIC_apply, hz]
  simp only [WeightedComp.compFun, liftScWC, LinearMap.smul_apply, LinearMap.id_apply, liftU,
    mul_smul, jConst]
  rfl

theorem norm_liftSc (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (b : HSpace c E) :
    ‖liftSc hε hc hP b‖ = ‖b‖ := (liftSc hε hc hP).norm_map b

end Scalar

/-! ### The meridional vector lift -/

/-- Complex meridional components `(b_r, b_z)`. -/
abbrev MeridC := EuclideanSpace ℂ (Fin 2)

/-- Complex Cartesian vectors `ℂ³`. -/
abbrev SpaceC := EuclideanSpace ℂ (Fin 3)

/-- `e_r` with complex coefficients (its Lean value on the axis is `0`). -/
def unitRC (x : Space) : SpaceC :=
  ((x 0 / radius x : ℝ) : ℂ) • EuclideanSpace.single 0 1 +
    ((x 1 / radius x : ℝ) : ℂ) • EuclideanSpace.single 1 1

/-- `e_z` with complex coefficients. -/
def unitZC : SpaceC := EuclideanSpace.single 2 1

/-- The complex meridional frame `(v_r, v_z) ↦ v_r e_r + v_z e_z` (tex line 3295). -/
def frameC (x : Space) : MeridC →ₗ[ℂ] SpaceC where
  toFun v := v 0 • unitRC x + v 1 • unitZC
  map_add' u v := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' r v := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

theorem frameC_apply (x : Space) (v : MeridC) : frameC x v = v 0 • unitRC x + v 1 • unitZC := rfl

theorem norm_frameC {x : Space} (hx : radius x ≠ 0) (v : MeridC) : ‖frameC x v‖ = ‖v‖ := by
  have hr2 : radius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [frameC_apply, unitRC, unitZC, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, add_zero,
    zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  linear_combination (-(‖v 0‖ ^ 2)) * hr2

theorem measurable_unitRC : Measurable unitRC := by
  have h0 : Measurable fun x : Space => x 0 := (PiLp.continuous_apply 2 _ 0).measurable
  have h1 : Measurable fun x : Space => x 1 := (PiLp.continuous_apply 2 _ 1).measurable
  exact ((Complex.measurable_ofReal.comp (h0.div measurable_radius)).smul_const _).add
    ((Complex.measurable_ofReal.comp (h1.div measurable_radius)).smul_const _)

theorem measurable_frameC_uncurry {α : Type*} [MeasurableSpace α] {Y : α → Space}
    (hY : Measurable Y) : Measurable fun p : α × MeridC => frameC (Y p.1) p.2 := by
  have h0 : Measurable fun p : α × MeridC => p.2 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).measurable.comp measurable_snd
  have h1 : Measurable fun p : α × MeridC => p.2 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).measurable.comp measurable_snd
  simp only [frameC_apply]
  exact (h0.smul (measurable_unitRC.comp (hY.comp measurable_fst))).add (h1.smul_const _)

theorem norm_smul_frameC (hε : 0 < ε) (x : Space) (v : MeridC) :
    ‖(jConst ε * liftA x) • frameC x v‖ = jConst ε * liftA x * ‖v‖ := by
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (jConst_nonneg hε) (liftA_nonneg x))]
  by_cases hx : radius x = 0
  · simp [liftA_eq_zero hx]
  · rw [norm_frameC hx]

/-- The meridional lift as a weighted composition into the periodic `ℂ³`-valued space. -/
def liftVecWC (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    WeightedComp (volume : Measure (PSpace P)) (measureH c) MeridC SpaceC where
  T z := cellChart ε c (toCell P z)
  L z := (jConst ε * liftA z.1) • (frameC z.1).restrictScalars ℝ
  ρ z := jConst ε * liftA z.1
  measurable_T := (measurable_cellChart ε c).comp measurable_toCell
  measurable_ρ := (measurable_liftA.comp measurable_fst).const_mul _
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.restrictScalars_apply]
    exact (((measurable_liftA.comp measurable_fst).const_mul _).comp measurable_fst).smul
      (measurable_frameC_uncurry measurable_fst)
  nonneg_ρ z := mul_nonneg (jConst_nonneg hε) (liftA_nonneg _)
  norm_L z v := by
    rw [LinearMap.smul_apply, LinearMap.restrictScalars_apply]
    exact norm_smul_frameC hε z.1 v
  map_eq := map_liftDensity hε hc hP

theorem liftVecWC_smul (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (z : PSpace P) (k : ℂ)
    (v : MeridC) : (liftVecWC hε hc hP).L z (k • v) = k • (liftVecWC hε hc hP).L z v := by
  simp only [liftVecWC, LinearMap.smul_apply, LinearMap.restrictScalars_apply, map_smul]
  exact smul_comm _ _ _

/-- **The complex meridional lift `J_ε`** (tex lines 3289–3311, complexified):
`b ↦ (√(2π) ε)⁻¹ a (b_r e_r + b_z e_z)` from `H = L²(s^{-3/2} ds dq dη; ℂ²)` into the
`τ`-periodic `ℂ³`-valued fields; a complex linear isometry. -/
def liftVec (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    HSpace c MeridC →ₗᵢ[ℂ] X SpaceC P :=
  wcToLIC (liftVecWC hε hc hP) (liftVecWC_smul hε hc hP)

theorem coeFn_liftVec (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (b : HSpace c MeridC) :
    (liftVec hε hc hP b : PSpace P → SpaceC) =ᵐ[volume]
      fun z => (√(2 * Real.pi) * ε)⁻¹ • liftA z.1 •
        frameC z.1 (periodize c (b : Profile → MeridC) (chart ε (toCell P z))) := by
  filter_upwards [(liftVecWC hε hc hP).coeFn_toLI b] with z hz
  rw [liftVec, wcToLIC_apply, hz]
  simp only [WeightedComp.compFun, liftVecWC, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply, mul_smul, jConst]
  rfl

end UnforcedLeray.B0223
