import UnforcedLeray.Units.B0220.Chart
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# B0220 helper: the change of variables `dx dτ = ε² s^{-5/2} ds dq dη dφ`

Blueprint unit B0220 (label `eq:st18-t00113`), `paper/main.tex` lines 3279–3314.
The proof outline of the blueprint: at fixed `x`, `dτ = 2ε dq` (and one `τ` period covers one
`q`-cell by periodicity); at fixed `s`, `dz = εr dη`; `dr = (1/2) s^{-3/2} ds`; and
`dx = r dr dφ dz`. The main result is `lintegral_chart`:
`∫ a² h(s,q,η) dx dτ = 2πε² ∫_{cell} s^{-3/2} h ds dq dη` for nonnegative measurable
`c`-periodic `h`, and its measure form `map_cellChart`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.B0220

/-! ### The reduction of `q` into the cell -/

theorem reduceIoc_eq_sub (c q : ℝ) :
    reduceIoc c q = q - ((⌈q / c⌉ - 1 : ℤ) : ℝ) * c := by
  unfold reduceIoc; push_cast; ring

theorem reduceIoc_mem {c : ℝ} (hc : 0 < c) (q : ℝ) : reduceIoc c q ∈ Ioc 0 c := by
  have h1 : q / c ≤ ⌈q / c⌉ := Int.le_ceil _
  have h2 : (⌈q / c⌉ : ℝ) < q / c + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ hc] at h1
  have h2' : (⌈q / c⌉ : ℝ) * c < q + c := by
    have := mul_lt_mul_of_pos_right h2 hc
    rwa [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at this
  unfold reduceIoc
  constructor <;> nlinarith

theorem reduceIoc_of_mem {c q : ℝ} (hc : 0 < c) (hq : q ∈ Ioc 0 c) : reduceIoc c q = q := by
  have : ⌈q / c⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; simp only [sub_self]; exact div_pos hq.1 hc
    · push_cast; exact (div_le_one hc).2 hq.2
  unfold reduceIoc; rw [this]; simp

theorem reduceIoc_add {c : ℝ} (hc : 0 < c) (q : ℝ) : reduceIoc c (q + c) = reduceIoc c q := by
  have : (q + c) / c = q / c + 1 := by field_simp
  unfold reduceIoc
  rw [this, Int.ceil_add_one]
  push_cast; ring

theorem periodic_reduceIoc_eq {E : Type*} {c : ℝ} (b : Profile → E) (hb : QPeriodic c b)
    (s q η : ℝ) : b (s, reduceIoc c q, η) = b (s, q, η) := by
  have hper : Function.Periodic (fun q => b (s, q, η)) c := fun q => hb (s, q, η)
  rw [reduceIoc_eq_sub]
  exact hper.sub_int_mul_eq _

theorem qPeriodic_periodize {E : Type*} {c : ℝ} (hc : 0 < c) (b : Profile → E) :
    QPeriodic c (periodize c b) := by
  intro p
  simp only [periodize, reduceIoc_add hc]

theorem periodize_of_mem {E : Type*} {c : ℝ} (hc : 0 < c) (b : Profile → E) {p : Profile}
    (hp : p ∈ cell c) : periodize c b p = b p := by
  obtain ⟨s, q, η⟩ := p
  simp only [periodize, reduceIoc_of_mem hc hp.2.1]

theorem periodize_of_periodic {E : Type*} {c : ℝ} (b : Profile → E) (hb : QPeriodic c b) :
    periodize c b = b := by
  funext p
  exact periodic_reduceIoc_eq b hb p.1 p.2.1 p.2.2

theorem measurable_periodize {c : ℝ} {h : Profile → ℝ≥0∞} (hh : Measurable h) :
    Measurable (periodize c h) :=
  hh.comp (measurable_fst.prodMk (((measurable_reduceIoc c).comp (measurable_fst.comp
    measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))

/-! ### One-variable substitutions -/

/-- One `τ` period covers one `q`-cell: `∫_0^{2εc} h(q₀ + τ/(2ε)) dτ = 2ε ∫_0^c h(q) dq`
for `c`-periodic `h`. -/
theorem lintegral_period_shift {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (h : ℝ → ℝ≥0∞)
    (hper : Function.Periodic h c) (q0 : ℝ) :
    ∫⁻ τ in Ioc 0 (2 * ε * c), h (q0 + τ / (2 * ε)) =
      ENNReal.ofReal (2 * ε) * ∫⁻ q in Ioc 0 c, h q := by
  have h2ε : 0 < 2 * ε := by positivity
  set f : ℝ → ℝ := fun τ => q0 + τ / (2 * ε) with hf
  have hderiv : ∀ x ∈ Ioc 0 (2 * ε * c), HasDerivWithinAt f (1 / (2 * ε)) (Ioc 0 (2 * ε * c)) x :=
    fun x _ => by
      have := ((hasDerivAt_id x).div_const (2 * ε)).const_add q0
      simpa [f] using this.hasDerivWithinAt
  have hinj : InjOn f (Ioc 0 (2 * ε * c)) := by
    intro x _ y _ hxy
    simp only [f, add_right_inj] at hxy
    field_simp at hxy
    linarith
  have himage : f '' Ioc 0 (2 * ε * c) = Ioc q0 (q0 + c) := by
    ext x
    simp only [mem_image, mem_Ioc, f]
    constructor
    · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
      refine ⟨by have := div_pos h1 h2ε; linarith, ?_⟩
      have : τ / (2 * ε) ≤ c := by rw [div_le_iff₀ h2ε]; linarith
      linarith
    · rintro ⟨h1, h2⟩
      have hx : 0 < x - q0 := by linarith
      refine ⟨2 * ε * (x - q0), ⟨by positivity, ?_⟩, ?_⟩
      · have : x - q0 ≤ c := by linarith
        nlinarith
      · rw [mul_div_cancel_left₀ _ h2ε.ne']; ring
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj h
  rw [himage, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hjac
  have hcircle : ∫⁻ q in Ioc q0 (q0 + c), h q = ∫⁻ q in Ioc 0 c, h q := by
    haveI : Fact (0 < c) := ⟨hc⟩
    have e1 := AddCircle.lintegral_preimage (T := c) q0 hper.lift
    have e2 := AddCircle.lintegral_preimage (T := c) 0 hper.lift
    simp only [Function.Periodic.lift_coe, zero_add] at e1 e2
    rw [e1, e2]
  rw [← hcircle, hjac, ← mul_assoc, ← ENNReal.ofReal_mul h2ε.le, abs_of_pos (by positivity),
    mul_one_div_cancel h2ε.ne', ENNReal.ofReal_one, one_mul]

/-- `∫ K(z/k) dz = k ∫ K(η) dη` for `k > 0`. -/
theorem lintegral_comp_div_pos {k : ℝ} (hk : 0 < k) (K : ℝ → ℝ≥0∞) :
    ∫⁻ z, K (z / k) = ENNReal.ofReal k * ∫⁻ η, K η := by
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun η => k * η) k univ x :=
    fun x _ => (by simpa using (hasDerivAt_id' x).const_mul k :
      HasDerivAt (fun η : ℝ => k * η) k x).hasDerivWithinAt
  have hinj : InjOn (fun η : ℝ => k * η) univ := fun x _ y _ h =>
    mul_left_cancel₀ hk.ne' h
  have himage : (fun η : ℝ => k * η) '' univ = univ := by
    ext z; simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨z / k, by field_simp⟩
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hderiv hinj
    (fun z => K (z / k))
  rw [himage, Measure.restrict_univ] at hjac
  rw [hjac, abs_of_pos hk, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 2
  funext η
  congr 1
  field_simp

/-- The age substitution `s = r⁻²`: `∫_{s>0} s^{-3/2} N(s) ds = 2 ∫_{r>0} N(r⁻²) dr`. -/
theorem lintegral_age_substitution (N : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * N s =
      2 * ∫⁻ r in Ioi (0 : ℝ), N ((r ^ 2)⁻¹) := by
  set f : ℝ → ℝ := fun r => (r ^ 2)⁻¹ with hf
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (-(2 * (x ^ 3)⁻¹)) (Ioi 0) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2 := h1.inv (pow_ne_zero 2 hx0)
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    field_simp
  have hinj : InjOn f (Ioi 0) := by
    intro x hx y hy hxy
    simp only [f, inv_inj] at hxy
    exact (pow_left_inj₀ (le_of_lt hx) (le_of_lt hy) two_ne_zero).1 hxy
  have himage : f '' Ioi 0 = Ioi 0 := by
    ext s
    simp only [mem_image, mem_Ioi, f]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro hs
      refine ⟨√(s⁻¹), Real.sqrt_pos.2 (inv_pos.2 hs), ?_⟩
      rw [Real.sq_sqrt (inv_nonneg.2 hs.le), inv_inv]
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun s => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * N s)
  rw [himage] at hjac
  rw [hjac, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : 0 < r := hr
  simp only [f]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_neg, abs_of_pos (by positivity)]
  have hpow : ((r ^ 2)⁻¹) ^ (-(3 / 2 : ℝ)) = r ^ 3 := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]
    norm_num
  rw [hpow, inv_mul_cancel_right₀ (by positivity : r ^ 3 ≠ 0)]
  · norm_num

/-! ### The change of variables -/

theorem physMeasure_eq (ε c : ℝ) :
    physMeasure ε c = (volume : Measure Space).prod (volume.restrict (Ioc 0 (2 * ε * c))) := by
  rw [physMeasure, physDomain, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ]

theorem lintegral_cellMeasure (c : ℝ) (F : Profile → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂cellMeasure c =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ q in Ioc 0 c, ∫⁻ η, F (s, q, η) := by
  rw [cellMeasure, cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun s => ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun y : ℝ × ℝ => F (s, y)) (hF.comp measurable_prodMk_left).aemeasurable]

/-- The exact change of variables (blueprint proof outline of B0220):
`∫ a² h(s,q,η) dx dτ = 2πε² ∫_{cell} s^{-3/2} h ds dq dη` over one `τ` period, for
nonnegative measurable `h`, `c`-periodic in `q`. -/
theorem lintegral_chart {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (h : Profile → ℝ≥0∞)
    (hh : Measurable h) (hper : QPeriodic c h) :
    ∫⁻ y, ENNReal.ofReal (liftA y.1 ^ 2) * h (chart ε y) ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) * ∫⁻ p in cell c, weightH p * h p := by
  -- the `q`-cell integral and its `η` integral
  set Q : ℝ → ℝ → ℝ≥0∞ := fun s η => ∫⁻ q in Ioc 0 c, h (s, q, η) with hQ
  set N : ℝ → ℝ≥0∞ := fun s => ∫⁻ η, Q s η with hN
  have hhm : Measurable fun u : (ℝ × ℝ) × ℝ => h (u.1.1, u.2, u.1.2) :=
    hh.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hQm : Measurable (Function.uncurry Q) := hhm.lintegral_prod_right'
  set G : ℝ → ℝ → ℝ≥0∞ := fun r z =>
    ENNReal.ofReal (r⁻¹ ^ 2) * (ENNReal.ofReal (2 * ε) * Q ((r ^ 2)⁻¹) (z / (ε * r))) with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hm1 : Measurable fun u : ℝ × ℝ => ((u.1 ^ 2)⁻¹, u.2 / (ε * u.1)) :=
      ((measurable_fst.pow_const 2).inv).prodMk (measurable_snd.div (measurable_fst.const_mul ε))
    exact (ENNReal.measurable_ofReal.comp ((measurable_fst.inv).pow_const 2)).mul
      ((hQm.comp hm1).const_mul _)
  -- Step 1: the `τ` integral at fixed `x`
  have hmeasL : Measurable fun y : Space × ℝ => ENNReal.ofReal (liftA y.1 ^ 2) * h (chart ε y) :=
    (ENNReal.measurable_ofReal.comp ((measurable_liftA.comp measurable_fst).pow_const 2)).mul
      (hh.comp (measurable_chart ε))
  have step1 : ∫⁻ y, ENNReal.ofReal (liftA y.1 ^ 2) * h (chart ε y) ∂physMeasure ε c =
      ∫⁻ x : Space, G (radius x) (x 2) := by
    rw [physMeasure_eq, lintegral_prod _ hmeasL.aemeasurable]
    refine lintegral_congr fun x => ?_
    dsimp only
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hper1 : Function.Periodic (fun q => h (ageS x, q, etaCoord ε x)) c :=
      fun q => hper (ageS x, q, etaCoord ε x)
    have := lintegral_period_shift hε hc _ hper1 (ε⁻¹ * Real.log (radius x))
    simp only [chart, cellQ]
    rw [this]
    rfl
  -- Step 2: cylindrical coordinates
  rw [step1, lintegral_space_axisymmetric G hGm]
  -- Step 3: the `z` integral at fixed `r > 0`
  have step3 : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ z, ENNReal.ofReal r * G r z =
      ENNReal.ofReal (2 * ε ^ 2) * N ((r ^ 2)⁻¹) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hεr : 0 < ε * r := mul_pos hε hr0
    have hpt : ∀ z, ENNReal.ofReal r * G r z =
        ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 2) * ENNReal.ofReal (2 * ε) *
          Q ((r ^ 2)⁻¹) (z / (ε * r)) := by
      intro z
      simp only [G]
      ring
    have hconst : ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ 2) * ENNReal.ofReal (2 * ε) *
        ENNReal.ofReal (ε * r) = ENNReal.ofReal (2 * ε ^ 2) := by
      rw [← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      try ring
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]),
      lintegral_comp_div_pos hεr (Q ((r ^ 2)⁻¹)), ← mul_assoc, hconst]
  rw [setLIntegral_congr_fun measurableSet_Ioi step3,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Step 4: the profile side
  have hcell : ∫⁻ p in cell c, weightH p * h p = 2 * ∫⁻ r in Ioi (0 : ℝ), N ((r ^ 2)⁻¹) := by
    have hm : Measurable fun p : Profile => weightH p * h p := measurable_weightH.mul hh
    have e1 := lintegral_cellMeasure c _ hm
    rw [cellMeasure] at e1
    rw [e1, ← lintegral_age_substitution N]
    refine lintegral_congr fun s => ?_
    have hsw : ∫⁻ q in Ioc 0 c, ∫⁻ η, h (s, q, η) = ∫⁻ η, ∫⁻ q in Ioc 0 c, h (s, q, η) :=
      lintegral_lintegral_swap ((hh.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    have e2 : ∀ q, ∫⁻ η, weightH (s, q, η) * h (s, q, η) =
        ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ∫⁻ η, h (s, q, η) := fun q => by
      simp only [weightH]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr e2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsw]
  rw [hcell]
  -- constants: `2π · 2ε² = 2πε² · 2`
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The change of variables with `q` reduced into the cell, for any nonnegative measurable
`h` on profiles: `∫ a² h(Φ(x,τ)) dx dτ = 2πε² ∫ h dμ_H`. -/
theorem lintegral_cellChart {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (h : Profile → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ y, ENNReal.ofReal (liftA y.1 ^ 2) * h (cellChart ε c y) ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) * ∫⁻ p, h p ∂measureH c := by
  have := lintegral_chart hε hc (periodize c h) (measurable_periodize hh)
    (qPeriodic_periodize hc h)
  simp only [periodize, chart] at this
  rw [show (fun y : Space × ℝ => ENNReal.ofReal (liftA y.1 ^ 2) * h (cellChart ε c y)) =
    fun y => ENNReal.ofReal (liftA y.1 ^ 2) *
      h (ageS y.1, reduceIoc c (cellQ ε y.1 y.2), etaCoord ε y.1) from rfl, this,
    measureH, lintegral_withDensity_eq_lintegral_mul _ measurable_weightH hh, cellMeasure]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_cell c) (fun p hp => ?_)
  obtain ⟨s, q, η⟩ := p
  simp only [Pi.mul_apply, reduceIoc_of_mem hc hp.2.1]

/-- The density `a²` of the lifted measure. -/
def liftDensity (y : Space × ℝ) : ℝ≥0∞ := ENNReal.ofReal (liftA y.1 ^ 2)

theorem measurable_liftDensity : Measurable liftDensity :=
  ENNReal.measurable_ofReal.comp ((measurable_liftA.comp measurable_fst).pow_const 2)

/-- Measure form of the change of variables: the reduced chart pushes `a² dx dτ` forward to
`2πε² s^{-3/2} ds dq dη` on the cell. -/
theorem map_cellChart {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ((physMeasure ε c).withDensity liftDensity).map (cellChart ε c) =
      ENNReal.ofReal (2 * π * ε ^ 2) • measureH c := by
  ext A hA
  rw [Measure.map_apply (measurable_cellChart ε c) hA, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurable_cellChart ε c hA)]
  have h1 := lintegral_cellChart hε hc (A.indicator 1) (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA] at h1
  rw [← h1, ← lintegral_indicator (measurable_cellChart ε c hA)]
  refine lintegral_congr fun y => ?_
  by_cases hy : cellChart ε c y ∈ A
  · simp [Set.indicator_of_mem (show y ∈ cellChart ε c ⁻¹' A from hy),
      Set.indicator_of_mem hy, liftDensity]
  · simp [Set.indicator_of_notMem (show y ∉ cellChart ε c ⁻¹' A from hy),
      Set.indicator_of_notMem hy]

/-- Almost-everywhere transfer: a property holding `μ_H`-a.e. holds at `Φ(x,τ)` for a.e.
`(x,τ)` off the axis. -/
theorem ae_transfer {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {P : Profile → Prop}
    (hP : ∀ᵐ p ∂measureH c, P p) :
    ∀ᵐ y ∂physMeasure ε c, liftA y.1 ≠ 0 → P (cellChart ε c y) := by
  have h1 : ∀ᵐ p ∂((physMeasure ε c).withDensity liftDensity).map (cellChart ε c), P p := by
    rw [map_cellChart hε hc]
    exact Measure.ae_smul_measure hP _
  have h2 := ae_of_ae_map (measurable_cellChart ε c).aemeasurable h1
  rw [ae_withDensity_iff measurable_liftDensity] at h2
  filter_upwards [h2] with y hy ha
  apply hy
  simp only [liftDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

end UnforcedLeray.B0220
