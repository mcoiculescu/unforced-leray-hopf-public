import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg

/-!
# The young-jet decay integral (`PartIII-b:C/rep/8/2/pres/4/org2/2`)

Source `the November 2 reference manuscript`, 5470-5476 (density
`π R² s^{-5/2} ds dq/c dη`, `R = ε⁻¹`).  The weight `youngJetWeight` is supported in `0 < s ≤ 1/ν`
and is `≤ ε³ s^{5/2}`; with `c⁻¹ = ν²` and `s^{-5/2}·s^{5/2}·s^{5/2}`-cancellation, the `s`-integral
is `≤ (1/ν)` times `(1/ν)³`, the `q`-cell has mass `c`, and `∫ e^{-m|η|} dη < ∞` (bounded by
`K/(1+η²)`).  The total is `π ε⁴ ν^{-4} ∫e^{-m|η|}`, whose square root gives `ε² ν^{-2}`.
At the period rate `m = m₁ν²` (restated `YoungJetDecayInt`), `∫e^{-m₁ν²|η|} ≤ (2 + 4/m₁²)π ν^{-4}`,
so the bound is `C ν^{-4} ε²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The exponential bound `e^{-a|x|} ≤ (2 + 4/a²)/(1+x²)`. -/
lemma yjd_exp_le (a : ℝ) (ha : 0 < a) (x : ℝ) :
    Real.exp (-a * |x|) ≤ (2 + 4 / a ^ 2) * (1 + x ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hy0 : 0 ≤ a * |x| := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hE : 0 < Real.exp (a * |x|) := Real.exp_pos _
  have hexp : Real.exp (-a * |x|) = (Real.exp (a * |x|))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp]
  have h3 : (a * |x|) ^ 2 = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
  have h5 : (0:ℝ) ≤ 4 / a ^ 2 := by positivity
  rcases le_total 1 |x| with h1 | h1
  · have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
    have h2 : (a * |x|) ^ 2 ≤ 2 * Real.exp (a * |x|) := by nlinarith
    have key : (1 + x ^ 2) * a ^ 2 ≤ 4 * Real.exp (a * |x|) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hx2) (sq_nonneg a)]
    have h4 : (Real.exp (a * |x|))⁻¹ * (1 + x ^ 2) ≤ 4 / a ^ 2 := by
      rw [inv_mul_eq_div, div_le_div_iff₀ hE (by positivity)]
      linarith
    linarith
  · have hE1 : (Real.exp (a * |x|))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp hy0)
    have hx : 1 + x ^ 2 ≤ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hm := mul_le_mul hE1 hx (by positivity) zero_le_one
    linarith

/-- The `η`-integral of `e^{-m|η|}` is finite. -/
lemma yjd_eta_lt_top (a : ℝ) (ha : 0 < a) :
    ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-a * |η|)) < ⊤ := by
  have hint : Integrable (fun x : ℝ => (2 + 4 / a ^ 2) * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine lt_of_le_of_lt
    (lintegral_mono fun η => ENNReal.ofReal_le_ofReal (yjd_exp_le a ha η)) ?_
  exact hint.lintegral_lt_top

/-- The pointwise bound of the squared young weight against the transverse decay. -/
lemma yjd_pt {m ν ε : ℝ} (hm : 0 < m) (hε : 0 < ε) (p : Chart) :
    ‖Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p‖ ^ 2 ≤
      (Ioc 0 (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 * Real.exp (-m * |p.2.2|) := by
  have he0 : 0 ≤ Real.exp (-m * |p.2.2|) := (Real.exp_pos _).le
  have he1 : Real.exp (-m * |p.2.2|) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := abs_nonneg p.2.2; nlinarith)
  have he2 : Real.exp (-m * |p.2.2|) ^ 2 ≤ Real.exp (-m * |p.2.2|) := by nlinarith
  by_cases hp : 0 < p.1 ∧ p.1 ≤ 1 / ν
  · have hmem : p.1 ∈ Ioc 0 (1 / ν) := ⟨hp.1, hp.2⟩
    rw [indicator_of_mem hmem]
    have hyw : youngJetWeight ν ε p =
        ε ^ 3 * p.1 ^ (5 / 2 : ℝ) * (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ)) := by
      unfold youngJetWeight; rw [if_pos hp]
    have hw0 : 0 ≤ (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have hw1 : (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (ε * p.2.2)]) (by norm_num)
    have ht : (p.1 ^ (5 / 2 : ℝ)) ^ 2 = p.1 ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.1.le,
        show (5 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hX0 : 0 ≤ ε ^ 3 * p.1 ^ (5 / 2 : ℝ) :=
      mul_nonneg (pow_nonneg hε.le 3) (Real.rpow_nonneg hp.1.le _)
    have hA : |youngJetWeight ν ε p| ≤ ε ^ 3 * p.1 ^ (5 / 2 : ℝ) := by
      rw [hyw, abs_of_nonneg (mul_nonneg hX0 hw0)]
      exact mul_le_of_le_one_right hX0 hw1
    have hA0 : 0 ≤ |youngJetWeight ν ε p| := abs_nonneg _
    rw [norm_mul, Real.norm_of_nonneg he0, Real.norm_eq_abs]
    calc (Real.exp (-m * |p.2.2|) * |youngJetWeight ν ε p|) ^ 2
        = Real.exp (-m * |p.2.2|) ^ 2 * |youngJetWeight ν ε p| ^ 2 := by ring
      _ ≤ Real.exp (-m * |p.2.2|) * (ε ^ 3 * p.1 ^ (5 / 2 : ℝ)) ^ 2 :=
          mul_le_mul he2 (pow_le_pow_left₀ hA0 hA 2) (sq_nonneg _) he0
      _ = ε ^ 6 * p.1 ^ 5 * Real.exp (-m * |p.2.2|) := by rw [mul_pow, ht]; ring
  · have hy : youngJetWeight ν ε p = 0 := by unfold youngJetWeight; rw [if_neg hp]
    have hn : p.1 ∉ Ioc 0 (1 / ν) := fun h => hp ⟨h.1, h.2⟩
    rw [hy, mul_zero, norm_zero, indicator_of_notMem hn]
    simp

/-- The density identity in real form: `s^{-5/2}·s⁵ ≤ (1/ν)³` on `0 < s ≤ 1/ν`. -/
lemma yjd_dens {ν s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1 / ν) :
    s ^ (-5 / 2 : ℝ) * s ^ 5 ≤ (1 / ν) ^ 3 := by
  have ht : s ^ (-5 / 2 : ℝ) = (s ^ (5 / 2 : ℝ))⁻¹ := by
    rw [show (-5 / 2 : ℝ) = -(5 / 2) by norm_num, Real.rpow_neg hs.le]
  have hpow : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le,
      show (5 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpos : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have h1 : 1 ≤ 1 / ν := by rw [le_div_iff₀ hν]; linarith
  have hle : s ^ (5 / 2 : ℝ) ≤ (1 / ν) ^ 3 := by
    calc s ^ (5 / 2 : ℝ) ≤ (1 / ν) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hs.le hs1 (by norm_num)
      _ ≤ (1 / ν) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (1 / ν) ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [ht, ← hpow]
  have e : (s ^ (5 / 2 : ℝ))⁻¹ * (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ (5 / 2 : ℝ) := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [e]
  exact hle

/-- The product integral of three one-dimensional factors (`volume` on `ℝ × (ℝ × ℝ)`). -/
lemma yjd_prod3 (a b e : ℝ → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) (he : Measurable e) :
    ∫⁻ p : ℝ × (ℝ × ℝ), a p.1 * (b p.2.1 * e p.2.2) =
      (∫⁻ x, a x) * ((∫⁻ y, b y) * ∫⁻ z, e z) := by
  have h2 : ∫⁻ y : ℝ × ℝ, b y.1 * e y.2 = (∫⁻ y, b y) * ∫⁻ z, e z := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod_mul hb.aemeasurable he.aemeasurable
  have hm2 : Measurable fun y : ℝ × ℝ => b y.1 * e y.2 :=
    (hb.comp measurable_fst).mul (he.comp measurable_snd)
  rw [Measure.volume_eq_prod, lintegral_prod_mul ha.aemeasurable hm2.aemeasurable]
  exact congrArg (fun t => (∫⁻ x, a x) * t) h2

/-- The `η`-integral of `e^{-a|η|}` is at most `(2 + 4/a²)π`. -/
private lemma yjd_eta_le (a : ℝ) (ha : 0 < a) :
    ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-a * |η|)) ≤ ENNReal.ofReal ((2 + 4 / a ^ 2) * Real.pi) := by
  have hint : Integrable (fun x : ℝ => (2 + 4 / a ^ 2) * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hval : ∫ x : ℝ, (2 + 4 / a ^ 2) * (1 + x ^ 2)⁻¹ = (2 + 4 / a ^ 2) * Real.pi := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)]
  exact lintegral_mono fun η => ENNReal.ofReal_le_ofReal (yjd_exp_le a ha η)

/-- **The `(s, η)` integration at a fixed rate `m`**, given a bound `Ψr` on `∫e^{-m|η|}dη`
(source 5470-5476). -/
private lemma yjd_main {m Ψr ν ε : ℝ} (hm : 0 < m) (hΨr0 : 0 ≤ Ψr)
    (hΨ : ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-m * |η|)) ≤ ENNReal.ofReal Ψr)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) :
    eLpNorm (fun p : Chart => Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p) 2
        (ringPhysμ ε⁻¹ (cOf ν)) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * Ψr) * ν⁻¹ ^ 2 * ε ^ 2) := by
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hcval : cOf ν = (ν ^ 2)⁻¹ := rfl
  -- Step 0: the `L²` norm squared is the lower integral
  have hX : eLpNorm (fun p : Chart => Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p) 2
      (ringPhysμ ε⁻¹ (cOf ν)) ^ 2 =
      ∫⁻ p : Chart, ‖Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p‖ₑ ^ 2 ∂(ringPhysμ ε⁻¹ (cOf ν)) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (f := fun p : Chart => Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p)
      (μ := ringPhysμ ε⁻¹ (cOf ν)) (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using h
  -- the majorant `Φ` (measurable)
  have hΦm : Measurable (fun p : Chart => ENNReal.ofReal
      ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
        Real.exp (-m * |p.2.2|))) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact (Measurable.indicator (by fun_prop) measurableSet_Ioc).comp measurable_fst
    · exact Real.continuous_exp.measurable.comp (by fun_prop)
  -- Step 1: pointwise bound and the ring measure
  have hS1 : ∫⁻ p : Chart, ‖Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p‖ₑ ^ 2
      ∂(ringPhysμ ε⁻¹ (cOf ν)) ≤
      ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p : Chart, ENNReal.ofReal
        ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
          Real.exp (-m * |p.2.2|)) ∂(ageμ (cOf ν) (-5 / 2)) := by
    unfold ringPhysμ
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun p => ?_) zero_le
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (yjd_pt hm hε p)
  -- Step 2: the `(s,q,η)` cell integral
  have hS2 : ∫⁻ p : Chart, ENNReal.ofReal
        ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
          Real.exp (-m * |p.2.2|)) ∂(ageμ (cOf ν) (-5 / 2)) =
      ∫⁻ p : Chart in Ioi (0 : ℝ) ×ˢ qCell (cOf ν), ENNReal.ofReal ((cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
        ENNReal.ofReal ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
          Real.exp (-m * |p.2.2|)) :=
    lintegral_ageμ hc _ hΦm
  -- Step 3: pointwise on the cell, against the product majorant
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell (cOf ν) : Set Chart) :=
    MeasurableSet.prod measurableSet_Ioi (by unfold qCell; exact measurableSet_Ico.prod MeasurableSet.univ)
  have hS3 : ∫⁻ p : Chart in Ioi (0 : ℝ) ×ˢ qCell (cOf ν), ENNReal.ofReal ((cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
        ENNReal.ofReal ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
          Real.exp (-m * |p.2.2|)) ≤
      ∫⁻ p : Chart, ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
        ((Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          ((Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) p.2.1 *
            ENNReal.ofReal (Real.exp (-m * |p.2.2|)))) := by
    rw [← lintegral_indicator hSm]
    refine lintegral_mono fun p => ?_
    by_cases hpS : p ∈ (Ioi (0 : ℝ) ×ˢ qCell (cOf ν) : Set Chart)
    · have hs0 : 0 < p.1 := hpS.1
      have hq1 : p.2.1 ∈ Ico (-cOf ν / 2) (cOf ν / 2) := by
        have h := hpS.2
        unfold qCell at h
        exact h.1
      rw [indicator_of_mem hpS]
      beta_reduce
      by_cases hsI : p.1 ∈ Ioc (0 : ℝ) (1 / ν)
      · have e1 : (Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 =
            ε ^ 6 * p.1 ^ 5 := indicator_of_mem hsI _
        have e2 : (Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 = 1 :=
          indicator_of_mem hsI _
        have e3 : (Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) p.2.1 = 1 :=
          indicator_of_mem hq1 _
        rw [e1, e2, e3]
        simp only [one_mul]
        have hreal : (cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ) * (ε ^ 6 * p.1 ^ 5 * Real.exp (-m * |p.2.2|)) ≤
            (cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3 * Real.exp (-m * |p.2.2|) := by
          have hpos : 0 ≤ (cOf ν)⁻¹ * ε ^ 6 * Real.exp (-m * |p.2.2|) :=
            mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg hε.le 6)) (Real.exp_pos _).le
          calc (cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ) * (ε ^ 6 * p.1 ^ 5 * Real.exp (-m * |p.2.2|))
              = ((cOf ν)⁻¹ * ε ^ 6 * Real.exp (-m * |p.2.2|)) * (p.1 ^ (-5 / 2 : ℝ) * p.1 ^ 5) := by
                ring
            _ ≤ ((cOf ν)⁻¹ * ε ^ 6 * Real.exp (-m * |p.2.2|)) * (1 / ν) ^ 3 :=
                mul_le_mul_of_nonneg_left (yjd_dens hν hν1 hs0 hsI.2) hpos
            _ = (cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3 * Real.exp (-m * |p.2.2|) := by ring
        have hA0 : 0 ≤ (cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ) :=
          mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs0.le _)
        have hK0 : 0 ≤ (cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3 :=
          mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg hε.le 6)) (by positivity)
        have hB0 : 0 ≤ ε ^ 6 * p.1 ^ 5 * Real.exp (-m * |p.2.2|) :=
          mul_nonneg (mul_nonneg (pow_nonneg hε.le 6) (pow_nonneg hs0.le 5)) (Real.exp_pos _).le
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal hreal
      · have e1 : (Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 = 0 :=
          indicator_of_notMem hsI _
        rw [e1, zero_mul, ENNReal.ofReal_zero, mul_zero]
        exact zero_le
    · rw [indicator_of_notMem hpS]
      exact zero_le
  -- Step 4: the product integral
  have hIoc : ∫⁻ x, (Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) x =
      ENNReal.ofReal (1 / ν) := by
    rw [lintegral_indicator_const measurableSet_Ioc, one_mul, Real.volume_Ioc, sub_zero]
  have hIco : ∫⁻ y, (Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) y =
      ENNReal.ofReal (cOf ν) := by
    rw [lintegral_indicator_const measurableSet_Ico, one_mul, Real.volume_Ico]
    congr 1
    ring
  have hQ : ∫⁻ p : Chart, ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
        ((Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          ((Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) p.2.1 *
            ENNReal.ofReal (Real.exp (-m * |p.2.2|)))) =
      ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
        ((∫⁻ x, (Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) x) *
          ((∫⁻ y, (Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-m * |z|)))) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact yjd_prod3 (fun s : ℝ => (Ioc (0 : ℝ) (1 / ν)).indicator (fun _ => (1 : ℝ≥0∞)) s)
      (fun q : ℝ => (Ico (-cOf ν / 2) (cOf ν / 2)).indicator (fun _ => (1 : ℝ≥0∞)) q)
      (fun η : ℝ => ENNReal.ofReal (Real.exp (-m * |η|)))
      (measurable_const.indicator measurableSet_Ioc)
      (measurable_const.indicator measurableSet_Ico)
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (by fun_prop)))
  -- Step 5: combine the constants
  have hcomb : ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) *
      (ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
        (ENNReal.ofReal (1 / ν) * (ENNReal.ofReal (cOf ν) * ENNReal.ofReal Ψr))) =
      ENNReal.ofReal (Real.pi * Ψr * ν⁻¹ ^ 4 * ε ^ 4) := by
    have h4 : 0 ≤ cOf ν := hc.le
    have h3 : 0 ≤ 1 / ν := by positivity
    have h2 : 0 ≤ (cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3 :=
      mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (pow_nonneg hε.le 6)) (by positivity)
    have h1 : 0 ≤ Real.pi * ε⁻¹ ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul h4, ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h2,
      ← ENNReal.ofReal_mul h1]
    congr 1
    rw [hcval]
    field_simp
  -- Step 6: the bound on the squared norm
  have hfinal : ∫⁻ p : Chart, ‖Real.exp (-m * |p.2.2|) * youngJetWeight ν ε p‖ₑ ^ 2
      ∂(ringPhysμ ε⁻¹ (cOf ν)) ≤ ENNReal.ofReal (Real.pi * Ψr * ν⁻¹ ^ 4 * ε ^ 4) := by
    calc _ ≤ _ := hS1
      _ = ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p : Chart in Ioi (0 : ℝ) ×ˢ qCell (cOf ν),
            ENNReal.ofReal ((cOf ν)⁻¹ * p.1 ^ (-5 / 2 : ℝ)) *
            ENNReal.ofReal ((Ioc (0 : ℝ) (1 / ν)).indicator (fun s : ℝ => ε ^ 6 * s ^ 5) p.1 *
              Real.exp (-m * |p.2.2|)) := by rw [hS2]
      _ ≤ ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * _ :=
          mul_le_mul_of_nonneg_left hS3 zero_le
      _ = ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * (ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
            (ENNReal.ofReal (1 / ν) * (ENNReal.ofReal (cOf ν) *
              ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-m * |z|))))) := by
          rw [hQ, hIoc, hIco]
      _ ≤ ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * (ENNReal.ofReal ((cOf ν)⁻¹ * ε ^ 6 * (1 / ν) ^ 3) *
            (ENNReal.ofReal (1 / ν) * (ENNReal.ofReal (cOf ν) * ENNReal.ofReal Ψr))) := by
          gcongr
      _ = _ := hcomb
  -- Step 7: take square roots
  have hZ0 : 0 ≤ Real.sqrt (Real.pi * Ψr) * ν⁻¹ ^ 2 * ε ^ 2 := by positivity
  have hZ2 : (Real.sqrt (Real.pi * Ψr) * ν⁻¹ ^ 2 * ε ^ 2) ^ 2 = Real.pi * Ψr * ν⁻¹ ^ 4 * ε ^ 4 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg Real.pi_pos.le hΨr0)]
    ring
  apply (ENNReal.pow_le_pow_left_iff two_ne_zero).1
  rw [hX, ← ENNReal.ofReal_pow hZ0, hZ2]
  exact hfinal

/-- **The `(s, η)` integration** (`YoungJetDecayInt`, source 5470-5476), at the period rate
`m₁ν²`: `∫e^{-m₁ν²|η|}dη ≤ (2 + 4/(m₁ν²)²)π ≤ (2 + 4/m₁²)π ν^{-4}` for `ν ≤ 1`. -/
theorem youngJetDecayInt : YoungJetDecayInt := by
  intro m₁ hm₁
  refine ⟨Real.sqrt (Real.pi * (Real.pi * (2 + 4 / m₁ ^ 2))), 4, ?_⟩
  intro ν ε hν hν1 hε
  have ha : 0 < m₁ * ν ^ 2 := by positivity
  have hνi : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hν4 : 1 ≤ ν⁻¹ ^ 4 := one_le_pow₀ hνi
  have hA0 : 0 ≤ Real.pi * (2 + 4 / m₁ ^ 2) := by positivity
  set Ψr : ℝ := Real.pi * (2 + 4 / m₁ ^ 2) * ν⁻¹ ^ 4 with hΨr
  have hΨr0 : 0 ≤ Ψr := by positivity
  have hΨ : ∫⁻ η : ℝ, ENNReal.ofReal (Real.exp (-(m₁ * ν ^ 2) * |η|)) ≤ ENNReal.ofReal Ψr := by
    refine (yjd_eta_le _ ha).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 4 / (m₁ * ν ^ 2) ^ 2 = 4 / m₁ ^ 2 * ν⁻¹ ^ 4 := by
      have := hm₁.ne'
      have := hν.ne'
      rw [mul_pow, ← pow_mul, inv_pow, div_mul_eq_mul_div]
      field_simp
    rw [h1, hΨr]
    have h2 : (2 : ℝ) ≤ 2 * ν⁻¹ ^ 4 := by linarith
    have h3 : 0 ≤ 4 / m₁ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le, mul_nonneg h3 Real.pi_pos.le]
  refine (yjd_main ha hΨr0 hΨ hν hν1 hε).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hΨr, show Real.pi * (Real.pi * (2 + 4 / m₁ ^ 2) * ν⁻¹ ^ 4) =
      Real.pi * (Real.pi * (2 + 4 / m₁ ^ 2)) * (ν⁻¹ ^ 2) ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
