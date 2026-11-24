import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2

/-!
# `PartIII-b:C/ward/13/8/2/5`: the cutoff argument for `GradL2Closure`

Source of record `the November 2 reference manuscript`
117-118 and 2641-2642. Given a cutoff family `χ_R` and the Deny-Lions constant `c` of `p`, the
compact tests `φ_n = χ_{n+1} (p - c)` have gradients `χ_{n+1} ∇p + (p - c) ∇χ_{n+1}`. Their
difference from `∇p` splits into `(χ_{n+1} - 1) ∇p`, which tends to `0` in `L²` by dominated
convergence, and `(p - c) ∇χ_{n+1}`, whose squared `L²` norm is at most
`(3C)² R⁻² ∫_{R ≤ |y| ≤ 2R} (p - c)²`, which tends to `0` by the Deny-Lions property.
The closedness of the gradient closure then gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GradCut

abbrev Sp := UnforcedLeray.Space

theorem norm_coordVec (i : Fin 3) : ‖UnforcedLeray.coordinateVector i‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

theorem physGrad_eq_sum (f : Sp → ℝ) (x : Sp) :
    physGrad f x = ∑ i : Fin 3,
      UnforcedLeray.spatialTestDerivative i f x • UnforcedLeray.coordinateVector i := by
  ext j
  simp [physGrad, UnforcedLeray.spatialTestDerivative, UnforcedLeray.coordinateVector,
    Finset.sum_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem continuous_physGrad {f : Sp → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (physGrad f) := by
  have h : physGrad f = fun x => ∑ i : Fin 3,
      (fderiv ℝ f x (UnforcedLeray.coordinateVector i)) • UnforcedLeray.coordinateVector i := by
    funext x
    exact physGrad_eq_sum f x
  rw [h]
  exact continuous_finsetSum _ fun i _ =>
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const)

theorem fderiv_eq_zero_off {χ : Sp → ℝ} {R : ℝ}
    (h1 : ∀ y, ‖y‖ ≤ R → χ y = 1) (h0 : ∀ y, 2 * R ≤ ‖y‖ → χ y = 0)
    {x : Sp} (hx : ¬ (R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R)) : fderiv ℝ χ x = 0 := by
  by_cases hlt : ‖x‖ < R
  · have hev : (fun y => χ y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
      Filter.eventually_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hlt)
        (fun y hy => h1 y (le_of_lt hy))
    rw [hev.fderiv_eq, fderiv_const_apply]
  · have h2 : 2 * R < ‖x‖ := by
      by_contra hcon
      exact hx ⟨not_lt.1 hlt, not_lt.1 hcon⟩
    have hev : (fun y => χ y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds h2)
        (fun y hy => h0 y (le_of_lt hy))
    rw [hev.fderiv_eq, fderiv_const_apply]

theorem physGrad_cut_zero {χ : Sp → ℝ} {R : ℝ}
    (h1 : ∀ y, ‖y‖ ≤ R → χ y = 1) (h0 : ∀ y, 2 * R ≤ ‖y‖ → χ y = 0)
    {x : Sp} (hx : ¬ (R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R)) : physGrad χ x = 0 := by
  rw [physGrad_eq_sum]
  simp [UnforcedLeray.spatialTestDerivative, fderiv_eq_zero_off h1 h0 hx]

theorem norm_physGrad_le {f : Sp → ℝ} {x : Sp} {M : ℝ} (hM : ‖fderiv ℝ f x‖ ≤ M) :
    ‖physGrad f x‖ ≤ 3 * M := by
  rw [physGrad_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hi : ∀ i : Fin 3,
      ‖UnforcedLeray.spatialTestDerivative i f x • UnforcedLeray.coordinateVector i‖ ≤ M := by
    intro i
    rw [norm_smul, norm_coordVec, mul_one]
    have h := (fderiv ℝ f x).le_opNorm (UnforcedLeray.coordinateVector i)
    rw [norm_coordVec, mul_one] at h
    exact h.trans hM
  calc ∑ i : Fin 3,
        ‖UnforcedLeray.spatialTestDerivative i f x • UnforcedLeray.coordinateVector i‖
      ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * M := by simp

theorem grad_mul_cut {χ p : Sp → ℝ} (hχ : ContDiff ℝ ∞ χ) (hp : ContDiff ℝ ∞ p) (c : ℝ)
    (x : Sp) :
    physGrad (fun y => χ y * (p y - c)) x = χ x • physGrad p x + (p x - c) • physGrad χ x := by
  have hprod : ∀ i : Fin 3, UnforcedLeray.spatialTestDerivative i (fun y => χ y * (p y - c)) x =
      χ x * UnforcedLeray.spatialTestDerivative i p x +
        (p x - c) * UnforcedLeray.spatialTestDerivative i χ x := by
    intro i
    unfold UnforcedLeray.spatialTestDerivative
    rw [fderiv_fun_mul ((hχ.differentiable (by simp)) x)
      (((hp.sub contDiff_const).differentiable (by simp)) x)]
    simp [fderiv_sub_const]
  simp only [physGrad_eq_sum, hprod, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]

theorem coe_toL2 {f : Sp → Sp} (hf : MemLp f 2 volume) :
    (UnforcedLeray.toL2 f : Sp → Sp) =ᵐ[volume] f := by
  unfold UnforcedLeray.toL2
  rw [dif_pos hf]
  exact hf.coeFn_toLp

theorem isSpatialTest_cut {χR p : Sp → ℝ} {R c : ℝ} (hsm : ContDiff ℝ ∞ χR)
    (hp : ContDiff ℝ ∞ p) (h0 : ∀ y, 2 * R ≤ ‖y‖ → χR y = 0) :
    UnforcedLeray.IsSpatialTest (fun y => χR y * (p y - c)) := by
  refine ⟨hsm.mul (hp.sub contDiff_const), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Sp) (2 * R)) (fun y hy => ?_)
  rw [mem_closedBall_zero_iff, not_le] at hy
  simp [h0 y hy.le]

/-- Dominated convergence in `L²` for sequences dominated by a fixed `L²` function. -/
theorem tendsto_eLpNorm_two_dom {E : Type*} [NormedAddCommGroup E] {D : ℕ → Sp → E}
    (hD : ∀ n, AEStronglyMeasurable (D n) volume) {B : Sp → ℝ} (hB : MemLp B 2 volume)
    (hbound : ∀ n x, ‖D n x‖ ≤ B x) (hlim : ∀ x, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (D n) 2 volume) atTop (𝓝 0) := by
  have hDm : ∀ n, MemLp (D n) 2 volume := fun n =>
    hB.of_le (hD n) (Eventually.of_forall fun x =>
      (hbound n x).trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm))
  have heq : ∀ n, eLpNorm (D n) 2 volume =
      ENNReal.ofReal ((∫ x, ‖D n x‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) := fun n => by
    simpa using (hDm n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  have hint : Tendsto (fun n => ∫ x, ‖D n x‖ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have hBi : Integrable (fun x => ‖B x‖ ^ (2 : ℝ)) volume := by
      simpa using hB.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    have h := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n x => ‖D n x‖ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ))
      (fun x => ‖B x‖ ^ (2 : ℝ))
      (fun n => ((hD n).norm.aemeasurable.pow_const (2 : ℝ)).aestronglyMeasurable)
      hBi
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact Real.rpow_le_rpow (norm_nonneg _)
          ((hbound n x).trans (le_abs_self _) |>.trans_eq (Real.norm_eq_abs _).symm)
          (by norm_num))
      (Eventually.of_forall fun x => by
        have := ((Real.continuous_rpow_const (q := 2) (by norm_num)).tendsto 0).comp (hlim x)
        simpa [Function.comp_def] using this)
    simpa using h
  have hc : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (2 : ℝ)⁻¹)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.comp
      (Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by norm_num))).tendsto 0
    simpa [Function.comp_def] using this
  simp_rw [heq]
  exact hc.comp hint

/-- The squared `L²` mass of `(p - c) ∇χ_R` is bounded by the Deny-Lions annular integral. -/
theorem int_sq_term2_le {p χR : Sp → ℝ} {R C c : ℝ} (hp : ContDiff ℝ ∞ p) (hR : 0 < R)
    (hsm : ContDiff ℝ ∞ χR) (h1 : ∀ y, ‖y‖ ≤ R → χR y = 1)
    (h0 : ∀ y, 2 * R ≤ ‖y‖ → χR y = 0) (hd : ∀ y, ‖fderiv ℝ χR y‖ ≤ C / R) :
    ∫ x, ‖(p x - c) • physGrad χR x‖ ^ (2 : ℝ) ≤
      (3 * C / R) ^ 2 * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 := by
  have hS : MeasurableSet {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  have hIntS : IntegrableOn (fun y => (p y - c) ^ 2) {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} := by
    have hK : IsCompact {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact (isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const)
      · apply (Metric.isBounded_closedBall (x := (0 : Sp)) (r := 2 * R)).subset
        intro y hy
        rw [mem_closedBall_zero_iff]
        exact hy.2
    exact ContinuousOn.integrableOn_compact hK
      (((hp.continuous.sub continuous_const).pow 2).continuousOn)
  have hrhs_int : Integrable (fun y => (3 * C / R) ^ 2 *
      {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}.indicator (fun y => (p y - c) ^ 2) y) :=
    ((integrable_indicator_iff hS).2 hIntS).const_mul _
  have hpt : ∀ x : Sp, ‖(p x - c) • physGrad χR x‖ ^ (2 : ℝ) ≤
      (3 * C / R) ^ 2 * {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}.indicator (fun y => (p y - c) ^ 2) x := by
    intro x
    rw [Real.rpow_two]
    by_cases hx : R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R
    · rw [Set.indicator_of_mem (show x ∈ {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} from hx)]
      have hb : ‖physGrad χR x‖ ≤ 3 * C / R := by
        have h := norm_physGrad_le (x := x) (M := C / R) (hd x)
        calc ‖physGrad χR x‖ ≤ 3 * (C / R) := h
          _ = 3 * C / R := by ring
      calc ‖(p x - c) • physGrad χR x‖ ^ 2 = (|p x - c| * ‖physGrad χR x‖) ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (|p x - c| * (3 * C / R)) ^ 2 := by gcongr
        _ = (3 * C / R) ^ 2 * (p x - c) ^ 2 := by rw [mul_pow, sq_abs]; ring
    · rw [Set.indicator_of_notMem (show x ∉ {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} from hx),
      physGrad_cut_zero h1 h0 hx, smul_zero, norm_zero]
      simp
  calc ∫ x, ‖(p x - c) • physGrad χR x‖ ^ (2 : ℝ)
      ≤ ∫ x, (3 * C / R) ^ 2 * {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}.indicator
          (fun y => (p y - c) ^ 2) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
          hrhs_int (Eventually.of_forall hpt)
    _ = (3 * C / R) ^ 2 * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 := by
        rw [integral_const_mul, integral_indicator hS]

/-- The gradient-difference piece `(p - c) ∇χ_{n+1}` tends to `0` in `L²`. -/
theorem term2_tendsto {p : Sp → ℝ} (hp : ContDiff ℝ ∞ p) {χ : ℝ → Sp → ℝ} {C : ℝ}
    (hχ : ∀ R : ℝ, 0 < R → ContDiff ℝ ∞ (χ R) ∧ (∀ y, 0 ≤ χ R y ∧ χ R y ≤ 1) ∧
      (∀ y, ‖y‖ ≤ R → χ R y = 1) ∧ (∀ y, 2 * R ≤ ‖y‖ → χ R y = 0) ∧
      (∀ y, ‖fderiv ℝ (χ R) y‖ ≤ C / R))
    {c : ℝ}
    (hc : Tendsto (fun R : ℝ => (1 / R ^ 2) * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R},
      (p y - c) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume)
      atTop (𝓝 0) := by
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcs : ∀ n : ℕ, HasCompactSupport
      (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) := by
    intro n
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Sp) (2 * ((n : ℝ) + 1)))
      (fun x hx => ?_)
    rw [mem_closedBall_zero_iff] at hx
    apply smul_eq_zero_of_right
    apply physGrad_cut_zero (hχ _ (hRpos n)).2.2.1 (hχ _ (hRpos n)).2.2.2.1
    rintro ⟨_, h2⟩
    exact hx h2
  have hcont : ∀ n : ℕ, Continuous (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) :=
    fun n => (hp.continuous.sub continuous_const).smul (continuous_physGrad (hχ _ (hRpos n)).1)
  have hmem : ∀ n : ℕ, MemLp (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume :=
    fun n => (hcont n).memLp_of_hasCompactSupport (hcs n)
  have hK0 : Tendsto (fun n : ℕ => (3 * C / ((n : ℝ) + 1)) ^ 2 *
      ∫ y in {y : Sp | (n : ℝ) + 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * ((n : ℝ) + 1)}, (p y - c) ^ 2)
      atTop (𝓝 0) := by
    have hc' := hc.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h9 := hc'.const_mul (9 * C ^ 2)
    rw [mul_zero] at h9
    have key : ∀ x : ℝ, (3 * C / x) ^ 2 = 9 * C ^ 2 * (1 / x ^ 2) := fun x => by
      rw [div_pow]; ring
    refine Tendsto.congr (fun n => ?_) h9
    simp only [Function.comp_apply]
    rw [key]
    ring
  have hbd : ∀ n : ℕ, eLpNorm (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume ≤
      ENNReal.ofReal ((((3 * C / ((n : ℝ) + 1)) ^ 2 *
        ∫ y in {y : Sp | (n : ℝ) + 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * ((n : ℝ) + 1)}, (p y - c) ^ 2)) ^
          (2 : ℝ)⁻¹) := by
    intro n
    have heq : eLpNorm (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume =
        ENNReal.ofReal ((∫ x, ‖(p x - c) • physGrad (χ ((n : ℝ) + 1)) x‖ ^ (2 : ℝ)) ^
          (2 : ℝ)⁻¹) := by
      simpa using (hmem n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
    · exact int_sq_term2_le hp (hRpos n) (hχ _ (hRpos n)).1 (hχ _ (hRpos n)).2.2.1
        (hχ _ (hRpos n)).2.2.2.1 (hχ _ (hRpos n)).2.2.2.2
    · norm_num
  have hc2 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (2 : ℝ)⁻¹)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.comp
      (Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by norm_num))).tendsto 0
    simpa [Function.comp_def] using this
  have hlim2 := hc2.comp hK0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2
    (fun n => zero_le) (fun n => hbd n)

/-- The gradient-difference piece `(χ_{n+1} - 1) ∇p` tends to `0` in `L²`. -/
theorem term1_tendsto {p : Sp → ℝ} (hp : ContDiff ℝ ∞ p) {χ : ℝ → Sp → ℝ} {C : ℝ}
    (hχ : ∀ R : ℝ, 0 < R → ContDiff ℝ ∞ (χ R) ∧ (∀ y, 0 ≤ χ R y ∧ χ R y ≤ 1) ∧
      (∀ y, ‖y‖ ≤ R → χ R y = 1) ∧ (∀ y, 2 * R ≤ ‖y‖ → χ R y = 0) ∧
      (∀ y, ‖fderiv ℝ (χ R) y‖ ≤ C / R))
    (hL : MemLp (physGrad p) 2 volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => (χ ((n : ℝ) + 1) x - 1) • physGrad p x) 2 volume)
      atTop (𝓝 0) := by
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  refine tendsto_eLpNorm_two_dom (E := Sp) (B := fun x => ‖physGrad p x‖) (fun n => ?_) hL.norm
    (fun n x => ?_) (fun x => ?_)
  · exact (((hχ _ (hRpos n)).1.continuous.sub continuous_const).smul
      (continuous_physGrad hp)).aestronglyMeasurable
  · show ‖(χ ((n : ℝ) + 1) x - 1) • physGrad p x‖ ≤ ‖physGrad p x‖
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_of_le_one_left (norm_nonneg _)
    have h01 := (hχ _ (hRpos n)).2.1 x
    rw [abs_le]
    constructor <;> linarith [h01.1, h01.2]
  · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : ‖x‖ ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    show (0 : ℝ) = ‖(χ ((n : ℝ) + 1) x - 1) • physGrad p x‖
    rw [(hχ _ (hRpos n)).2.2.1 x hx, sub_self, zero_smul, norm_zero]

end GradCut

open GradCut in
theorem gradL2Closure_of_cutoff (h1 : CutoffFamily) (h2 : DenyLionsConst) : GradL2Closure := by
  obtain ⟨χ, C, hχ⟩ := h1
  unfold GradL2Closure
  intro p hp hL
  obtain ⟨c, hc⟩ := h2 p hp hL
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hψ : ∀ n : ℕ, UnforcedLeray.IsSpatialTest (fun y => χ ((n : ℝ) + 1) y * (p y - c)) :=
    fun n => isSpatialTest_cut (hχ _ (hRpos n)).1 hp (hχ _ (hRpos n)).2.2.2.1
  have hconv : Tendsto (fun n : ℕ => UnforcedLeray.Leray.testGradient
      (fun y => χ ((n : ℝ) + 1) y * (p y - c)) (hψ n)) atTop
      (𝓝 (UnforcedLeray.toL2 (physGrad p))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hsum := (term1_tendsto hp hχ hL).add (term2_tendsto hp hχ hc)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => zero_le) (fun n => ?_)
    have hae : (⇑(UnforcedLeray.Leray.testGradient (fun y => χ ((n : ℝ) + 1) y * (p y - c))
          (hψ n)) - ⇑(UnforcedLeray.toL2 (physGrad p))) =ᵐ[volume]
        (fun x => (χ ((n : ℝ) + 1) x - 1) • physGrad p x +
          (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) := by
      filter_upwards [UnforcedLeray.Leray.coeFn_testGradient
        (fun y => χ ((n : ℝ) + 1) y * (p y - c)) (hψ n), coe_toL2 hL] with x hx1 hx2
      rw [Pi.sub_apply, hx1, hx2, ← physGrad_eq_sum,
        grad_mul_cut (hχ _ (hRpos n)).1 hp c x]
      simp only [sub_smul, one_smul]
      abel
    have m1 : AEStronglyMeasurable (fun x => (χ ((n : ℝ) + 1) x - 1) • physGrad p x) volume :=
      (((hχ _ (hRpos n)).1.continuous.sub continuous_const).smul
        (continuous_physGrad hp)).aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) volume :=
      ((hp.continuous.sub continuous_const).smul
        (continuous_physGrad (hχ _ (hRpos n)).1)).aestronglyMeasurable
    calc eLpNorm (⇑(UnforcedLeray.Leray.testGradient
            (fun y => χ ((n : ℝ) + 1) y * (p y - c)) (hψ n)) -
          ⇑(UnforcedLeray.toL2 (physGrad p))) 2 volume
        = eLpNorm (fun x => (χ ((n : ℝ) + 1) x - 1) • physGrad p x +
            (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume := eLpNorm_congr_ae hae
      _ ≤ eLpNorm (fun x => (χ ((n : ℝ) + 1) x - 1) • physGrad p x) 2 volume +
            eLpNorm (fun x => (p x - c) • physGrad (χ ((n : ℝ) + 1)) x) 2 volume :=
          eLpNorm_add_le m1 m2 (by norm_num)
  exact (UnforcedLeray.Leray.isClosed_gradientClosure).mem_of_tendsto hconv
    (Eventually.of_forall fun n =>
      UnforcedLeray.Leray.testGradient_mem_gradientClosure _ _)

end UnforcedLeray.Short.PartIIIb.Concrete
