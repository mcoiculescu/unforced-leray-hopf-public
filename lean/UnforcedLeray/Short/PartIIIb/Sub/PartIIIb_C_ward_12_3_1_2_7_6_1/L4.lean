import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1
import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# `MajLp` (task `PartIII-b:C/ward/12/3/1/2/7/6/1/4`)

Source `the November 2 reference manuscript` lines 2385-2387, 2562-2564, 2347-2369.
A pointwise bound `‖F(τ,y)‖ ≤ M age^k (1+T+|η|)^N e^{-κ|η|/c}` on `age ≤ T` is dominated by
`‖N_v b'(τ,y)‖` for the profile `b' = majG • e₀`: the factor `√(age)` of the ring lift absorbs
`age^{1/2}`. The `L^q` norm of `N_v b'` on `(0,P] × ℝ³` is given by `Axi.lintegral_Nv_rpow`, and
`Axi.lintegral_ageμ` reduces it to a finite integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Nat
open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi

/-! ### Whole-line integrability of `(1+|η|)^m e^{-a|η|}` (self-contained copy of the
`B0172` moment lemmas; the `B0172` module is not importable from this draft). -/

theorem eta_integral_Ioi_pow_mul_exp (j : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ j * Real.exp (-(a * t)) = j ! / a ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := a) (by positivity) ha
  rw [Real.Gamma_nat_eq_factorial] at h
  have e : ∀ t ∈ Ioi (0 : ℝ), t ^ ((j : ℝ) + 1 - 1) * Real.exp (-(a * t)) =
      t ^ j * Real.exp (-(a * t)) := by
    intro t _
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, div_pow,
    one_pow]
  field_simp

theorem eta_integral_pow_abs_mul_exp (j : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ η : ℝ, |η| ^ j * Real.exp (-(a * |η|)) = 2 * (j ! / a ^ (j + 1)) := by
  rw [integral_comp_abs (f := fun t => t ^ j * Real.exp (-(a * t))),
    eta_integral_Ioi_pow_mul_exp j ha]

theorem eta_integrable_pow_abs_mul_exp (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun η : ℝ => |η| ^ j * Real.exp (-(a * |η|)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [eta_integral_pow_abs_mul_exp j ha]
  have : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  positivity

theorem eta_one_add_abs_pow_eq (m : ℕ) (η : ℝ) :
    (1 + |η|) ^ m = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * |η| ^ j := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, mul_comm]

theorem eta_integrable_one_add_abs_pow_mul_exp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun η : ℝ => (1 + |η|) ^ m * Real.exp (-(a * |η|)) := by
  have e : (fun η : ℝ => (1 + |η|) ^ m * Real.exp (-(a * |η|))) =
      fun η => ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * (|η| ^ j * Real.exp (-(a * |η|))) := by
    funext η; rw [eta_one_add_abs_pow_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun j _ => (eta_integrable_pow_abs_mul_exp j ha).const_mul _

/-- The scalar majorant profile: `G(s,ξ,η) = |M| s^{k-1/2}(1+T+|η|)^N e^{-κ|η|/c}` on `0 < s ≤ T`,
zero otherwise. -/
def majG (M κ c T k : ℝ) (N : ℕ) (m : ℝ × (ℝ × ℝ)) : ℝ :=
  if 0 < m.1 ∧ m.1 ≤ T then
    |M| * m.1 ^ (k - 1 / 2) * (1 + T + |m.2.2|) ^ N * Real.exp (-(κ * |m.2.2| / c))
  else 0

theorem majG_nonneg {M κ c T k : ℝ} {N : ℕ} (hT : 0 ≤ T) (m : ℝ × (ℝ × ℝ)) :
    0 ≤ majG M κ c T k N m := by
  unfold majG
  split_ifs with h
  · have h1 : 0 ≤ 1 + T + |m.2.2| := by linarith [abs_nonneg m.2.2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg M) (Real.rpow_nonneg h.1.le _))
      (pow_nonneg h1 _)) (Real.exp_nonneg _)
  · exact le_rfl

theorem measurable_majG (M κ c T k : ℝ) (N : ℕ) :
    Measurable (majG M κ c T k N) := by
  unfold majG
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  · fun_prop

/-- The `η`-weight `((1+T+|η|)^N)^q e^{-κ|η|/c·q}` is integrable on `ℝ`. -/
theorem integrable_eta_weight (T c κ qr : ℝ) (N : ℕ) (hT : 0 ≤ T) (hc : 0 < c) (hκ : 0 < κ)
    (hqr : 0 < qr) :
    Integrable (fun η : ℝ => ((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * |η| / c)) ^ qr) := by
  set m : ℕ := ⌈(N : ℝ) * qr⌉₊ with hm
  have ha : 0 < κ * qr / c := by positivity
  have hint := (eta_integrable_one_add_abs_pow_mul_exp m ha).const_mul
    ((1 + T) ^ ((N : ℝ) * qr))
  refine hint.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · refine ae_of_all _ fun η => ?_
    have hX : 0 ≤ 1 + T + |η| := by linarith [abs_nonneg η]
    have hW0 : 0 ≤ ((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * |η| / c)) ^ qr := by
      apply mul_nonneg
      · exact Real.rpow_nonneg (pow_nonneg hX _) _
      · exact Real.rpow_nonneg (Real.exp_nonneg _) _
    rw [Real.norm_of_nonneg hW0]
    have h1 : ((1 + T + |η|) ^ N) ^ qr ≤ (1 + T) ^ ((N : ℝ) * qr) * (1 + |η|) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
      have hY : (1 + T + |η|) ≤ (1 + T) * (1 + |η|) := by nlinarith [abs_nonneg η]
      calc (1 + T + |η|) ^ ((N : ℝ) * qr)
          ≤ ((1 + T) * (1 + |η|)) ^ ((N : ℝ) * qr) :=
            Real.rpow_le_rpow hX hY (by positivity)
        _ = (1 + T) ^ ((N : ℝ) * qr) * (1 + |η|) ^ ((N : ℝ) * qr) :=
            Real.mul_rpow (by linarith) (by linarith [abs_nonneg η])
        _ ≤ (1 + T) ^ ((N : ℝ) * qr) * (1 + |η|) ^ (m : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg η])
              (Nat.le_ceil _)
        _ = (1 + T) ^ ((N : ℝ) * qr) * (1 + |η|) ^ m := by
            rw [Real.rpow_natCast]
    have hE : Real.exp (-(κ * |η| / c)) ^ qr = Real.exp (-(κ * qr / c * |η|)) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    have h2 := mul_le_mul_of_nonneg_right h1
      (Real.exp_nonneg (-(κ * qr / c * |η|)))
    calc ((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * |η| / c)) ^ qr
        = ((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * qr / c * |η|)) := by rw [hE]
      _ ≤ (1 + T) ^ ((N : ℝ) * qr) * (1 + |η|) ^ m * Real.exp (-(κ * qr / c * |η|)) := h2
      _ = (1 + T) ^ ((N : ℝ) * qr) * ((1 + |η|) ^ m * Real.exp (-(κ * qr / c * |η|))) := by
          ring

/-- The `s`-weight `s^r` is integrable on `(0,T]` for `r > -1`. -/
theorem integrableOn_s_pow (T r : ℝ) (hT : 0 < T) (hr : -1 < r) :
    IntegrableOn (fun s : ℝ => s ^ r) (Ioc 0 T) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

/-- The vector profile `majG • e₀` whose ring lift dominates the chart-majorized field. -/
def majProf (M κ c T k : ℝ) (N : ℕ) (m : ℝ × (ℝ × ℝ)) : Merid :=
  majG M κ c T k N m • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Merid)

theorem norm_majProf {M κ c T k : ℝ} {N : ℕ} (hT : 0 ≤ T) (m : ℝ × (ℝ × ℝ)) :
    ‖majProf M κ c T k N m‖ = majG M κ c T k N m := by
  unfold majProf
  rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg (majG_nonneg hT m)]

theorem majProf_periodic (M κ c T k : ℝ) (N : ℕ) (s ξ η : ℝ) :
    majProf M κ c T k N (s, (ξ + c, η)) = majProf M κ c T k N (s, (ξ, η)) := rfl

theorem measurable_majProf (M κ c T k : ℝ) (N : ℕ) :
    Measurable (majProf M κ c T k N) :=
  (measurable_majG M κ c T k N).smul_const _

/-- The real identity for the `L^q` power of the majorant on `0 < s ≤ T`. -/
theorem majG_rpow_eq {M κ c T k qr : ℝ} {N : ℕ} (hT : 0 ≤ T) (hc : 0 < c) (hqr : 0 < qr)
    (ξ : ℝ) {s η : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    c⁻¹ * s ^ (qr / 2 - 5 / 2) * (majG M κ c T k N (s, (ξ, η))) ^ qr =
      c⁻¹ * |M| ^ qr * s ^ (k * qr - 5 / 2) *
        (((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * |η| / c)) ^ qr) := by
  have hG : majG M κ c T k N (s, (ξ, η)) =
      |M| * s ^ (k - 1 / 2) * (1 + T + |η|) ^ N * Real.exp (-(κ * |η| / c)) := by
    unfold majG
    rw [if_pos ⟨hs, hsT⟩]
  rw [hG]
  have e1 : (|M| * s ^ (k - 1 / 2) * (1 + T + |η|) ^ N * Real.exp (-(κ * |η| / c))) ^ qr =
      |M| ^ qr * (s ^ (k - 1 / 2)) ^ qr * ((1 + T + |η|) ^ N) ^ qr *
        Real.exp (-(κ * |η| / c)) ^ qr := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
  have e2 : (s ^ (k - 1 / 2)) ^ qr = s ^ ((k - 1 / 2) * qr) := by
    rw [← Real.rpow_mul hs.le]
  have hsa : s ^ (qr / 2 - 5 / 2) * s ^ ((k - 1 / 2) * qr) = s ^ (k * qr - 5 / 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [e1, e2, ← hsa]
  ring

/-- The `s`-weight of the majorant, on the cell measure. -/
def pI1 (M c T k qr : ℝ) (s : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) T).indicator (fun s : ℝ => ENNReal.ofReal (c⁻¹ * |M| ^ qr * s ^ (k * qr - 5 / 2))) s

/-- The `ξ`-weight: indicator of the cell `[-c/2, c/2)`. -/
def pI2 (c : ℝ) (ξ : ℝ) : ℝ≥0∞ := (Ico (-c / 2) (c / 2)).indicator (fun _ => (1 : ℝ≥0∞)) ξ

/-- The `η`-weight `((1+T+|η|)^N)^q e^{-q κ|η|/c}`. -/
def pG3 (T κ c qr : ℝ) (N : ℕ) (η : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + T + |η|) ^ N) ^ qr * Real.exp (-(κ * |η| / c)) ^ qr)

/-- The product majorant on the cell. -/
def pPhi (M κ c T k qr : ℝ) (N : ℕ) (p : ℝ × (ℝ × ℝ)) : ℝ≥0∞ :=
  pI1 M c T k qr p.1 * (pI2 c p.2.1 * pG3 T κ c qr N p.2.2)

theorem measurable_pI1 (M c T k qr : ℝ) : Measurable (pI1 M c T k qr) := by
  unfold pI1
  exact Measurable.indicator (Measurable.ennreal_ofReal (by fun_prop)) measurableSet_Ioc

theorem measurable_pI2 (c : ℝ) : Measurable (pI2 c) := by
  unfold pI2
  exact measurable_const.indicator measurableSet_Ico

theorem measurable_pG3 (T κ c qr : ℝ) (N : ℕ) : Measurable (pG3 T κ c qr N) := by
  unfold pG3
  exact Measurable.ennreal_ofReal (by fun_prop)

theorem ageμ_majProf_lt_top {M κ c T k qr : ℝ} {N : ℕ} (hT : 0 < T) (hc : 0 < c) (hκ : 0 < κ)
    (hqr : 0 < qr) (hk : 3 / 2 < k * qr) :
    ∫⁻ p, ‖majProf M κ c T k N p‖ₑ ^ qr ∂ageμ c (qr / 2 - 5 / 2) < ⊤ := by
  have hr1 : -1 < k * qr - 5 / 2 := by linarith
  have hWint := integrable_eta_weight T c κ qr N hT.le hc hκ hqr
  have hcongr : ∀ p, ‖majProf M κ c T k N p‖ₑ ^ qr = ENNReal.ofReal (majG M κ c T k N p) ^ qr := by
    intro p
    have h : ‖majProf M κ c T k N p‖ₑ = ENNReal.ofReal (majG M κ c T k N p) := by
      rw [← ofReal_norm_eq_enorm, norm_majProf hT.le p]
    rw [h]
  simp only [hcongr]
  rw [lintegral_ageμ hc _ ((measurable_majG M κ c T k N).ennreal_ofReal.pow_const qr)]
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ p : ℝ × (ℝ × ℝ), p ∈ Ioi (0 : ℝ) ×ˢ qCell c →
      ENNReal.ofReal (c⁻¹ * p.1 ^ (qr / 2 - 5 / 2)) * ENNReal.ofReal (majG M κ c T k N p) ^ qr
        ≤ pPhi M κ c T k qr N p := by
    rintro ⟨s, ξ, η⟩ hp
    have hs' : (0 : ℝ) < s := hp.1
    have hξ' : ξ ∈ Ico (-c / 2) (c / 2) := (show (ξ, η) ∈ Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) from hp.2).1
    by_cases hsT : s ≤ T
    · have hmem : s ∈ Ioc (0 : ℝ) T := ⟨hs', hsT⟩
      have hreal := majG_rpow_eq (M := M) (κ := κ) (c := c) (T := T) (k := k) (N := N) (qr := qr)
        hT.le hc hqr ξ hs' hsT (η := η)
      unfold pPhi pI1 pI2 pG3
      dsimp only
      rw [indicator_of_mem hmem, indicator_of_mem hξ', one_mul,
        ENNReal.ofReal_rpow_of_nonneg (majG_nonneg hT.le _) hqr.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hreal]
    · have hz : majG M κ c T k N (s, (ξ, η)) = 0 := by
        unfold majG
        rw [if_neg (fun h => hsT h.2)]
      have hz' : ENNReal.ofReal (majG M κ c T k N (s, (ξ, η))) ^ qr = 0 := by
        rw [hz, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hqr]
      rw [hz', mul_zero]
      exact _root_.zero_le
  calc ∫⁻ p : ℝ × (ℝ × ℝ) in Ioi (0 : ℝ) ×ˢ qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (qr / 2 - 5 / 2)) * ENNReal.ofReal (majG M κ c T k N p) ^ qr
      ≤ ∫⁻ p : ℝ × (ℝ × ℝ) in Ioi (0 : ℝ) ×ˢ qCell c, pPhi M κ c T k qr N p :=
        setLIntegral_mono' hS hpt
    _ ≤ ∫⁻ p, pPhi M κ c T k qr N p := setLIntegral_le_lintegral _ _
    _ < ⊤ := by
        have hr1' : -1 < k * qr - 5 / 2 := hr1
        have hsplit : ∫⁻ p : ℝ × (ℝ × ℝ), pPhi M κ c T k qr N p =
            (∫⁻ s, pI1 M c T k qr s) *
              ((∫⁻ ξ, pI2 c ξ) * ∫⁻ η, pG3 T κ c qr N η) := by
          have h1 : ∫⁻ p : ℝ × (ℝ × ℝ), pI1 M c T k qr p.1 * (pI2 c p.2.1 * pG3 T κ c qr N p.2.2) =
              (∫⁻ s, pI1 M c T k qr s) *
                ∫⁻ z : ℝ × ℝ, pI2 c z.1 * pG3 T κ c qr N z.2 :=
            lintegral_prod_mul (measurable_pI1 M c T k qr).aemeasurable
              ((((measurable_pI2 c).comp measurable_fst).mul
                ((measurable_pG3 T κ c qr N).comp measurable_snd)).aemeasurable)
          have h2 : ∫⁻ z : ℝ × ℝ, pI2 c z.1 * pG3 T κ c qr N z.2 =
              (∫⁻ ξ, pI2 c ξ) * ∫⁻ η, pG3 T κ c qr N η :=
            lintegral_prod_mul (measurable_pI2 c).aemeasurable
              (measurable_pG3 T κ c qr N).aemeasurable
          rw [h2] at h1
          exact h1
        have hI1 : ∫⁻ s, pI1 M c T k qr s < ⊤ := by
          unfold pI1
          rw [lintegral_indicator measurableSet_Ioc]
          have hint : Integrable (fun s : ℝ => c⁻¹ * |M| ^ qr * s ^ (k * qr - 5 / 2))
              (volume.restrict (Ioc (0 : ℝ) T)) :=
            (integrableOn_s_pow T _ hT hr1').const_mul _
          exact hint.lintegral_lt_top
        have hI2 : ∫⁻ ξ, pI2 c ξ < ⊤ := by
          unfold pI2
          rw [lintegral_indicator_const measurableSet_Ico, one_mul, Real.volume_Ico]
          exact ENNReal.ofReal_lt_top
        have hG3 : ∫⁻ η, pG3 T κ c qr N η < ⊤ := by
          unfold pG3
          exact hWint.lintegral_lt_top
        rw [hsplit]
        exact ENNReal.mul_lt_top hI1 (ENNReal.mul_lt_top hI2 hG3)

/-- **Sub4: `L^q` of a chart-majorized field on `(0,P] × ℝ³`.** -/
theorem majLp : MajLp := by
  intro R c P T κ k qr M N q hR hc hP hT hκ hq hqr hk F hF hbound
  subst hq
  have hk0 : 0 < k := by
    by_contra h
    push_neg at h
    nlinarith
  have hT0 : 0 ≤ T := hT.le
  have hPpos : 0 < P := by rw [hP]; positivity
  have hb'm := measurable_majProf M κ c T k N
  have hb'per : ∀ s ξ η : ℝ, majProf M κ c T k N (s, (ξ + c, η)) =
      majProf M κ c T k N (s, (ξ, η)) := majProf_periodic M κ c T k N
  have hdom : ∀ (τ : ℝ) (y : UnforcedLeray.Space),
      ‖F (τ, y)‖ ≤ ‖Nv R (majProf M κ c T k N) τ y‖ := by
    intro τ y
    by_cases hy : y ∈ axis
    · have hϱ : ϱ y = 0 := by
        obtain ⟨h0, h1⟩ := hy
        simp [ϱ, h0, h1]
      have hage : age R y = 0 := by simp [age, hϱ]
      have hA0 : age R y ≤ T := by rw [hage]; exact hT0
      have hb := hbound τ y
      rw [if_pos hA0, hage, Real.zero_rpow hk0.ne', mul_zero, zero_mul, zero_mul] at hb
      have hN : ‖Nv R (majProf M κ c T k N) τ y‖ = 0 := by simp [Nv, hage]
      rw [hN]
      exact hb
    · have hpos : 0 < age R y := age_pos hR.ne' hy
      rw [norm_Nv R (majProf M κ c T k N) τ hy, norm_majProf hT0]
      have hb := hbound τ y
      by_cases hA : age R y ≤ T
      · rw [if_pos hA] at hb
        have hG : majG M κ c T k N (chart R τ y) =
            |M| * age R y ^ (k - 1 / 2) * (1 + T + |trans R y|) ^ N *
              Real.exp (-(κ * |trans R y| / c)) := by
          unfold majG chart
          dsimp only
          rw [if_pos ⟨hpos, hA⟩]
        rw [hG]
        have hid : √(age R y) * age R y ^ (k - 1 / 2) = age R y ^ k := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
          congr 1
          ring
        have hXE : 0 ≤ (1 + T + |trans R y|) ^ N * Real.exp (-(κ * |trans R y| / c)) :=
          mul_nonneg (pow_nonneg (by linarith [abs_nonneg (trans R y)]) _) (Real.exp_nonneg _)
        have hak : 0 ≤ age R y ^ k := Real.rpow_nonneg hpos.le _
        have h1 : M * age R y ^ k ≤ |M| * age R y ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self M) hak
        have h2 := mul_le_mul_of_nonneg_right h1 hXE
        calc ‖F (τ, y)‖
            ≤ M * age R y ^ k * (1 + T + |trans R y|) ^ N *
                Real.exp (-(κ * |trans R y| / c)) := hb
          _ = M * age R y ^ k * ((1 + T + |trans R y|) ^ N *
                Real.exp (-(κ * |trans R y| / c))) := by ring
          _ ≤ |M| * age R y ^ k * ((1 + T + |trans R y|) ^ N *
                Real.exp (-(κ * |trans R y| / c))) := h2
          _ = √(age R y) * (|M| * age R y ^ (k - 1 / 2) * (1 + T + |trans R y|) ^ N *
                Real.exp (-(κ * |trans R y| / c))) := by
              rw [← hid]
              ring
      · rw [if_neg hA] at hb
        exact hb.trans (mul_nonneg (Real.sqrt_nonneg _) (majG_nonneg hT0 _))
  have hmeasN : Measurable fun x : ℝ × UnforcedLeray.Space =>
      ‖Nv R (majProf M κ c T k N) x.1 x.2‖ₑ ^ qr :=
    ((measurable_Nv R hb'm).enorm).pow_const qr
  have hIle : ∫⁻ x : ℝ × UnforcedLeray.Space, ‖F x‖ₑ ^ qr
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) ≤
      ∫⁻ x : ℝ × UnforcedLeray.Space, ‖Nv R (majProf M κ c T k N) x.1 x.2‖ₑ ^ qr
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) := by
    apply lintegral_mono
    intro x
    refine ENNReal.rpow_le_rpow ?_ hqr.le
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hdom x.1 x.2)
  have hI : ∫⁻ x : ℝ × UnforcedLeray.Space, ‖Nv R (majProf M κ c T k N) x.1 x.2‖ₑ ^ qr
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) =
      ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
        ‖Nv R (majProf M κ c T k N) τ y‖ₑ ^ qr := by
    exact lintegral_prod _ hmeasN.aemeasurable
  have hNv := lintegral_Nv_rpow hR hc hP hqr hb'm hb'per
  have hJ := ageμ_majProf_lt_top (M := M) (κ := κ) (c := c) (T := T) (k := k) (qr := qr) (N := N)
    hT hc hκ hqr hk
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hPpos).ne'
  have hPt : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hXfin : (∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
        ‖Nv R (majProf M κ c T k N) τ y‖ₑ ^ qr) < ⊤ := by
    set X := ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
        ‖Nv R (majProf M κ c T k N) τ y‖ₑ ^ qr with hX
    have hcancel : ENNReal.ofReal P * ((ENNReal.ofReal P)⁻¹ * X) = X := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hPne hPt, one_mul]
    rw [hNv] at hcancel
    rw [← hcancel]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ)
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr hqr).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hqr.le]
  exact (hIle.trans_eq hI).trans_lt hXfin

end UnforcedLeray.Short.PartIIIb.Concrete
