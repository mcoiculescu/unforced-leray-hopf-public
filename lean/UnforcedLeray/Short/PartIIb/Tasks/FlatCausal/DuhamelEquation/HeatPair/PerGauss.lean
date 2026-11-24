import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_4_4

/-!
# Part II-b, task `PartII-b:T12/7/4/4/1` (`DeqhpPerGauss`): the per-Gaussian leaf

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Proof. A nonnegative-or-signed measurable `c`-periodic profile `G` (a.e. periodic in the first
variable) with `∫_cell |G|^r < ∞` (`r > 1`) has `∫_{ℝ²} |G e^{-b|z|²}| < ∞`:
1. Cover `ℝ²` by the translates `S n = {z | z₁ - n c ∈ [-c/2, c/2)}` of the cell.
2. Translate each piece back to the cell; a.e. periodicity turns `G(w₁ + n c, w₂)` into `G(w)`.
3. The Gaussian over the translates is bounded by `K · e^{-b w₂²}` on the cell, with
   `K = Σ_n e^{-(b c²/4) n²} < ∞`.
4. Hölder on the cell with exponents `r, q = r/(r-1)`; `e^{-b q w₂²}` is integrable on the cell.

The reduction from `F` to a measurable representative `G` uses `F =ᵐ G`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Translation `(z₁, z₂) ↦ (z₁ + a, z₂)` preserves Lebesgue measure on the plane. -/
theorem pg_tau (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + a, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).prod
    (MeasurePreserving.id (volume : Measure ℝ))

/-- Shifts by `n c` preserve a.e. periodicity. -/
theorem pg_shift_ae {c : ℝ} {F : ℝ × ℝ → ℝ}
    (hper : ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + c, z.2) = F z) :
    ∀ n : ℤ, ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + n * c, z.2) = F z := by
  have hstep : ∀ a : ℝ, ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + a + c, z.2) = F (z.1 + a, z.2) :=
    fun a => (pg_tau a).quasiMeasurePreserving.ae hper
  have hiff : ∀ a : ℝ, (∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + a, z.2) = F z) ↔
      (∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + (a + c), z.2) = F z) := by
    intro a
    constructor
    · intro h
      filter_upwards [h, hstep a] with z hz hz1
      rw [show z.1 + (a + c) = z.1 + a + c by ring, hz1, hz]
    · intro h
      filter_upwards [h, hstep a] with z hz hz1
      rw [← hz1, show z.1 + a + c = z.1 + (a + c) by ring, hz]
  intro n
  induction n using Int.induction_on with
  | zero => exact Filter.Eventually.of_forall fun z => by simp
  | succ i ih =>
    have e : (((i : ℤ) + 1 : ℤ) : ℝ) * c = ((i : ℤ) : ℝ) * c + c := by push_cast; ring
    rw [e]
    exact (hiff _).1 ih
  | pred i ih =>
    refine (hiff _).2 ?_
    have e : (((-(i : ℤ) - 1 : ℤ)) : ℝ) * c + c = (((-(i : ℤ)) : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e]
    exact ih

/-- A measurable (a.e.-equal) representative inherits a.e. periodicity. -/
theorem pg_mk_periodic {c : ℝ} {F G : ℝ × ℝ → ℝ} (hae : F =ᵐ[volume] G)
    (hper : ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + c, z.2) = F z) :
    ∀ᵐ z : ℝ × ℝ ∂volume, G (z.1 + c, z.2) = G z := by
  have h2 : ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + c, z.2) = G (z.1 + c, z.2) :=
    (pg_tau c).quasiMeasurePreserving.ae hae
  filter_upwards [hper, h2, hae] with z h1 h2z h3
  have h2z' : G (z.1 + c, z.2) = F (z.1 + c, z.2) := h2z.symm
  rw [h2z', h1]
  exact h3

/-- Covering of `ℝ` by the translates of `[-c/2, c/2)`. -/
theorem pg_cover (c : ℝ) (hc : 0 < c) (x : ℝ) :
    ∃ n : ℤ, x - n * c ∈ Ico (-c / 2) (c / 2) := by
  refine ⟨⌊(x + c / 2) / c⌋, ?_⟩
  have h1 := Int.floor_le ((x + c / 2) / c)
  have h2 := Int.lt_floor_add_one ((x + c / 2) / c)
  have e1 := mul_le_mul_of_nonneg_right h1 hc.le
  have e2 := mul_lt_mul_of_pos_right h2 hc
  rw [div_mul_cancel₀ _ hc.ne'] at e1
  rw [div_mul_cancel₀ _ hc.ne'] at e2
  rw [Set.mem_Ico]
  constructor <;> nlinarith

/-- Integer-translate bound for the squared coordinate. -/
theorem pg_sq_shift_bound {c x : ℝ} (hc : 0 < c) (hx : |x| ≤ c / 2) (n : ℤ) :
    (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x + n * c) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Int.cast_zero, zero_mul, add_zero]
    nlinarith [sq_nonneg x]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (n : ℝ) * c := ⟨_, rfl⟩
    rw [← ht]
    have hte : |t| = |(n : ℝ)| * c := by rw [ht, abs_mul, abs_of_pos hc]
    have ht1 : c ≤ |t| := by rw [hte]; nlinarith
    have h3 : |t| ≤ |x + t| + |x| := by
      calc |t| = |(x + t) + -x| := by congr 1; ring
        _ ≤ |x + t| + |-x| := abs_add_le _ _
        _ = |x + t| + |x| := by rw [abs_neg]
    have h2 : |t| / 2 ≤ |x + t| := by linarith
    have h5 : |t| / 2 * (|t| / 2) ≤ |x + t| * |x + t| :=
      mul_le_mul h2 h2 (by positivity) (abs_nonneg _)
    have h6 : (n : ℝ) ^ 2 * c ^ 2 = t ^ 2 := by rw [ht]; ring
    nlinarith [sq_abs (x + t), sq_abs t, h5, h6]

/-- Pointwise Gaussian translate bound on the cell. -/
theorem pg_theta_bound {c b x y : ℝ} (hc : 0 < c) (hb : 0 < b) (hx : |x| ≤ c / 2) (n : ℤ) :
    Real.exp (-b * ((x + n * c) ^ 2 + y ^ 2)) ≤
      Real.exp (-(b * c ^ 2 / 4) * (n : ℝ) ^ 2) * Real.exp (-b * y ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := pg_sq_shift_bound hc hx n
  nlinarith [mul_le_mul_of_nonneg_left h hb.le]

/-- Summability of a Gaussian over `ℤ`. -/
theorem pg_summable_gauss_int {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℤ => Real.exp (-β * (n : ℝ) ^ 2)) := by
  have hN : Summable (fun n : ℕ => Real.exp (-β * ((n : ℤ) : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one (Real.exp_pos (-β)).le (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)))
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hn hβ.le]
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using hN
  · simpa [neg_sq] using hN

/-- Measurable core: integrability of `G e^{-b|z|²}` from the cell `L^r` bound. -/
theorem pg_main_meas {c r b : ℝ} (hc : 0 < c) (hr : 1 < r) (hb : 0 < b) {G : ℝ × ℝ → ℝ}
    (hGm : Measurable G) (hper : ∀ᵐ z : ℝ × ℝ ∂volume, G (z.1 + c, z.2) = G z)
    (hX : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖G z‖ₑ ^ r < ⊤) :
    ∫⁻ z, ‖G z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))‖ₑ < ⊤ := by
  have hgm : Measurable (fun z : ℝ × ℝ => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))) := by
    fun_prop
  have hcell : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  let S : ℤ → Set (ℝ × ℝ) := fun n =>
    (fun z : ℝ × ℝ => (z.1 - n * c, z.2)) ⁻¹' UnforcedLeray.Cyl.cell c
  have hSm : ∀ n : ℤ, MeasurableSet (S n) := fun n =>
    hcell.preimage ((measurable_fst.sub_const ((n : ℝ) * c)).prodMk measurable_snd)
  let φ : ℝ × ℝ → ℝ≥0∞ := fun z => ‖G z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))‖ₑ
  have hφm : Measurable φ := (hGm.mul hgm).enorm
  have hcov : ∀ z : ℝ × ℝ, ∃ n : ℤ, z ∈ S n := by
    intro z
    obtain ⟨n, hn⟩ := pg_cover c hc z.1
    exact ⟨n, hn, Set.mem_univ _⟩
  -- Step 3: unfold over the translates of the cell.
  have step3 : ∫⁻ z, φ z ≤ ∑' n : ℤ, ∫⁻ z, (S n).indicator φ z := by
    calc ∫⁻ z, φ z ≤ ∫⁻ z, ∑' n : ℤ, (S n).indicator φ z := by
          refine lintegral_mono fun z => ?_
          obtain ⟨n, hn⟩ := hcov z
          calc φ z = (S n).indicator φ z := (indicator_of_mem hn φ).symm
            _ ≤ ∑' m : ℤ, (S m).indicator φ z := ENNReal.le_tsum n
      _ = ∑' n : ℤ, ∫⁻ z, (S n).indicator φ z :=
          lintegral_tsum fun n => (hφm.indicator (hSm n)).aemeasurable
  -- Step 4: each piece is a cell integral of a translate.
  have step4 : ∀ n : ℤ, ∫⁻ z, (S n).indicator φ z =
      ∫⁻ w in UnforcedLeray.Cyl.cell c,
        ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) := by
    intro n
    have hmeasI : Measurable ((S n).indicator φ) := hφm.indicator (hSm n)
    have h1 : ∫⁻ z, (S n).indicator φ z = ∫⁻ w : ℝ × ℝ, (S n).indicator φ (w.1 + n * c, w.2) :=
      ((pg_tau (n * c)).lintegral_comp hmeasI).symm
    have h2 : (fun w : ℝ × ℝ => (S n).indicator φ (w.1 + n * c, w.2)) =
        (UnforcedLeray.Cyl.cell c).indicator (fun w => φ (w.1 + n * c, w.2)) := by
      funext w
      by_cases hw : w ∈ UnforcedLeray.Cyl.cell c
      · have hw' : (w.1 + n * c, w.2) ∈ S n := by
          show (w.1 + n * c - n * c, w.2) ∈ UnforcedLeray.Cyl.cell c
          rw [add_sub_cancel_right]; exact hw
        rw [indicator_of_mem hw', indicator_of_mem hw]
      · have hw' : (w.1 + n * c, w.2) ∉ S n := by
          show ¬ ((w.1 + n * c - n * c, w.2) ∈ UnforcedLeray.Cyl.cell c)
          rw [add_sub_cancel_right]; exact hw
        rw [indicator_of_notMem hw', indicator_of_notMem hw]
    have h3 : ∫⁻ w : ℝ × ℝ, (S n).indicator φ (w.1 + n * c, w.2) =
        ∫⁻ w in UnforcedLeray.Cyl.cell c, φ (w.1 + n * c, w.2) := by
      rw [← lintegral_indicator hcell]
      exact lintegral_congr fun w => congrFun h2 w
    have h4 : ∫⁻ w in UnforcedLeray.Cyl.cell c, φ (w.1 + n * c, w.2) =
        ∫⁻ w in UnforcedLeray.Cyl.cell c,
          ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (pg_shift_ae hper n)] with w hw
      show ‖G (w.1 + n * c, w.2) * Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))‖ₑ = _
      rw [hw, enorm_mul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
    rw [h1, h3, h4]
  -- Step 5: sum over `n` inside the integral.
  have step5 : ∑' n : ℤ, ∫⁻ w in UnforcedLeray.Cyl.cell c,
        ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) =
      ∫⁻ w in UnforcedLeray.Cyl.cell c,
        ‖G w‖ₑ * ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) := by
    rw [← lintegral_tsum]
    · refine lintegral_congr fun w => ?_
      exact ENNReal.tsum_mul_left
    · intro n
      exact (hGm.enorm.mul ((ENNReal.measurable_ofReal).comp (by fun_prop))).aemeasurable
  -- Step 6: bound the Gaussian sum on the cell.
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ≥0∞, K = ∑' n : ℤ,
      ENNReal.ofReal (Real.exp (-(b * c ^ 2 / 4) * (n : ℝ) ^ 2)) := ⟨_, rfl⟩
  have hK : K ≠ ⊤ := by
    rw [hKdef, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le)
      (pg_summable_gauss_int (div_pos (mul_pos hb (pow_pos hc 2)) (by norm_num)))]
    exact ENNReal.ofReal_ne_top
  have hΘ : ∀ w ∈ UnforcedLeray.Cyl.cell c,
      ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) ≤
        K * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) := by
    intro w hw
    obtain ⟨⟨h1, h2⟩, _⟩ := hw
    have hx : |w.1| ≤ c / 2 := by
      rw [abs_le]; constructor <;> linarith
    rw [hKdef, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (pg_theta_bound hc hb hx n)
  have step6 : ∫⁻ w in UnforcedLeray.Cyl.cell c,
        ‖G w‖ₑ * ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) ≤
      K * ∫⁻ w in UnforcedLeray.Cyl.cell c,
        ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) := by
    calc ∫⁻ w in UnforcedLeray.Cyl.cell c,
          ‖G w‖ₑ * ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2)))
        ≤ ∫⁻ w in UnforcedLeray.Cyl.cell c,
            K * (‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hcell] with w hw
          calc ‖G w‖ₑ * ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2)))
              ≤ ‖G w‖ₑ * (K * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2))) :=
                by gcongr; exact hΘ w hw
            _ = K * (‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2))) := by ring
      _ = K * ∫⁻ w in UnforcedLeray.Cyl.cell c,
            ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) :=
          lintegral_const_mul' K _ hK
  -- Step 7: Hölder on the cell.
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.conjExponent r := ⟨_, rfl⟩
  have hq : r.HolderConjugate q := hqdef ▸ Real.HolderConjugate.conjExponent hr
  have hq0 : 0 < q := by
    rw [hqdef]; unfold Real.conjExponent; apply div_pos <;> linarith
  have hB : Measurable (fun w : ℝ × ℝ => ENNReal.ofReal (Real.exp (-b * w.2 ^ 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hBq : ∀ w : ℝ × ℝ, ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) ^ q =
      ENNReal.ofReal (Real.exp (-(b * q) * w.2 ^ 2)) := by
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul]
    congr 2; ring
  have hGauss : ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(b * q) * y ^ 2)) < ⊤ :=
    (integrable_exp_neg_mul_sq (mul_pos hb hq0)).lintegral_lt_top
  have hY : ∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-(b * q) * w.2 ^ 2)) < ⊤ := by
    have e0 : ∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-(b * q) * w.2 ^ 2)) =
        ∫⁻ w, (fun _ : ℝ => (1 : ℝ≥0∞)) w.1 *
          (fun y : ℝ => ENNReal.ofReal (Real.exp (-(b * q) * y ^ 2))) w.2
          ∂((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
      rw [← UnforcedLeray.Cyl.cellμ_eq_prod]
      simp only [one_mul]
      rfl
    have hmeasE : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-(b * q) * y ^ 2))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have e1 : ∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-(b * q) * w.2 ^ 2)) =
        (∫⁻ x in Ico (-c / 2) (c / 2), (1 : ℝ≥0∞)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (-(b * q) * y ^ 2)) :=
      e0.trans (lintegral_prod_mul (measurable_const.aemeasurable)
        (hmeasE).aemeasurable)
    rw [e1]
    refine ENNReal.mul_lt_top ?_ hGauss
    rw [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hY' : ∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) ^ q < ⊤ := by
    simp only [hBq]; exact hY
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (UnforcedLeray.Cyl.cell c)) hq hGm.enorm.aemeasurable hB.aemeasurable
  have hholder' : ∫⁻ w in UnforcedLeray.Cyl.cell c, ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2))
      ≤ (∫⁻ w in UnforcedLeray.Cyl.cell c, ‖G w‖ₑ ^ r) ^ (1 / r) *
        (∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) ^ q) ^ (1 / q) :=
    hholder
  have hfin : (∫⁻ w in UnforcedLeray.Cyl.cell c, ‖G w‖ₑ ^ r) ^ (1 / r) *
      (∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) ^ q) ^ (1 / q) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 (by linarith)) hX.ne)
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hq0.le) hY'.ne)
  calc ∫⁻ z, φ z ≤ ∑' n : ℤ, ∫⁻ z, (S n).indicator φ z := step3
    _ = ∑' n : ℤ, ∫⁻ w in UnforcedLeray.Cyl.cell c,
          ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) :=
        tsum_congr step4
    _ = ∫⁻ w in UnforcedLeray.Cyl.cell c,
          ‖G w‖ₑ * ∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * ((w.1 + n * c) ^ 2 + w.2 ^ 2))) := step5
    _ ≤ K * ∫⁻ w in UnforcedLeray.Cyl.cell c, ‖G w‖ₑ * ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) :=
        step6
    _ ≤ K * ((∫⁻ w in UnforcedLeray.Cyl.cell c, ‖G w‖ₑ ^ r) ^ (1 / r) *
          (∫⁻ w in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (Real.exp (-b * w.2 ^ 2)) ^ q) ^ (1 / q)) :=
        by gcongr
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) hfin

/-- **Leaf** (SP 1923-1927): `F ≥ 0` measurable, `c`-periodic in the first variable a.e., with
`‖F‖_{L^r(Cyl.avgμ c)} < ∞` for some `r > 1`. Then `F e^{-b(z₁²+z₂²)}` is integrable on the plane. -/
theorem deqhpPerGauss : DeqhpPerGauss := by
  intro c r b hc hr hb F hF0 hFm hper hL
  obtain ⟨G, hGs, hae⟩ : ∃ G : ℝ × ℝ → ℝ, StronglyMeasurable G ∧ F =ᵐ[volume] G :=
    ⟨hFm.mk F, hFm.stronglyMeasurable_mk, hFm.ae_eq_mk⟩
  have hGm : Measurable G := hGs.measurable
  have hperG := pg_mk_periodic hae hper
  have hXF : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖F z‖ₑ ^ r < ⊤ := by
    have h1 : ∫⁻ z, ‖F z‖ₑ ^ (ENNReal.ofReal r).toReal ∂(UnforcedLeray.Cyl.avgμ c) < ⊤ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top).1 hL
    rw [ENNReal.toReal_ofReal (by linarith), UnforcedLeray.Cyl.lintegral_avgμ] at h1
    rcases ENNReal.mul_lt_top_iff.1 h1 with ⟨_, h2⟩ | h2 | h2
    · exact h2
    · exact absurd h2 (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
    · rw [h2]; exact ENNReal.zero_lt_top
  have hXG : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖G z‖ₑ ^ r < ⊤ := by
    have e : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖G z‖ₑ ^ r =
        ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖F z‖ₑ ^ r :=
      lintegral_congr_ae ((ae_restrict_of_ae hae).mono fun z hz => by simp only [hz])
    rw [e]; exact hXF
  have hmain := pg_main_meas hc hr hb hGm hperG hXG
  refine ⟨?_, ?_⟩
  · exact hFm.mul (by fun_prop :
      Continuous fun z : ℝ × ℝ => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))).aestronglyMeasurable
  · have hae2 : (fun z : ℝ × ℝ => ‖F z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))‖ₑ) =ᵐ[volume]
        (fun z : ℝ × ℝ => ‖G z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))‖ₑ) :=
      hae.mono fun z hz => by simp only [hz]
    show ∫⁻ z, ‖F z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))‖ₑ < ⊤
    rw [lintegral_congr_ae hae2]
    exact hmain

end UnforcedLeray.Short.IIb
