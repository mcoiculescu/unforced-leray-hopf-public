import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Theta
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.SigmaToLambda
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `pdSourceFinite`: reduction to the period shift

Source `the November 2 reference manuscript` 2667 (period `P = 2c/R`), 3631-3646,
5585-5589.

The part `σ < τ₀` of the weighted source integral is bounded here by the two majorants
(`pd_kernel_compare`, `pdSupport`, `pdTheta`, `pdSigmaToLambda`).  The part `σ ∈ [τ₀, τ₀+ε)` is the
period shift `PDShiftBound`: shifting the source down by whole periods `2c/R` (`oldPhys` is
`2c/R`-periodic in the phase, `oldPhysPeriodic`) moves it into `σ < τ₀`, and the weight `srcWeight`
changes by at most the bounded factor `e^{(2μ+3) m c/R}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Period shift for the weighted source integral** (source 2667 `P = 2c/R`; 3631-3646).  The
integral of `srcWeight μ (τ₀ - σ) z |𝒩_T g|` over `σ < τ₀ + ε` is at most a finite multiple
(`K = 1 + e^{(2μ+3) m c/R}`, `m` whole periods with `m·2c/R > ε`) of the same integral over
`σ < τ₀`.  Proof: for `σ ∈ [τ₀, τ₀+ε)` translate `σ ↦ σ - m·2c/R` (measure preserving on
`ℝ × Space`; `oldPhysPeriodic` leaves `oldPhys` unchanged; `measurable_oldPhys_entry` for
measurability); with `λ = e^{-(τ₀-σ)/2}` the shifted `λ` is `λ' = e^{mc/R} λ ≥ λ`, and
`srcWeight μ h' z = λ'^{2μ+3}((1+λ'|z|)^{-4} + (1+(λ'z₃)²)^{-1}) ≤ e^{(2μ+3)mc/R} srcWeight μ h z`
since the bracket is decreasing in `λ` and `2μ+3 > 0`. -/
def PDShiftBound : Prop :=
  ∀ (μ R c : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → -(1 / 4) < μ → Measurable g →
    ∀ (τ₀ ε : ℝ), 0 < ε → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∫⁻ e : ℝ × Space, (if e.1 < τ₀ + ε then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≤
      K * ∫⁻ e : ℝ × Space, (if e.1 < τ₀ then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2

/-- Pointwise comparison of the crude weight with the two kernels, for `ϱ z < ϱ y₀` and `λ ∈ (0,1]`
(source 3604-3610 kernel `|y - λz|^{-4}`, 4178-4186 stream kernel; `λ^{2μ+3} ≤ λ`,
`‖y₀ - λz‖ ≤ ‖y₀‖ + λ‖z‖`, `(a-b)² ≤ 2a²+2b²`). -/
lemma pd_kernel_compare (μ : ℝ) (hμ : -(1 / 4) < μ) (y₀ : Space) (hy : 0 < ϱ y₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ z : Space, ϱ z < ϱ y₀ →
      l ^ (2 * μ + 3) * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹) ≤
        l * (C * ((‖y₀ - l • z‖ ^ 4)⁻¹ +
          (ϱ y₀ ^ 2 * (ϱ y₀ ^ 2 + (y₀ 2 - l * z 2) ^ 2))⁻¹)) := by
  set N : ℝ := max 1 ‖y₀‖ with hN
  have hN1 : 1 ≤ N := le_max_left _ _
  have hN2 : ‖y₀‖ ≤ N := le_max_right _ _
  set r : ℝ := ϱ y₀ ^ 2 with hr
  have hr0 : 0 < r := by positivity
  set a : ℝ := y₀ 2 with ha
  set C2 : ℝ := r ^ 2 + 2 * r * a ^ 2 + 2 * r with hC2
  have hC20 : 0 < C2 := by positivity
  refine ⟨N ^ 4 + C2, by positivity, ?_⟩
  intro l hl0 hl1 z hz
  have hp : l ^ (2 * μ + 3) ≤ l := by
    have := Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (show (1 : ℝ) ≤ 2 * μ + 3 by linarith)
    simpa using this
  have hne : y₀ - l • z ≠ 0 := by
    intro h0
    have h1 : y₀ = l • z := sub_eq_zero.mp h0
    have h2 : ϱ y₀ = l * ϱ z := by rw [h1, ϱ_smul, abs_of_pos hl0]
    have h3 : l * ϱ z ≤ ϱ z := by nlinarith [show 0 ≤ ϱ z from Real.sqrt_nonneg _]
    linarith
  have hW : 0 < ‖y₀ - l • z‖ := norm_pos_iff.mpr hne
  have hnz : 0 ≤ ‖z‖ := norm_nonneg _
  -- first kernel
  have hA : ((1 + l * ‖z‖) ^ 4)⁻¹ ≤ N ^ 4 * (‖y₀ - l • z‖ ^ 4)⁻¹ := by
    have hP : 0 < (1 + l * ‖z‖) ^ 4 := by positivity
    have hW4 : 0 < ‖y₀ - l • z‖ ^ 4 := by positivity
    have hle : ‖y₀ - l • z‖ ≤ N * (1 + l * ‖z‖) := by
      calc ‖y₀ - l • z‖ ≤ ‖y₀‖ + ‖l • z‖ := norm_sub_le _ _
        _ = ‖y₀‖ + l * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
        _ ≤ N * (1 + l * ‖z‖) := by nlinarith [mul_nonneg hl0.le hnz]
    have h4 : ‖y₀ - l • z‖ ^ 4 ≤ N ^ 4 * (1 + l * ‖z‖) ^ 4 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hW.le hle 4
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hP hW4]
    linarith
  -- second kernel
  have hB : (1 + (l * z 2) ^ 2)⁻¹ ≤ C2 * (r * (r + (a - l * z 2) ^ 2))⁻¹ := by
    set b : ℝ := l * z 2 with hb
    have h1 : 0 < 1 + b ^ 2 := by positivity
    have h2 : 0 < r * (r + (a - b) ^ 2) := by positivity
    have h3 : r * (r + (a - b) ^ 2) ≤ C2 * (1 + b ^ 2) := by
      have : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
      have h5 : r * (r + (a - b) ^ 2) ≤ r * (r + (2 * a ^ 2 + 2 * b ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hr0.le
      have h6 : r * (r + (2 * a ^ 2 + 2 * b ^ 2)) ≤ C2 * (1 + b ^ 2) := by
        simp only [hC2]
        nlinarith [mul_nonneg hr0.le (sq_nonneg b), sq_nonneg b, sq_nonneg a, hr0]
      exact h5.trans h6
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ h1 h2]
    linarith
  have hKpos1 : 0 ≤ (‖y₀ - l • z‖ ^ 4)⁻¹ := by positivity
  have hKpos2 : 0 ≤ (r * (r + (a - l * z 2) ^ 2))⁻¹ := by positivity
  have hpr : ϱ y₀ ^ 2 * (ϱ y₀ ^ 2 + (y₀ 2 - l * z 2) ^ 2) = r * (r + (a - l * z 2) ^ 2) := rfl
  rw [hpr]
  have hsum : ((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹ ≤
      (N ^ 4 + C2) * ((‖y₀ - l • z‖ ^ 4)⁻¹ + (r * (r + (a - l * z 2) ^ 2))⁻¹) := by
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4) hKpos2,
      mul_nonneg hC20.le hKpos1]
  calc l ^ (2 * μ + 3) * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹)
      ≤ l * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ l * ((N ^ 4 + C2) * ((‖y₀ - l • z‖ ^ 4)⁻¹ + (r * (r + (a - l * z 2) ^ 2))⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum hl0.le

lemma srcNorm_eq_zero_of (R c : ℝ) (g : Chart → Ten3) (σ : ℝ) (z : Space)
    (h : oldPhys R c g σ z = 0) : IIIa.srcNorm (oldPhys R c g) σ z = 0 := by
  unfold IIIa.srcNorm IIIa.tensorNorm
  rw [h]; simp

lemma measurable_srcNorm' (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun e : ℝ × Space => IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
  unfold IIIa.srcNorm IIIa.tensorNorm
  refine Measurable.ennreal_ofReal (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (T8_1.measurable_oldPhys_entry R c g hg i j).pow_const 2

lemma pd_lam_log (τ l : ℝ) (hl : 0 < l) : pdLam (τ - (τ + 2 * Real.log l)) = l := by
  unfold pdLam
  rw [show -((τ - (τ + 2 * Real.log l)) / 2) = Real.log l by ring]
  exact Real.exp_log hl

lemma measurable_pdLam_comp : Measurable (fun e : ℝ × Space => pdLam e.1) := by
  unfold pdLam; fun_prop

/-- The part `σ < τ₀` of the weighted source integral is finite when the two majorants are
(source 3611-3621, 5588-5589). -/
lemma pd_below_finite (ν μ R c δ : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R)
    (hμ1 : -(1 / 4) < μ) (hδ0 : 0 < δ) (hδ1 : δ < Real.log (12 / 11)) (hg : Measurable g)
    (hgy : ∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) (τ₀ : ℝ) (y₀ : Space) (hϱ : 0 < ϱ y₀)
    (hage : ν * age R y₀ ≤ 1)
    (hfin : wardYKerMaj R c (Real.exp (-(δ / 2))) g τ₀ y₀ +
          wardYStreamMaj R c (Real.exp (-(δ / 2))) g τ₀ y₀ < ⊤) :
    ∫⁻ e : ℝ × Space, (if e.1 < τ₀ then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := pd_kernel_compare μ hμ1 y₀ hϱ
  set θ : ℝ := Real.exp (-(δ / 2)) with hθdef
  have hθ : Real.sqrt (5 / 6) < θ := pdTheta δ hδ1
  have hθ1 : θ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hsupp : ∀ σ z, ¬ (ϱ z < θ * ϱ y₀) → IIIa.srcNorm (oldPhys R c g) σ z = 0 := by
    intro σ z hz
    apply srcNorm_eq_zero_of
    apply pdSupport ν R c g hν hR hgy y₀ hϱ hage σ z
    push_neg at hz
    calc Real.sqrt (5 / 6) * ϱ y₀ < θ * ϱ y₀ := mul_lt_mul_of_pos_right hθ hϱ
      _ ≤ ϱ z := hz
  have hsm := measurable_srcNorm' R c g hg
  have hlam := measurable_pdLam_comp
  let K1 : ℝ × Space → ℝ≥0∞ := fun e => ENNReal.ofReal
    ((‖y₀ - pdLam (τ₀ - e.1) • e.2‖ ^ 4)⁻¹)
  let K2 : ℝ × Space → ℝ≥0∞ := fun e => ENNReal.ofReal
    ((ϱ y₀ ^ 2 * (ϱ y₀ ^ 2 + (y₀ 2 - pdLam (τ₀ - e.1) * e.2 2) ^ 2))⁻¹)
  have hK1 : Measurable K1 := by
    refine Measurable.ennreal_ofReal (Measurable.inv (Measurable.pow_const ?_ _))
    unfold pdLam; fun_prop
  have hK2 : Measurable K2 := by
    refine Measurable.ennreal_ofReal (Measurable.inv ?_)
    unfold pdLam; fun_prop
  let Φ1 : ℝ × Space → ℝ≥0∞ := fun e => ENNReal.ofReal C * (K1 e *
    IIIa.srcNorm (oldPhys R c g) e.1 e.2)
  let Φ2 : ℝ × Space → ℝ≥0∞ := fun e => ENNReal.ofReal C * (K2 e *
    IIIa.srcNorm (oldPhys R c g) e.1 e.2)
  have hΦ1 : Measurable Φ1 := measurable_const.mul (hK1.mul hsm)
  have hΦ2 : Measurable Φ2 := measurable_const.mul (hK2.mul hsm)
  have hind : Measurable (fun e : ℝ × Space =>
      if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
    exact Measurable.ennreal_ofReal (by unfold pdLam; fun_prop)
  -- pointwise
  have hpt : ∀ e : ℝ × Space,
      (if e.1 < τ₀ then ENNReal.ofReal (srcWeight μ (τ₀ - e.1) e.2) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2 ≤
      (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) * Φ1 e +
      (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) * Φ2 e := by
    intro e
    by_cases hlt : e.1 < τ₀
    · simp only [hlt, ↓reduceIte]
      by_cases hs : IIIa.srcNorm (oldPhys R c g) e.1 e.2 = 0
      · simp [hs]
      · have hz : ϱ e.2 < θ * ϱ y₀ := by
          by_contra hcon; exact hs (hsupp _ _ hcon)
        have hz' : ϱ e.2 < ϱ y₀ := lt_of_lt_of_le hz
          (by nlinarith [hϱ, hθ1])
        have hl0 : 0 < pdLam (τ₀ - e.1) := Real.exp_pos _
        have hl1 : pdLam (τ₀ - e.1) ≤ 1 := by
          unfold pdLam; rw [Real.exp_le_one_iff]; linarith
        have hcmp := hC _ hl0 hl1 e.2 hz'
        have hsw : srcWeight μ (τ₀ - e.1) e.2 = pdLam (τ₀ - e.1) ^ (2 * μ + 3) *
            (((1 + pdLam (τ₀ - e.1) * ‖e.2‖) ^ 4)⁻¹ + (1 + (pdLam (τ₀ - e.1) * e.2 2) ^ 2)⁻¹) := rfl
        rw [hsw]
        have h1 := ENNReal.ofReal_le_ofReal hcmp
        rw [ENNReal.ofReal_mul hl0.le, ENNReal.ofReal_mul hC0, ENNReal.ofReal_add
          (by positivity) (by positivity)] at h1
        calc _ ≤ (ENNReal.ofReal (pdLam (τ₀ - e.1)) * (ENNReal.ofReal C * (K1 e + K2 e))) *
              IIIa.srcNorm (oldPhys R c g) e.1 e.2 := mul_le_mul' h1 le_rfl
          _ = _ := by
            simp only [Φ1, Φ2]
            ring
    · simp [hlt]
  -- the two applications of the change of variables
  have hbase : ∀ (K : ℝ × Space → ℝ≥0∞) (hK : Measurable K),
      ∫⁻ e : ℝ × Space, (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) *
        (ENNReal.ofReal C * (K e * IIIa.srcNorm (oldPhys R c g) e.1 e.2)) =
      2 * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal C * ∫⁻ z : Space,
        K (τ₀ + 2 * Real.log l, z) * IIIa.srcNorm (oldPhys R c g) (τ₀ + 2 * Real.log l) z := by
    intro K hK
    refine (pdSigmaToLambda τ₀ (fun e => ENNReal.ofReal C * (K e *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2)) (measurable_const.mul (hK.mul hsm))).trans ?_
    congr 1
    refine lintegral_congr (fun l => ?_)
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  have hset : ∀ (f : Space → ℝ≥0∞) (σ : ℝ),
      ∫⁻ z : Space, f z * IIIa.srcNorm (oldPhys R c g) σ z =
        ∫⁻ z in {z : Space | ϱ z < θ * ϱ y₀}, f z * IIIa.srcNorm (oldPhys R c g) σ z := by
    intro f σ
    symm
    refine setLIntegral_eq_of_support_subset ?_
    intro z hz
    by_contra hzz
    exact hz (by simp [hsupp σ z hzz])
  have hI1 : ∫⁻ e : ℝ × Space, (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) *
      Φ1 e = 2 * (ENNReal.ofReal C * wardYKerMaj R c θ g τ₀ y₀) := by
    show ∫⁻ e : ℝ × Space, _ * (ENNReal.ofReal C * (K1 e * _)) = _
    rw [hbase K1 hK1, wardYKerMaj, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    congr 1
    rw [hset]
    refine setLIntegral_congr_fun ?_ (fun z _ => ?_)
    · exact measurableSet_lt (by unfold ϱ; fun_prop) measurable_const
    · simp only [K1, pd_lam_log τ₀ l hl.1]
  have hI2 : ∫⁻ e : ℝ × Space, (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) *
      Φ2 e = 2 * (ENNReal.ofReal C * wardYStreamMaj R c θ g τ₀ y₀) := by
    show ∫⁻ e : ℝ × Space, _ * (ENNReal.ofReal C * (K2 e * _)) = _
    rw [hbase K2 hK2, wardYStreamMaj, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    congr 1
    rw [hset]
    refine setLIntegral_congr_fun ?_ (fun z _ => ?_)
    · exact measurableSet_lt (by unfold ϱ; fun_prop) measurable_const
    · simp only [K2, pd_lam_log τ₀ l hl.1]
  have hm1 : Measurable (fun e : ℝ × Space => (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1))
      else 0) * Φ1 e) := hind.mul hΦ1
  calc _ ≤ ∫⁻ e : ℝ × Space, ((if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) * Φ1 e +
        (if e.1 < τ₀ then ENNReal.ofReal (pdLam (τ₀ - e.1)) else 0) * Φ2 e) :=
        lintegral_mono hpt
    _ = _ := lintegral_add_left hm1 _
    _ < ⊤ := by
        rw [hI1, hI2]
        have h1 := lt_of_le_of_lt le_self_add hfin
        have h2 := lt_of_le_of_lt le_add_self hfin
        refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩ <;>
          exact ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ‹_›)

/-- **Reduction of `PDSourceFinite` to the period shift.** -/
theorem pdSourceFinite_of (hshift : PDShiftBound) : PDSourceFinite := by
  intro ν μ R c δ g hν hR hc hμ1 hμ2 hδ0 hδ1 hg hgy τ₀ y₀ hϱ hage hfin ε hε
  have hbelow := pd_below_finite ν μ R c δ g hν hR hμ1 hδ0 hδ1 hg hgy τ₀ y₀ hϱ hage hfin
  obtain ⟨K, hK, hle⟩ := hshift μ R c g hR hc hμ1 hg τ₀ ε hε
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) hbelow)

end UnforcedLeray.Short.PartIIIb.Concrete

end
