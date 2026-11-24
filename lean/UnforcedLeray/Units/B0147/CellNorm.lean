import UnforcedLeray.Units.B0147.Bilinear

/-!
# B0147 helper: `L²` norms over one cell of the cylinder

Blueprint unit **B0147** (`eq:st18-t00145`, `paper/main.tex` lines 2217–2234), helper file.

Norms over one cell are unit B0151's `eLpNorm · 2 (cellMeasure c)`, Lebesgue measure on
`(0, c] × ℝ` (tex lines 2109–2110). The cell estimates of tex lines 2231–2233 ("modulo one cell
its midpoint lattice has two possible translates; its `L²` norm contributes `C√a`") are proved
here from pointwise product bounds `F² ≤ φ(q) ψ(η)` and the Gaussian integral
`∫ e^{-b t²} dt = √(π/b)` (Mathlib's `integral_gaussian`):

* `eLpNorm_lattice_cell`: a field bounded on the cell by `λ³` times a transverse Gaussian of
  width `λ⁻¹ = √a` times the two nearest Gaussians plus the exponentially small remainder has
  cell `L²` norm `≤ λ² M`, i.e. `≤ M a⁻¹`;
* `eLpNorm_bs_cell`: a field bounded by `λⁿ C e^{-γ(λc)²} e^{-γ(λη)²}` has cell `L²` norm
  `≤ λⁿ λ⁻¹ M e^{-γ(λc)²/2}`, i.e. `≤ M a^{-(n-1)/2} e^{-(γ/2)c²/a}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0151 (cellMeasure cellMeasure_eq_prod)

/-- An `L²` bound from a bound on the integral of the square. -/
theorem eLpNorm_two_le_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (h : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm F 2 μ ≤ ENNReal.ofReal B := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have e : ∀ x, ‖F x‖ₑ ^ (ENNReal.toReal 2) = ENNReal.ofReal (F x ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
  simp_rw [e]
  calc (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ) ^ (1 / ENNReal.toReal 2)
      ≤ (ENNReal.ofReal (B ^ 2)) ^ (1 / ENNReal.toReal 2) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal B := by
        rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hB]

/-- Product bound over one cell: `∫_{cell} F² ≤ (∫₀ᶜ φ)(∫_ℝ ψ)` when `F(z)² ≤ φ(q) ψ(η)`. -/
theorem lintegral_cell_le {c : ℝ} {F : Plane → ℝ} {φ ψ : ℝ → ℝ} (hφ : Measurable φ)
    (hψ : Measurable ψ) (hφ0 : ∀ t, 0 ≤ φ t)
    (h : ∀ z : Plane, z.1 ∈ Ioc 0 c → F z ^ 2 ≤ φ z.1 * ψ z.2) :
    ∫⁻ z, ENNReal.ofReal (F z ^ 2) ∂(cellMeasure c) ≤
      (∫⁻ t in Ioc 0 c, ENNReal.ofReal (φ t)) * ∫⁻ t, ENNReal.ofReal (ψ t) := by
  calc ∫⁻ z, ENNReal.ofReal (F z ^ 2) ∂(cellMeasure c)
      ≤ ∫⁻ z, ENNReal.ofReal (φ z.1) * ENNReal.ofReal (ψ z.2) ∂(cellMeasure c) := by
        apply lintegral_mono_ae
        rw [cellMeasure, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)]
        refine Eventually.of_forall fun z hz => ?_
        rw [← ENNReal.ofReal_mul (hφ0 _)]
        exact ENNReal.ofReal_le_ofReal (h z hz.1)
    _ = (∫⁻ t in Ioc 0 c, ENNReal.ofReal (φ t)) * ∫⁻ t, ENNReal.ofReal (ψ t) := by
        rw [cellMeasure_eq_prod]
        exact lintegral_prod_mul hφ.ennreal_ofReal.aemeasurable hψ.ennreal_ofReal.aemeasurable

/-- `∫ A e^{-b(t-x₀)²} dt = A √(π/b)`. -/
theorem lintegral_gauss {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (x₀ : ℝ) :
    ∫⁻ t, ENNReal.ofReal (A * Real.exp (-(b * (t - x₀) ^ 2))) =
      ENNReal.ofReal (A * Real.sqrt (Real.pi / b)) := by
  have hs := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => ENNReal.ofReal (A * Real.exp (-(b * t ^ 2)))) x₀
  rw [hs]
  have hI : Integrable (fun t : ℝ => A * Real.exp (-(b * t ^ 2))) := by
    have := (integrable_exp_neg_mul_sq hb).const_mul A
    simpa only [neg_mul] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun t => by positivity)]
  congr 1
  rw [integral_const_mul]
  have := integral_gaussian b
  simp only [neg_mul] at this
  rw [this]

theorem setLIntegral_gauss_le {A b c : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (x₀ : ℝ) :
    ∫⁻ t in Ioc 0 c, ENNReal.ofReal (A * Real.exp (-(b * (t - x₀) ^ 2))) ≤
      ENNReal.ofReal (A * Real.sqrt (Real.pi / b)) :=
  (setLIntegral_le_lintegral _ _).trans (lintegral_gauss hA hb x₀).le

theorem setLIntegral_const_Ioc {d c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ _ in Ioc 0 c, ENNReal.ofReal d = ENNReal.ofReal (d * c) := by
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  by_cases hd : 0 ≤ d
  · rw [ENNReal.ofReal_mul hd]
  · push_neg at hd
    rw [ENNReal.ofReal_of_nonpos hd.le, zero_mul,
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hd.le hc)]

/-- `L e^{-βL²} ≤ β⁻¹` for `L ≥ 1`. -/
theorem mul_exp_neg_le {β L : ℝ} (hβ : 0 < β) (hL : 1 ≤ L) :
    L * Real.exp (-(β * L ^ 2)) ≤ β⁻¹ := by
  have h1 : β * L ≤ Real.exp (β * L ^ 2) := by
    have := Real.add_one_le_exp (β * L ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left (show L ≤ L ^ 2 by nlinarith) hβ.le]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  rw [inv_mul_eq_div, le_div_iff₀ hβ]
  linarith

theorem exp_sq' (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem sqrt_scale {p l : ℝ} (hp : 0 ≤ p) (hl : 0 < l) :
    Real.sqrt (p / l ^ 2) = Real.sqrt p / l := by
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hl.le]

/-! ### The two cell estimates -/

/-- Cell `L²` bound for a periodized Gaussian profile at width `λ⁻² = a` (the estimate
`‖V_c‖₂ ≤ C a^{-1}` of tex line 2221). -/
theorem eLpNorm_lattice_cell {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam c : ℝ) (F : Plane → ℝ), 0 < lam → 0 < c → 1 ≤ lam * c →
      (∀ z : Plane, z.1 ∈ Ioc 0 c → |F z| ≤ lam ^ 3 * (K * Real.exp (-(β * (lam * z.2) ^ 2)) *
        (Real.exp (-(β * (lam * z.1) ^ 2)) + Real.exp (-(β * (lam * z.1 - lam * c) ^ 2)) +
          Real.exp (-(β * (lam * c) ^ 2 / 2)) * theta (β / 8)))) →
      eLpNorm F 2 (cellMeasure c) ≤ ENNReal.ofReal (lam ^ 2 * M) := by
  set θ := theta (β / 8)
  have hθ : 0 ≤ θ := theta_nonneg _
  set P := Real.sqrt (Real.pi / (2 * β))
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  set M0 := 3 * K ^ 2 * (2 * (Real.pi / (2 * β)) + θ ^ 2 * P * β⁻¹)
  have hM0 : 0 ≤ M0 := by positivity
  refine ⟨M0 + 1, by positivity, fun lam c F hl hc hL hF => ?_⟩
  set b := 2 * β * lam ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set A := 3 * lam ^ 6 * K ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set d := (Real.exp (-(β * (lam * c) ^ 2 / 2)) * θ) ^ 2 with hd
  have hd0 : 0 ≤ d := sq_nonneg _
  set φ : ℝ → ℝ := fun t => A * Real.exp (-(b * (t - 0) ^ 2)) +
    A * Real.exp (-(b * (t - c) ^ 2)) + A * d with hφ
  set ψ : ℝ → ℝ := fun t => 1 * Real.exp (-(b * (t - 0) ^ 2)) with hψ
  have hpt : ∀ z : Plane, z.1 ∈ Ioc 0 c → F z ^ 2 ≤ φ z.1 * ψ z.2 := by
    intro z hz
    have h := hF z hz
    set e2 := Real.exp (-(β * (lam * z.2) ^ 2))
    set p := Real.exp (-(β * (lam * z.1) ^ 2))
    set q := Real.exp (-(β * (lam * z.1 - lam * c) ^ 2))
    set r := Real.exp (-(β * (lam * c) ^ 2 / 2)) * θ
    have he2 : e2 ^ 2 = Real.exp (-(b * (z.2 - 0) ^ 2)) := by
      rw [exp_sq']; congr 1; rw [hb]; ring
    have hp : p ^ 2 = Real.exp (-(b * (z.1 - 0) ^ 2)) := by
      rw [exp_sq']; congr 1; rw [hb]; ring
    have hq : q ^ 2 = Real.exp (-(b * (z.1 - c) ^ 2)) := by
      rw [exp_sq']; congr 1; rw [hb]; ring
    have hp0 : 0 ≤ p := (Real.exp_pos _).le
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hr0 : 0 ≤ r := by positivity
    have he0 : 0 ≤ e2 := (Real.exp_pos _).le
    have hR : 0 ≤ lam ^ 3 * (K * e2 * (p + q + r)) := by positivity
    have h1 : F z ^ 2 ≤ (lam ^ 3 * (K * e2 * (p + q + r))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]
    have h3 : (lam ^ 3 * (K * e2 * (p + q + r))) ^ 2 =
        lam ^ 6 * K ^ 2 * e2 ^ 2 * (p + q + r) ^ 2 := by ring
    have h4 : φ z.1 * ψ z.2 = 3 * lam ^ 6 * K ^ 2 * e2 ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2) := by
      simp only [hφ, hψ, hA, hd]
      rw [← he2, ← hp, ← hq]
      ring
    rw [h4]
    calc F z ^ 2 ≤ lam ^ 6 * K ^ 2 * e2 ^ 2 * (p + q + r) ^ 2 := h3 ▸ h1
      _ ≤ lam ^ 6 * K ^ 2 * e2 ^ 2 * (3 * (p ^ 2 + q ^ 2 + r ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * lam ^ 6 * K ^ 2 * e2 ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2) := by ring
  have hφm : Measurable φ := by simp only [hφ]; fun_prop
  have hψm : Measurable ψ := by simp only [hψ]; fun_prop
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => by simp only [hφ]; positivity
  have hmain := lintegral_cell_le hφm hψm hφ0 hpt
  have hI1 : ∫⁻ t in Ioc 0 c, ENNReal.ofReal (φ t) ≤
      ENNReal.ofReal (A * Real.sqrt (Real.pi / b) + A * Real.sqrt (Real.pi / b) + A * d * c) := by
    have e : ∀ t, ENNReal.ofReal (φ t) = ENNReal.ofReal (A * Real.exp (-(b * (t - 0) ^ 2))) +
        ENNReal.ofReal (A * Real.exp (-(b * (t - c) ^ 2))) + ENNReal.ofReal (A * d) := by
      intro t
      simp only [hφ]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    simp_rw [e]
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
      setLIntegral_const_Ioc hc.le]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    · exact setLIntegral_gauss_le hA0 hb0 0
    · exact setLIntegral_gauss_le hA0 hb0 c
  have hI2 : ∫⁻ t, ENNReal.ofReal (ψ t) = ENNReal.ofReal (1 * Real.sqrt (Real.pi / b)) :=
    lintegral_gauss zero_le_one hb0 0
  have hG : Real.sqrt (Real.pi / b) = P / lam := by
    rw [hb, show Real.pi / (2 * β * lam ^ 2) = Real.pi / (2 * β) / lam ^ 2 by
      field_simp]
    exact sqrt_scale (by positivity) hl
  apply eLpNorm_two_le_of_sq (by positivity)
  refine hmain.trans ?_
  rw [hI2]
  refine (mul_le_mul_of_nonneg_right hI1 zero_le).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hG]
  -- real inequality
  have hPsq : P ^ 2 = Real.pi / (2 * β) := Real.sq_sqrt (by positivity)
  have hLe := mul_exp_neg_le hβ hL
  have hd' : d * c = θ ^ 2 * ((lam * c) * Real.exp (-(β * (lam * c) ^ 2))) / lam := by
    rw [hd, mul_pow, exp_sq']
    field_simp
  have hdc : d * c ≤ θ ^ 2 * β⁻¹ / lam := by
    rw [hd']
    apply div_le_div_of_nonneg_right _ hl.le
    exact mul_le_mul_of_nonneg_left hLe (sq_nonneg _)
  have key : (A * (P / lam) + A * (P / lam) + A * d * c) * (1 * (P / lam)) ≤
      lam ^ 4 * M0 := by
    have e1 : (A * (P / lam) + A * (P / lam) + A * d * c) * (1 * (P / lam)) =
        3 * lam ^ 4 * K ^ 2 * (2 * P ^ 2) + 3 * lam ^ 5 * K ^ 2 * (d * c) * P := by
      rw [hA]; field_simp; ring
    rw [e1, hPsq]
    have : 3 * lam ^ 5 * K ^ 2 * (d * c) * P ≤ 3 * lam ^ 5 * K ^ 2 * (θ ^ 2 * β⁻¹ / lam) * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdc (by positivity)) hP
    have e2 : 3 * lam ^ 5 * K ^ 2 * (θ ^ 2 * β⁻¹ / lam) * P =
        lam ^ 4 * (3 * K ^ 2 * (θ ^ 2 * P * β⁻¹)) := by field_simp
    rw [e2] at this
    have e3 : lam ^ 4 * M0 = 3 * lam ^ 4 * K ^ 2 * (2 * (Real.pi / (2 * β))) +
        lam ^ 4 * (3 * K ^ 2 * (θ ^ 2 * P * β⁻¹)) := by ring
    rw [e3]
    linarith
  have hfin : lam ^ 4 * M0 ≤ (lam ^ 2 * (M0 + 1)) ^ 2 := by
    have : M0 ≤ (M0 + 1) ^ 2 := by nlinarith
    calc lam ^ 4 * M0 ≤ lam ^ 4 * (M0 + 1) ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (lam ^ 2 * (M0 + 1)) ^ 2 := by ring
  exact key.trans hfin

/-- Cell `L²` bound for a field with an exponentially small factor (the estimate
`‖D^jQ_c‖₂ ≤ C_j a^{-(5+j)/2} e^{-b_jc²/a}` of tex line 2221). -/
theorem eLpNorm_bs_cell {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (lam c : ℝ) (n : ℕ) (F : Plane → ℝ), 0 < lam → 0 < c → 1 ≤ lam * c →
      (∀ z : Plane, z.1 ∈ Ioc 0 c → |F z| ≤ lam ^ n * (C * Real.exp (-(γ * (lam * c) ^ 2)) *
        Real.exp (-(γ * (lam * z.2) ^ 2)))) →
      eLpNorm F 2 (cellMeasure c) ≤
        ENNReal.ofReal (lam ^ n * lam⁻¹ * M * Real.exp (-(γ / 2 * (lam * c) ^ 2))) := by
  set P := Real.sqrt (Real.pi / (2 * γ))
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  set M0 := C ^ 2 * P * γ⁻¹
  have hM0 : 0 ≤ M0 := by positivity
  refine ⟨M0 + 1, by positivity, fun lam c n F hl hc hL hF => ?_⟩
  set b := 2 * γ * lam ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set E := Real.exp (-(γ * (lam * c) ^ 2)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set A := lam ^ (2 * n) * C ^ 2 * E ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set φ : ℝ → ℝ := fun _ => A with hφ
  set ψ : ℝ → ℝ := fun t => 1 * Real.exp (-(b * (t - 0) ^ 2)) with hψ
  have hpt : ∀ z : Plane, z.1 ∈ Ioc 0 c → F z ^ 2 ≤ φ z.1 * ψ z.2 := by
    intro z hz
    have h := hF z hz
    have hR : 0 ≤ lam ^ n * (C * E * Real.exp (-(γ * (lam * z.2) ^ 2))) := by positivity
    have h1 : F z ^ 2 ≤ (lam ^ n * (C * E * Real.exp (-(γ * (lam * z.2) ^ 2)))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine h1.trans (le_of_eq ?_)
    simp only [hφ, hψ, hA]
    have : Real.exp (-(γ * (lam * z.2) ^ 2)) ^ 2 = Real.exp (-(b * (z.2 - 0) ^ 2)) := by
      rw [exp_sq']; congr 1; rw [hb]; ring
    rw [mul_pow, mul_pow, mul_pow, this, ← pow_mul]
    ring
  have hmain := lintegral_cell_le (φ := φ) (ψ := ψ) measurable_const
    (by simp only [hψ]; fun_prop) (fun _ => hA0) hpt
  have hI1 : ∫⁻ t in Ioc 0 c, ENNReal.ofReal (φ t) = ENNReal.ofReal (A * c) :=
    setLIntegral_const_Ioc hc.le
  have hI2 : ∫⁻ t, ENNReal.ofReal (ψ t) = ENNReal.ofReal (1 * Real.sqrt (Real.pi / b)) :=
    lintegral_gauss zero_le_one hb0 0
  have hG : Real.sqrt (Real.pi / b) = P / lam := by
    rw [hb, show Real.pi / (2 * γ * lam ^ 2) = Real.pi / (2 * γ) / lam ^ 2 by field_simp]
    exact sqrt_scale (by positivity) hl
  apply eLpNorm_two_le_of_sq (by positivity)
  refine hmain.trans ?_
  rw [hI1, hI2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hG]
  have hLe := mul_exp_neg_le hγ hL
  have hE2 : Real.exp (-(γ / 2 * (lam * c) ^ 2)) ^ 2 = E := by
    rw [exp_sq', hE]; congr 1; ring
  have e1 : A * c * (1 * (P / lam)) =
      (lam ^ n * lam⁻¹) ^ 2 * (C ^ 2 * P) * ((lam * c) * E) * E := by
    rw [hA]; field_simp; ring
  rw [e1]
  have h2 : (lam ^ n * lam⁻¹) ^ 2 * (C ^ 2 * P) * ((lam * c) * E) * E ≤
      (lam ^ n * lam⁻¹) ^ 2 * (C ^ 2 * P) * γ⁻¹ * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLe (by positivity)) hE0.le
  refine h2.trans ?_
  have : M0 ≤ (M0 + 1) ^ 2 := by nlinarith
  calc (lam ^ n * lam⁻¹) ^ 2 * (C ^ 2 * P) * γ⁻¹ * E
      = (lam ^ n * lam⁻¹) ^ 2 * M0 * E := by ring
    _ ≤ (lam ^ n * lam⁻¹) ^ 2 * (M0 + 1) ^ 2 * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) hE0.le
    _ = (lam ^ n * lam⁻¹ * (M0 + 1) * Real.exp (-(γ / 2 * (lam * c) ^ 2))) ^ 2 := by
        rw [show (lam ^ n * lam⁻¹ * (M0 + 1) * Real.exp (-(γ / 2 * (lam * c) ^ 2))) ^ 2 =
          (lam ^ n * lam⁻¹ * (M0 + 1)) ^ 2 * Real.exp (-(γ / 2 * (lam * c) ^ 2)) ^ 2 by ring,
          hE2]
        ring

end UnforcedLeray.B0147
