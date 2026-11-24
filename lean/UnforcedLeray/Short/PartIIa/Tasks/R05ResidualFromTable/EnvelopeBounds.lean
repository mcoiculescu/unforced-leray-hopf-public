import UnforcedLeray.Short.PartIIa.Tasks.R05ResidualFromTable.ProfileDerivs

/-!
# Helper module `EnvelopeBounds` for `PartII-a:R05`

Defines the τ-independent similarity envelope `resEnvelope s η` and proves that `RingLateTable`
and `RingEarlyBound` (at `m = 1`) bound `‖ringResidual R ν ψ pr τ y‖` and
`‖fderiv ℝ (ringResidual R ν ψ pr τ) y (coordinateVector i)‖` off the axis by
`polyConst C d ν (ν ^ (-ρ)) * R⁻¹ * resEnvelope (Axi.age R y) (Axi.trans R y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.R05

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0188 UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

/-! ### 1. The similarity envelope `resEnvelope` -/

/-- The τ-independent similarity envelope on `(s, η)`:
`0` for `s ≤ 0`, `s^{3/2} (1 + η²)^{-1}` for `0 < s ≤ 1`, and `(1 + η²/s)^{-1}` for `s > 1`. -/
def resEnvelope (s η : ℝ) : ℝ :=
  if s ≤ 0 then 0
  else if s ≤ 1 then s ^ (3 / 2 : ℝ) * (1 + η ^ 2) ^ (-1 : ℝ)
  else (1 + η ^ 2 / s) ^ (-1 : ℝ)

theorem resEnvelope_nonneg (s η : ℝ) : 0 ≤ resEnvelope s η := by
  unfold resEnvelope
  split_ifs with hs0 hs1
  · exact le_rfl
  · have hs : 0 < s := not_le.mp hs0
    positivity
  · have hs : 0 < s := by linarith [not_le.mp hs0]
    positivity

theorem measurable_resEnvelope : Measurable (fun p : ℝ × ℝ => resEnvelope p.1 p.2) := by
  unfold resEnvelope
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

/-! ### 2. Elementary inequalities for `WtdBound`, `ExpBound`, and `polyConst` -/

theorem wtdBound_mono {m : ℕ} {X : ProfilePoint → ℝ} {a₁ a₂ B₁ B₂ : ℝ}
    (ha : a₁ ≤ a₂) (hB : B₁ ≤ B₂) (hB₂ : 0 ≤ B₂) (h : WtdBound m X a₂ B₁) :
    WtdBound m X a₁ B₂ := by
  intro x hx
  have hs0 : 0 < x.2.2 := by linarith
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x|
      ≤ B₁ * x.2.2 ^ (-a₂) := h x hx
    _ ≤ B₂ * x.2.2 ^ (-a₂) := by gcongr
    _ ≤ B₂ * x.2.2 ^ (-a₁) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg ha)) hB₂

theorem exp_neg_le_four_div_sq {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ 4 / t ^ 2 := by
  have h1 : t / 2 ≤ Real.exp (t / 2) := by
    linarith [Real.add_one_le_exp (t / 2)]
  have h2 : (t / 2) ^ 2 ≤ (Real.exp (t / 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : t ^ 2 / 4 ≤ Real.exp t := by
    calc t ^ 2 / 4 = (t / 2) ^ 2 := by ring
      _ ≤ (Real.exp (t / 2)) ^ 2 := h2
      _ = Real.exp (t / 2 + t / 2) := by rw [sq, ← Real.exp_add]
      _ = Real.exp t := by ring_nf
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos t) (pow_pos ht 2)]
  linarith

theorem c_sq_inv_nu_sq_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    (c ^ 2 / ν) ^ 2 ≤ (1 + c + ν⁻¹) ^ 6 := by
  have hc1 : c ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    linarith
  have hν1 : ν⁻¹ ≤ 1 + c + ν⁻¹ := by linarith
  have h3 : c ^ 2 / ν ≤ (1 + c + ν⁻¹) ^ 3 := by
    rw [div_eq_mul_inv]
    calc c ^ 2 * ν⁻¹ ≤ (1 + c + ν⁻¹) ^ 2 * (1 + c + ν⁻¹) := by gcongr
      _ = (1 + c + ν⁻¹) ^ 3 := by ring
  calc (c ^ 2 / ν) ^ 2 ≤ ((1 + c + ν⁻¹) ^ 3) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
    _ = (1 + c + ν⁻¹) ^ 6 := by ring

theorem wtdBound_of_expBound {κ ν c B : ℝ} (hκ : 0 < κ) (hν : 0 < ν) (hc : 0 < c)
    (hB : 0 ≤ B) {m : ℕ} {X : ProfilePoint → ℝ} (h : ExpBound κ ν c m X B) :
    WtdBound m X 2 (B * (4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6) := by
  intro x hx
  have hs : 0 < x.2.2 := by linarith
  have ht : 0 < κ * ν * x.2.2 / c ^ 2 := by positivity
  have hexp := exp_neg_le_four_div_sq ht
  have hcsq := c_sq_inv_nu_sq_le hν hc
  have halg : 4 / (κ * ν * x.2.2 / c ^ 2) ^ 2 =
      (4 / κ ^ 2) * (c ^ 2 / ν) ^ 2 * x.2.2 ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hs.le, Real.rpow_two]
    field_simp
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x|
      ≤ B * Real.exp (-(κ * ν * x.2.2 / c ^ 2)) := h x hx
    _ ≤ B * (4 / (κ * ν * x.2.2 / c ^ 2) ^ 2) := by gcongr
    _ = B * ((4 / κ ^ 2) * (c ^ 2 / ν) ^ 2 * x.2.2 ^ (-2 : ℝ)) := by rw [halg]
    _ ≤ B * ((4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6 * x.2.2 ^ (-2 : ℝ)) := by gcongr
    _ = B * (4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6 * x.2.2 ^ (-2 : ℝ) := by ring

/-! ### 3. Converting early + late bounds into `resEnvelope` bounds -/

/-- A profile `Y` satisfies `EnvValBound B Y` if `s^{3/2} |Y(q, η, s)| ≤ B * resEnvelope s η`
for all `s > 0`. -/
def EnvValBound (B : ℝ) (Y : ProfilePoint → ℝ) : Prop :=
  ∀ x : ProfilePoint, 0 < x.2.2 →
    x.2.2 ^ (3 / 2 : ℝ) * |Y x| ≤ B * resEnvelope x.2.2 x.2.1

/-- A profile `Y` satisfies `EnvDerivBound B Y` if `s^2 |Y(q, η, s)| ≤ B * resEnvelope s η`
for all `s > 0`. -/
def EnvDerivBound (B : ℝ) (Y : ProfilePoint → ℝ) : Prop :=
  ∀ x : ProfilePoint, 0 < x.2.2 →
    x.2.2 ^ 2 * |Y x| ≤ B * resEnvelope x.2.2 x.2.1

theorem envValBound_of_early_late {B : ℝ} {Y : ProfilePoint → ℝ}
    (hearly : ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |Y x| ≤ B)
    (hlate : WtdBound 1 Y (3 / 2) B) :
    EnvValBound B Y := by
  intro x hs
  unfold resEnvelope
  rw [if_neg (not_le.mpr hs)]
  split_ifs with hs1
  · have he := hearly x hs hs1
    rw [pow_one] at he
    have hηpos : 0 < 1 + x.2.1 ^ 2 := by positivity
    have hY : |Y x| ≤ B * (1 + x.2.1 ^ 2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀' hηpos]
      exact he
    calc x.2.2 ^ (3 / 2 : ℝ) * |Y x|
        ≤ x.2.2 ^ (3 / 2 : ℝ) * (B * (1 + x.2.1 ^ 2) ^ (-1 : ℝ)) := by gcongr
      _ = B * (x.2.2 ^ (3 / 2 : ℝ) * (1 + x.2.1 ^ 2) ^ (-1 : ℝ)) := by ring
  · have hs1' : 1 ≤ x.2.2 := by linarith
    have hl := hlate x hs1'
    rw [pow_one] at hl
    have hwpos : 0 < 1 + x.2.1 ^ 2 / x.2.2 := by positivity
    have hY : |Y x| ≤ B * x.2.2 ^ (-(3 / 2 : ℝ)) * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀' hwpos]
      exact hl
    have hcancel : x.2.2 ^ (3 / 2 : ℝ) * x.2.2 ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
    calc x.2.2 ^ (3 / 2 : ℝ) * |Y x|
        ≤ x.2.2 ^ (3 / 2 : ℝ) *
            (B * x.2.2 ^ (-(3 / 2 : ℝ)) * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ)) := by gcongr
      _ = B * (x.2.2 ^ (3 / 2 : ℝ) * x.2.2 ^ (-(3 / 2 : ℝ))) *
            (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by ring
      _ = B * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by rw [hcancel, mul_one]

theorem envDerivBound_of_early_late {B : ℝ} {Y : ProfilePoint → ℝ}
    (hearly : ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |Y x| ≤ B)
    (hlate : WtdBound 1 Y 2 B) :
    EnvDerivBound B Y := by
  intro x hs
  unfold resEnvelope
  rw [if_neg (not_le.mpr hs)]
  split_ifs with hs1
  · have he := hearly x hs hs1
    rw [pow_one] at he
    have hηpos : 0 < 1 + x.2.1 ^ 2 := by positivity
    have hY : |Y x| ≤ B * (1 + x.2.1 ^ 2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀' hηpos]
      exact he
    have hpow : x.2.2 ^ 2 ≤ x.2.2 ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
    calc x.2.2 ^ 2 * |Y x|
        ≤ x.2.2 ^ (3 / 2 : ℝ) * (B * (1 + x.2.1 ^ 2) ^ (-1 : ℝ)) := by gcongr
      _ = B * (x.2.2 ^ (3 / 2 : ℝ) * (1 + x.2.1 ^ 2) ^ (-1 : ℝ)) := by ring
  · have hs1' : 1 ≤ x.2.2 := by linarith
    have hl := hlate x hs1'
    rw [pow_one] at hl
    have hwpos : 0 < 1 + x.2.1 ^ 2 / x.2.2 := by positivity
    have hY : |Y x| ≤ B * x.2.2 ^ (-2 : ℝ) * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀' hwpos]
      exact hl
    have hcancel : x.2.2 ^ 2 * x.2.2 ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_two, ← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
    calc x.2.2 ^ 2 * |Y x|
        ≤ x.2.2 ^ 2 *
            (B * x.2.2 ^ (-2 : ℝ) * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ)) := by gcongr
      _ = B * (x.2.2 ^ 2 * x.2.2 ^ (-2 : ℝ)) *
            (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by ring
      _ = B * (1 + x.2.1 ^ 2 / x.2.2) ^ (-1 : ℝ) := by rw [hcancel, mul_one]

/-! ### 4. Bundled envelope bounds for a single coefficient `X` -/

structure CoeffEnvBounds (B : ℝ) (X : ProfilePoint → ℝ) : Prop where
  val : EnvValBound B X
  dQ : EnvDerivBound B (partialQ X)
  dEta : EnvDerivBound B (partialEta X)
  shift3 : EnvDerivBound B (ageShift 3 X)

structure RadCoeffEnvBounds (B : ℝ) (X : ProfilePoint → ℝ) : Prop extends CoeffEnvBounds B X where
  val2 : EnvDerivBound B X

theorem norm_radLift_le_env {R : ℝ} (hR : 0 < R) (τ : ℝ) {B : ℝ} {X : ProfilePoint → ℝ}
    (hX : CoeffEnvBounds B X) {y : Space} (hy : y ∉ Axi.axis) :
    ‖radLift R X τ y‖ ≤ B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
  calc ‖radLift R X τ y‖
      ≤ (Axi.age R y) ^ (3 / 2 : ℝ) * |X (chartPtR03 R τ y)| := norm_radLift_le R τ X hy
    _ ≤ B * resEnvelope (Axi.age R y) (Axi.trans R y) :=
        hX.val (chartPtR03 R τ y) (Axi.age_pos hR.ne' hy)

theorem norm_axLift_le_env {R : ℝ} (hR : 0 < R) (τ : ℝ) {B : ℝ} {X : ProfilePoint → ℝ}
    (hX : CoeffEnvBounds B X) {y : Space} (hy : y ∉ Axi.axis) :
    ‖axLift R X τ y‖ ≤ B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
  calc ‖axLift R X τ y‖
      ≤ (Axi.age R y) ^ (3 / 2 : ℝ) * |X (chartPtR03 R τ y)| := norm_axLift_le R τ X y
    _ ≤ B * resEnvelope (Axi.age R y) (Axi.trans R y) :=
        hX.val (chartPtR03 R τ y) (Axi.age_pos hR.ne' hy)

theorem norm_fderiv_radLift_le_env {R : ℝ} (hR : 2 ≤ R) (τ : ℝ) {B : ℝ}
    {X : ProfilePoint → ℝ} (hsm : ContDiffOn ℝ ∞ X ageDomain) (hX : RadCoeffEnvBounds B X)
    {y : Space} (hy : y ∉ Axi.axis) {v : Space} (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (radLift R X τ) y v‖ ≤ 5 * B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
  have hR0 : 0 < R := by linarith
  have hs : 0 < (chartPtR03 R τ y).2.2 := Axi.age_pos hR0.ne' hy
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have bQ : (Axi.age R y) ^ 2 * |partialQ X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.dQ (chartPtR03 R τ y) hs
  have bS : (Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.shift3 (chartPtR03 R τ y) hs
  have bE : (Axi.age R y) ^ 2 * |partialEta X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.dEta (chartPtR03 R τ y) hs
  have bV : (Axi.age R y) ^ 2 * |X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.val2 (chartPtR03 R τ y) hs
  have h1 := norm_fderiv_radLift_le hR0 τ hsm hy hv
  have h2 : (Axi.age R y) ^ 2 *
        (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)| + 2 * R⁻¹ * |X (chartPtR03 R τ y)|) ≤
      (Axi.age R y) ^ 2 * |partialQ X (chartPtR03 R τ y)| +
        1 * ((Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)|) +
        (Axi.age R y) ^ 2 * |partialEta X (chartPtR03 R τ y)| +
        2 * 1 * ((Axi.age R y) ^ 2 * |X (chartPtR03 R τ y)|) := by
    have hS0 : 0 ≤ (Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)| := by positivity
    have hV0 : 0 ≤ (Axi.age R y) ^ 2 * |X (chartPtR03 R τ y)| := by positivity
    nlinarith
  linarith

theorem norm_fderiv_axLift_le_env {R : ℝ} (hR : 2 ≤ R) (τ : ℝ) {B : ℝ}
    {X : ProfilePoint → ℝ} (hsm : ContDiffOn ℝ ∞ X ageDomain) (hX : CoeffEnvBounds B X)
    {y : Space} (hy : y ∉ Axi.axis) {v : Space} (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (axLift R X τ) y v‖ ≤ 3 * B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
  have hR0 : 0 < R := by linarith
  have hs : 0 < (chartPtR03 R τ y).2.2 := Axi.age_pos hR0.ne' hy
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have bQ : (Axi.age R y) ^ 2 * |partialQ X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.dQ (chartPtR03 R τ y) hs
  have bS : (Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.shift3 (chartPtR03 R τ y) hs
  have bE : (Axi.age R y) ^ 2 * |partialEta X (chartPtR03 R τ y)| ≤
      B * resEnvelope (Axi.age R y) (Axi.trans R y) := hX.dEta (chartPtR03 R τ y) hs
  have h1 := norm_fderiv_axLift_le hR0 τ hsm hy hv
  have h2 : (Axi.age R y) ^ 2 *
        (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)|) ≤
      (Axi.age R y) ^ 2 * |partialQ X (chartPtR03 R τ y)| +
        1 * ((Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)|) +
        (Axi.age R y) ^ 2 * |partialEta X (chartPtR03 R τ y)| := by
    have hS0 : 0 ≤ (Axi.age R y) ^ 2 * |ageShift 3 X (chartPtR03 R τ y)| := by positivity
    nlinarith
  linarith

/-! ### 5. Extracting `RadCoeffEnvBounds` and `CoeffEnvBounds` from `RingLateTable` + `RingEarlyBound` -/

theorem polyConst_le_of_le {C₁ C₂ : ℝ} {d₁ d₂ : ℕ} {ν c : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hC : C₁ ≤ C₂) (hC₂ : 0 ≤ C₂) (hd : d₁ ≤ d₂) :
    polyConst C₁ d₁ ν c ≤ polyConst C₂ d₂ ν c := by
  unfold polyConst
  have h1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    linarith
  calc C₁ * (1 + c + ν⁻¹) ^ d₁
      ≤ C₂ * (1 + c + ν⁻¹) ^ d₁ := by gcongr
    _ ≤ C₂ * (1 + c + ν⁻¹) ^ d₂ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hd) hC₂

theorem extract_all_coeff_bounds (hLate : RingLateTable) (hEarly : RingEarlyBound)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ pr →
        let B := polyConst C d ν (ν ^ (-ρ))
        RadCoeffEnvBounds B (coeffA₁ ν ψ pr) ∧
          RadCoeffEnvBounds B (coeffB₁ ν ψ) ∧
          CoeffEnvBounds B (coeffA₂ ν ψ) ∧
          CoeffEnvBounds B (coeffB₂ ν ψ) ∧
          CoeffEnvBounds B (coeffB₃ ν ψ) := by
  obtain ⟨ν₁, hν₁, C₁, d₁, κ, hκ, hL⟩ := hLate ρ 1 hρ
  obtain ⟨ν₂, hν₂, C₂, d₂, hE⟩ := hEarly ρ 1 hρ
  let C : ℝ := (max 0 C₁ + max 0 C₂ + 1) * (1 + 4 / κ ^ 2)
  let d : ℕ := d₁ + d₂ + 6
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, C, d, hC0, ?_⟩
  intro ν hν ψ pr htr
  have hνpos : 0 < ν := hν.1
  have hcpos : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hνpos _
  have hν1 : ν ∈ Ioo 0 ν₁ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioo 0 ν₂ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have hLν := hL ν hν1 ψ pr htr
  have hEν := hE ν hν2 ψ pr htr
  let c := ν ^ (-ρ)
  let B := polyConst C d ν c
  have hB0 : 0 ≤ B := by
    change 0 ≤ polyConst C d ν c
    unfold polyConst
    positivity
  have hC1_le : C₁ ≤ max 0 C₁ + max 0 C₂ + 1 := by
    linarith [le_max_right 0 C₁, le_max_left 0 C₂]
  have hC2_le : C₂ ≤ max 0 C₁ + max 0 C₂ + 1 := by
    linarith [le_max_left 0 C₁, le_max_right 0 C₂]
  have h1_le_fac : 1 ≤ 1 + 4 / κ ^ 2 := by
    have : 0 ≤ 4 / κ ^ 2 := by positivity
    linarith
  have hC1_C : C₁ ≤ C := by
    calc C₁ ≤ (max 0 C₁ + max 0 C₂ + 1) * 1 := by linarith
      _ ≤ (max 0 C₁ + max 0 C₂ + 1) * (1 + 4 / κ ^ 2) := by gcongr
  have hC2_C : C₂ ≤ C := by
    calc C₂ ≤ (max 0 C₁ + max 0 C₂ + 1) * 1 := by linarith
      _ ≤ (max 0 C₁ + max 0 C₂ + 1) * (1 + 4 / κ ^ 2) := by gcongr
  have hB1_le : polyConst C₁ d₁ ν c ≤ B :=
    polyConst_le_of_le hνpos hcpos hC1_C hC0 (by omega)
  have hB2_le : polyConst C₂ d₂ ν c ≤ B :=
    polyConst_le_of_le hνpos hcpos hC2_C hC0 (by omega)
  let B1p := polyConst (max 0 C₁) d₁ ν c
  have hB1p0 : 0 ≤ B1p := by
    change 0 ≤ polyConst (max 0 C₁) d₁ ν c
    unfold polyConst
    positivity
  have hB1_B1p : polyConst C₁ d₁ ν c ≤ B1p :=
    polyConst_le_of_le hνpos hcpos (le_max_right 0 C₁) (le_max_left 0 C₁) le_rfl
  have hexp_le : B1p * (4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6 ≤ B := by
    have heq : B1p * (4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6 =
        polyConst (max 0 C₁ * (4 / κ ^ 2)) (d₁ + 6) ν c := by
      change polyConst (max 0 C₁) d₁ ν c * (4 / κ ^ 2) * (1 + c + ν⁻¹) ^ 6 = _
      unfold polyConst
      ring
    rw [heq]
    refine polyConst_le_of_le hνpos hcpos ?_ hC0 (by omega)
    have h4 : 0 ≤ 4 / κ ^ 2 := by positivity
    have hm1 : max 0 C₁ ≤ max 0 C₁ + max 0 C₂ + 1 := by linarith [le_max_left 0 C₂]
    change max 0 C₁ * (4 / κ ^ 2) ≤ (max 0 C₁ + max 0 C₂ + 1) * (1 + 4 / κ ^ 2)
    nlinarith [le_max_left 0 C₁]
  have exp_to_wtd : ∀ {a : ℝ} {Y : ProfilePoint → ℝ}, a ≤ 2 →
      ExpBound κ ν c 1 Y (polyConst C₁ d₁ ν c) → WtdBound 1 Y a B := by
    intro a Y ha hexp
    have hexp' : ExpBound κ ν c 1 Y B1p := fun x hx =>
      (hexp x hx).trans (mul_le_mul_of_nonneg_right hB1_B1p (Real.exp_pos _).le)
    have hw2 := wtdBound_of_expBound hκ hνpos hcpos hB1p0 hexp'
    exact wtdBound_mono ha hexp_le hB0 hw2
  have early_of_mem : ∀ {X : ProfilePoint → ℝ},
      X ∈ ({coeffA₁ ν ψ pr, coeffA₂ ν ψ, coeffB₁ ν ψ, coeffB₂ ν ψ, coeffB₃ ν ψ} :
        Set (ProfilePoint → ℝ)) →
      (∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |X x| ≤ B) ∧
        (∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |partialEta X x| ≤ B) ∧
        (∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |partialQ X x| ≤ B) ∧
        (∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → (1 + x.2.1 ^ 2) ^ 1 * |ageShift 3 X x| ≤ B) := by
    intro X hX
    refine ⟨fun x hx0 hx1 => (hEν x hx0 hx1 X hX).1.trans hB2_le,
      fun x hx0 hx1 => (hEν x hx0 hx1 X hX).2.1.trans hB2_le,
      fun x hx0 hx1 => (hEν x hx0 hx1 X hX).2.2.1.trans hB2_le,
      fun x hx0 hx1 => (hEν x hx0 hx1 X hX).2.2.2.trans hB2_le⟩
  rcases hLν with ⟨⟨hA1_v, hA1_e, hA1_s, hA1_q⟩, ⟨hB1_v, hB1_e, hB1_s, hB1_q⟩,
    ⟨hB2_v, hB2_e, hB2_s, hB2_q⟩, ⟨hB3_v, hB3_e, hB3_s, hB3_q⟩,
    ⟨hA2_v, hA2_e, hA2_s, hA2_q⟩⟩
  obtain ⟨eA1_v, eA1_e, eA1_q, eA1_s⟩ := early_of_mem (Or.inl rfl)
  obtain ⟨eA2_v, eA2_e, eA2_q, eA2_s⟩ := early_of_mem (Or.inr (Or.inl rfl))
  obtain ⟨eB1_v, eB1_e, eB1_q, eB1_s⟩ := early_of_mem (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨eB2_v, eB2_e, eB2_q, eB2_s⟩ := early_of_mem (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨eB3_v, eB3_e, eB3_q, eB3_s⟩ := early_of_mem (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨envValBound_of_early_late eA1_v (wtdBound_mono (by norm_num) hB1_le hB0 hA1_v),
      envDerivBound_of_early_late eA1_q (exp_to_wtd le_rfl hA1_q),
      envDerivBound_of_early_late eA1_e (wtdBound_mono (by norm_num) hB1_le hB0 hA1_e),
      envDerivBound_of_early_late eA1_s (wtdBound_mono le_rfl hB1_le hB0 hA1_s)⟩,
      envDerivBound_of_early_late eA1_v (wtdBound_mono le_rfl hB1_le hB0 hA1_v)⟩
  · refine ⟨⟨envValBound_of_early_late eB1_v (wtdBound_mono (by norm_num) hB1_le hB0 hB1_v),
      envDerivBound_of_early_late eB1_q (exp_to_wtd le_rfl hB1_q),
      envDerivBound_of_early_late eB1_e (wtdBound_mono (by norm_num) hB1_le hB0 hB1_e),
      envDerivBound_of_early_late eB1_s (wtdBound_mono le_rfl hB1_le hB0 hB1_s)⟩,
      envDerivBound_of_early_late eB1_v (wtdBound_mono le_rfl hB1_le hB0 hB1_v)⟩
  · exact ⟨envValBound_of_early_late eA2_v (exp_to_wtd (by norm_num) hA2_v),
      envDerivBound_of_early_late eA2_q (exp_to_wtd le_rfl hA2_q),
      envDerivBound_of_early_late eA2_e (exp_to_wtd le_rfl hA2_e),
      envDerivBound_of_early_late eA2_s (exp_to_wtd le_rfl hA2_s)⟩
  · exact ⟨envValBound_of_early_late eB2_v (wtdBound_mono le_rfl hB1_le hB0 hB2_v),
      envDerivBound_of_early_late eB2_q (exp_to_wtd le_rfl hB2_q),
      envDerivBound_of_early_late eB2_e (wtdBound_mono le_rfl hB1_le hB0 hB2_e),
      envDerivBound_of_early_late eB2_s (wtdBound_mono (by norm_num) hB1_le hB0 hB2_s)⟩
  · exact ⟨envValBound_of_early_late eB3_v (wtdBound_mono le_rfl hB1_le hB0 hB3_v),
      envDerivBound_of_early_late eB3_q (exp_to_wtd le_rfl hB3_q),
      envDerivBound_of_early_late eB3_e (wtdBound_mono le_rfl hB1_le hB0 hB3_e),
      envDerivBound_of_early_late eB3_s (wtdBound_mono (by norm_num) hB1_le hB0 hB3_s)⟩

/-! ### 6. Pointwise envelope bounds for `ringResidual` and `fderiv (ringResidual)` -/

theorem norm_five_smul_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {u1 u2 u3 u4 u5 : Space} {E : ℝ}
    (h1 : ‖u1‖ ≤ E) (h2 : ‖u2‖ ≤ E) (h3 : ‖u3‖ ≤ E) (h4 : ‖u4‖ ≤ E) (h5 : ‖u5‖ ≤ E) :
    ‖ε • u1 + (ε ^ 2) • u2 + ε • u3 + (ε ^ 2) • u4 + (ε ^ 3) • u5‖ ≤ 5 * ε * E := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε := by nlinarith
  have t1 : ‖ε • u1‖ ≤ ε * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]; gcongr
  have t2 : ‖(ε ^ 2) • u2‖ ≤ ε * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hε2 h2 (norm_nonneg _) hε0
  have t3 : ‖ε • u3‖ ≤ ε * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]; gcongr
  have t4 : ‖(ε ^ 2) • u4‖ ≤ ε * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hε2 h4 (norm_nonneg _) hε0
  have t5 : ‖(ε ^ 3) • u5‖ ≤ ε * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hε3 h5 (norm_nonneg _) hε0
  have s12 := norm_add_le (ε • u1) ((ε ^ 2) • u2)
  have s123 := norm_add_le (ε • u1 + (ε ^ 2) • u2) (ε • u3)
  have s1234 := norm_add_le (ε • u1 + (ε ^ 2) • u2 + ε • u3) ((ε ^ 2) • u4)
  have s12345 := norm_add_le (ε • u1 + (ε ^ 2) • u2 + ε • u3 + (ε ^ 2) • u4) ((ε ^ 3) • u5)
  linarith

theorem ringResidual_pointwise_envelope_bounds
    {R ν c B : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr)
    (bA1 : RadCoeffEnvBounds B (coeffA₁ ν ψ pr))
    (bB1 : RadCoeffEnvBounds B (coeffB₁ ν ψ))
    (bA2 : CoeffEnvBounds B (coeffA₂ ν ψ))
    (bB2 : CoeffEnvBounds B (coeffB₂ ν ψ))
    (bB3 : CoeffEnvBounds B (coeffB₃ ν ψ))
    (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    ‖ringResidual R ν ψ pr τ y‖ ≤
        (25 * B * R⁻¹) * resEnvelope (Axi.age R y) (Axi.trans R y) ∧
      ∀ v : Space, ‖v‖ ≤ 1 →
        ‖fderiv ℝ (ringResidual R ν ψ pr τ) y v‖ ≤
          (25 * B * R⁻¹) * resEnvelope (Axi.age R y) (Axi.trans R y) := by
  have hR0 : 0 < R := by linarith
  have hε0 : 0 ≤ ringEps R := by unfold ringEps; positivity
  have hε1 : ringEps R ≤ 1 := by unfold ringEps; exact inv_le_one_of_one_le₀ (by linarith)
  have hEnv0 : 0 ≤ resEnvelope (Axi.age R y) (Axi.trans R y) := resEnvelope_nonneg _ _
  have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have hBE0 : 0 ≤ B * resEnvelope (Axi.age R y) (Axi.trans R y) := mul_nonneg hB hEnv0
  have hRBE0 : 0 ≤ R⁻¹ * (B * resEnvelope (Axi.age R y) (Axi.trans R y)) := mul_nonneg hRinv0 hBE0
  constructor
  · rw [ringResidual_eq_resFiveTerms hR hν hc htr τ hy]
    unfold resFiveTerms
    have n1 := norm_radLift_le_env hR0 τ bA1.toCoeffEnvBounds hy
    have n2 := norm_radLift_le_env hR0 τ bB1.toCoeffEnvBounds hy
    have n3 := norm_axLift_le_env hR0 τ bA2 hy
    have n4 := norm_axLift_le_env hR0 τ bB2 hy
    have n5 := norm_axLift_le_env hR0 τ bB3 hy
    have hsum := norm_five_smul_le hε0 hε1 n1 n2 n3 n4 n5
    have hle : 5 * ringEps R * (B * resEnvelope (Axi.age R y) (Axi.trans R y)) ≤
        (25 * B * R⁻¹) * resEnvelope (Axi.age R y) (Axi.trans R y) := by
      unfold ringEps
      linarith
    exact hsum.trans hle
  · intro v hv
    rw [fderiv_ringResidual_eq_resFiveTerms hR hν hc htr τ hy v]
    obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
    have d1 := norm_fderiv_radLift_le_env hR τ (contDiffOn_coeffA1 ν hψ hpr) bA1 hy hv
    have d2 := norm_fderiv_radLift_le_env hR τ (contDiffOn_coeffB1 ν hψ) bB1 hy hv
    have d3 : ‖fderiv ℝ (axLift R (coeffA₂ ν ψ) τ) y v‖ ≤
        5 * B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
      linarith [norm_fderiv_axLift_le_env hR τ (contDiffOn_coeffA2 ν hψ) bA2 hy hv, hBE0]
    have d4 : ‖fderiv ℝ (axLift R (coeffB₂ ν ψ) τ) y v‖ ≤
        5 * B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
      linarith [norm_fderiv_axLift_le_env hR τ (contDiffOn_coeffB2 ν hψ) bB2 hy hv, hBE0]
    have d5 : ‖fderiv ℝ (axLift R (coeffB₃ ν ψ) τ) y v‖ ≤
        5 * B * resEnvelope (Axi.age R y) (Axi.trans R y) := by
      linarith [norm_fderiv_axLift_le_env hR τ (contDiffOn_coeffB3 ν hψ) bB3 hy hv, hBE0]
    have hsum := norm_five_smul_le hε0 hε1 d1 d2 d3 d4 d5
    have hle : 5 * ringEps R * (5 * B * resEnvelope (Axi.age R y) (Axi.trans R y)) =
        (25 * B * R⁻¹) * resEnvelope (Axi.age R y) (Axi.trans R y) := by
      unfold ringEps
      ring
    exact hsum.trans_eq hle

end UnforcedLeray.Short.PartIIa.R05
