import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.WtCore

/-!
# `PartIII-a:T21/2/2/2/2/1/1`: the weight bound `WtPhysBound`

With `a = a(r) = 1 + νr` and `P(x) = x₂² + (c/π)² sin²(π x₁/c)`, the base of `periodicWeight` is
`1 + P/a` (`cellLen c a = c/√a`), so `wt(r, x) = a⁻³ (1 + P/a)^{-m}`. Its `r`-derivative is
`ν · a⁻³ (1 + P/a)^{-m} · E` with `|E| ≤ (3 + |m|)/a`, and the weight ratio over `a' ∈ [a/2, 2a]`
is bounded uniformly in `x`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The offset `P(x) = x₂² + (c/π)² sin²(π x₁/c)`; the base of the weight is `1 + P/a`. -/
def wbP (c : ℝ) (x : ℝ × ℝ) : ℝ :=
  x.2 ^ 2 + (c / Real.pi) ^ 2 * Real.sin (Real.pi * x.1 / c) ^ 2

theorem wbP_nonneg (c : ℝ) (x : ℝ × ℝ) : 0 ≤ wbP c x := by
  unfold wbP; positivity

/-- The one-variable weight `a ↦ a⁻³ (1 + P/a)^{-m}`. -/
def wbW (m P a : ℝ) : ℝ := (a ^ 3)⁻¹ * (1 + P / a) ^ (-m)

theorem wbW_nonneg (m P a : ℝ) (hP : 0 ≤ P) (ha : 0 < a) : 0 ≤ wbW m P a := by
  unfold wbW
  have : 0 < 1 + P / a := by positivity
  positivity

theorem wtPhys_eq_wbW (ν c m r : ℝ) (x : ℝ × ℝ) (hc : 0 < c) (ha : 0 < clockA ν r) :
    wtPhys ν c m r x = wbW m (wbP c x) (clockA ν r) := by
  unfold wtPhys wbW
  rw [← wtF0_eq_periodicWeight c m (clockA ν r) hc ha x, wtF0_eq_base]
  have hb : wtBase c (clockA ν r) x = 1 + wbP c x / clockA ν r := by
    unfold wtBase wbP; ring
  rw [hb]

/-- The derivative of `a ↦ wbW m P a`, and its size bound. -/
theorem wbW_hasDeriv (m P a : ℝ) (ha : 0 < a) (hP : 0 ≤ P) :
    ∃ D : ℝ, HasDerivAt (fun b => wbW m P b) D a ∧
      |D| ≤ (3 + |m|) / a * wbW m P a := by
  have hB : 0 < 1 + P / a := by positivity
  have h1 : HasDerivAt (fun b : ℝ => P / b) (-(P / a ^ 2)) a := by
    have := (hasDerivAt_const a P).div (hasDerivAt_id' a) ha.ne'
    exact this.congr_deriv (by ring)
  have hBd : HasDerivAt (fun b : ℝ => 1 + P / b) (-(P / a ^ 2)) a := by
    have := (hasDerivAt_const a (1 : ℝ)).add h1
    exact this.congr_deriv (by ring)
  have hpow : HasDerivAt (fun b : ℝ => (1 + P / b) ^ (-m))
      ((-(P / a ^ 2)) * (-m) * (1 + P / a) ^ (-m - 1)) a :=
    hBd.rpow_const (Or.inl hB.ne')
  have hinv : HasDerivAt (fun b : ℝ => (b ^ 3)⁻¹)
      (-((3 : ℕ) * a ^ (3 - 1)) / (a ^ 3) ^ 2) a :=
    (hasDerivAt_pow 3 a).inv (pow_ne_zero 3 ha.ne')
  have hW := hinv.mul hpow
  have ht0 : 0 < (1 + P / a) ^ (-m) := by positivity
  have hsub : (1 + P / a) ^ (-m - 1) = (1 + P / a) ^ (-m) / (1 + P / a) :=
    Real.rpow_sub_one hB.ne' (-m)
  have hap : 0 < a + P := by linarith
  have hq : (P / a ^ 2) / (1 + P / a) = P / (a * (a + P)) := by
    field_simp
  have hq2 : P / (a * (a + P)) ≤ 1 / a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hk1 : (P / a ^ 2) / (1 + P / a) ≤ 1 / a := by rw [hq]; exact hq2
  have hk0 : 0 ≤ (P / a ^ 2) / (1 + P / a) := by positivity
  refine ⟨(a ^ 3)⁻¹ * (1 + P / a) ^ (-m) * (-3 / a + m * ((P / a ^ 2) / (1 + P / a))), ?_, ?_⟩
  · refine hW.congr_deriv ?_
    rw [hsub]
    field_simp
    ring
  · have hE : |-3 / a + m * ((P / a ^ 2) / (1 + P / a))| ≤ (3 + |m|) / a := by
      calc |-3 / a + m * ((P / a ^ 2) / (1 + P / a))|
          ≤ |-3 / a| + |m * ((P / a ^ 2) / (1 + P / a))| := abs_add_le _ _
        _ = 3 / a + |m| * ((P / a ^ 2) / (1 + P / a)) := by
            rw [abs_mul, abs_of_nonneg hk0, abs_div, abs_neg,
              abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos ha]
        _ ≤ 3 / a + |m| * (1 / a) := by
            gcongr
        _ = (3 + |m|) / a := by ring
    have hpos : (0 : ℝ) ≤ (a ^ 3)⁻¹ * (1 + P / a) ^ (-m) := by positivity
    rw [abs_mul, abs_of_nonneg hpos]
    unfold wbW
    calc (a ^ 3)⁻¹ * (1 + P / a) ^ (-m) *
          |-3 / a + m * ((P / a ^ 2) / (1 + P / a))|
        ≤ (a ^ 3)⁻¹ * (1 + P / a) ^ (-m) * ((3 + |m|) / a) :=
          mul_le_mul_of_nonneg_left hE hpos
      _ = (3 + |m|) / a * ((a ^ 3)⁻¹ * (1 + P / a) ^ (-m)) := by ring

/-- `ρ^{-m} ≤ 4^{|m|}` for `ρ ∈ [1/4, 4]`. -/
theorem rpow_neg_m_le (m ρ : ℝ) (h0 : 1 / 4 ≤ ρ) (h1 : ρ ≤ 4) : ρ ^ (-m) ≤ 4 ^ |m| := by
  have hρ : 0 < ρ := by linarith
  have h4 : (1 : ℝ) ≤ 4 := by norm_num
  rcases le_total 0 m with hm | hm
  · have hz : -m ≤ 0 := by linarith
    calc ρ ^ (-m) ≤ (1 / 4 : ℝ) ^ (-m) := Real.rpow_le_rpow_of_nonpos (by norm_num) h0 hz
      _ = 4 ^ m := by
          rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), inv_inv]
      _ ≤ 4 ^ |m| := Real.rpow_le_rpow_of_exponent_le h4 (le_abs_self m)
  · have hz : 0 ≤ -m := by linarith
    calc ρ ^ (-m) ≤ 4 ^ (-m) := Real.rpow_le_rpow hρ.le h1 hz
      _ ≤ 4 ^ |m| := Real.rpow_le_rpow_of_exponent_le h4 (neg_le_abs m)

/-- The weight ratio over `a' ∈ [a/2, 2a]`, uniform in `P ≥ 0`. -/
theorem wbW_ratio_le (m P a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (hP : 0 ≤ P)
    (h1 : a / 2 ≤ a') (h2 : a' ≤ 2 * a) :
    wbW m P a' ≤ 8 * 4 ^ |m| * wbW m P a := by
  have hB : 0 < 1 + P / a := by positivity
  have hB' : 0 < 1 + P / a' := by positivity
  have hu : P / a * a = P := div_mul_cancel₀ P ha.ne'
  have hv : P / a' * a' = P := div_mul_cancel₀ P ha'.ne'
  have hu0 : 0 ≤ P / a := by positivity
  have hv0 : 0 ≤ P / a' := by positivity
  have hv2 : P / a' ≤ 2 * (P / a) := by
    nlinarith [mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 2 * a' - a)]
  have hu2 : P / a ≤ 2 * (P / a') := by
    nlinarith [mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 2 * a - a')]
  have hρ1 : 1 / 4 ≤ (1 + P / a') / (1 + P / a) := by
    rw [le_div_iff₀ hB]; linarith
  have hρ2 : (1 + P / a') / (1 + P / a) ≤ 4 := by
    rw [div_le_iff₀ hB]; linarith
  have hsplit : (1 + P / a') ^ (-m) =
      ((1 + P / a') / (1 + P / a)) ^ (-m) * (1 + P / a) ^ (-m) := by
    rw [← Real.mul_rpow (div_nonneg hB'.le hB.le) hB.le, div_mul_cancel₀ _ hB.ne']
  have hρpow := rpow_neg_m_le m _ hρ1 hρ2
  have hinv : (a' ^ 3)⁻¹ ≤ 8 * (a ^ 3)⁻¹ := by
    have h3 : a ^ 3 ≤ 8 * a' ^ 3 := by
      have : a ≤ 2 * a' := by linarith
      nlinarith [pow_le_pow_left₀ ha.le this 3]
    have := inv_anti₀ (show 0 < a ^ 3 / 8 by positivity) (show a ^ 3 / 8 ≤ a' ^ 3 by linarith)
    rw [inv_div] at this
    have e : (8 : ℝ) / a ^ 3 = 8 * (a ^ 3)⁻¹ := by ring
    linarith
  unfold wbW
  rw [hsplit]
  calc (a' ^ 3)⁻¹ * (((1 + P / a') / (1 + P / a)) ^ (-m) * (1 + P / a) ^ (-m))
      ≤ (8 * (a ^ 3)⁻¹) * (4 ^ |m| * (1 + P / a) ^ (-m)) :=
        mul_le_mul hinv (mul_le_mul_of_nonneg_right hρpow (by positivity))
          (by positivity) (by positivity)
    _ = 8 * 4 ^ |m| * ((a ^ 3)⁻¹ * (1 + P / a) ^ (-m)) := by ring

theorem wtPhysBound (m : ℝ) : WtPhysBound m := by
  intro ν c r hc ha
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = clockA ν r / (2 * (|ν| + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos ha (by positivity)
  have hδeq : δ * (2 * (|ν| + 1)) = clockA ν r := by
    rw [hδdef]; exact div_mul_cancel₀ _ (by positivity)
  have hK : 0 ≤ 2 * |ν| * (3 + |m|) / clockA ν r :=
    div_nonneg (by positivity) ha.le
  refine ⟨8 * 4 ^ |m| * (1 + 2 * |ν| * (3 + |m|) / clockA ν r), δ, ?_, hδpos, ?_⟩
  · exact mul_nonneg (by positivity) (by linarith)
  intro x r' hr'
  rw [Metric.mem_ball, Real.dist_eq] at hr'
  have hνr : |clockA ν r' - clockA ν r| ≤ clockA ν r / 2 := by
    have e : clockA ν r' - clockA ν r = ν * (r' - r) := by unfold clockA; ring
    rw [e, abs_mul]
    calc |ν| * |r' - r| ≤ |ν| * δ := mul_le_mul_of_nonneg_left hr'.le (abs_nonneg _)
      _ ≤ (|ν| + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδpos.le
      _ = clockA ν r / 2 := by linarith
  have ha'lo : clockA ν r / 2 ≤ clockA ν r' := by linarith [(abs_le.mp hνr).1]
  have ha'hi : clockA ν r' ≤ 2 * clockA ν r := by linarith [(abs_le.mp hνr).2]
  have ha' : 0 < clockA ν r' := by linarith
  have hP := wbP_nonneg c x
  have hwt_r : wtPhys ν c m r x = wbW m (wbP c x) (clockA ν r) :=
    wtPhys_eq_wbW ν c m r x hc ha
  have hwt_r' : wtPhys ν c m r' x = wbW m (wbP c x) (clockA ν r') :=
    wtPhys_eq_wbW ν c m r' x hc ha'
  have hcont : Continuous (fun q => clockA ν q) := by
    unfold clockA; fun_prop
  have hopen : ∀ᶠ q in 𝓝 r', 0 < clockA ν q :=
    (hcont.tendsto r').eventually (lt_mem_nhds ha')
  have hev : (fun q => wtPhys ν c m q x) =ᶠ[𝓝 r'] (fun q => wbW m (wbP c x) (clockA ν q)) := by
    filter_upwards [hopen] with q hq
    exact wtPhys_eq_wbW ν c m q x hc hq
  obtain ⟨D, hD, hDb⟩ := wbW_hasDeriv m (wbP c x) (clockA ν r') ha' hP
  have hinner : HasDerivAt (fun q => clockA ν q) ν r' := by
    unfold clockA
    have := ((hasDerivAt_id' r').const_mul ν).const_add 1
    exact this.congr_deriv (by ring)
  have hcomp : HasDerivAt (fun q => wbW m (wbP c x) (clockA ν q)) (D * ν) r' :=
    hD.comp r' hinner
  have hderiv : HasDerivAt (fun q => wtPhys ν c m q x) (D * ν) r' :=
    hcomp.congr_of_eventuallyEq hev
  have hW0 : 0 ≤ wbW m (wbP c x) (clockA ν r) := wbW_nonneg m _ _ hP ha
  have hratio := wbW_ratio_le m (wbP c x) (clockA ν r) (clockA ν r') ha ha' hP ha'lo ha'hi
  refine ⟨hderiv.differentiableAt, ?_, ?_, ?_⟩
  · rw [hwt_r']; exact wbW_nonneg m _ _ hP ha'
  · rw [hwt_r', hwt_r]
    have key : 8 * 4 ^ |m| * (1 + 2 * |ν| * (3 + |m|) / clockA ν r) *
        wbW m (wbP c x) (clockA ν r) =
        8 * 4 ^ |m| * wbW m (wbP c x) (clockA ν r) +
          8 * 4 ^ |m| * (2 * |ν| * (3 + |m|) / clockA ν r) * wbW m (wbP c x) (clockA ν r) := by
      ring
    have hnn : 0 ≤ 8 * 4 ^ |m| * (2 * |ν| * (3 + |m|) / clockA ν r) *
        wbW m (wbP c x) (clockA ν r) := by positivity
    rw [key]
    linarith
  · rw [hderiv.deriv, hwt_r]
    have hinvle : (3 + |m|) / clockA ν r' ≤ 2 * (3 + |m|) / clockA ν r := by
      rw [div_le_div_iff₀ ha' ha]
      nlinarith [abs_nonneg m]
    have s1 : |D| ≤ 2 * (3 + |m|) / clockA ν r * (8 * 4 ^ |m| * wbW m (wbP c x) (clockA ν r)) := by
      refine le_trans hDb ?_
      calc (3 + |m|) / clockA ν r' * wbW m (wbP c x) (clockA ν r')
          ≤ 2 * (3 + |m|) / clockA ν r * wbW m (wbP c x) (clockA ν r') :=
            mul_le_mul_of_nonneg_right hinvle (wbW_nonneg m _ _ hP ha')
        _ ≤ 2 * (3 + |m|) / clockA ν r * (8 * 4 ^ |m| * wbW m (wbP c x) (clockA ν r)) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
    rw [abs_mul]
    calc |D| * |ν| ≤ (2 * (3 + |m|) / clockA ν r * (8 * 4 ^ |m| * wbW m (wbP c x) (clockA ν r))) * |ν| :=
          mul_le_mul_of_nonneg_right s1 (abs_nonneg ν)
      _ = 8 * 4 ^ |m| * (2 * |ν| * (3 + |m|) / clockA ν r) * wbW m (wbP c x) (clockA ν r) := by ring
      _ ≤ 8 * 4 ^ |m| * (1 + 2 * |ν| * (3 + |m|) / clockA ν r) * wbW m (wbP c x) (clockA ν r) := by
          apply mul_le_mul_of_nonneg_right _ hW0
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end UnforcedLeray.Short.IIIa.E0
