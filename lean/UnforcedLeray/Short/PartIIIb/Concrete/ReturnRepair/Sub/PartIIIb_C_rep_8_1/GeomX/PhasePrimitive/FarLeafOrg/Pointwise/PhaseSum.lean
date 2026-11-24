import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Summing a periodic profile over the dilation variable (helper for `OscFarPt`)

`∫_0^1 l^a g(q₀ + ε⁻¹ log l) dl ≤ ε (1 - e^{-ε(a+1)c})⁻¹ ∫_0^c g`, `g` `c`-periodic, `a > -1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

theorem lint_periodic_shift (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ≥0∞) (hper : ∀ q, g (q + c) = g q)
    (t : ℝ) : ∫⁻ s in Ioc t (t + c), g s = ∫⁻ s in Ioc 0 c, g s := by
  have h0 := isAddFundamentalDomain_Ioc hc 0 (volume : Measure ℝ)
  have ht := isAddFundamentalDomain_Ioc hc t (volume : Measure ℝ)
  have := ht.setLIntegral_eq h0 g (by
    rintro ⟨x, hx⟩ y
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
    show g ((n • c : ℝ) + y) = g y
    have : ∀ n : ℤ, ∀ y, g (n • c + y) = g y := by
      intro n
      have hp : Function.Periodic g c := hper
      intro y
      rw [add_comm]
      exact (hp.zsmul n) y
    exact this n y)
  rw [this, zero_add]

theorem phaseSum_le (ε c q0 a : ℝ) (hε : 0 < ε) (hc : 0 < c) (ha : -1 < a) (g : ℝ → ℝ≥0∞)
    (hper : ∀ q, g (q + c) = g q) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * g (q0 + ε⁻¹ * Real.log l) ≤
      ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (a + 1) * c)))) * ∫⁻ q in Ioc 0 c, g q := by
  set G : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (l ^ a) * g (q0 + ε⁻¹ * Real.log l) with hG
  set φ : ℝ → ℝ := fun s => Real.exp (ε * (s - q0)) with hφ
  have himg : φ '' Iio q0 = Ioo 0 1 := by
    ext l
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by have : s - q0 < 0 := by simpa using hs
                                  nlinarith)
    · rintro ⟨h0, h1⟩
      refine ⟨q0 + ε⁻¹ * Real.log l, ?_, ?_⟩
      · have : Real.log l < 0 := Real.log_neg h0 h1
        have : ε⁻¹ * Real.log l < 0 := mul_neg_of_pos_of_neg (inv_pos.2 hε) this
        simp only [mem_Iio]; linarith
      · simp only [hφ]
        have : ε * (q0 + ε⁻¹ * Real.log l - q0) = Real.log l := by field_simp; ring
        rw [this, Real.exp_log h0]
  have hinj : InjOn φ (Iio q0) := by
    intro s _ t _ h
    have := Real.exp_injective h
    have : s - q0 = t - q0 := by nlinarith [mul_left_cancel₀ hε.ne' this]
    linarith
  have hd : ∀ s ∈ Iio q0, HasDerivWithinAt φ (ε * Real.exp (ε * (s - q0))) (Iio q0) s := by
    intro s _
    have h1 : HasDerivAt (fun x : ℝ => ε * (x - q0)) (ε * 1) s :=
      ((hasDerivAt_id s).sub_const q0).const_mul ε
    have := (h1.exp).hasDerivWithinAt (s := Iio q0)
    exact this.congr_deriv (by ring)
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio hd hinj G
  rw [himg] at hcv
  have step1 : ∫⁻ l in Ioo (0 : ℝ) 1, G l =
      ∫⁻ s in Iio q0, ENNReal.ofReal (ε * Real.exp ((a + 1) * (ε * (s - q0)))) * g s := by
    rw [hcv]
    refine setLIntegral_congr_fun measurableSet_Iio (fun s _ => ?_)
    simp only [hG, hφ]
    have e1 : q0 + ε⁻¹ * Real.log (Real.exp (ε * (s - q0))) = s := by
      rw [Real.log_exp]; field_simp; ring
    rw [e1, abs_of_pos (mul_pos hε (Real.exp_pos _)), ← mul_assoc, ← ENNReal.ofReal_mul (mul_pos hε (Real.exp_pos _)).le]
    congr 2
    rw [← Real.exp_mul, mul_assoc ε, ← Real.exp_add]
    congr 2
    ring
  rw [step1]
  set r : ℝ := Real.exp (-(ε * (a + 1) * c)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]
    refine lt_of_lt_of_eq (Real.exp_lt_exp.2 ?_) Real.exp_zero
    have : 0 < ε * (a + 1) * c := by
      have : 0 < a + 1 := by linarith
      positivity
    linarith
  have hcover : Iio q0 ⊆ ⋃ n : ℕ, Ioc (q0 - (n + 1) * c) (q0 - n * c) := by
    intro s hs
    simp only [mem_Iio] at hs
    simp only [mem_iUnion, mem_Ioc]
    refine ⟨⌊(q0 - s) / c⌋₊, ?_, ?_⟩
    · have h1 := Nat.lt_floor_add_one ((q0 - s) / c)
      rw [div_lt_iff₀ hc] at h1
      linarith
    · have h1 := Nat.floor_le (div_nonneg (sub_nonneg.2 hs.le) hc.le)
      rw [le_div_iff₀ hc] at h1
      linarith
  have hge : ∀ n : ℕ, ∫⁻ s in Ioc (q0 - (n + 1) * c) (q0 - n * c),
      ENNReal.ofReal (ε * Real.exp ((a + 1) * (ε * (s - q0)))) * g s ≤
      ENNReal.ofReal (ε * r ^ n) * ∫⁻ q in Ioc 0 c, g q := by
    intro n
    have hshift := lint_periodic_shift c hc g hper (q0 - (n + 1) * c)
    have e : q0 - (n + 1) * c + c = q0 - n * c := by ring
    rw [e] at hshift
    calc _ ≤ ∫⁻ s in Ioc (q0 - (n + 1) * c) (q0 - n * c), ENNReal.ofReal (ε * r ^ n) * g s := by
          refine setLIntegral_mono' measurableSet_Ioc (fun s hs => ?_)
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          rw [hr, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          have : 0 < a + 1 := by linarith
          have h2 : s - q0 ≤ -(n * c) := by linarith [hs.2]
          nlinarith [mul_le_mul_of_nonneg_left h2 (mul_pos hε this).le]
      _ = ENNReal.ofReal (ε * r ^ n) * ∫⁻ s in Ioc (q0 - (n + 1) * c) (q0 - n * c), g s :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by rw [hshift]
  calc ∫⁻ s in Iio q0, ENNReal.ofReal (ε * Real.exp ((a + 1) * (ε * (s - q0)))) * g s
      ≤ ∫⁻ s in ⋃ n : ℕ, Ioc (q0 - (n + 1) * c) (q0 - n * c),
          ENNReal.ofReal (ε * Real.exp ((a + 1) * (ε * (s - q0)))) * g s :=
        lintegral_mono_set hcover
    _ ≤ ∑' n : ℕ, ∫⁻ s in Ioc (q0 - (n + 1) * c) (q0 - n * c),
          ENNReal.ofReal (ε * Real.exp ((a + 1) * (ε * (s - q0)))) * g s :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (ε * r ^ n) * ∫⁻ q in Ioc 0 c, g q := ENNReal.tsum_le_tsum hge
    _ = ENNReal.ofReal (ε / (1 - r)) * ∫⁻ q in Ioc 0 c, g q := by
        rw [ENNReal.tsum_mul_right]
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((summable_geometric_of_lt_one hr0.le hr1).mul_left ε)]
        congr 1
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, div_eq_mul_inv]

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
