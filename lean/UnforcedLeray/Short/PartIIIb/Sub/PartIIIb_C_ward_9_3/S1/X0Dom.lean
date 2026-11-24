import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.SepX0Dom

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `SepX0Dom` with the genuine weight `2μ + 2` kept (no antitone weakening to `0`). -/
theorem sepX0DomW : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ rOut rIn P : ℝ), 0 < ν → -(1 / 4) < μ → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T → ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        ‖sepX0 ν μ T τ y‖ₑ ≤
            ENNReal.ofReal C * IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y ∧
          ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ ≤
            ENNReal.ofReal C * (IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y +
              IIIa.sepDom (2 * μ + 2) 1 (rIn - rOut) (IIIa.srcNorm T) τ y) := by
  classical
  obtain ⟨A0, hA0, hW0⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 0
  obtain ⟨A1, hA1, hW1⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 1
  have hCpos : 0 < ‖reL‖ * (2 * A0 + 2 * A1) + 1 := by
    have := mul_nonneg (norm_nonneg reL) (by linarith : (0 : ℝ) ≤ 2 * A0 + 2 * A1)
    linarith
  refine ⟨‖reL‖ * (2 * A0 + 2 * A1) + 1, hCpos.le, ?_⟩
  intro ν μ rOut rIn P hν hμre hrO hrr hP T hT hM τ y hry
  have hm1re : -(1 / 4) < ((μ : ℂ)).re := by
    simp only [Complex.ofReal_re]
    exact hμre
  have hm2re : -(1 / 4) < ((μ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hri : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hry
  have hy : y ∈ {y : Space | rOut < ϱ y} := lt_of_lt_of_le hrr hry
  -- smoothness of `W_μ`, `W_{μ+1}` on the open set `{rOut < ϱ y}`
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWa : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1re hrO hP hT hM τ i)
  have hWb : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν
      hm2re hrO hP hT hM τ i)
  -- pointwise derivative bound for `sepX0` (orders `0` and `1`)
  have hder : ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ ≤
        ENNReal.ofReal ‖reL‖ * (IIIa.wDerivNorm ν (μ : ℂ) T j τ y +
          IIIa.wDerivNorm ν ((μ : ℂ) + 1) T j τ y) := by
    intro j hj
    rw [sepX0_eq_reL]
    exact iteratedFDeriv_reL_le hU hWa hWb hj hy
  -- the order-`0` and order-`1` majorants at `y`
  set S0 : ℝ≥0∞ := IIIa.sepDom (2 * μ + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y with hS0
  set S1 : ℝ≥0∞ := IIIa.sepDom (2 * μ + 2) 1 (rIn - rOut) (IIIa.srcNorm T) τ y with hS1
  set C : ℝ := ‖reL‖ * (2 * A0 + 2 * A1) + 1 with hC
  have hCne : ENNReal.ofReal C ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hCpos
  by_cases hfin : S0 = ⊤
  · -- the order-`0` majorant is infinite: both right sides are `⊤`
    constructor
    · rw [hfin, ENNReal.mul_top hCne]
      exact le_top
    · rw [hfin, top_add, ENNReal.mul_top hCne]
      exact le_top
  have hS0lt : S0 < ⊤ := lt_top_iff_ne_top.2 hfin
  -- comparison of the majorants at `2 Re mu + 2` and `2 Re(mu+1) + 2` with `a = 0`
  have hb1 : 2 * μ + 2 ≤ 2 * ((μ : ℂ)).re + 2 := by
    simp only [Complex.ofReal_re]; exact le_rfl
  have hb2 : 2 * μ + 2 ≤ 2 * ((μ : ℂ) + 1).re + 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hd1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y ≤ S0 :=
    sepDom_anti_a' hb1 0 _ _ _ _
  have hd2 : IIIa.sepDom (2 * ((μ : ℂ) + 1).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y ≤ S0 :=
    sepDom_anti_a' hb2 0 _ _ _ _
  have hd1' : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 1 (rIn - rOut) (IIIa.srcNorm T) τ y ≤ S1 :=
    sepDom_anti_a' hb1 1 _ _ _ _
  have hd2' : IIIa.sepDom (2 * ((μ : ℂ) + 1).re + 2) 1 (rIn - rOut) (IIIa.srcNorm T) τ y ≤ S1 :=
    sepDom_anti_a' hb2 1 _ _ _ _
  have hf1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt hd1 hS0lt
  have hf2 : IIIa.sepDom (2 * ((μ : ℂ) + 1).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt hd2 hS0lt
  -- the derivative bounds for `W_μ` and `W_{μ+1}`
  have wa0 := hW0 ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hri hf1
  have wb0 := hW0 ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hri hf2
  have wa1 := hW1 ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hri hf1
  have wb1 := hW1 ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hri hf2
  have ea0 : IIIa.wDerivNorm ν (μ : ℂ) T 0 τ y ≤ ENNReal.ofReal A0 * S0 :=
    wa0.trans (by gcongr)
  have eb0 : IIIa.wDerivNorm ν ((μ : ℂ) + 1) T 0 τ y ≤ ENNReal.ofReal A0 * S0 :=
    wb0.trans (by gcongr)
  have ea1 : IIIa.wDerivNorm ν (μ : ℂ) T 1 τ y ≤ ENNReal.ofReal A1 * S1 :=
    wa1.trans (by gcongr)
  have eb1 : IIIa.wDerivNorm ν ((μ : ℂ) + 1) T 1 τ y ≤ ENNReal.ofReal A1 * S1 :=
    wb1.trans (by gcongr)
  -- constant bookkeeping: `ofReal ‖reL‖ * ofReal A_j ≤ ofReal C`
  have hA0c : ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A0 + ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A0
      ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (norm_nonneg reL),
      ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg reL) hA0) (mul_nonneg (norm_nonneg reL) hA0)]
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (norm_nonneg reL) hA1
    rw [hC]
    nlinarith
  have hA1c : ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A1 + ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A1
      ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (norm_nonneg reL),
      ← ENNReal.ofReal_add (mul_nonneg (norm_nonneg reL) hA1) (mul_nonneg (norm_nonneg reL) hA1)]
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (norm_nonneg reL) hA0
    rw [hC]
    nlinarith
  have e0 : ‖sepX0 ν μ T τ y‖ₑ = ‖iteratedFDeriv ℝ 0 (sepX0 ν μ T τ) y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  have e1 : ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ = ‖iteratedFDeriv ℝ 1 (sepX0 ν μ T τ) y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_one]
  constructor
  · calc ‖sepX0 ν μ T τ y‖ₑ = ‖iteratedFDeriv ℝ 0 (sepX0 ν μ T τ) y‖ₑ := e0
      _ ≤ ENNReal.ofReal ‖reL‖ * (IIIa.wDerivNorm ν (μ : ℂ) T 0 τ y +
          IIIa.wDerivNorm ν ((μ : ℂ) + 1) T 0 τ y) := hder 0 (by norm_num)
      _ ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal A0 * S0 + ENNReal.ofReal A0 * S0) :=
          by gcongr
      _ = (ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A0 + ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A0) *
          S0 := by ring
      _ ≤ ENNReal.ofReal C * S0 := by gcongr
  · calc ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ = ‖iteratedFDeriv ℝ 1 (sepX0 ν μ T τ) y‖ₑ := e1
      _ ≤ ENNReal.ofReal ‖reL‖ * (IIIa.wDerivNorm ν (μ : ℂ) T 1 τ y +
          IIIa.wDerivNorm ν ((μ : ℂ) + 1) T 1 τ y) := hder 1 (by norm_num)
      _ ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal A1 * S1 + ENNReal.ofReal A1 * S1) :=
          by gcongr
      _ = (ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A1 + ENNReal.ofReal ‖reL‖ * ENNReal.ofReal A1) *
          S1 := by ring
      _ ≤ ENNReal.ofReal C * S1 := by gcongr
      _ ≤ ENNReal.ofReal C * (S0 + S1) := mul_le_mul_of_nonneg_left le_add_self (by positivity)


end UnforcedLeray.Short.PartIIIb.Concrete

end
