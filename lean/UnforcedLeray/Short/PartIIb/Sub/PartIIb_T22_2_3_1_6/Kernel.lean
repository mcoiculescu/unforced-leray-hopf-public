import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.DConv

/-!


Source: `the November 2 reference manuscript`, lines 2100-2105 (standard heat-kernel
calculus).  `K_a(z) = 2 K_{2a}(z) e^{-U}`, `U = |z|²/(8a)`, turns polynomial factors into powers of
`a`: pointwise, `|∂K_a| ≤ 9 a^{-1/2} K_{2a}`, `|∂²K_a| ≤ 5 a^{-1} K_{2a}` and
`|z₂| |∂²K_a(z)| ≤ 77 a^{-1/2} K_{2a}(z)`; the last one is the gain of the commutator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

/-- The second derivative `∂_i ∂_j K_a(z) = (z_i z_j/(4a²) - δ_ij/(2a)) K_a(z)`. -/
def heatKdd (i j : Fin 2) (a : ℝ) (z : Pl) : ℝ :=
  (![z.1, z.2] i * ![z.1, z.2] j / (4 * a ^ 2) - (if i = j then 1 / (2 * a) else 0)) * heatK a z

/-- The operator `g ↦ (∂_i ∂_j K_a) * g`. -/
def heatSGdd (i j : Fin 2) (a : ℝ) (g : Pl → ℝ) (x : Pl) : ℝ :=
  ∫ y : Pl, heatKdd i j a (x - y) * g y

theorem heatK_pos' {a : ℝ} (ha : 0 < a) (z : Pl) : 0 < heatK a z :=
  (heatKernelMoments a ha).1 z

theorem heatK_int {a : ℝ} (ha : 0 < a) : Integrable (heatK a) := (heatKernelMoments a ha).2.1

theorem heatK_cont' (a : ℝ) : Continuous (heatK a) := by
  unfold heatK
  fun_prop

/-- `∫ K_a(x - y) dy = 1`. -/
theorem integral_heatK_sub {a : ℝ} (ha : 0 < a) (x : Pl) : ∫ y : Pl, heatK a (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => heatK a z) volume x]
  exact (heatKernelMoments a ha).2.2.1

theorem heatK_sub_int {a : ℝ} (ha : 0 < a) (x : Pl) : Integrable (fun y : Pl => heatK a (x - y)) :=
  (heatK_int ha).comp_sub_left x

/-- `K_a = 2 K_{2a} e^{-U}`. -/
theorem heatK_eq_two {a : ℝ} (ha : 0 < a) (z : Pl) :
    heatK a z = 2 * heatK (2 * a) z * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / (8 * a))) := by
  have hexp : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a)) =
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * (2 * a))) *
        Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / (8 * a))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold heatK
  rw [hexp]
  field_simp

theorem exp_facts {U : ℝ} (hU : 0 ≤ U) :
    Real.exp (-U) ≤ 1 ∧ U * Real.exp (-U) ≤ 1 ∧ U ^ 2 * Real.exp (-U) ≤ 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg hU
  have he : Real.exp (-U) * Real.exp U = 1 := by
    rw [← Real.exp_add]
    simp
  have hp := Real.exp_pos (-U)
  have h1 := mul_le_mul_of_nonneg_left hq hp.le
  have h2 : 0 ≤ Real.exp (-U) * U := by positivity
  have h3 : 0 ≤ Real.exp (-U) * U ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem coord_sq_le (z : Pl) (i : Fin 2) : (![z.1, z.2] i) ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · change z.1 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2
    nlinarith [sq_nonneg z.2]
  · change z.2 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2
    nlinarith [sq_nonneg z.1]

theorem coord_mul_le (z : Pl) (i j : Fin 2) :
    |![z.1, z.2] i * ![z.1, z.2] j| ≤ z.1 ^ 2 + z.2 ^ 2 := by
  have h1 := coord_sq_le z i
  have h2 := coord_sq_le z j
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (![z.1, z.2] i - ![z.1, z.2] j),
    sq_nonneg (![z.1, z.2] i + ![z.1, z.2] j)]

/-- `|t| ≤ √a (1 + 8U)` when `t² ≤ |z|²`. -/
theorem abs_le_sqrt_mul {a t Q : ℝ} (ha : 0 < a) (ht : t ^ 2 ≤ Q) :
    |t| ≤ Real.sqrt a * (1 + 8 * (Q / (8 * a))) := by
  set s := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hss : a = s * s := (Real.mul_self_sqrt ha.le).symm
  have e : s * (1 + 8 * (Q / (8 * a))) = s + Q / s := by
    rw [hss]
    field_simp
  rw [e]
  have h2 : |t| ^ 2 ≤ Q := by rwa [sq_abs]
  have h3 : |t| * s ≤ s ^ 2 + Q := by nlinarith [sq_nonneg (|t| - s), abs_nonneg t]
  have h4 : s + Q / s = (s ^ 2 + Q) / s := by
    field_simp
  rw [h4, le_div_iff₀ hs0]
  exact h3

theorem heatKd_le {a : ℝ} (ha : 0 < a) (i : Fin 2) (z : Pl) :
    |heatKd i a z| ≤ 9 * (Real.sqrt a)⁻¹ * heatK (2 * a) z := by
  set Q := z.1 ^ 2 + z.2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set U := Q / (8 * a) with hU
  have hU0 : 0 ≤ U := by positivity
  have hK2 := heatK_pos' (by linarith : 0 < 2 * a) z
  have hK1 := heatK_pos' ha z
  set s := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hss : a = s * s := (Real.mul_self_sqrt ha.le).symm
  obtain ⟨he1, he2, -⟩ := exp_facts hU0
  have hE := Real.exp_pos (-U)
  have h1 : |![z.1, z.2] i| ≤ s * (1 + 8 * U) := abs_le_sqrt_mul ha (coord_sq_le z i)
  have hKe : heatK a z = 2 * heatK (2 * a) z * Real.exp (-U) := heatK_eq_two ha z
  have h3 : (1 + 8 * U) * Real.exp (-U) ≤ 9 := by nlinarith
  calc |heatKd i a z| = |![z.1, z.2] i| / (2 * a) * heatK a z := by
        unfold heatKd
        rw [abs_mul, abs_div, abs_neg, abs_of_pos hK1, abs_of_pos (by linarith : 0 < 2 * a)]
    _ ≤ (s * (1 + 8 * U)) / (2 * a) * heatK a z := by gcongr
    _ = s⁻¹ * ((1 + 8 * U) * Real.exp (-U)) * heatK (2 * a) z := by
        rw [hKe]
        have hs' : s ≠ 0 := hs0.ne'
        rw [hss]
        field_simp
    _ ≤ s⁻¹ * 9 * heatK (2 * a) z := by gcongr
    _ = _ := by ring

theorem heatKdd_abs_le {a : ℝ} (ha : 0 < a) (i j : Fin 2) (z : Pl) :
    |heatKdd i j a z| ≤ ((z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) + 1 / (2 * a)) * heatK a z := by
  have hK1 := heatK_pos' ha z
  unfold heatKdd
  rw [abs_mul, abs_of_pos hK1]
  refine mul_le_mul_of_nonneg_right ?_ hK1.le
  have h1 : |![z.1, z.2] i * ![z.1, z.2] j / (4 * a ^ 2)| ≤ (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * a ^ 2)]
    gcongr
    exact coord_mul_le z i j
  have h2 : |if i = j then 1 / (2 * a) else (0 : ℝ)| ≤ 1 / (2 * a) := by
    split_ifs
    · rw [abs_of_pos (by positivity)]
    · rw [abs_zero]
      positivity
  exact (abs_sub _ _).trans (add_le_add h1 h2)

theorem heatKdd_le {a : ℝ} (ha : 0 < a) (i j : Fin 2) (z : Pl) :
    |heatKdd i j a z| ≤ 5 * a⁻¹ * heatK (2 * a) z := by
  set Q := z.1 ^ 2 + z.2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set U := Q / (8 * a) with hU
  have hU0 : 0 ≤ U := by positivity
  have hK2 := heatK_pos' (by linarith : 0 < 2 * a) z
  obtain ⟨he1, he2, -⟩ := exp_facts hU0
  have hKe : heatK a z = 2 * heatK (2 * a) z * Real.exp (-U) := heatK_eq_two ha z
  have h3 : (4 * U + 1) * Real.exp (-U) ≤ 5 := by nlinarith
  have hA : 0 < a⁻¹ := inv_pos.2 ha
  calc |heatKdd i j a z| ≤ (Q / (4 * a ^ 2) + 1 / (2 * a)) * heatK a z := heatKdd_abs_le ha i j z
    _ = a⁻¹ * ((4 * U + 1) * Real.exp (-U)) * heatK (2 * a) z := by
        rw [hKe, hU]
        field_simp
        ring
    _ ≤ a⁻¹ * 5 * heatK (2 * a) z := by gcongr
    _ = _ := by ring

theorem z_heatKdd_le {a : ℝ} (ha : 0 < a) (i j : Fin 2) (z : Pl) :
    |z.2| * |heatKdd i j a z| ≤ 77 * (Real.sqrt a)⁻¹ * heatK (2 * a) z := by
  set Q := z.1 ^ 2 + z.2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set U := Q / (8 * a) with hU
  have hU0 : 0 ≤ U := by positivity
  have hK2 := heatK_pos' (by linarith : 0 < 2 * a) z
  have hK1 := heatK_pos' ha z
  set s := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hss : a = s * s := (Real.mul_self_sqrt ha.le).symm
  obtain ⟨he1, he2, he3⟩ := exp_facts hU0
  have hE := Real.exp_pos (-U)
  have hKe : heatK a z = 2 * heatK (2 * a) z * Real.exp (-U) := heatK_eq_two ha z
  have h1 : |z.2| ≤ s * (1 + 8 * U) := abs_le_sqrt_mul ha (by nlinarith [sq_nonneg z.1])
  have hb := heatKdd_abs_le ha i j z
  have hC0 : 0 ≤ (Q / (4 * a ^ 2) + 1 / (2 * a)) * heatK a z := by positivity
  have h3 : (32 * U ^ 2 + 12 * U + 1) * Real.exp (-U) ≤ 77 := by nlinarith
  calc |z.2| * |heatKdd i j a z| ≤ (s * (1 + 8 * U)) * ((Q / (4 * a ^ 2) + 1 / (2 * a)) * heatK a z) :=
        mul_le_mul h1 hb (abs_nonneg _) (by positivity)
    _ = s⁻¹ * ((32 * U ^ 2 + 12 * U + 1) * Real.exp (-U)) * heatK (2 * a) z := by
        rw [hKe, hU, hss]
        have hs' : s ≠ 0 := hs0.ne'
        field_simp
        ring
    _ ≤ s⁻¹ * 77 * heatK (2 * a) z := by gcongr
    _ = _ := by ring

/-- The shift of the Gaussian on a unit ball. -/
theorem heatK_shift {a : ℝ} (ha : 0 < a) {x x₀ : Pl} (hx : x ∈ ball x₀ 1) (y : Pl) :
    heatK (2 * a) (x - y) ≤ 2 * Real.exp (1 / (4 * a)) * heatK (4 * a) (x₀ - y) := by
  have hd : dist x x₀ < 1 := hx
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hd
  obtain ⟨h1, h2⟩ := hd
  rw [abs_lt] at h1 h2
  set s1 := x₀.1 - y.1 with hs1
  set s2 := x₀.2 - y.2 with hs2
  set t1 := x.1 - x₀.1 with ht1
  set t2 := x.2 - x₀.2 with ht2
  have e1 : (x - y).1 = s1 + t1 := by simp [hs1, ht1]
  have e2 : (x - y).2 = s2 + t2 := by simp [hs2, ht2]
  have e3 : (x₀ - y).1 = s1 := by simp [hs1]
  have e4 : (x₀ - y).2 = s2 := by simp [hs2]
  have hq1 : s1 ^ 2 / 2 - 1 ≤ (s1 + t1) ^ 2 := by nlinarith [sq_nonneg (s1 + 2 * t1), h1.1, h1.2]
  have hq2 : s2 ^ 2 / 2 - 1 ≤ (s2 + t2) ^ 2 := by nlinarith [sq_nonneg (s2 + 2 * t2), h2.1, h2.2]
  unfold heatK
  rw [e1, e2, e3, e4]
  have hexp : Real.exp (-((s1 + t1) ^ 2 + (s2 + t2) ^ 2) / (4 * (2 * a))) ≤
      Real.exp (1 / (4 * a)) * Real.exp (-(s1 ^ 2 + s2 ^ 2) / (4 * (4 * a))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e5 : 1 / (4 * a) + -(s1 ^ 2 + s2 ^ 2) / (4 * (4 * a)) =
        (-(s1 ^ 2 / 2 - 1 + (s2 ^ 2 / 2 - 1))) / (4 * (2 * a)) := by
      field_simp
      ring
    rw [e5]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hc : 1 / (4 * Real.pi * (2 * a)) = 2 * (1 / (4 * Real.pi * (4 * a))) := by
    field_simp
    ring
  rw [hc]
  calc 2 * (1 / (4 * Real.pi * (4 * a))) * Real.exp (-((s1 + t1) ^ 2 + (s2 + t2) ^ 2) / (4 * (2 * a)))
      ≤ 2 * (1 / (4 * Real.pi * (4 * a))) *
          (Real.exp (1 / (4 * a)) * Real.exp (-(s1 ^ 2 + s2 ^ 2) / (4 * (4 * a)))) := by gcongr
    _ = _ := by ring

/-- The linear form of the second derivative of the kernel. -/
def kddCLM (j : Fin 2) (a : ℝ) (z : Pl) : Pl →L[ℝ] ℝ :=
  heatKdd 0 j a z • ContinuousLinearMap.fst ℝ ℝ ℝ + heatKdd 1 j a z • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- `∂K_a` has the derivative `∂²K_a`. -/
theorem heatKd_hasFDeriv {a : ℝ} (ha : 0 < a) (j : Fin 2) (z : Pl) :
    HasFDerivAt (heatKd j a) (kddCLM j a z) z := by
  have hK : HasFDerivAt (heatK a) (heatKdCLM a z) z := by
    have h := heatKHasFDeriv a ha z 0
    simpa using h
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have hc : HasFDerivAt (fun w : Pl => -(w.1) / (2 * a))
        (-(1 / (2 * a)) • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul (-(1 / (2 * a)))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only
      ring
    have hm := hc.mul hK
    have hfun : heatKd 0 a = fun w : Pl => -(w.1) / (2 * a) * heatK a w := by
      funext w
      simp [heatKd]
    rw [hfun]
    refine hm.congr_fderiv ?_
    ext
    · simp [kddCLM, heatKdCLM, heatKd, heatKdd]
      field_simp
      ring
    · simp [kddCLM, heatKdCLM, heatKd, heatKdd]
      field_simp
      ring
  · have hc : HasFDerivAt (fun w : Pl => -(w.2) / (2 * a))
        (-(1 / (2 * a)) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
      have := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul (-(1 / (2 * a)))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only
      ring
    have hm := hc.mul hK
    have hfun : heatKd 1 a = fun w : Pl => -(w.2) / (2 * a) * heatK a w := by
      funext w
      simp [heatKd]
    rw [hfun]
    refine hm.congr_fderiv ?_
    ext
    · simp [kddCLM, heatKdCLM, heatKd, heatKdd]
      field_simp
      ring
    · simp [kddCLM, heatKdCLM, heatKd, heatKdd]
      field_simp
      ring

theorem heatKd_cont (i : Fin 2) (a : ℝ) : Continuous (heatKd i a) := by
  unfold heatKd
  have : Continuous (fun z : Pl => (![z.1, z.2] : Fin 2 → ℝ) i) := by
    fin_cases i <;> simp <;> fun_prop
  exact (this.neg.div_const _).mul (heatK_cont' a)

theorem heatKdd_cont (i j : Fin 2) (a : ℝ) : Continuous (heatKdd i j a) := by
  unfold heatKdd
  have hi : ∀ i : Fin 2, Continuous (fun z : Pl => (![z.1, z.2] : Fin 2 → ℝ) i) := by
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact ((((hi i).mul (hi j)).div_const _).sub continuous_const).mul (heatK_cont' a)

end LS

end UnforcedLeray.Short.IIb.BwdRoute
