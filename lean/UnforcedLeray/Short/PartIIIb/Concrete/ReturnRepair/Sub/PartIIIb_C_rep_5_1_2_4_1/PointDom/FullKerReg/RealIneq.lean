import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-variable estimates for the outward primitive (helper for `pdFullKerReg`, `pdYKerBound`)

* `primJ2`: `∫_{u>0} (a+u)((a+u)²+b²)^{-2} du = 1/(2(a²+b²))`;
* `primPt`: the pointwise reduction of the integrands `ρ α₀`, `α₀ + ρ α₁`, `2α₁ + ρ α₂` (decay
  `t^{-4}, t^{-5}, t^{-6}`) to the single profile `v (v²+b²)^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∫_{u>0} (a+u)((a+u)²+b²)^{-2} du = 1/(2(a²+b²))` for `a > 0`. -/
theorem primJ2 {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun u : ℝ => (a + u) * (((a + u) ^ 2 + b ^ 2) ^ 2)⁻¹) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (a + u) * (((a + u) ^ 2 + b ^ 2) ^ 2)⁻¹ = 1 / (2 * (a ^ 2 + b ^ 2)) := by
  have hS : ∀ u : ℝ, 0 ≤ u → 0 < (a + u) ^ 2 + b ^ 2 := fun u hu => by positivity
  have hderiv : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ => -(1 / 2) * (((a + u) ^ 2 + b ^ 2))⁻¹)
        ((a + u) * (((a + u) ^ 2 + b ^ 2) ^ 2)⁻¹) u := by
    intro u hu
    have hpos := hS u hu
    have h1 : HasDerivAt (fun u : ℝ => (a + u) ^ 2 + b ^ 2) (2 * (a + u)) u := by
      have := ((hasDerivAt_id u).const_add a).pow 2
      simpa using this.add_const (b ^ 2)
    have h2 := (h1.inv hpos.ne').const_mul (-(1 / 2))
    refine h2.congr_deriv ?_
    field_simp
  have hnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ (a + u) * (((a + u) ^ 2 + b ^ 2) ^ 2)⁻¹ := fun u hu => by
    have : 0 < a + u := by have : (0:ℝ) < u := hu; linarith
    positivity
  have hcont : ContinuousWithinAt (fun u : ℝ => -(1 / 2) * (((a + u) ^ 2 + b ^ 2))⁻¹) (Ici 0) 0 := by
    have : ContinuousAt (fun u : ℝ => -(1 / 2) * (((a + u) ^ 2 + b ^ 2))⁻¹) 0 :=
      (hderiv 0 (Set.mem_Ici.mpr le_rfl)).continuousAt
    exact this.continuousWithinAt
  have htend : Tendsto (fun u : ℝ => -(1 / 2) * (((a + u) ^ 2 + b ^ 2))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => (a + u) ^ 2 + b ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_right _ _ ?_
      exact (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_left _ _ tendsto_id)
    have := (h.inv_tendsto_atTop).const_mul (-(1 / 2))
    rwa [mul_zero] at this
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont
    (fun u hu => hderiv u (Set.mem_Ici.mpr (le_of_lt hu))) hnn htend
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hderiv u (Set.mem_Ici.mpr (le_of_lt hu))) hint htend]
  have : (a + 0) ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 := by ring
  simp only [this]
  field_simp
  ring

/-- Pointwise reduction.  `ρ = ρ₀ + v`, `v ≥ δ > 0`, `t² ≥ v² + b²`, `α₀ ≤ K t^{-4}`,
`α₁ ≤ K t^{-5}`, `α₂ ≤ K t^{-6}`: the three integrands are `≤ C v (v²+b²)^{-2}` with
`C = (2 + (ρ₀/δ + 1))(1 + δ⁻²) K`. -/
theorem primPt {K ρ₀ δ v b t α₀ α₁ α₂ : ℝ} (hK : 0 ≤ K) (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) (hv : δ ≤ v)
    (ht : v ^ 2 + b ^ 2 ≤ t ^ 2) (ht0 : 0 ≤ t) (h0 : 0 ≤ α₀) (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂)
    (hα₀ : α₀ ≤ K * (t ^ 4)⁻¹) (hα₁ : α₁ ≤ K * (t ^ 5)⁻¹) (hα₂ : α₂ ≤ K * (t ^ 6)⁻¹) :
    (ρ₀ + v) * α₀ ≤ (2 + (ρ₀ / δ + 1)) * (1 + (δ ^ 2)⁻¹) * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
    α₀ + (ρ₀ + v) * α₁ ≤ (2 + (ρ₀ / δ + 1)) * (1 + (δ ^ 2)⁻¹) * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
    2 * α₁ + (ρ₀ + v) * α₂ ≤ (2 + (ρ₀ / δ + 1)) * (1 + (δ ^ 2)⁻¹) * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
  set S := v ^ 2 + b ^ 2 with hSdef
  have hv0 : 0 < v := lt_of_lt_of_le hδ hv
  have hS0 : 0 < S := by positivity
  have hSδ : δ ^ 2 ≤ S := by nlinarith [sq_nonneg b]
  have htδ : δ ≤ t := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have ht0' : 0 < t := lt_of_lt_of_le hδ htδ
  set m := ρ₀ / δ + 1 with hm
  have hm0 : 0 ≤ m := by positivity
  have hρ : ρ₀ + v ≤ m * v := by
    have : ρ₀ ≤ ρ₀ / δ * v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    rw [hm]; nlinarith
  have hS2 : 0 < S ^ 2 := by positivity
  have ht4 : S ^ 2 ≤ t ^ 4 := by nlinarith
  have ht5 : S ^ 2 * δ ≤ t ^ 5 := by
    have : t ^ 5 = t ^ 4 * t := by ring
    rw [this]
    exact mul_le_mul ht4 htδ hδ.le (by positivity)
  have ht6 : S ^ 2 * δ ^ 2 ≤ t ^ 6 := by
    have : t ^ 6 = t ^ 4 * t ^ 2 := by ring
    rw [this]
    exact mul_le_mul ht4 (by nlinarith) (by positivity) (by positivity)
  have i4 : (t ^ 4)⁻¹ ≤ (S ^ 2)⁻¹ := inv_anti₀ hS2 ht4
  have i5 : (t ^ 5)⁻¹ ≤ (S ^ 2 * δ)⁻¹ := inv_anti₀ (by positivity) ht5
  have i6 : (t ^ 6)⁻¹ ≤ (S ^ 2 * δ ^ 2)⁻¹ := inv_anti₀ (by positivity) ht6
  set P := (S ^ 2)⁻¹ with hP
  have hP0 : 0 ≤ P := by positivity
  have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have a0 : α₀ ≤ K * P := hα₀.trans (mul_le_mul_of_nonneg_left i4 hK)
  have a1 : α₁ ≤ K * (P * δ⁻¹) := by
    refine hα₁.trans (mul_le_mul_of_nonneg_left ?_ hK)
    refine i5.trans (le_of_eq ?_)
    rw [mul_inv]
  have a2 : α₂ ≤ K * (P * (δ ^ 2)⁻¹) := by
    refine hα₂.trans (mul_le_mul_of_nonneg_left ?_ hK)
    refine i6.trans (le_of_eq ?_)
    rw [mul_inv]
  have one_le : 1 ≤ v * δ⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hδ]; linarith
  have KP : 0 ≤ K * P := by positivity
  have hq : 0 ≤ (δ ^ 2)⁻¹ := by positivity
  set Q := (δ ^ 2)⁻¹ with hQ
  have hQ' : Q = δ⁻¹ * δ⁻¹ := by rw [hQ, sq, mul_inv]
  have T0 : 0 ≤ K * (v * P) := by positivity
  have W : 0 ≤ (K * (v * P)) := T0
  have D1 : δ⁻¹ ≤ 1 + Q := by
    rw [hQ']; nlinarith [sq_nonneg (δ⁻¹ - 1)]
  have D2 : Q ≤ 1 + Q := by linarith
  have cm : ∀ c c' : ℝ, c ≤ c' → c * (K * (v * P)) ≤ c' * (K * (v * P)) :=
    fun c c' h => mul_le_mul_of_nonneg_right h W
  have key : ∀ c : ℝ, c ≤ (2 + m) * (1 + Q) → c * (K * (v * P)) ≤ (2 + m) * (1 + Q) * K * (v * P) := by
    intro c hc
    have := cm c _ hc
    calc c * (K * (v * P)) ≤ (2 + m) * (1 + Q) * (K * (v * P)) := this
      _ = (2 + m) * (1 + Q) * K * (v * P) := by ring
  refine ⟨?_, ?_, ?_⟩
  · calc (ρ₀ + v) * α₀ ≤ (m * v) * (K * P) := mul_le_mul hρ a0 h0 (by positivity)
      _ = m * (K * (v * P)) := by ring
      _ ≤ (2 + m) * (1 + Q) * K * (v * P) := by
        refine key m ?_
        have : (0:ℝ) ≤ (1 + Q) := by linarith
        nlinarith
  · have e1 : α₀ ≤ K * P * (v * δ⁻¹) := by
      calc α₀ ≤ K * P := a0
        _ = K * P * 1 := by ring
        _ ≤ K * P * (v * δ⁻¹) := mul_le_mul_of_nonneg_left one_le KP
    have e2 : (ρ₀ + v) * α₁ ≤ (m * v) * (K * (P * δ⁻¹)) :=
      mul_le_mul hρ a1 h1 (by positivity)
    calc α₀ + (ρ₀ + v) * α₁ ≤ K * P * (v * δ⁻¹) + (m * v) * (K * (P * δ⁻¹)) := add_le_add e1 e2
      _ = ((1 + m) * δ⁻¹) * (K * (v * P)) := by ring
      _ ≤ (2 + m) * (1 + Q) * K * (v * P) := by
        refine key _ ?_
        have h1m : (1 + m) * δ⁻¹ ≤ (1 + m) * (1 + Q) := mul_le_mul_of_nonneg_left D1 (by linarith)
        have : (1 + m) * (1 + Q) ≤ (2 + m) * (1 + Q) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
  · have e1 : 2 * α₁ ≤ 2 * (K * (P * δ⁻¹)) := by linarith
    have e1' : K * (P * δ⁻¹) ≤ K * P * ((v * δ⁻¹) * δ⁻¹) := by
      have : δ⁻¹ ≤ (v * δ⁻¹) * δ⁻¹ := by
        calc δ⁻¹ = 1 * δ⁻¹ := by ring
          _ ≤ (v * δ⁻¹) * δ⁻¹ := mul_le_mul_of_nonneg_right one_le hδinv.le
      calc K * (P * δ⁻¹) = K * P * δ⁻¹ := by ring
        _ ≤ K * P * ((v * δ⁻¹) * δ⁻¹) := mul_le_mul_of_nonneg_left this KP
    have e2 : (ρ₀ + v) * α₂ ≤ (m * v) * (K * (P * Q)) :=
      mul_le_mul hρ a2 h2 (by positivity)
    calc 2 * α₁ + (ρ₀ + v) * α₂
        ≤ 2 * (K * P * ((v * δ⁻¹) * δ⁻¹)) + (m * v) * (K * (P * Q)) := by linarith
      _ = ((2 + m) * Q) * (K * (v * P)) := by rw [hQ']; ring
      _ ≤ (2 + m) * (1 + Q) * K * (v * P) := by
        refine key _ ?_
        exact mul_le_mul_of_nonneg_left D2 (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete

end
