import UnforcedLeray.Short.PartIIb.Sub.T12_1_1

/-!
# The planar Riesz kernel is a Calderón–Zygmund kernel

Proof of `PlaneRieszKernelCZ` (the `N = 2` analogue of `newtonHessianKernel` in
`Lib/CZL2/HessianKernel.lean`). Source: `the November 2 reference manuscript`,
lines 1670 and 1923–1926; Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb

namespace PlaneRieszKernelCZProof

/-! ### Sup-norm facts for `planeWeight` -/

theorem abs_le_anisoNorm_plane (z : Fin 2 → ℝ) (j : Fin 2) :
    |z j| ≤ UnforcedLeray.CZ.anisoNorm planeWeight z := by
  simpa [planeWeight] using UnforcedLeray.CZ.abs_le_anisoNorm_pow planeWeight z j

theorem anisoNorm_plane_le {z : Fin 2 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ j, |z j| ≤ r) :
    UnforcedLeray.CZ.anisoNorm planeWeight z ≤ r := by
  refine (UnforcedLeray.CZ.anisoNorm_le_iff planeWeight hr).2 fun j => ?_
  simpa [planeWeight] using h j

theorem homDim_planeWeight : UnforcedLeray.CZ.homDim planeWeight = 2 := by
  simp [UnforcedLeray.CZ.homDim, planeWeight]

theorem abs_le_sqrt_sum (z : Fin 2 → ℝ) (j : Fin 2) :
    |z j| ≤ Real.sqrt (z 0 * z 0 + z 1 * z 1) := by
  apply Real.abs_le_sqrt
  fin_cases j
  · show z 0 ^ 2 ≤ z 0 * z 0 + z 1 * z 1
    nlinarith [mul_self_nonneg (z 1)]
  · show z 1 ^ 2 ≤ z 0 * z 0 + z 1 * z 1
    nlinarith [mul_self_nonneg (z 0)]

/-! ### The kernel in product form -/

theorem planeRieszKernel_eq (i k : Fin 2) (z : Fin 2 → ℝ) :
    planeRieszKernel i k z =
      (2 * Real.pi)⁻¹ * ((if i = k then (1 : ℝ) else 0) * (z 0 * z 0 + z 1 * z 1)
        - 2 * (z i * z k)) / ((z 0 * z 0 + z 1 * z 1) * (z 0 * z 0 + z 1 * z 1)) := by
  by_cases hz : z = 0
  · subst hz
    simp [planeRieszKernel]
  · rw [planeRieszKernel, if_neg hz]
    ring

/-! ### The segment `t ↦ x - t • y` -/

/-- Component `j` of `x - t • y`. -/
def segA (x y : Fin 2 → ℝ) (t : ℝ) (j : Fin 2) : ℝ := x j - t * y j

/-- `|x - t • y|²` on the segment. -/
def segQ (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  segA x y t 0 * segA x y t 0 + segA x y t 1 * segA x y t 1

/-- Numerator `δ |z|² - 2 z_i z_k` on the segment. -/
def segN (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  δ * segQ x y t - 2 * (segA x y t i * segA x y t k)

/-- The kernel along the segment: `g(t) = (2π)⁻¹ N(t) / |z(t)|⁴`. -/
def segG (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * segN δ i k x y t / (segQ x y t * segQ x y t)

/-- Derivative of `segQ`. -/
def segQd (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  -2 * (segA x y t 0 * y 0 + segA x y t 1 * y 1)

/-- Derivative of `segN`. -/
def segNd (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  δ * segQd x y t + 2 * (y i * segA x y t k + segA x y t i * y k)

/-- Derivative of `segG`. -/
def segD (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (segNd δ i k x y t * segQ x y t - 2 * (segN δ i k x y t * segQd x y t)) /
    segQ x y t ^ 3

theorem planeRieszKernel_segment (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) :
    planeRieszKernel i k (x - t • y) = segG (if i = k then 1 else 0) i k x y t := by
  rw [planeRieszKernel_eq]
  simp only [segG, segN, segQ, segA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem hQ_nonneg (x y : Fin 2 → ℝ) (t : ℝ) : 0 ≤ segQ x y t := by
  unfold segQ
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem hasDerivAt_segA (x y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => segA x y s j) (-y j) t := by
  have h := ((hasDerivAt_id t).mul_const (y j)).const_sub (x j)
  simpa [segA] using h

theorem hasDerivAt_segQ (x y : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => segQ x y s) (segQd x y t) t := by
  have h := ((hasDerivAt_segA x y 0 t).mul (hasDerivAt_segA x y 0 t)).add
    ((hasDerivAt_segA x y 1 t).mul (hasDerivAt_segA x y 1 t))
  refine h.congr_deriv ?_
  simp only [segQd]
  ring

theorem hasDerivAt_segN (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => segN δ i k x y s) (segNd δ i k x y t) t := by
  have h := ((hasDerivAt_segQ x y t).const_mul δ).sub
    (((hasDerivAt_segA x y i t).mul (hasDerivAt_segA x y k t)).const_mul 2)
  refine h.congr_deriv ?_
  simp only [segNd]
  ring

theorem hasDerivAt_segG (δ : ℝ) (i k : Fin 2) (x y : Fin 2 → ℝ) (t : ℝ)
    (ht : segQ x y t ≠ 0) :
    HasDerivAt (segG δ i k x y) (segD δ i k x y t) t := by
  have hnum : HasDerivAt (fun s => (2 * Real.pi)⁻¹ * segN δ i k x y s)
      ((2 * Real.pi)⁻¹ * segNd δ i k x y t) t :=
    (hasDerivAt_segN δ i k x y t).const_mul _
  have hden : HasDerivAt (fun s => segQ x y s * segQ x y s)
      (segQd x y t * segQ x y t + segQ x y t * segQd x y t) t :=
    (hasDerivAt_segQ x y t).mul (hasDerivAt_segQ x y t)
  have hne : segQ x y t * segQ x y t ≠ 0 := mul_ne_zero ht ht
  refine (hnum.div hden hne).congr_deriv ?_
  unfold segD
  field_simp
  ring

/-! ### Bounds on the segment -/

theorem abs_segA_le (x y : Fin 2 → ℝ) (t : ℝ) (j : Fin 2) :
    |segA x y t j| ≤ Real.sqrt (segQ x y t) := by
  apply Real.abs_le_sqrt
  unfold segQ
  fin_cases j
  · show segA x y t 0 ^ 2 ≤ segA x y t 0 * segA x y t 0 + segA x y t 1 * segA x y t 1
    nlinarith [mul_self_nonneg (segA x y t 1)]
  · show segA x y t 1 ^ 2 ≤ segA x y t 0 * segA x y t 0 + segA x y t 1 * segA x y t 1
    nlinarith [mul_self_nonneg (segA x y t 0)]

theorem seg_lower (x y : Fin 2 → ℝ) {m : ℝ} (hm : 0 ≤ m) (hy : ∀ j, |y j| ≤ m)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x) :
    UnforcedLeray.CZ.anisoNorm planeWeight x < 2 * Real.sqrt (segQ x y t) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hxj : ∀ j, |x j| ≤ Real.sqrt (segQ x y t) + m := by
    intro j
    have e : x j = segA x y t j + t * y j := by unfold segA; ring
    have h2 : |t * y j| ≤ m := by
      rw [abs_mul, abs_of_nonneg ht0]
      calc t * |y j| ≤ 1 * |y j| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
        _ ≤ m := by linarith [hy j]
    calc |x j| = |segA x y t j + t * y j| := by rw [← e]
      _ ≤ |segA x y t j| + |t * y j| := abs_add_le _ _
      _ ≤ Real.sqrt (segQ x y t) + m := add_le_add (abs_segA_le x y t j) h2
  have hle := anisoNorm_plane_le (add_nonneg (Real.sqrt_nonneg _) hm) hxj
  linarith

theorem div_sigma_le (c m s σ : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hs : 0 < s)
    (hlt : s < 2 * σ) : 32 * c * m / σ ^ 3 ≤ 256 * c * m * (s ^ 3)⁻¹ := by
  have hsub : s ^ 3 / 8 ≤ σ ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ s / 2) (by linarith : s / 2 ≤ σ) 3
    calc s ^ 3 / 8 = (s / 2) ^ 3 := by ring
      _ ≤ σ ^ 3 := h
  have h1 : (σ ^ 3)⁻¹ ≤ (s ^ 3 / 8)⁻¹ :=
    inv_anti₀ (div_pos (pow_pos hs 3) (by norm_num)) hsub
  have h2 : (s ^ 3 / 8)⁻¹ = 8 * (s ^ 3)⁻¹ := by
    rw [inv_div]; ring
  have hcm : 0 ≤ 32 * c * m := mul_nonneg (mul_nonneg (by norm_num) hc) hm
  calc 32 * c * m / σ ^ 3 = 32 * c * m * (σ ^ 3)⁻¹ := by ring
    _ ≤ 32 * c * m * ((s ^ 3 / 8)⁻¹) := mul_le_mul_of_nonneg_left h1 hcm
    _ = 256 * c * m * (s ^ 3)⁻¹ := by rw [h2]; ring

/-- The derivative bound along the segment, with `σ` any bound for the coordinates of `z(t)`. -/
theorem segD_bound (δ : ℝ) (hδ : |δ| ≤ 1) (i k : Fin 2) (x y : Fin 2 → ℝ) (t m σ : ℝ)
    (hm : 0 ≤ m) (hσ : 0 < σ) (hy : ∀ j, |y j| ≤ m)
    (ha : ∀ j, |segA x y t j| ≤ σ) (hQ : segQ x y t = σ * σ) :
    |segD δ i k x y t| ≤ 32 * (2 * Real.pi)⁻¹ * m / σ ^ 3 := by
  have hc : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hσ0 : 0 ≤ σ := hσ.le
  have hσne : σ ≠ 0 := hσ.ne'
  have hQd : |segQd x y t| ≤ 4 * σ * m := by
    have h0 : |segA x y t 0 * y 0| ≤ σ * m := by
      rw [abs_mul]; exact mul_le_mul (ha 0) (hy 0) (abs_nonneg _) hσ0
    have h1 : |segA x y t 1 * y 1| ≤ σ * m := by
      rw [abs_mul]; exact mul_le_mul (ha 1) (hy 1) (abs_nonneg _) hσ0
    have h0' := abs_le.1 h0
    have h1' := abs_le.1 h1
    unfold segQd
    rw [abs_le]
    constructor <;> linarith [h0'.1, h0'.2, h1'.1, h1'.2]
  have hNd : |segNd δ i k x y t| ≤ 8 * σ * m := by
    have h1 : |δ * segQd x y t| ≤ 4 * σ * m := by
      rw [abs_mul]
      calc |δ| * |segQd x y t| ≤ 1 * |segQd x y t| :=
            mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
        _ ≤ 4 * σ * m := by linarith
    have h2 : |y i * segA x y t k| ≤ σ * m := by
      rw [abs_mul, mul_comm σ m]
      exact mul_le_mul (hy i) (ha k) (abs_nonneg _) hm
    have h3 : |segA x y t i * y k| ≤ σ * m := by
      rw [abs_mul]; exact mul_le_mul (ha i) (hy k) (abs_nonneg _) hσ0
    have h1' := abs_le.1 h1
    have h2' := abs_le.1 h2
    have h3' := abs_le.1 h3
    unfold segNd
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, h3'.1, h3'.2]
  have hN : |segN δ i k x y t| ≤ 3 * (σ * σ) := by
    have hQabs : |segQ x y t| ≤ σ * σ := by
      rw [hQ, abs_of_nonneg (mul_self_nonneg σ)]
    have h1 : |δ * segQ x y t| ≤ σ * σ := by
      rw [abs_mul]
      calc |δ| * |segQ x y t| ≤ 1 * |segQ x y t| :=
            mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
        _ ≤ σ * σ := by linarith
    have h2 : |segA x y t i * segA x y t k| ≤ σ * σ := by
      rw [abs_mul]; exact mul_le_mul (ha i) (ha k) (abs_nonneg _) hσ0
    have h1' := abs_le.1 h1
    have h2' := abs_le.1 h2
    unfold segN
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hQabs : |segQ x y t| ≤ σ * σ := by
    rw [hQ, abs_of_nonneg (mul_self_nonneg σ)]
  have hQpos : 0 < segQ x y t := by rw [hQ]; exact mul_pos hσ hσ
  have hX : |segNd δ i k x y t * segQ x y t - 2 * (segN δ i k x y t * segQd x y t)| ≤
      32 * (σ ^ 3 * m) := by
    have e1 : |segNd δ i k x y t * segQ x y t| ≤ 8 * σ * m * (σ * σ) := by
      rw [abs_mul]
      exact mul_le_mul hNd hQabs (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hσ0) hm)
    have e2 : |segN δ i k x y t * segQd x y t| ≤ 3 * (σ * σ) * (4 * σ * m) := by
      rw [abs_mul]
      exact mul_le_mul hN hQd (abs_nonneg _) (by positivity)
    have e3 : |2 * (segN δ i k x y t * segQd x y t)| ≤ 2 * (3 * (σ * σ) * (4 * σ * m)) := by
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left e2 (by norm_num)
    have e1' := abs_le.1 e1
    have e3' := abs_le.1 e3
    rw [abs_le]
    constructor <;> linarith [e1'.1, e1'.2, e3'.1, e3'.2]
  have hD3 : 0 < segQ x y t ^ 3 := pow_pos hQpos 3
  unfold segD
  rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos hD3]
  calc (2 * Real.pi)⁻¹ * |segNd δ i k x y t * segQ x y t
        - 2 * (segN δ i k x y t * segQd x y t)| / segQ x y t ^ 3
      ≤ (2 * Real.pi)⁻¹ * (32 * (σ ^ 3 * m)) / segQ x y t ^ 3 := by
        gcongr
    _ = 32 * (2 * Real.pi)⁻¹ * m / σ ^ 3 := by
        rw [hQ]; field_simp

/-- Mean value bound for the kernel along the segment `x - t • y`, `t ∈ [0, 1]`. -/
theorem mvt_segment (δ : ℝ) (hδ : |δ| ≤ 1) (i k : Fin 2) (x y : Fin 2 → ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hy : ∀ j, |y j| ≤ m)
    (hs : 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x) :
    ‖segG δ i k x y 1 - segG δ i k x y 0‖ ≤
      256 * (2 * Real.pi)⁻¹ * m * (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 3)⁻¹ := by
  have hs0 : 0 < UnforcedLeray.CZ.anisoNorm planeWeight x := by linarith
  have hsqrt : ∀ t ∈ Icc (0 : ℝ) 1, 0 < Real.sqrt (segQ x y t) := fun t ht => by
    have := seg_lower x y hm hy ht hs
    linarith
  have hQne : ∀ t ∈ Icc (0 : ℝ) 1, segQ x y t ≠ 0 := fun t ht =>
    (Real.sqrt_pos.1 (hsqrt t ht)).ne'
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (segG δ i k x y) (segD δ i k x y t) (Icc (0 : ℝ) 1) t := fun t ht =>
    (hasDerivAt_segG δ i k x y t (hQne t ht)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖segD δ i k x y t‖ ≤ 256 * (2 * Real.pi)⁻¹ * m * (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 3)⁻¹ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hσ := hsqrt t ht'
    have hlow := seg_lower x y hm hy ht' hs
    have hQeq : segQ x y t = Real.sqrt (segQ x y t) * Real.sqrt (segQ x y t) :=
      (Real.mul_self_sqrt (hQ_nonneg x y t)).symm
    rw [Real.norm_eq_abs]
    refine (segD_bound δ hδ i k x y t m _ hm hσ hy (abs_segA_le x y t) hQeq).trans ?_
    exact div_sigma_le _ _ _ _ (by positivity) hm hs0 hlow
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := segG δ i k x y)
    (f' := fun t => segD δ i k x y t) hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
  rw [sub_zero, mul_one] at key
  exact key

/-! ### Pointwise and integrated Hörmander estimates -/

theorem pointwise_hormander (i k : Fin 2) (x y : Fin 2 → ℝ)
    (h : 2 * UnforcedLeray.CZ.anisoNorm planeWeight y < UnforcedLeray.CZ.anisoNorm planeWeight x) :
    ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ ≤
      256 * (2 * Real.pi)⁻¹ * UnforcedLeray.CZ.anisoNorm planeWeight y *
        (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 3)⁻¹ := by
  have hm : 0 ≤ UnforcedLeray.CZ.anisoNorm planeWeight y :=
    UnforcedLeray.CZ.anisoNorm_nonneg planeWeight y
  have hδ : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  have e1 := planeRieszKernel_segment i k x y 1
  have e0 := planeRieszKernel_segment i k x y 0
  simp only [one_smul, zero_smul, sub_zero] at e1 e0
  rw [e1, e0]
  exact mvt_segment _ hδ i k x y hm (abs_le_anisoNorm_plane y) h

theorem tail_bound {m : ℝ} (hm : 0 < m) :
    ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
      ENNReal.ofReal (UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(3 : ℝ))) ≤
      ENNReal.ofReal (16 / m) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hL := UnforcedLeray.CZ.lintegral_anisoNorm_rpow_neg_le planeWeight (b := 3) (R := 2 * m)
    (by rw [homDim_planeWeight]; norm_num) (by linarith)
  refine hL.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [homDim_planeWeight]
  have e : ((2 : ℕ) : ℝ) - 3 = -1 := by norm_num
  rw [e, Real.rpow_neg_one, Real.rpow_neg_one]
  field_simp
  ring

theorem planeRiesz_hormander (i k : Fin 2) (y : Fin 2 → ℝ) :
    ∫⁻ x in {x : Fin 2 → ℝ | 2 * UnforcedLeray.CZ.anisoNorm planeWeight y <
        UnforcedLeray.CZ.anisoNorm planeWeight x},
      ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ₑ ≤
        ENNReal.ofReal (4096 * (2 * Real.pi)⁻¹) := by
  set m := UnforcedLeray.CZ.anisoNorm planeWeight y with hmdef
  have hm : 0 ≤ m := UnforcedLeray.CZ.anisoNorm_nonneg planeWeight y
  have hc0 : (0 : ℝ) ≤ 256 * (2 * Real.pi)⁻¹ := by positivity
  have hSm : MeasurableSet {x : Fin 2 → ℝ | 2 * m <
      UnforcedLeray.CZ.anisoNorm planeWeight x} :=
    measurableSet_lt measurable_const (UnforcedLeray.CZ.measurable_anisoNorm planeWeight)
  have hpt : ∀ x ∈ {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
      ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ₑ ≤
        ENNReal.ofReal (256 * (2 * Real.pi)⁻¹ * m) *
          ENNReal.ofReal (UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(3 : ℝ))) := by
    intro x hx
    have hx' : 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x := hx
    have hs : 0 < UnforcedLeray.CZ.anisoNorm planeWeight x := by linarith
    have hpow : UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(3 : ℝ)) =
        (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hs.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← ENNReal.ofReal_mul (mul_nonneg hc0 hm), hpow, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (pointwise_hormander i k x y hx')
  by_cases hm0 : m = 0
  · calc ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
          ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ₑ
        ≤ ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x}, (0 : ENNReal) := by
          refine setLIntegral_mono' hSm fun x hx => ?_
          have := hpt x hx
          rw [hm0] at this
          simpa using this
      _ = 0 := by simp
      _ ≤ ENNReal.ofReal (4096 * (2 * Real.pi)⁻¹) := zero_le
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hm0' : m ≠ 0 := hmpos.ne'
    calc ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
          ‖planeRieszKernel i k (x - y) - planeRieszKernel i k x‖ₑ
        ≤ ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
            ENNReal.ofReal (256 * (2 * Real.pi)⁻¹ * m) *
              ENNReal.ofReal (UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(3 : ℝ))) :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (256 * (2 * Real.pi)⁻¹ * m) *
            ∫⁻ x in {x : Fin 2 → ℝ | 2 * m < UnforcedLeray.CZ.anisoNorm planeWeight x},
              ENNReal.ofReal (UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(3 : ℝ))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (256 * (2 * Real.pi)⁻¹ * m) * ENNReal.ofReal (16 / m) :=
          by gcongr; exact tail_bound hmpos
      _ = ENNReal.ofReal (4096 * (2 * Real.pi)⁻¹) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hc0 hm)]
          congr 1
          field_simp
          ring

/-- Size bound `|K_ik(x)| ≤ 3 (2π)⁻¹ |x|_∞^{-2}` for `x ≠ 0`. -/
theorem planeRieszKernel_size (i k : Fin 2) (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    |planeRieszKernel i k x| ≤
      3 * (2 * Real.pi)⁻¹ *
        UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-(UnforcedLeray.CZ.homDim planeWeight : ℝ)) := by
  rw [homDim_planeWeight, planeRieszKernel_eq]
  have hc : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hs : 0 < UnforcedLeray.CZ.anisoNorm planeWeight x :=
    UnforcedLeray.CZ.anisoNorm_pos planeWeight hx
  have hsQ : UnforcedLeray.CZ.anisoNorm planeWeight x ≤
      Real.sqrt (x 0 * x 0 + x 1 * x 1) :=
    anisoNorm_plane_le (Real.sqrt_nonneg _) (abs_le_sqrt_sum x)
  have hQpos : 0 < x 0 * x 0 + x 1 * x 1 := Real.sqrt_pos.1 (lt_of_lt_of_le hs hsQ)
  have hQ0 : 0 ≤ x 0 * x 0 + x 1 * x 1 := hQpos.le
  have hs2 : UnforcedLeray.CZ.anisoNorm planeWeight x ^ 2 ≤ x 0 * x 0 + x 1 * x 1 := by
    have h := pow_le_pow_left₀ hs.le hsQ 2
    rwa [Real.sq_sqrt hQ0] at h
  have hδ : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  have hprod : |x i * x k| ≤ x 0 * x 0 + x 1 * x 1 := by
    rw [abs_mul]
    calc |x i| * |x k| ≤ Real.sqrt (x 0 * x 0 + x 1 * x 1) * Real.sqrt (x 0 * x 0 + x 1 * x 1) :=
          mul_le_mul (abs_le_sqrt_sum x i) (abs_le_sqrt_sum x k) (abs_nonneg _)
            (Real.sqrt_nonneg _)
      _ = x 0 * x 0 + x 1 * x 1 := Real.mul_self_sqrt hQ0
  have hδQ : |(if i = k then (1 : ℝ) else 0) * (x 0 * x 0 + x 1 * x 1)| ≤
      x 0 * x 0 + x 1 * x 1 := by
    rw [abs_mul, abs_of_nonneg hQ0]
    exact mul_le_of_le_one_left hQ0 hδ
  have hN : |(if i = k then (1 : ℝ) else 0) * (x 0 * x 0 + x 1 * x 1) - 2 * (x i * x k)| ≤
      3 * (x 0 * x 0 + x 1 * x 1) := by
    have h1 := abs_le.1 hδQ
    have h2 := abs_le.1 hprod
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hr : UnforcedLeray.CZ.anisoNorm planeWeight x ^ (-((2 : ℕ) : ℝ)) =
      (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 2)⁻¹ := by
    rw [show -((2 : ℕ) : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hs.le, Real.rpow_two]
  rw [hr]
  have hQQ : 0 ≤ (x 0 * x 0 + x 1 * x 1) * (x 0 * x 0 + x 1 * x 1) := mul_self_nonneg _
  calc |(2 * Real.pi)⁻¹ * ((if i = k then (1 : ℝ) else 0) * (x 0 * x 0 + x 1 * x 1)
        - 2 * (x i * x k)) / ((x 0 * x 0 + x 1 * x 1) * (x 0 * x 0 + x 1 * x 1))|
      = (2 * Real.pi)⁻¹ * |(if i = k then (1 : ℝ) else 0) * (x 0 * x 0 + x 1 * x 1)
        - 2 * (x i * x k)| / ((x 0 * x 0 + x 1 * x 1) * (x 0 * x 0 + x 1 * x 1)) := by
        rw [abs_div, abs_mul, abs_of_pos hc, abs_of_nonneg hQQ]
    _ ≤ (2 * Real.pi)⁻¹ * (3 * (x 0 * x 0 + x 1 * x 1)) /
          ((x 0 * x 0 + x 1 * x 1) * (x 0 * x 0 + x 1 * x 1)) := by
        gcongr
    _ = 3 * (2 * Real.pi)⁻¹ * (x 0 * x 0 + x 1 * x 1)⁻¹ := by
        field_simp
    _ ≤ 3 * (2 * Real.pi)⁻¹ * (UnforcedLeray.CZ.anisoNorm planeWeight x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hs 2) hs2) (by positivity)

end PlaneRieszKernelCZProof

open PlaneRieszKernelCZProof

theorem planeRieszKernelCZ : PlaneRieszKernelCZ := by
  have hc : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have hB : (0 : ℝ) ≤ 3 * (2 * Real.pi)⁻¹ + 4096 * (2 * Real.pi)⁻¹ := by positivity
  refine ⟨Real.toNNReal (3 * (2 * Real.pi)⁻¹ + 4096 * (2 * Real.pi)⁻¹), fun i k => ?_⟩
  have hBc : ((Real.toNNReal (3 * (2 * Real.pi)⁻¹ + 4096 * (2 * Real.pi)⁻¹) : ℝ≥0) : ℝ) =
      3 * (2 * Real.pi)⁻¹ + 4096 * (2 * Real.pi)⁻¹ := Real.coe_toNNReal _ hB
  refine ⟨?_, ?_, ?_⟩
  · rw [show planeRieszKernel i k = fun z => (2 * Real.pi)⁻¹ *
        ((if i = k then (1 : ℝ) else 0) * (z 0 * z 0 + z 1 * z 1) - 2 * (z i * z k)) /
          ((z 0 * z 0 + z 1 * z 1) * (z 0 * z 0 + z 1 * z 1)) from
        funext (planeRieszKernel_eq i k)]
    fun_prop
  · intro x hx
    rw [hBc]
    have h1 := planeRieszKernel_size i k x hx
    have hr : 0 ≤ UnforcedLeray.CZ.anisoNorm planeWeight x ^
        (-(UnforcedLeray.CZ.homDim planeWeight : ℝ)) :=
      Real.rpow_nonneg (UnforcedLeray.CZ.anisoNorm_nonneg planeWeight x) _
    have h2 : 0 ≤ 4096 * (2 * Real.pi)⁻¹ * UnforcedLeray.CZ.anisoNorm planeWeight x ^
        (-(UnforcedLeray.CZ.homDim planeWeight : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hc) hr
    nlinarith [h1, h2]
  · intro y
    refine le_trans (planeRiesz_hormander i k y) ?_
    rw [← ENNReal.ofReal_coe_nnreal, hBc]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end UnforcedLeray.Short.IIb
