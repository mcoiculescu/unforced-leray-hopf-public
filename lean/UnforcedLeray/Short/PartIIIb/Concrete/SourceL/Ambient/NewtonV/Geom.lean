import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# Geometry of the zero-width Newton field (helper of `Ambient/NewtonV.lean`)

Source 4776-4782: for `|x'|² ≤ 5ν/6` and `|w|² > 11ν/12` the shifted point `w - t(x',0)`,
`t ∈ [0,1]`, satisfies `|w - t(x',0)| ≥ (1 - √(10/11)) |w|`; hence `|z|^{-4-m} ≤ a^{-4-m}|w|^{-4-m}`
for `z = w - t(x',0)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonVGeom

theorem eucSq_nonneg (w : Vec3) : 0 ≤ eucSq w := Finset.sum_nonneg fun i _ => sq_nonneg (w i)

theorem sum_mul_le_sqrt (u v : Vec3) :
    ∑ i, u i * v i ≤ Real.sqrt (eucSq u) * Real.sqrt (eucSq v) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hprod : Real.sqrt (eucSq u) * Real.sqrt (eucSq v) = Real.sqrt (eucSq u * eucSq v) :=
    (Real.sqrt_mul (eucSq_nonneg u) _).symm
  rw [hprod]
  have h' : (∑ i, u i * v i) ^ 2 ≤ eucSq u * eucSq v := h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h')

theorem sqrt_sub_le (u v : Vec3) :
    Real.sqrt (eucSq u) - Real.sqrt (eucSq v) ≤ Real.sqrt (eucSq (u - v)) := by
  have hexp : eucSq (u - v) = eucSq u - 2 * ∑ i, u i * v i + eucSq v := by
    have h1 : ∀ i, (u - v) i ^ 2 = u i ^ 2 - 2 * (u i * v i) + v i ^ 2 := fun i => by
      simp only [Pi.sub_apply]; ring
    unfold eucSq
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs := sum_mul_le_sqrt u v
  have ha : Real.sqrt (eucSq u) ^ 2 = eucSq u := Real.sq_sqrt (eucSq_nonneg u)
  have hb : Real.sqrt (eucSq v) ^ 2 = eucSq v := Real.sq_sqrt (eucSq_nonneg v)
  have key : (Real.sqrt (eucSq u) - Real.sqrt (eucSq v)) ^ 2 ≤ eucSq (u - v) := by
    rw [hexp]; nlinarith [hs, ha, hb]
  exact (le_abs_self _).trans (Real.abs_le_sqrt key)

theorem sqrt_eucSq_smul {t : ℝ} (ht : 0 ≤ t) (e : Vec3) :
    Real.sqrt (eucSq (t • e)) = t * Real.sqrt (eucSq e) := by
  have h : eucSq (t • e) = t ^ 2 * eucSq e := by
    unfold eucSq
    simp [Finset.mul_sum, mul_pow]
  rw [h, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

theorem eucSq_embPlane (x' : ℝ × ℝ) : eucSq (embPlane x') = x'.1 ^ 2 + x'.2 ^ 2 := by
  simp [eucSq, embPlane, Fin.sum_univ_three]

theorem sqrt_one_tenth_elevenths_lt : Real.sqrt (10 / 11) < 1 := by
  rw [Real.sqrt_lt' one_pos]; norm_num

/-- Geometric lower bound (source 4776-4782): `|w - t(x',0)| ≥ (1 - √(10/11)) |w|`. -/
theorem shift_lower {ν t : ℝ} {w : Vec3} {x' : ℝ × ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : ν * (11 / 12) < eucSq w) (hx : x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6) :
    (1 - Real.sqrt (10 / 11)) * Real.sqrt (eucSq w) ≤
      Real.sqrt (eucSq (w - t • embPlane x')) := by
  have he : eucSq (embPlane x') = x'.1 ^ 2 + x'.2 ^ 2 := eucSq_embPlane x'
  have h0 : 0 ≤ eucSq (embPlane x') := eucSq_nonneg _
  have h1 := sqrt_sub_le w (t • embPlane x')
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hE : eucSq (embPlane x') ≤ 5 * ν / 6 := by rw [he]; exact hx
  have hte : eucSq (t • embPlane x') ≤ 5 * ν / 6 := by
    have hsc : eucSq (t • embPlane x') = t ^ 2 * eucSq (embPlane x') := by
      unfold eucSq
      simp [Finset.mul_sum, mul_pow]
    rw [hsc]
    calc t ^ 2 * eucSq (embPlane x') ≤ 1 * eucSq (embPlane x') :=
          mul_le_mul_of_nonneg_right ht2 h0
      _ ≤ 5 * ν / 6 := by rw [one_mul]; exact hE
  have h2 : Real.sqrt (eucSq (t • embPlane x')) ≤ Real.sqrt (5 * ν / 6) :=
    Real.sqrt_le_sqrt hte
  have h3 : Real.sqrt (5 * ν / 6) ≤ Real.sqrt (10 / 11) * Real.sqrt (eucSq w) := by
    rw [show 5 * ν / 6 = (10 / 11) * (11 * ν / 12) by ring, Real.sqrt_mul (by norm_num)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  rw [sub_mul, one_mul]
  linarith

/-- Monotonicity of `z ↦ z^p` for `p ≤ 0`, on the shifted lower bound. -/
theorem rpow_neg_shift {a X Z p : ℝ} (ha : 0 < a) (hX : 0 < X) (hZ : a * X ≤ Z) (hp : p ≤ 0) :
    Z ^ p ≤ a ^ p * X ^ p := by
  rw [← Real.mul_rpow ha.le hX.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hX) hZ hp

/-- Shifted derivative bound (source 4776-4782): the `m`-th derivative of `x ↦ D³N(x - t(x',0))`
at `w` is bounded by `K |w|^{-4-m}` on the receiver region, `K` independent of `ν, t, w, x'`. -/
theorem newtonD3_shift_bound (m : ℕ) : ∃ K : ℝ, ∀ (ν t : ℝ) (w : Vec3) (x' : ℝ × ℝ) (i j k : Fin 3),
    0 < ν → 0 ≤ t → t ≤ 1 → ν * (11 / 12) < eucSq w → x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
    ‖iteratedFDeriv ℝ m (fun x => newtonD3 (x - t • embPlane x') i j k) w‖ ≤
      K * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
  obtain ⟨C, hC⟩ := newtonD3_bound m
  refine ⟨|C| * (1 - Real.sqrt (10 / 11)) ^ (-(4 : ℝ) - m), ?_⟩
  intro ν t w x' i j k hν ht0 ht1 hw hx
  have ha : 0 < 1 - Real.sqrt (10 / 11) := by linarith [sqrt_one_tenth_elevenths_lt]
  have hwpos : 0 < eucSq w := by linarith
  have hX : 0 < Real.sqrt (eucSq w) := Real.sqrt_pos.2 hwpos
  have hlow := shift_lower ht0 ht1 hw hx
  have hZpos : 0 < Real.sqrt (eucSq (w - t • embPlane x')) := lt_of_lt_of_le (mul_pos ha hX) hlow
  have hz0 : w - t • embPlane x' ≠ 0 := by
    intro h
    rw [h] at hZpos
    simp [eucSq] at hZpos
  have hb := hC (w - t • embPlane x') hz0 i j k
  have hsh : iteratedFDeriv ℝ m (fun x => newtonD3 (x - t • embPlane x') i j k) w =
      iteratedFDeriv ℝ m (fun x => newtonD3 x i j k) (w - t • embPlane x') :=
    iteratedFDeriv_comp_sub (f := fun x => newtonD3 x i j k) m _ w
  have hp : -(4 : ℝ) - m ≤ 0 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [hsh]
  calc ‖iteratedFDeriv ℝ m (fun x => newtonD3 x i j k) (w - t • embPlane x')‖
      ≤ C * (Real.sqrt (eucSq (w - t • embPlane x'))) ^ (-(4 : ℝ) - m) := hb.2
    _ ≤ |C| * (Real.sqrt (eucSq (w - t • embPlane x'))) ^ (-(4 : ℝ) - m) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hZpos.le _)
    _ ≤ |C| * ((1 - Real.sqrt (10 / 11)) ^ (-(4 : ℝ) - m) *
          (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
        mul_le_mul_of_nonneg_left (rpow_neg_shift ha hX hlow hp) (abs_nonneg C)
    _ = |C| * (1 - Real.sqrt (10 / 11)) ^ (-(4 : ℝ) - m) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
        ring

end NewtonVGeom

end UnforcedLeray.Short.PartIIIb.Concrete
