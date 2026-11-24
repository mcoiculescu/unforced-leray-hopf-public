import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv

/-!
# `PartIII-b:C/rep/4/1/org/2/1` (d): the age integral of the thin-source velocity

Source `the November 2 reference manuscript` 5347-5353 ("its square is integrable at
zero, and the integral up to `S` is polynomial in `S`"): with `N₀(e^δ s) ≤ C((e^δ s)^{-3/4} +
(e^δ s)^{-1/2})‖T‖_{Z₁}` (5573-5576) the density of the output stress is
`s^{-3/2}E²(K s²(a^{-3/4}+a^{-1/2})Z)²`, `a = e^δ s ≥ s`, and
`s^{-3/2}(s²(s^{-3/4}+s^{-1/2}))² = s(1+s^{1/4})² ≤ 4S^{3/2}` on `(0,S)`, `S ≥ 1`; the integral
over `(0,S)` is at most `4E²K²S^{5/2}Z²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FTT

/-- The elementary bound `s^{-3/2}(s²(s^{-3/4}+s^{-1/2}))² ≤ 4S^{3/2}` for `0 < s < S`, `1 ≤ S`. -/
theorem real_bound {s S : ℝ} (hs : 0 < s) (hsS : s < S) (hS : 1 ≤ S) :
    s ^ (-3 / 2 : ℝ) * (s ^ (2 : ℝ) * (s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ))) ^ 2 ≤
      4 * S ^ (3 / 2 : ℝ) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = s ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hS0 : 0 < S := by linarith
  have hw1 : 1 ≤ w := by rw [hw]; exact Real.one_le_rpow hS (by norm_num)
  have hu4 : u ^ 4 = s := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hw4 : w ^ 4 = S := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
  have hw6 : w ^ 6 = S ^ (3 / 2 : ℝ) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
  have huw : u < w := by
    have : u ^ 4 < w ^ 4 := by rw [hu4, hw4]; exact hsS
    exact lt_of_pow_lt_pow_left₀ 4 (by linarith) this
  have hpow : ∀ n : ℕ, s ^ ((n : ℝ) / 4) = u ^ n := by
    intro n
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have e1 : s ^ (-3 / 2 : ℝ) = (u ^ 6)⁻¹ := by
    rw [show (-3 / 2 : ℝ) = -(((6 : ℕ) : ℝ) / 4) by norm_num, Real.rpow_neg hs.le, hpow]
  have e2 : s ^ (-3 / 4 : ℝ) = (u ^ 3)⁻¹ := by
    rw [show (-3 / 4 : ℝ) = -(((3 : ℕ) : ℝ) / 4) by norm_num, Real.rpow_neg hs.le, hpow]
  have e3 : s ^ (-1 / 2 : ℝ) = (u ^ 2)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(((2 : ℕ) : ℝ) / 4) by norm_num, Real.rpow_neg hs.le, hpow]
  have e4 : s ^ (2 : ℝ) = u ^ 8 := by
    rw [show (2 : ℝ) = (((8 : ℕ) : ℝ) / 4) by norm_num, hpow]
  rw [e1, e2, e3, e4]
  have key : (u ^ 6)⁻¹ * (u ^ 8 * ((u ^ 3)⁻¹ + (u ^ 2)⁻¹)) ^ 2 = u ^ 4 * (1 + u) ^ 2 := by
    field_simp
  rw [key, ← hw6]
  have h1 : u ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ hu0.le huw.le 4
  have h2 : (1 + u) ^ 2 ≤ (2 * w) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc u ^ 4 * (1 + u) ^ 2 ≤ w ^ 4 * (2 * w) ^ 2 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 4 * w ^ 6 := by ring

/-- **The age integral** (source 5347-5353): polynomial in `S`. -/
theorem age_integral {S δ E K1 : ℝ} (hS : 1 ≤ S) (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hK : 0 ≤ K1)
    (Z : ℝ≥0∞) :
    ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) * Z) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * E ^ 2 * K1 ^ 2 * S ^ (5 / 2 : ℝ)) * Z ^ (2 : ℝ) := by
  have hS0 : 0 < S := by linarith
  have hpt : ∀ s ∈ Ioo (0 : ℝ) S, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) * Z) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ)) * Z ^ (2 : ℝ) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have ha : s ≤ Real.exp δ * s := by
      have := Real.one_le_exp hδ
      nlinarith
    have hB : (Real.exp δ * s) ^ (-3 / 4 : ℝ) + (Real.exp δ * s) ^ (-1 / 2 : ℝ) ≤
        s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ) :=
      add_le_add (Real.rpow_le_rpow_of_nonpos hs0 ha (by norm_num))
        (Real.rpow_le_rpow_of_nonpos hs0 ha (by norm_num))
    have hB0 : 0 ≤ (Real.exp δ * s) ^ (-3 / 4 : ℝ) + (Real.exp δ * s) ^ (-1 / 2 : ℝ) := by
      have : 0 < Real.exp δ * s := mul_pos (Real.exp_pos δ) hs0
      positivity
    have hX : K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) + (Real.exp δ * s) ^ (-1 / 2 : ℝ)) ≤
        K1 * (s ^ (2 : ℝ) * (s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ))) := by
      rw [show s ^ 2 = s ^ (2 : ℝ) by norm_cast, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hB (by positivity)
    have hX0 : 0 ≤ K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
        (Real.exp δ * s) ^ (-1 / 2 : ℝ)) := by positivity
    have hreal : s ^ (-3 / 2 : ℝ) * E ^ 2 * (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) ^ 2 ≤ 4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ) := by
      have hr := real_bound hs0 hs.2 hS
      have h1 : (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) ^ 2 ≤
          K1 ^ 2 * (s ^ (2 : ℝ) * (s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ))) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hX0 hX 2
      have hs32 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
      calc s ^ (-3 / 2 : ℝ) * E ^ 2 * (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
            (Real.exp δ * s) ^ (-1 / 2 : ℝ))) ^ 2
          ≤ s ^ (-3 / 2 : ℝ) * E ^ 2 * (K1 ^ 2 * (s ^ (2 : ℝ) *
              (s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ))) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = E ^ 2 * K1 ^ 2 * (s ^ (-3 / 2 : ℝ) * (s ^ (2 : ℝ) *
              (s ^ (-3 / 4 : ℝ) + s ^ (-1 / 2 : ℝ))) ^ 2) := by ring
        _ ≤ E ^ 2 * K1 ^ 2 * (4 * S ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ = 4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ) := by ring
    -- back to `ℝ≥0∞`
    have e : ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) * Z) ^ (2 : ℝ) =
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * E ^ 2 * (K1 * s ^ 2 * ((Real.exp δ * s) ^ (-3 / 4 : ℝ) +
          (Real.exp δ * s) ^ (-1 / 2 : ℝ))) ^ 2) * Z ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hE (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num), Real.rpow_two, Real.rpow_two,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le
  calc _ ≤ ∫⁻ s in Ioo (0 : ℝ) S, ENNReal.ofReal (4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ)) * Z ^ (2 : ℝ) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal (4 * E ^ 2 * K1 ^ 2 * S ^ (5 / 2 : ℝ)) * Z ^ (2 : ℝ) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
        have : 4 * E ^ 2 * K1 ^ 2 * S ^ (5 / 2 : ℝ) =
            4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ) * S := by
          rw [mul_assoc (4 * E ^ 2 * K1 ^ 2), ← Real.rpow_add_one hS0.ne']
          norm_num
        rw [this, ENNReal.ofReal_mul (show 0 ≤ 4 * E ^ 2 * K1 ^ 2 * S ^ (3 / 2 : ℝ) by positivity)]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.FTT

end
