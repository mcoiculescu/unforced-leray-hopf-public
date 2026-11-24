import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `RawD1Bound1`: the `j = 1` bound of the raw ring derivative (`PartIII-b:C/rep/8/2/1/2/8`, (B1))

Source `the November 2 reference manuscript`,
lines 5462-5476 (chain rule through `(age, phase, trans)`) and 2073-2077 (`U_raw`).

The `j = 1` (hoop) component of `D_flat v` vanishes, since `flatDir 1 = (0,0)`, so the target is
`ε s |b₀| = ε s |v₁|` with `b₀ = bRaw L p 0 = v 0` (`rawProfile_zero`), and `|v₁|` is bounded by
the `j = 0` term of the weight `trainWeight 3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- The zeroth-order part of the weight: `|v₀(s, x)| ≤ 𝔴₃(s, x)` (the `j = 0` term of the sum,
times `(1 + |η|)³ ≥ 1`). -/
theorem rawD1_abs_v0_le (L : ReturnLevel) (p : Chart) (hp0 : 0 < p.1) :
    |L.train.v p.1 p.2 0| ≤ trainWeight 3 L p := by
  have hz : trainFv L (Real.log p.1, p.2) = L.train.v p.1 p.2 := by
    unfold trainFv
    rw [Real.exp_log hp0]
  have h0 : ‖iteratedFDeriv ℝ 0 (trainFv L) (Real.log p.1, p.2)‖ = ‖L.train.v p.1 p.2‖ := by
    rw [norm_iteratedFDeriv_zero, hz]
  have hf := Finset.single_le_sum
    (f := fun j : ℕ => ‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖)
    (fun j _ => by positivity) (Finset.mem_range.2 (by norm_num : (0 : ℕ) < 5))
  have hnn : 0 ≤ ∑ j ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hpow : (1 : ℝ) ≤ (1 + |p.2.2|) ^ 3 :=
    one_le_pow₀ (by linarith [abs_nonneg p.2.2])
  have hcomp : |L.train.v p.1 p.2 0| ≤ ‖L.train.v p.1 p.2‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (L.train.v p.1 p.2) 0
  have hsum : ‖L.train.v p.1 p.2‖ ≤ ∑ j ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) := by
    have hB := norm_nonneg (iteratedFDeriv ℝ 0 (trainFp L) (Real.log p.1, p.2))
    have hC := norm_nonneg (iteratedFDeriv ℝ 0 (trainFpsi L) (Real.log p.1, p.2))
    rw [← h0]
    linarith
  unfold trainWeight
  calc |L.train.v p.1 p.2 0| ≤ ‖L.train.v p.1 p.2‖ := hcomp
    _ ≤ _ := hsum
    _ ≤ (1 + |p.2.2|) ^ 3 * ∑ j ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
      le_mul_of_one_le_left hnn hpow

theorem rawD1Bound1 : RawD1Bound1 := by
  refine ⟨1, fun L hε p hp0 => ?_⟩
  have hd : flatDir 1 = 0 := by
    simp [flatDir]
  have hflat : flatD1 L p.1 p.2 1 = 0 := by
    unfold flatD1
    rw [hd, map_zero]
    funext i
    fin_cases i <;> simp [emb]
  have hz : p.1 • vecSp (flatD1 L p.1 p.2 1) = 0 := by
    rw [hflat]
    simp [vecSp]
  have hnorm : ‖vecSp ![0, L.ε * p.1 * bRaw L p 0, 0]‖ = |L.ε * p.1 * bRaw L p 0| := by
    simp [vecSp, EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_sq_eq_abs]
  rw [hz, sub_zero, hnorm]
  have hεs : 0 < L.ε * p.1 := mul_pos L.ε_pos hp0
  have hb : bRaw L p 0 = L.train.v p.1 p.2 0 := by
    unfold bRaw
    exact UnforcedLeray.Cons.C03.rawProfile_zero _ _ _ _
  rw [hb, abs_mul, abs_of_pos hεs, one_mul]
  exact mul_le_mul_of_nonneg_left (rawD1_abs_v0_le L p hp0) hεs.le

end UnforcedLeray.Short.PartIIIb.Concrete
