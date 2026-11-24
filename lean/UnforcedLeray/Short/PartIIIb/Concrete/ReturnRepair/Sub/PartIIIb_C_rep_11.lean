import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# Decomposition of `nearBody` (`PartIII-b:C/rep/11`, source 5540-5547, 5551-5552, 5621-5622)

`nearBody_of` assembles `NearBody` from the two operator-norm estimates it uses:
`RopFreeBodyBound` (the free body bound of 1351-1362 transported through `NearInst.bodyG`, with
`g ≥ 1`) and `MultOpNormBound` (the split multiplier bound 2706-2713 transported by `NearOps.MG`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **The body inverse is `P_ν`-bounded on the return spaces** (source 1351-1362, the free body bound
for `T_ε = (μ - A_ε)⁻¹P_ε`, in real form `bodyReps`; `bodyG` conjugates by the gain `g ≥ 1`, and the
input carries no gain, 4116-4118): `‖R_μ f‖ ≤ C ν^{-k} ‖f‖`. -/
def RopFreeBodyBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ f : LSrc (D.level n),
    ‖Rop D.Pl (D.level n) (D.mu n z) f‖ ≤ C * (D.level n).ν⁻¹ ^ k * ‖f‖

/-- **The split multiplier is `P_ν`-bounded on the return spaces** (source 2706-2713, 3876-3878,
`SplitMultBound`, transported by `NearOps.MG`): `‖M_U w‖ ≤ C ν^{-k} ‖w‖`. -/
def MultOpNormBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ w : LVel D.Pl (D.level n),
    ‖multOp D.Pl D.K (D.level n) w‖ ≤ C * (D.level n).ν⁻¹ ^ k * ‖w‖

theorem nearBody_of (hω : D.Pl.eigenvalue.im ≠ 0) (hR : D.RopFreeBodyBound)
    (hM : D.MultOpNormBound) : D.NearBody := by
  obtain ⟨C1, k1, h1⟩ := hR
  obtain ⟨C2, k2, h2⟩ := hM
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hω).eventually_lt_const one_pos).mono fun n h => h.le
  refine ⟨|C1| * |C2| + |C1|, k1 + k2, ?_⟩
  filter_upwards [h1, h2, hν1] with n hn1 hn2 hn3 z hz f
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hn3
  have hi : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hν).2 hν1'
  have hp : 0 < (D.level n).ν⁻¹ := inv_pos.2 hν
  have b1 := hn1 z hz f
  have b2 := hn2 (Rop D.Pl (D.level n) (D.mu n z) f)
  have hf := norm_nonneg f
  have hpk : ∀ k : ℕ, 0 < (D.level n).ν⁻¹ ^ k := fun k => pow_pos hp k
  have hmono : (D.level n).ν⁻¹ ^ k1 ≤ (D.level n).ν⁻¹ ^ (k1 + k2) :=
    pow_le_pow_right₀ hi (Nat.le_add_right _ _)
  have hC1 : C1 ≤ |C1| := le_abs_self _
  have hC2 : C2 ≤ |C2| := le_abs_self _
  have hnn1 : 0 ≤ |C1| := abs_nonneg _
  have hnn2 : 0 ≤ |C2| := abs_nonneg _
  constructor
  · calc ‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) f)‖
        ≤ C2 * (D.level n).ν⁻¹ ^ k2 * ‖Rop D.Pl (D.level n) (D.mu n z) f‖ := b2
      _ ≤ |C2| * (D.level n).ν⁻¹ ^ k2 * (C1 * (D.level n).ν⁻¹ ^ k1 * ‖f‖) := by
          have := hpk k2
          have hR : ‖Rop D.Pl (D.level n) (D.mu n z) f‖ ≤ C1 * (D.level n).ν⁻¹ ^ k1 * ‖f‖ := b1
          have hC2' : C2 * (D.level n).ν⁻¹ ^ k2 ≤ |C2| * (D.level n).ν⁻¹ ^ k2 :=
            mul_le_mul_of_nonneg_right hC2 this.le
          have hnorm := norm_nonneg (Rop D.Pl (D.level n) (D.mu n z) f)
          calc C2 * (D.level n).ν⁻¹ ^ k2 * ‖Rop D.Pl (D.level n) (D.mu n z) f‖
              ≤ |C2| * (D.level n).ν⁻¹ ^ k2 * ‖Rop D.Pl (D.level n) (D.mu n z) f‖ :=
                mul_le_mul_of_nonneg_right hC2' hnorm
            _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
      _ ≤ |C2| * (D.level n).ν⁻¹ ^ k2 * (|C1| * (D.level n).ν⁻¹ ^ k1 * ‖f‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : C1 * (D.level n).ν⁻¹ ^ k1 ≤ |C1| * (D.level n).ν⁻¹ ^ k1 :=
            mul_le_mul_of_nonneg_right hC1 (hpk k1).le
          exact mul_le_mul_of_nonneg_right this hf
      _ = |C1| * |C2| * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by rw [pow_add]; ring
      _ ≤ (|C1| * |C2| + |C1|) * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by
          have := hpk (k1 + k2)
          have : 0 ≤ |C1| * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by positivity
          nlinarith
  · calc ‖Rop D.Pl (D.level n) (D.mu n z) f‖ ≤ C1 * (D.level n).ν⁻¹ ^ k1 * ‖f‖ := b1
      _ ≤ |C1| * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by
          apply mul_le_mul_of_nonneg_right _ hf
          calc C1 * (D.level n).ν⁻¹ ^ k1 ≤ |C1| * (D.level n).ν⁻¹ ^ k1 :=
                mul_le_mul_of_nonneg_right hC1 (hpk k1).le
            _ ≤ _ := mul_le_mul_of_nonneg_left hmono hnn1
      _ ≤ (|C1| * |C2| + |C1|) * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by
          have := hpk (k1 + k2)
          have : 0 ≤ |C1| * |C2| * (D.level n).ν⁻¹ ^ (k1 + k2) * ‖f‖ := by positivity
          nlinarith

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
