import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1

/-!
# Spine: leaf 3, `MildBase` (level 0 of a mild curve)

Proves `MildBase` (`Sub/SP_CAN4_1.lean`, task `Spine:SP-CAN/4/1`, leaf 3): every mild solution `V`
has `MildLevel V 0`, i.e. `V θ ∈ X_G` for `θ > 0` and `‖V s‖_{X_G}` is bounded on each compact
`[α, β] ⊂ (0, ∞)`.

Source of record: `the November 2 reference manuscript` line 1086 and lines
1127-1131 (`sup_{0<θ≤b} ‖V(θ)‖ ≤ e^{b‖L‖} ‖V(b)‖`).

Route: `X_{G,0} = ⊤` (`B0123.XGj_zero`); for `f ∈ X_{G,0}` the graph norm is `√(2) ‖f‖`, because
`IDpow 0` multiplies the `ℓ`-th coefficient by `1` (`B0123.hasSum_norm_IDpow_sq` and
`B0123.hasSum_norm_inner_sq` give the same sum, hence the same value); and
`V s = S(s, β) (V β)` for `0 < s ≤ β` (`IsMildOnPos`) with `‖S(s, β)‖ ≤ e^{‖L₀‖(β - s)}`
(`UnforcedLeray.Cons.G3b.norm_S_le`).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 3, level 0** (shorter proof lines 1086, 1127-1131): a mild solution is bounded in `X_G`
on compact subintervals of `(0, ∞)`. -/
theorem mildBase_proof : MildBase := by
  intro V hV
  unfold MildLevel
  refine ⟨fun s _ => ?_, fun α β hα _ => ?_⟩
  · -- `X_{G,0} = ⊤`
    rw [B0123.XGj_zero]
    exact Submodule.mem_top
  · -- on `X_{G,0}` the graph norm is `√(‖f‖² + ‖f‖²) = √2 ‖f‖`
    have hnorm : ∀ (f : XG) (h : f ∈ B0123.XGj 0),
        B0123.xgjNorm 0 ⟨f, h⟩ = Real.sqrt (‖f‖ ^ 2 + ‖f‖ ^ 2) := by
      intro f h
      have hs : ((0 : ℕ) : ℝ) / 2 = 0 := by norm_num
      have hpow : ∀ n : ℕ, ((1 + (n : ℝ)) ^ (((0 : ℕ) : ℝ) / 2)) ^ 2 = 1 := by
        intro n
        rw [hs, Real.rpow_zero]
        norm_num
      have h1 := B0123.hasSum_norm_IDpow_sq (((0 : ℕ) : ℝ) / 2) ⟨f, h⟩
      simp only [hpow, one_mul] at h1
      have h2 := B0123.hasSum_norm_inner_sq UnforcedLeray.B0094.oscBasis f
      have h3 : ‖B0123.IDpow (((0 : ℕ) : ℝ) / 2) ⟨f, h⟩‖ ^ 2 = ‖f‖ ^ 2 := h1.unique h2
      show Real.sqrt (‖f‖ ^ 2 + ‖B0123.IDpow (((0 : ℕ) : ℝ) / 2) ⟨f, h⟩‖ ^ 2) = _
      rw [h3]
    -- the level-0 bound `‖V s‖ ≤ e^{β‖L₀‖} ‖V β‖` on `[α, β]`
    have hbound : ∀ s ∈ Icc α β,
        ‖V s‖ ≤ Real.exp (‖UnforcedLeray.B0012.L0‖ * β) * ‖V β‖ := by
      intro s hs
      obtain ⟨hsα, hsβ⟩ := Set.mem_Icc.mp hs
      have hs0 : 0 < s := lt_of_lt_of_le hα hsα
      have hVs : V s = UnforcedLeray.Cons.G3b.S s β (V β) := hV s β hs0 hsβ
      rw [hVs]
      calc ‖UnforcedLeray.Cons.G3b.S s β (V β)‖
          ≤ ‖UnforcedLeray.Cons.G3b.S s β‖ * ‖V β‖ :=
            (UnforcedLeray.Cons.G3b.S s β).le_opNorm (V β)
        _ ≤ Real.exp (‖UnforcedLeray.B0012.L0‖ * (β - s)) * ‖V β‖ :=
            mul_le_mul_of_nonneg_right (UnforcedLeray.Cons.G3b.norm_S_le hs0 hsβ) (norm_nonneg _)
        _ ≤ Real.exp (‖UnforcedLeray.B0012.L0‖ * β) * ‖V β‖ :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)))
              (norm_nonneg _)
    refine ⟨2 * (Real.exp (‖UnforcedLeray.B0012.L0‖ * β) * ‖V β‖), fun s hs h => ?_⟩
    rw [hnorm (V s) h]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hb := hbound s hs
    nlinarith [norm_nonneg (V s), hb,
      mul_nonneg (Real.exp_pos (‖UnforcedLeray.B0012.L0‖ * β)).le (norm_nonneg (V β))]

end UnforcedLeray.Short.Spine
