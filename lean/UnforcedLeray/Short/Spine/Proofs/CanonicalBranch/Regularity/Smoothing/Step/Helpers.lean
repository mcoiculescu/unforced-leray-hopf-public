import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.Duhamel

/-!
# Helpers for `MildLevelStep` (task `Spine:SP-CAN/4/1/6`)

Three facts used by `Smoothing/Step.lean` (proof of `MildLevelStep`, `Sub/SP_CAN4_1.lean`):

* `euclid_add`, `xgjNorm_add_le`: the graph norm `xgjNorm` of `X_{G,k}` satisfies the triangle
  inequality; it is the Euclidean norm of the pair `(f, (I - D)^{k/2} f)`.
* `L0_xgj`: `L₀` is bounded on `X_{G,j}` in the `xgjNorm` form (from `B0122.L0_mem_XGj_norm`, the
  conversion of `Regularity/Bootstrap/Ops.lean` `BootOps.L0_bound`, copied here).
* `mild_decomp`: the Duhamel form of a mild curve, `V θ = e^{log(θ'/θ) D} V θ' + ∫_θ^{θ'} ...`
  (`CanonicalMild.S_mild_interval`).

Source of record: `the November 2 reference manuscript`, lines 1134-1145.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine.MildLevelStepHelp

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- Minkowski inequality for the Euclidean norm of a pair of reals. -/
theorem euclid_add (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  have hp := Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + b ^ 2 by positivity)
  have hq := Real.sq_sqrt (show (0 : ℝ) ≤ c ^ 2 + d ^ 2 by positivity)
  have hp0 := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  have hq0 := Real.sqrt_nonneg (c ^ 2 + d ^ 2)
  have hpq : (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    rw [mul_pow, hp, hq]
  have hcs : a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c), mul_nonneg hp0 hq0]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [hcs, hp, hq]

/-- Triangle inequality for the graph norm `xgjNorm k` of `X_{G,k}`. -/
theorem xgjNorm_add_le (k : ℕ) (x y z : XG) (hx : x ∈ B0123.XGj k) (hy : y ∈ B0123.XGj k)
    (hz : z ∈ B0123.XGj k) (h : z = x + y) :
    B0123.xgjNorm k ⟨z, hz⟩ ≤ B0123.xgjNorm k ⟨x, hx⟩ + B0123.xgjNorm k ⟨y, hy⟩ := by
  subst h
  have hadd : B0123.IDpow ((k : ℝ) / 2) ⟨x + y, hz⟩ =
      B0123.IDpow ((k : ℝ) / 2) ⟨x, hx⟩ + B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩ :=
    LinearPMap.map_add _ ⟨x, hx⟩ ⟨y, hy⟩
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖B0123.IDpow ((k : ℝ) / 2) ⟨x + y, hz⟩‖ ≤
      ‖B0123.IDpow ((k : ℝ) / 2) ⟨x, hx⟩‖ + ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖ := by
    rw [hadd]
    exact norm_add_le _ _
  have hs1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  show Real.sqrt (‖x + y‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨x + y, hz⟩‖ ^ 2) ≤
    Real.sqrt (‖x‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨x, hx⟩‖ ^ 2) +
      Real.sqrt (‖y‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖ ^ 2)
  calc Real.sqrt (‖x + y‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨x + y, hz⟩‖ ^ 2)
      ≤ Real.sqrt ((‖x‖ + ‖y‖) ^ 2 +
          (‖B0123.IDpow ((k : ℝ) / 2) ⟨x, hx⟩‖ + ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ ≤ _ := euclid_add _ _ _ _

/-- `L₀` is bounded on `X_{G,j}` in the graph norm `xgjNorm j` (conversion of
`B0122.L0_mem_XGj_norm`, which is stated with `B0121.graphNormSq`). -/
theorem L0_xgj (j : ℕ) (hE : B0122.GreenEllipticRegularity j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ B0123.XGj j,
      ∃ hL : B0012.L0 f ∈ B0123.XGj j,
        B0123.xgjNorm j ⟨B0012.L0 f, hL⟩ ≤ C * B0123.xgjNorm j ⟨f, hf⟩ := by
  obtain ⟨C, hC, h⟩ := B0122.L0_mem_XGj_norm j hE
  refine ⟨C, hC, fun f hf => ?_⟩
  obtain ⟨hL, hb⟩ := h f ((B0123.XGj_eq_B0121 j).le hf)
  refine ⟨(B0123.XGj_eq_B0121 j).ge hL, ?_⟩
  have e1 : Real.sqrt (B0121.graphNormSq j ⟨B0012.L0 f, hL⟩) =
      B0123.xgjNorm j ⟨B0012.L0 f, (B0123.XGj_eq_B0121 j).ge hL⟩ := by
    rw [B0123.graphNormSq_eq_xgjNorm_sq]
    exact Real.sqrt_sq (B0123.xgjNorm_nonneg _ _)
  have e2 : Real.sqrt (B0121.graphNormSq j ⟨f, (B0123.XGj_eq_B0121 j).le hf⟩) =
      B0123.xgjNorm j ⟨f, hf⟩ := by
    rw [B0123.graphNormSq_eq_xgjNorm_sq]
    exact Real.sqrt_sq (B0123.xgjNorm_nonneg _ _)
  rw [e1, e2] at hb
  exact hb

/-- The Duhamel form of a mild curve on `[θ, θ']` (`CanonicalMild.S_mild_interval`), with the
integrand written along the curve itself. -/
theorem mild_decomp {V : ℝ → XG} (hV : IsMildOnPos V) {θ θ' : ℝ} (hθ : 0 < θ)
    (hθθ' : θ ≤ θ') :
    V θ = B0123.expD (Real.log θ' - Real.log θ) (V θ') +
      ∫ v in θ..θ', B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v)) := by
  rw [hV θ θ' hθ hθθ', CanonicalMild.S_mild_interval hθ hθθ' (V θ')]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hθθ'] at hv
  exact congrArg (fun y => B0123.expD (Real.log v - Real.log θ) (B0012.L0 y))
    (hV v θ' (lt_of_lt_of_le hθ hv.1) hv.2).symm

end UnforcedLeray.Short.Spine.MildLevelStepHelp
