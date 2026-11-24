import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Scaling
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Fields
import UnforcedLeray.Loc.L01Coefficient

/-!
# `HeatProfileRegularity`: regularity of the heat profile `H_h[u_dss]`

Proof of the named hypothesis `HeatProfileRegularity` of `Loc/L01Coefficient.lean`
(infrastructure INF04; blueprint unit B0710 and the continuity in phase of B0711;
`paper/main.tex` lines 159–163 and 274–281: "`|D^j H_h[u_dss]| ≤ C_j⟨y⟩^{-1-j}`, `j ≤ 2` ...
`∇H_h ∈ L³`, `∇²H_h ∈ L²` uniformly in phase").

Theorem: `heatProfileRegularity : HeatProfileRegularity`.

Route (helpers in `Loc/Hyp/HeatProfileRegularity/`):
1. `Scaling`: the change of variables `z = e^{τ/2}w` gives `H_h[u](·, τ) = e^{hΔ}u_τ` with
   `u_τ(x) = e^{τ/2}u(e^{τ/2}x)` (`heatProfile_eq_average`); `u_τ` has the bounds of lines
   152–156 with the constants of `u` (`invDist_dil`), and `u_σ - u_τ` has them with constant
   `3C|σ - τ|` (`invDist_dil_sub`, mean value theorem in the phase, one more derivative of `u`).
2. `Smoothing`: near/far splitting of the heat integral with the cutoff of `Units/B0306`
   (`heat_smoothing`): `e^{hΔ}b ∈ C²` and `‖D^n e^{hΔ}b(y)‖ ≤ εQ_n(1 + |y|)^{-1-n}`, `n ≤ 2`,
   for every field with `‖D^k b(x)‖ ≤ ε|x|^{-1-k}`, `k ≤ 3`; `Q_n` depends only on `h`.
3. Here: `V(τ) = H(τ)` as a `C₀` map (decay `(1 + |y|)^{-1}`), `W(τ)ᵢ = ∂ᵢH(τ) ∈ L³`
   (decay `(1 + |y|)^{-2}`), `Y(τ)ᵢⱼ = ∂ⱼ∂ᵢH(τ) ∈ L²` (decay `(1 + |y|)^{-3}`); the classical
   derivatives of a `C²` field are weak derivatives (`hasWeakSpatialDerivative_of_contDiff`).
   By linearity, step 2 applied to `u_σ - u_τ` makes `V`, `W`, `Y` Lipschitz in the phase.

The self-similarity law and the period are not used: the regularity holds for every `u` with
the bounds of lines 152–156 (`k ≤ 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.Blueprint

open UnforcedLeray.HeatProfileReg

/-- **`HeatProfileRegularity`** (INF04, blueprint B0710 and B0711; tex lines 274–281). For
`h > 0` and `u` smooth off `0` with `|D^k u(x)| ≤ C_k|x|^{-1-k}` (`k ≤ 4`, lines 152–156), the heat
profile `H(τ) = H_h[u](·, τ)` of lines 159–163 has a `C₀` representative, weak first
derivatives in `L³` and weak second derivatives in `L²`, all continuous (indeed Lipschitz) in
the phase `τ`. -/
theorem heatProfileRegularity : HeatProfileRegularity := by
  intro h period u hh _hperiod hsmooth _hdss hbounds
  obtain ⟨C, hC0, hC⟩ := uniform_bound hbounds
  obtain ⟨Q, hQ0, hQ⟩ := heat_smoothing hh
  have hinv : ∀ τ, InvDist (dil τ u) C := invDist_dil hsmooth (fun k hk => hC k (by omega))
  have hdif : ∀ σ τ, InvDist (dil σ u - dil τ u) (3 * C * |σ - τ|) :=
    invDist_dil_sub hsmooth hC0 hC
  have hprof : ∀ τ, heatProfile h u τ = Heat.average h (dil τ u) := heatProfile_eq_average hh u
  have hreg : ∀ τ, ContDiff ℝ 2 (Heat.average h (dil τ u)) := fun τ => (hQ _ _ (hinv τ)).1
  have hsub : ∀ σ τ, Heat.average h (dil σ u) - Heat.average h (dil τ u) =
      Heat.average h (dil σ u - dil τ u) := fun σ τ => (average_sub hh (hinv σ) (hinv τ)).symm
  -- pointwise bounds for a field with the bounds of lines 152–156
  have hb0 : ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ y : Space,
      ‖Heat.average h b y‖ ≤ ε * Q 0 / (1 + ‖y‖) := by
    intro b ε hb y
    have h0 := (hQ b ε hb).2 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
  have hb1 : ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ (i : Fin 3) (y : Space),
      ‖d1 (Heat.average h b) i y‖ ≤ (ε * Q 1) * ‖((1 + ‖y‖) ^ 2)⁻¹‖ := by
    intro b ε hb i y
    refine (norm_d1_le _ i y).trans (((hQ b ε hb).2 1 (by omega) y).trans (le_of_eq ?_))
    rw [norm_weight]
    ring
  have hb2 : ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ (i j : Fin 3) (y : Space),
      ‖d2 (Heat.average h b) i j y‖ ≤ (ε * Q 2) * ‖((1 + ‖y‖) ^ 3)⁻¹‖ := by
    intro b ε hb i j y
    refine (norm_d2_le (hQ b ε hb).1 i j y).trans
      (((hQ b ε hb).2 2 (by omega) y).trans (le_of_eq ?_))
    rw [norm_weight]
    ring
  -- the weights
  have hw2 : MemLp (fun y : Space => ((1 + ‖y‖) ^ 2)⁻¹) 3 volume :=
    memLp_weight 2 3 (by norm_num) (by norm_num) (by norm_num)
  have hw3 : MemLp (fun y : Space => ((1 + ‖y‖) ^ 3)⁻¹) 2 volume :=
    memLp_weight 3 2 (by norm_num) (by norm_num) (by norm_num)
  have hW : ∀ (τ : ℝ) (i : Fin 3), MemLp (d1 (Heat.average h (dil τ u)) i) 3 volume :=
    fun τ i => hw2.of_le_mul ((d1_contDiff (hreg τ) i).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun y => hb1 _ _ (hinv τ) i y)
  have hY : ∀ (τ : ℝ) (i j : Fin 3), MemLp (d2 (Heat.average h (dil τ u)) i j) 2 volume :=
    fun τ i j => hw3.of_le_mul ((d2_continuous (hreg τ) i j).aestronglyMeasurable)
      (Eventually.of_forall fun y => hb2 _ _ (hinv τ) i j y)
  have hQ0' := hQ0 0
  have hQ1' := hQ0 1
  have hQ2' := hQ0 2
  have hd0 : ∀ σ τ : ℝ, 0 ≤ 3 * C * |σ - τ| := fun σ τ =>
    mul_nonneg (mul_nonneg (by norm_num) hC0) (abs_nonneg _)
  refine ⟨fun τ => ⟨⟨Heat.average h (dil τ u), (hreg τ).continuous⟩,
      tendsto_zero_of_decay (hb0 _ _ (hinv τ))⟩,
    fun τ i => (hW τ i).toLp _, fun τ i j => (hY τ i j).toLp _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `V` is Lipschitz in the phase for the sup norm
    refine continuous_of_dist_le (K := 3 * C * Q 0)
      (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ0') fun σ τ => ?_
    refine dist_C0_le (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ0')
      (abs_nonneg _)) fun y => ?_
    show ‖Heat.average h (dil σ u) y - Heat.average h (dil τ u) y‖ ≤ 3 * C * Q 0 * |σ - τ|
    have e : Heat.average h (dil σ u) y - Heat.average h (dil τ u) y =
        Heat.average h (dil σ u - dil τ u) y := congrFun (hsub σ τ) y
    rw [e]
    refine (hb0 _ _ (hdif σ τ) y).trans ?_
    calc 3 * C * |σ - τ| * Q 0 / (1 + ‖y‖) ≤ 3 * C * |σ - τ| * Q 0 :=
          div_le_self (mul_nonneg (hd0 σ τ) hQ0') (by linarith [norm_nonneg y])
      _ = 3 * C * Q 0 * |σ - τ| := by ring
  · -- `W` is Lipschitz in the phase in `L³`
    refine continuous_pi fun i => continuous_of_dist_le
      (K := 3 * C * Q 1 * (eLpNorm (fun y : Space => ((1 + ‖y‖) ^ 2)⁻¹) 3 volume).toReal)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ1') ENNReal.toReal_nonneg)
      fun σ τ => ?_
    refine (dist_toLp_le (hW σ i) (hW τ i) hw2 (c := 3 * C * |σ - τ| * Q 1)
      (mul_nonneg (hd0 σ τ) hQ1') fun y => ?_).trans (le_of_eq (by ring))
    rw [← d1_sub (hreg σ) (hreg τ), hsub σ τ]
    exact hb1 _ _ (hdif σ τ) i y
  · -- `Y` is Lipschitz in the phase in `L²`
    refine continuous_pi fun i => continuous_pi fun j => continuous_of_dist_le
      (K := 3 * C * Q 2 * (eLpNorm (fun y : Space => ((1 + ‖y‖) ^ 3)⁻¹) 2 volume).toReal)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ2') ENNReal.toReal_nonneg)
      fun σ τ => ?_
    refine (dist_toLp_le (hY σ i j) (hY τ i j) hw3 (c := 3 * C * |σ - τ| * Q 2)
      (mul_nonneg (hd0 σ τ) hQ2') fun y => ?_).trans (le_of_eq (by ring))
    rw [← d2_sub (hreg σ) (hreg τ), hsub σ τ]
    exact hb2 _ _ (hdif σ τ) i j y
  · -- the `C₀` representative
    exact fun τ => Eventually.of_forall fun y => (congrFun (hprof τ) y).symm
  · -- first weak derivatives
    intro τ i
    rw [hprof τ]
    exact (hasWeakSpatialDerivative_of_contDiff ((hreg τ).of_le (by norm_num)) i).congr
      EventuallyEq.rfl (hW τ i).coeFn_toLp.symm
  · -- second weak derivatives
    intro τ i j
    exact (hasWeakSpatialDerivative_of_contDiff (d1_contDiff (hreg τ) i) j).congr
      (hW τ i).coeFn_toLp.symm (hY τ i j).coeFn_toLp.symm

end UnforcedLeray.Blueprint
