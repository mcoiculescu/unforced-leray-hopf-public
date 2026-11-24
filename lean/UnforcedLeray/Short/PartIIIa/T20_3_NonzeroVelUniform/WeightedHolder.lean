import UnforcedLeray.Short.PartIIIa.Sub.T20_3

/-!
# Part III-a, task `PartIII-a:T20/3/1`: weighted Cauchy-Schwarz on the cell (`WeightedHolder`)

Source of record: `the November 2 reference manuscript`, lines 3239-3240
("the moment bound is weighted Cauchy-Schwarz", first moment bounded by `‖ω‖_{X_m}`).
Target: `WeightedHolder` in `Sub/T20_3.lean`.

Proof. Write `⟨x⟩ = bracket x = jb x ^ (1/2)`. Apply Hölder in `L²(cellVol c)` (Mathlib
`integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`) to
* `f1 x = g x * ⟨x⟩^(-m)`, so `f1 x ^ 2 = g x ^ 2 * jb x ^ (-m)`;
* `f2 x = ‖⟨x⟩^m * ω x‖`, so `(∫ f2 ^ 2)^(1/2) = ‖ω‖` (`B0579.norm_X`).

Since `f1 x * f2 x = g x * |ω x|`, the bound follows. Integrability of `g |ω|` is
`MemLp.integrable_mul` for two `L²` factors.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

namespace WeightedHolderProof

/-- `(y ^ (a / 2)) ^ 2 = y ^ a` for `y > 0`. -/
lemma sq_rpow_half (y : ℝ) (hy : 0 < y) (a : ℝ) : (y ^ (a / 2)) ^ 2 = y ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
  congr 1
  push_cast
  ring

lemma bracket_pos' (x : B0579.Plane) : 0 < B0579.bracket x := by
  unfold B0579.bracket
  exact Real.sqrt_pos.2 (B0579.jb_pos x)

/-- The squared cell weight: `(⟨x⟩^{-m})^2 = jb^{-m}`. -/
lemma bracket_neg_sq (m : ℝ) (x : B0579.Plane) :
    (B0579.bracket x ^ (-m)) ^ 2 = B0579.jb x ^ (-m) := by
  rw [B0579.bracket_rpow, sq_rpow_half _ (B0579.jb_pos x)]

/-- Pointwise identity: `(γ ⟨x⟩^{-m}) · ‖⟨x⟩^m w‖ = γ |w|`. -/
lemma pointwise_prod_eq (m : ℝ) (x : B0579.Plane) (γ w : ℝ) :
    (γ * B0579.bracket x ^ (-m)) * ‖B0579.bracket x ^ m * w‖ = γ * |w| := by
  have hinv : B0579.bracket x ^ (-m) * B0579.bracket x ^ m = 1 := by
    rw [← Real.rpow_add (bracket_pos' x)]
    simp
  have hb : 0 ≤ B0579.bracket x ^ m := (B0579.bracket_rpow_pos m x).le
  rw [norm_mul, Real.norm_of_nonneg hb, Real.norm_eq_abs]
  calc (γ * B0579.bracket x ^ (-m)) * (B0579.bracket x ^ m * |w|)
      = γ * (B0579.bracket x ^ (-m) * B0579.bracket x ^ m) * |w| := by ring
    _ = γ * |w| := by rw [hinv, mul_one]

/-- For `F ∈ L²(μ)`, `‖F‖_{L²}` equals `(∫ ‖F‖^2)^{1/2}`. -/
lemma toReal_eLpNorm_two (F : B0579.Plane → ℝ) (μ : Measure B0579.Plane) (hF : MemLp F 2 μ) :
    (eLpNorm F 2 μ).toReal = (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal]
  · simp only [ENNReal.toReal_ofNat, one_div]
  · exact Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _

end WeightedHolderProof

/-- **Weighted Cauchy-Schwarz on the cell** (task `PartIII-a:T20/3/1`; SP 3239-3240). Proves the
`Prop` `WeightedHolder` of `Sub/T20_3.lean`: for `ω ∈ X_{m,c}`, `0 ≤ m`, and a measurable
`g ≥ 0` with `∫_cell g² jb^{-m} < ∞`, `g |ω|` is integrable on the cell and
`∫_cell g |ω| ≤ (∫_cell g² jb^{-m})^{1/2} ‖ω‖`. -/
theorem weightedHolder : WeightedHolder := by
  intro c m ω g _hm hg0 hgm hgint
  -- the weighted function `⟨x⟩^m ω` lies in `L²(cellVol c)`
  have hW : MemLp (fun x => B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x) 2
      (B0581.cellVol c) :=
    (B0579.memLp_cellMeasure_iff c m).1 (Lp.memLp ω)
  -- the first Hölder factor `g ⟨x⟩^{-m}`
  have hf1m : Measurable (fun x => g x * B0579.bracket x ^ (-m)) :=
    hgm.mul (B0579.continuous_bracket_rpow (-m)).measurable
  have hf1 : MemLp (fun x => g x * B0579.bracket x ^ (-m)) 2 (B0581.cellVol c) := by
    refine (memLp_two_iff_integrable_sq hf1m.aestronglyMeasurable).2 ?_
    refine hgint.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow, WeightedHolderProof.bracket_neg_sq]
  -- the second Hölder factor `‖⟨x⟩^m ω‖`
  have hf2 : MemLp (fun x => ‖B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x‖) 2
      (B0581.cellVol c) :=
    hW.norm
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hf1' : MemLp (fun x => g x * B0579.bracket x ^ (-m)) (ENNReal.ofReal 2)
      (B0581.cellVol c) := by
    rw [h2]
    exact hf1
  have hf2' : MemLp (fun x => ‖B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x‖)
      (ENNReal.ofReal 2) (B0581.cellVol c) := by
    rw [h2]
    exact hf2
  have hf1_nn : 0 ≤ᵐ[B0581.cellVol c] (fun x => g x * B0579.bracket x ^ (-m)) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (hg0 x) (B0579.bracket_rpow_pos (-m) x).le
  have hf2_nn : 0 ≤ᵐ[B0581.cellVol c]
      (fun x => ‖B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x‖) :=
    Filter.Eventually.of_forall fun x => norm_nonneg _
  -- Hölder inequality in `L²(cellVol c)`
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := B0581.cellVol c) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf1_nn hf2_nn hf1' hf2'
  have hI1 : ∫ x, (g x * B0579.bracket x ^ (-m)) ^ (2 : ℝ) ∂(B0581.cellVol c) =
      ∫ x, g x ^ 2 * B0579.jb x ^ (-m) ∂(B0581.cellVol c) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_two, mul_pow, WeightedHolderProof.bracket_neg_sq]
  have hI2 : (∫ x, ‖B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x‖ ^ (2 : ℝ)
      ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) = ‖ω‖ := by
    rw [B0579.norm_X c m ω]
    exact (WeightedHolderProof.toReal_eLpNorm_two _ _ hW).symm
  -- integrability of `g |ω|`, as a product of two `L²` factors
  have hint : Integrable (fun x => g x * |(ω : B0579.Plane → ℝ) x|) (B0581.cellVol c) := by
    refine (MemLp.integrable_mul (p := 2) (q := 2) hf1 hf2).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    exact WeightedHolderProof.pointwise_prod_eq m x (g x) ((ω : B0579.Plane → ℝ) x)
  refine ⟨hint, ?_⟩
  have hcongr : ∫ x, g x * |(ω : B0579.Plane → ℝ) x| ∂(B0581.cellVol c) =
      ∫ x, (g x * B0579.bracket x ^ (-m)) *
        ‖B0579.bracket x ^ m * (ω : B0579.Plane → ℝ) x‖ ∂(B0581.cellVol c) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (WeightedHolderProof.pointwise_prod_eq m x (g x) ((ω : B0579.Plane → ℝ) x)).symm
  rw [hcongr]
  refine hH.trans (le_of_eq ?_)
  rw [hI1, hI2]

end UnforcedLeray.Short.IIIa.CTE.T20_3
