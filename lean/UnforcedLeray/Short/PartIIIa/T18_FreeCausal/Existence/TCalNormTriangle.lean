import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Tri
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin

/-!
# Part III-a, task `T18_FreeCausal/Existence/TCalNormTriangle`: the triangle inequality for `𝒯`

Proves `TCalNormTriangle` (`Sub/T18_2_Tri.lean`), the shared leaf of `T18/2/1` and `T18/2/3`
(Cauchy bookkeeping of "let `δ → 0`"). Source of record:
`the November 2 reference manuscript`, lines 3427-3440.

Proof. Pointwise, `X - Z = (X - Y) - (Z - Y)`. The Frobenius norm satisfies the triangle
inequality (`tCalNormTriangle_tnorm2_sub_le`) and is homogeneous under real scalars
(`tCalNormTriangle_tnorm2_smul`), so the gain-conjugated norms obey the same inequality
pointwise (`tCalNormTriangle_gain_tri`). Then `eLpNorm` is monotone and subadditive for the
measurable norm functions (`tCalNormTriangle_eLpNorm_le_add`). No hypothesis on `c, ν, γ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Scalar helpers (small contexts, so that `nlinarith` stays fast) -/

/-- From `x² ≤ y²` and `0 ≤ y` conclude `x ≤ y`. -/
theorem tCalNormTriangle_le_of_sq_le (x y : ℝ) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- From `0 ≤ x ≤ a + b` conclude `x² ≤ (a + b)²`. -/
theorem tCalNormTriangle_sq_le_of_le (x a b : ℝ) (hx : 0 ≤ x) (h : x ≤ a + b) :
    x ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hx, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h)]

/-- Cauchy-Schwarz for four terms, as a Lagrange identity. -/
theorem tCalNormTriangle_cs4 (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ) :
    (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3) ^ 2 ≤
      (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) := by
  nlinarith [sq_nonneg (a0 * b1 - a1 * b0), sq_nonneg (a0 * b2 - a2 * b0),
    sq_nonneg (a0 * b3 - a3 * b0), sq_nonneg (a1 * b2 - a2 * b1),
    sq_nonneg (a1 * b3 - a3 * b1), sq_nonneg (a2 * b3 - a3 * b2)]

/-! ## Elementary facts about the Frobenius norm -/

/-- The Frobenius norm of a `2 × 2` complex tensor, expanded into its four entries. -/
theorem tCalNormTriangle_tnorm2_sq_eq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ‖T 0 0‖ ^ 2 + ‖T 0 1‖ ^ 2 + ‖T 1 0‖ ^ 2 + ‖T 1 1‖ ^ 2 := by
  rw [causalLin_tnorm2_sq]
  simp only [Fin.sum_univ_two]
  ring

/-- Triangle inequality for the Frobenius norm: `‖u - v‖_F ≤ ‖u‖_F + ‖v‖_F`. -/
theorem tCalNormTriangle_tnorm2_sub_le (u v : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => u i j - v i j) ≤ tnorm2 u + tnorm2 v := by
  have hs : 0 ≤ tnorm2 u := Real.sqrt_nonneg _
  have ht : 0 ≤ tnorm2 v := Real.sqrt_nonneg _
  have hu := tCalNormTriangle_tnorm2_sq_eq u
  have hv := tCalNormTriangle_tnorm2_sq_eq v
  -- Cauchy-Schwarz on the four entry norms: `∑ ‖u_k‖ ‖v_k‖ ≤ ‖u‖_F ‖v‖_F`.
  have hcs := tCalNormTriangle_cs4 ‖u 0 0‖ ‖u 0 1‖ ‖u 1 0‖ ‖u 1 1‖
    ‖v 0 0‖ ‖v 0 1‖ ‖v 1 0‖ ‖v 1 1‖
  have hprod : (tnorm2 u * tnorm2 v) ^ 2 =
      (‖u 0 0‖ ^ 2 + ‖u 0 1‖ ^ 2 + ‖u 1 0‖ ^ 2 + ‖u 1 1‖ ^ 2) *
        (‖v 0 0‖ ^ 2 + ‖v 0 1‖ ^ 2 + ‖v 1 0‖ ^ 2 + ‖v 1 1‖ ^ 2) := by
    rw [mul_pow, hu, hv]
  have hXle : (‖u 0 0‖ * ‖v 0 0‖ + ‖u 0 1‖ * ‖v 0 1‖ + ‖u 1 0‖ * ‖v 1 0‖ +
      ‖u 1 1‖ * ‖v 1 1‖) ^ 2 ≤ (tnorm2 u * tnorm2 v) ^ 2 := by
    rw [hprod]
    exact hcs
  have hcross : ‖u 0 0‖ * ‖v 0 0‖ + ‖u 0 1‖ * ‖v 0 1‖ + ‖u 1 0‖ * ‖v 1 0‖ +
      ‖u 1 1‖ * ‖v 1 1‖ ≤ tnorm2 u * tnorm2 v :=
    tCalNormTriangle_le_of_sq_le _ _ (mul_nonneg hs ht) hXle
  have e00 : ‖u 0 0 - v 0 0‖ ^ 2 ≤ (‖u 0 0‖ + ‖v 0 0‖) ^ 2 :=
    tCalNormTriangle_sq_le_of_le _ _ _ (norm_nonneg _) (norm_sub_le _ _)
  have e01 : ‖u 0 1 - v 0 1‖ ^ 2 ≤ (‖u 0 1‖ + ‖v 0 1‖) ^ 2 :=
    tCalNormTriangle_sq_le_of_le _ _ _ (norm_nonneg _) (norm_sub_le _ _)
  have e10 : ‖u 1 0 - v 1 0‖ ^ 2 ≤ (‖u 1 0‖ + ‖v 1 0‖) ^ 2 :=
    tCalNormTriangle_sq_le_of_le _ _ _ (norm_nonneg _) (norm_sub_le _ _)
  have e11 : ‖u 1 1 - v 1 1‖ ^ 2 ≤ (‖u 1 1‖ + ‖v 1 1‖) ^ 2 :=
    tCalNormTriangle_sq_le_of_le _ _ _ (norm_nonneg _) (norm_sub_le _ _)
  have hL : tnorm2 (fun i j => u i j - v i j) ^ 2 =
      ‖u 0 0 - v 0 0‖ ^ 2 + ‖u 0 1 - v 0 1‖ ^ 2 + ‖u 1 0 - v 1 0‖ ^ 2 +
        ‖u 1 1 - v 1 1‖ ^ 2 :=
    tCalNormTriangle_tnorm2_sq_eq (fun i j => u i j - v i j)
  have hexp_e : (‖u 0 0‖ + ‖v 0 0‖) ^ 2 + (‖u 0 1‖ + ‖v 0 1‖) ^ 2 +
      (‖u 1 0‖ + ‖v 1 0‖) ^ 2 + (‖u 1 1‖ + ‖v 1 1‖) ^ 2 =
      (‖u 0 0‖ ^ 2 + ‖u 0 1‖ ^ 2 + ‖u 1 0‖ ^ 2 + ‖u 1 1‖ ^ 2) +
        (‖v 0 0‖ ^ 2 + ‖v 0 1‖ ^ 2 + ‖v 1 0‖ ^ 2 + ‖v 1 1‖ ^ 2) +
        2 * (‖u 0 0‖ * ‖v 0 0‖ + ‖u 0 1‖ * ‖v 0 1‖ + ‖u 1 0‖ * ‖v 1 0‖ +
          ‖u 1 1‖ * ‖v 1 1‖) := by
    ring
  have hexp_s : (tnorm2 u + tnorm2 v) ^ 2 =
      tnorm2 u ^ 2 + 2 * (tnorm2 u * tnorm2 v) + tnorm2 v ^ 2 := by
    ring
  have hsq : tnorm2 (fun i j => u i j - v i j) ^ 2 ≤ (tnorm2 u + tnorm2 v) ^ 2 := by
    rw [hL, hexp_s]
    linarith [e00, e01, e10, e11, hexp_e, hcross, hu, hv]
  exact tCalNormTriangle_le_of_sq_le _ _ (add_nonneg hs ht) hsq

/-- The Frobenius norm is homogeneous under real scalars: `‖r T‖_F = |r| ‖T‖_F`. -/
theorem tCalNormTriangle_tnorm2_smul (r : ℝ) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • T) = |r| * tnorm2 T := by
  have key : ∀ i j, ‖(r • T) i j‖ ^ 2 = |r| ^ 2 * ‖T i j‖ ^ 2 := fun i j => by
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2, ‖(r • T) i j‖ ^ 2 =
      |r| ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    simp only [key, Finset.mul_sum]
  unfold tnorm2
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]

/-- The pointwise triangle inequality for the gain-conjugated tensors:
`‖r (A - C)‖_F ≤ ‖r (A - B)‖_F + ‖r (C - B)‖_F` (`A - C = (A - B) - (C - B)`). -/
theorem tCalNormTriangle_gain_tri (r : ℝ) (A B C : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • (fun i j => A i j - C i j)) ≤
      tnorm2 (r • (fun i j => A i j - B i j)) + tnorm2 (r • (fun i j => C i j - B i j)) := by
  have hXZ : (fun i j => A i j - C i j) = fun i j => (A i j - B i j) - (C i j - B i j) := by
    funext i j
    ring
  rw [hXZ, tCalNormTriangle_tnorm2_smul, tCalNormTriangle_tnorm2_smul,
    tCalNormTriangle_tnorm2_smul, ← mul_add]
  exact mul_le_mul_of_nonneg_left
    (tCalNormTriangle_tnorm2_sub_le (fun i j => A i j - B i j) (fun i j => C i j - B i j))
    (abs_nonneg r)

/-! ## Monotonicity and subadditivity of the `L²` seminorm -/

/-- If `0 ≤ F ≤ G + H` pointwise and `G`, `H` are a.e. strongly measurable, then
`‖F‖_{L²} ≤ ‖G‖_{L²} + ‖H‖_{L²}`. -/
theorem tCalNormTriangle_eLpNorm_le_add {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G H : α → ℝ) (hG : AEStronglyMeasurable G μ) (hH : AEStronglyMeasurable H μ)
    (hF : ∀ a, 0 ≤ F a) (hle : ∀ a, F a ≤ G a + H a) :
    eLpNorm F 2 μ ≤ eLpNorm G 2 μ + eLpNorm H 2 μ := by
  have hmono : ∀ a, ‖F a‖ ≤ ‖(G + H) a‖ := fun a => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hF a), Pi.add_apply]
    exact (hle a).trans (le_abs_self _)
  calc eLpNorm F 2 μ ≤ eLpNorm (G + H) 2 μ := eLpNorm_mono_ae (ae_of_all μ hmono)
    _ ≤ eLpNorm G 2 μ + eLpNorm H 2 μ := eLpNorm_add_le hG hH (by norm_num)

/-! ## The triangle inequality for `𝒯` -/

/-- **Triangle inequality for the gain-conjugated `𝒯` norm** (`PartIII-a:T18/2/1/1`;
SP 3427-3440). Proves `TCalNormTriangle`. -/
theorem tCalNormTriangle : TCalNormTriangle := by
  unfold TCalNormTriangle
  intro c ν γ X Y Z hX hY hZ
  have hr : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
    unfold gainG
    fun_prop
  have hmA : ∀ i j, Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ • (X p i j - Y p i j) :=
    fun i j => hr.smul ((hX i j).sub (hY i j))
  have hmB : ∀ i j, Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ • (Z p i j - Y p i j) :=
    fun i j => hr.smul ((hZ i j).sub (hY i j))
  have hGm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      tnorm2 ((gainG γ ν p.1)⁻¹ • (fun i j => X p i j - Y p i j)) :=
    causalLin_measurable_tnorm2 (f := fun p => (gainG γ ν p.1)⁻¹ • (fun i j => X p i j - Y p i j))
      (fun i j => hmA i j)
  have hHm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      tnorm2 ((gainG γ ν p.1)⁻¹ • (fun i j => Z p i j - Y p i j)) :=
    causalLin_measurable_tnorm2 (f := fun p => (gainG γ ν p.1)⁻¹ • (fun i j => Z p i j - Y p i j))
      (fun i j => hmB i j)
  simp only [tCalNorm, gainConj]
  exact tCalNormTriangle_eLpNorm_le_add _ _ _ _ hGm.aestronglyMeasurable
    hHm.aestronglyMeasurable
    (fun p => Real.sqrt_nonneg _)
    (fun p => tCalNormTriangle_gain_tri ((gainG γ ν p.1)⁻¹) (fun i j => X p i j)
      (fun i j => Y p i j) (fun i j => Z p i j))

end UnforcedLeray.Short.IIIa
