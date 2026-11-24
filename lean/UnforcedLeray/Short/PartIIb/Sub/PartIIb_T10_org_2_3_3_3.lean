import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of

/-!
# `PartII-b:T10/org/2/3/3/3`: smoothness and decay of the Newton curl potential

`A = N ∗ curl f` with `(curl f)ᵢ = ∂ᵢ₊₁ fᵢ₊₂ - ∂ᵢ₊₂ fᵢ₊₁` is smooth, `|Aᵢ| ≲ (1+|x|)⁻²` and
`|∂ⱼ Aᵢ| ≲ (1+|x|)⁻³`.  Writing `Aᵢ = ∂ᵢ₊₁(N ∗ fᵢ₊₂) - ∂ᵢ₊₂(N ∗ fᵢ₊₁)`, the second derivative
`∂ⱼ∂ₖ(N ∗ g)` is a Riesz pair of a test (`rieszPairTest_decay`, with global boundedness from
continuity, `exists_decay_bound_three`), and `|N ∗ ∂ₖ g| ≲ (1+|x|)⁻²` is `newtonPair_decay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Linearity of the coordinate derivative under subtraction of smooth functions. -/
private theorem sdt_sub_aux3 {a b : Space → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (j : Fin 3) (x : Space) :
    spatialTestDerivative j (fun y => a y - b y) x =
      spatialTestDerivative j a x - spatialTestDerivative j b x := by
  unfold spatialTestDerivative
  rw [fderiv_fun_sub ((ha.differentiable (by simp)).differentiableAt)
    ((hb.differentiable (by simp)).differentiableAt)]
  simp

/-- Differences of tests are tests. -/
private theorem isSpatialTest_sub_aux3 {g h : Space → ℝ} (hg : IsSpatialTest g)
    (hh : IsSpatialTest h) : IsSpatialTest (fun y => g y - h y) :=
  ⟨hg.smooth.sub hh.smooth, hg.compact.sub hh.compact⟩

/-- The Newton potential is linear on tests (difference form). -/
private theorem newtonConv_sub_aux3 {g h : Space → ℝ} (hg : IsSpatialTest g)
    (hh : IsSpatialTest h) (x : Space) :
    newtonConv (fun y => g y - h y) x = newtonConv g x - newtonConv h x := by
  simp only [newtonConv, mul_sub]
  exact integral_sub (newtonConv_integrable hg.continuous hg.compact x)
    (newtonConv_integrable hh.continuous hh.compact x)

/-- `|a - b| ≤ A w + B w` from `|a| ≤ A w` and `|b| ≤ B w`. -/
private theorem abs_sub_le_aux3 {a b A B w : ℝ} (ha : |a| ≤ A * w) (hb : |b| ≤ B * w) :
    |a - b| ≤ A * w + B * w := by
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- `(1+|x|)^{-2}` is the decay weight. -/
private theorem decayWeight_eq_powWeight2 (x : Space) : decayWeight x = powWeight 2 x := by
  rw [decayWeight, powWeight, Real.rpow_neg (by positivity), Real.rpow_two]

theorem newtonCurlDecay_proof : UnforcedLeray.Short.IIb.NewtonCurlDecay := by
  intro f hf
  have hC : ∀ k : Fin 3, IsSpatialTest (curlComp f k) := fun k =>
    isSpatialTest_sub_aux3 ((hf (k + 2)).derivative (k + 1)) ((hf (k + 1)).derivative (k + 2))
  -- the two Newton pieces of the curl potential
  have hdec1 : ∀ k : Fin 3, ∀ x, newtonCurlPotential f k x =
      newtonConv (spatialTestDerivative (k + 1) (f (k + 2))) x
        - newtonConv (spatialTestDerivative (k + 2) (f (k + 1))) x := by
    intro k x
    show newtonConv (fun y => spatialTestDerivative (k + 1) (f (k + 2)) y
      - spatialTestDerivative (k + 2) (f (k + 1)) y) x = _
    exact newtonConv_sub_aux3 ((hf (k + 2)).derivative (k + 1)) ((hf (k + 1)).derivative (k + 2)) x
  have hdec2 : ∀ k : Fin 3, ∀ x, newtonCurlPotential f k x =
      spatialTestDerivative (k + 1) (newtonConv (f (k + 2))) x
        - spatialTestDerivative (k + 2) (newtonConv (f (k + 1))) x := by
    intro k x
    rw [hdec1 k x, spatialTestDerivative_newtonConv (hf (k + 2)) (k + 1),
      spatialTestDerivative_newtonConv (hf (k + 1)) (k + 2)]
  have hfun : ∀ k : Fin 3, newtonCurlPotential f k = fun x =>
      spatialTestDerivative (k + 1) (newtonConv (f (k + 2))) x
        - spatialTestDerivative (k + 2) (newtonConv (f (k + 1))) x :=
    fun k => funext (hdec2 k)
  -- smoothness
  have hsm : ∀ k : Fin 3, ContDiff ℝ ∞ (newtonCurlPotential f k) := fun k =>
    newtonConv_contDiff (hC k)
  -- decay of order two
  have hd2 : ∀ k : Fin 3, ∃ M, ∀ x, |newtonCurlPotential f k x| ≤ M * powWeight 2 x := by
    intro k
    obtain ⟨M1, hM1⟩ := newtonPair_decay (k + 1) (hf (k + 2))
    obtain ⟨M2, hM2⟩ := newtonPair_decay (k + 2) (hf (k + 1))
    refine ⟨|M1| + |M2|, fun x => ?_⟩
    have h1 : |newtonConv (spatialTestDerivative (k + 1) (f (k + 2))) x| ≤
        |M1| * powWeight 2 x := by
      rw [newtonConv_partial (hf (k + 2)) (k + 1) x, abs_neg, ← decayWeight_eq_powWeight2]
      exact (hM1 x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (decayWeight_pos x).le)
    have h2 : |newtonConv (spatialTestDerivative (k + 2) (f (k + 1))) x| ≤
        |M2| * powWeight 2 x := by
      rw [newtonConv_partial (hf (k + 1)) (k + 2) x, abs_neg, ← decayWeight_eq_powWeight2]
      exact (hM2 x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (decayWeight_pos x).le)
    rw [hdec1 k x, add_mul]
    exact abs_sub_le_aux3 h1 h2
  -- decay of order three of the second derivatives
  have hr3 : ∀ (j a : Fin 3) (φ : Space → ℝ), IsSpatialTest φ →
      ∃ M, ∀ y, |spatialTestDerivative j (spatialTestDerivative a (newtonConv φ)) y|
        ≤ M * powWeight 3 y := by
    intro j a φ hφ
    obtain ⟨C, R, hCR⟩ := rieszPairTest_decay hφ j a
    exact exists_decay_bound_three
      (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative
        (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative (newtonConv_contDiff hφ) a) j).continuous
      (r := max R 1) (A := C) (le_max_right _ _)
      (fun y hy => hCR y ((le_max_left _ _).trans hy))
  have hd3 : ∀ p : Fin 3 × Fin 3, ∃ M, ∀ x,
      |spatialTestDerivative p.2 (newtonCurlPotential f p.1) x| ≤ M * powWeight 3 x := by
    rintro ⟨k, j⟩
    obtain ⟨M1, h1⟩ := hr3 j (k + 1) (f (k + 2)) (hf (k + 2))
    obtain ⟨M2, h2⟩ := hr3 j (k + 2) (f (k + 1)) (hf (k + 1))
    refine ⟨|M1| + |M2|, fun x => ?_⟩
    show |spatialTestDerivative j (newtonCurlPotential f k) x| ≤ _
    rw [hfun k, sdt_sub_aux3
      (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative (newtonConv_contDiff (hf (k + 2))) (k + 1))
      (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative (newtonConv_contDiff (hf (k + 1))) (k + 2)) j x, add_mul]
    exact abs_sub_le_aux3
      ((h1 x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (powWeight_nonneg 3 x)))
      ((h2 x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (powWeight_nonneg 3 x)))
  refine ⟨hsm, ?_, ?_⟩
  · choose M hM using hd2
    refine ⟨∑ k : Fin 3, |M k|, fun k x => (hM k x).trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |M k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ k)))
      (powWeight_nonneg 2 x)
  · choose M hM using hd3
    refine ⟨∑ p : Fin 3 × Fin 3, |M p|, fun i j x => ?_⟩
    exact (hM (i, j) x).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (Finset.single_le_sum (f := fun p => |M p|)
        (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))))
      (powWeight_nonneg 3 x))

end UnforcedLeray.Short.IIb
