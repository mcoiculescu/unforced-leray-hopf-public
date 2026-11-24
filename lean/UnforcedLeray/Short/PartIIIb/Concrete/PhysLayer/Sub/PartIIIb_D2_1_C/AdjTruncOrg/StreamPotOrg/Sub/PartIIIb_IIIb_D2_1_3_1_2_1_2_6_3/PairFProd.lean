import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# Pairings of the product test with a field

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)

/-- The dot product against a scaled coordinate vector. -/
private theorem dotL_single_smul (c : ℂ) (i : Fin 3) (b : CVec3) :
    dotL (c • (EuclideanSpace.single i (1 : ℂ) : CVec3)) b = c * b i := by
  rw [dotL_apply]
  simp [EuclideanSpace.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The spatial derivative of the product test. -/
private theorem dy_prodTest (s : ℝ → ℂ) (g : Space → ℂ) (i j : Fin 3)
    (hs : ContDiff ℝ ∞ s) (hg : SmoothCS g) (x : ℝ × Space) :
    dy j (prodTest s g i) x =
      (s x.1 * fderiv ℝ g x.2 (EuclideanSpace.single j (1 : ℝ))) •
        (EuclideanSpace.single i (1 : ℂ) : CVec3) := by
  have hsd : HasFDerivAt s (fderiv ℝ s x.1) x.1 :=
    ((hs.differentiable (by simp)) x.1).hasFDerivAt
  have hgd : HasFDerivAt g (fderiv ℝ g x.2) x.2 :=
    ((hg.1.differentiable (by simp)) x.2).hasFDerivAt
  have hS : HasFDerivAt (fun z : ℝ × Space => s z.1)
      ((fderiv ℝ s x.1).comp (ContinuousLinearMap.fst ℝ ℝ Space)) x :=
    HasFDerivAt.comp x hsd hasFDerivAt_fst
  have hG : HasFDerivAt (fun z : ℝ × Space => g z.2)
      ((fderiv ℝ g x.2).comp (ContinuousLinearMap.snd ℝ ℝ Space)) x :=
    HasFDerivAt.comp x hgd hasFDerivAt_snd
  have hF : HasFDerivAt (fun z : ℝ × Space => (s z.1 * g z.2) • (EuclideanSpace.single i (1 : ℂ) : CVec3))
      ((s x.1 • (fderiv ℝ g x.2).comp (ContinuousLinearMap.snd ℝ ℝ Space) +
          g x.2 • (fderiv ℝ s x.1).comp (ContinuousLinearMap.fst ℝ ℝ Space)).smulRight
        (EuclideanSpace.single i (1 : ℂ) : CVec3)) x :=
    (hS.mul hG).smul_const (EuclideanSpace.single i (1 : ℂ) : CVec3)
  have hfun : prodTest s g i = fun z : ℝ × Space => (s z.1 * g z.2) • (EuclideanSpace.single i (1 : ℂ) : CVec3) := rfl
  simp only [dy]
  rw [hfun, hF.fderiv]
  simp [coordinateVector]

theorem pairFProd : PairFProd := by
  intro P s g j i hs hg f
  have hpt : ∀ t : ℝ, ∀ y : Space,
      dotL ((-dy j (prodTest s g i)) (t, y)) (f (t, y)) =
        -(s t * (fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * f (t, y) i)) := by
    intro t y
    rw [Pi.neg_apply, dy_prodTest s g i j hs hg (t, y), ← neg_smul, dotL_single_smul]
    dsimp only
    ring
  have hint : ∀ t : ℝ,
      ∫ y : Space, dotL ((-dy j (prodTest s g i)) (t, y)) (f (t, y)) =
        -(s t * ∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * f (t, y) i) := by
    intro t
    simp only [hpt t]
    rw [integral_neg, integral_const_mul]
  refine ⟨?_, ?_⟩
  · unfold pairF phaseInt
    simp only [hint]
    rw [integral_neg, smul_neg]
  · unfold pairF phaseInt
    have hpt2 : ∀ t y, dotL ((prodTest s g i) (t, y)) (f (t, y)) = s t * (g y * f (t, y) i) := by
      intro t y
      show dotL ((s t * g y) • (EuclideanSpace.single i (1 : ℂ) : CVec3)) (f (t, y)) = _
      rw [dotL_single_smul]
      ring
    simp only [hpt2, integral_const_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
