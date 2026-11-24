import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.FormulaW
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit

/-!
# Mean part helper: the integrand of `sepVmu0` (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The horizontal lift `(x', Y) ↦ (x', 0)` of the integration variable. -/
def mpV3 (w : (ℝ × ℝ) × ℝ) : Space := !₂[w.1.1, w.1.2, 0]

/-- The product measure `(vol|_{(0,1)}) ⊗ vol` on `(λ, w)`. -/
def mpRho2 : Measure (ℝ × ((ℝ × ℝ) × ℝ)) := (volume.restrict (Ioo (0 : ℝ) 1)).prod volume

/-- The integrand of `V_{μ,0}` (`i`-th component), with the factor `-2`. -/
def mpVF (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space)
    (i : Fin 3) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => heatLerayK0 i j x) (x - p.1 • mpV3 p.2) (coordinateVector k) : ℝ) : ℂ) *
      ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

/-- The candidate derivative of `mpVF` in `x`. -/
def mpVF' (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space)
    (i : Fin 3) : Space →L[ℝ] ℂ :=
  (-2 : ℂ) • (((p.1 : ℂ) ^ (2 * μ + 2)) • (∑ j : Fin 3, ∑ k : Fin 3,
    ((G p.2.1 p.2.2 j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
        (fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2))))))

theorem mp_entry_le (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) : |M j k| ≤ tensorNorm M := by
  have h := t17m_entry_sq_le M j k
  rw [t17m_tn_sq] at h
  unfold tensorNorm
  exact Real.abs_le_sqrt h

theorem mpVF_hasFDerivAt (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (p : ℝ × ((ℝ × ℝ) × ℝ)) (x : Space) (hx : x - p.1 • mpV3 p.2 ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun x => mpVF μ G p x i) (mpVF' μ G p x i) x := by
  have hS := mp_hasFDerivAt_sum (fun j => fun x => heatLerayK0 i j x) (p.1 • mpV3 p.2) x
    (fun j => by simpa using contDiffAt_nat (mp_K0_contDiffAt _ hx i j) 2)
    (fun j k => G p.2.1 p.2.2 j k)
  have := (hS.const_mul ((p.1 : ℂ) ^ (2 * μ + 2))).const_mul (-2 : ℂ)
  simpa [mpVF, mpVF'] using this

end UnforcedLeray.Short.IIIa

end
