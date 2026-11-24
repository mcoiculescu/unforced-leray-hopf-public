import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# Transposed test operators on phase tests (INF25 T25.1)

Blueprint units B0411 (tex 7313–7337) and B0005 (tex 136–147). The operators of the free
graph are `νΔ` and `T₀ = ∂_τ − ½ y·∇` (tex 7318). A distributional identity `L w = g` is
tested through the transpose `Lᵗ`: `⟪Lᵗ Φ, w⟫ = ⟪Φ, g⟫`. The transposes are

* `Δᵗ = Δ` (`lapT`),
* `T₀ᵗ Φ = −∂_τ Φ + ½ y·∇Φ + (3/2) Φ` (`driftT`), since `div y = 3`,
* `∂ⱼᵗ = −∂ⱼ` (`dy`, used with a minus sign),

and the distributional divergence is tested against gradients of scalar tests (`gradT`).
Derivatives are Fréchet derivatives of the test in the directions `(1, 0)` and `(0, eⱼ)` of
`ℝ × ℝ³`. Every operator maps phase tests to phase tests.

Status: infrastructure only; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The phase derivative `∂_τ Φ`. -/
def dτ (Φ : ℝ × Space → F) : ℝ × Space → F := fun p => fderiv ℝ Φ p (1, 0)

/-- The spatial derivative `∂_{y_j} Φ`. -/
def dy (j : Fin 3) (Φ : ℝ × Space → F) : ℝ × Space → F :=
  fun p => fderiv ℝ Φ p (0, coordinateVector j)

/-- The spatial Laplacian `Δ_y Φ = ∑ⱼ ∂ⱼ∂ⱼ Φ`. -/
def lapT (Φ : ℝ × Space → F) : ℝ × Space → F := fun p => ∑ j : Fin 3, dy j (dy j Φ) p

/-- The radial derivative `y·∇Φ = ∑ⱼ yⱼ ∂ⱼΦ`. -/
def radialT (Φ : ℝ × Space → F) : ℝ × Space → F := fun p => ∑ j : Fin 3, (p.2 j) • dy j Φ p

/-- The transpose of `T₀ = ∂_τ − ½ y·∇`: `T₀ᵗ Φ = −∂_τ Φ + ½ y·∇Φ + (3/2) Φ`. -/
def driftT (Φ : ℝ × Space → F) : ℝ × Space → F :=
  fun p => -dτ Φ p + (1 / 2 : ℝ) • radialT Φ p + (3 / 2 : ℝ) • Φ p

/-- The gradient `∇_y φ` of a scalar test, as a `ℂ³`-valued function. -/
def gradT (φ : ℝ × Space → ℂ) : ℝ × Space → CVec3 :=
  fun p => ∑ j : Fin 3, dy j φ p • EuclideanSpace.single j (1 : ℂ)

namespace IsPhaseTest

variable {P : ℝ} {Φ : ℝ × Space → F}

theorem dτ (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (PhaseSpace.dτ Φ) :=
  hΦ.fderiv_apply (1, 0)

theorem dy (hΦ : IsPhaseTest P Φ) (j : Fin 3) : IsPhaseTest P (PhaseSpace.dy j Φ) :=
  hΦ.fderiv_apply (0, coordinateVector j)

theorem lapT (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (PhaseSpace.lapT Φ) := by
  have h : PhaseSpace.lapT Φ = ∑ j : Fin 3, PhaseSpace.dy j (PhaseSpace.dy j Φ) := by
    funext p
    simp [PhaseSpace.lapT]
  rw [h]
  exact IsPhaseTest.sum _ fun j _ => (hΦ.dy j).dy j

theorem radialT (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (PhaseSpace.radialT Φ) := by
  have h : PhaseSpace.radialT Φ = ∑ j : Fin 3, fun p => (p.2 j) • PhaseSpace.dy j Φ p := by
    funext p
    simp [PhaseSpace.radialT]
  rw [h]
  exact IsPhaseTest.sum _ fun j _ => (hΦ.dy j).coord_smul j

theorem driftT (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (PhaseSpace.driftT Φ) := by
  have h : PhaseSpace.driftT Φ =
      -PhaseSpace.dτ Φ + (1 / 2 : ℝ) • PhaseSpace.radialT Φ + (3 / 2 : ℝ) • Φ := by
    funext p
    simp [PhaseSpace.driftT]
  rw [h]
  exact (hΦ.dτ.neg.add (hΦ.radialT.const_smul _)).add (hΦ.const_smul _)

theorem gradT {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (PhaseSpace.gradT φ) := by
  have h : PhaseSpace.gradT φ = ∑ j : Fin 3, fun p =>
      ((ContinuousLinearMap.id ℝ ℂ).smulRight (EuclideanSpace.single j (1 : ℂ) : CVec3))
        (PhaseSpace.dy j φ p) := by
    funext p
    simp [PhaseSpace.gradT]
  rw [h]
  exact IsPhaseTest.sum _ fun j _ => (hφ.dy j).clm_comp _

end IsPhaseTest

end UnforcedLeray.PhaseSpace
