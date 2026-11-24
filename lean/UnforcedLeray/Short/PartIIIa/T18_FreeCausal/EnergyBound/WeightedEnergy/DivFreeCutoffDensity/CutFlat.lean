import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/10`: the cut-off fields are spatial flat tests

Target (`Sub/T18_3_1_1.lean`): `DfcCutFlat`. Uses `dfcCutPd` (`CutPd.lean`).
Source of record: `the November 2 reference manuscript`, lines 3541-3552.

The four fields of `IsFlatSpatialTest` for `dfcCut u k φ θ`:
smoothness from the smoothness of `u_k`, `φ`, `θ`; `c`-periodicity from that of `φ` and `θ`;
vanishing for `|η| > 2(k+1)` from `DfcScaled.vanish`; divergence freeness from `dfcCutPd`,
`DfcPotential.pd0` (`∂_q θ = -φ₁`) and the divergence freeness of `φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcCutFlatAux

theorem apply0 (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    dfcCut u k φ θ y 0 = u k y.2 * φ y 0 + deriv (u k) y.2 * θ y := rfl

theorem apply1 (u : ℕ → ℝ → ℝ) (k : ℕ) (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    dfcCut u k φ θ y 1 = u k y.2 * φ y 1 := rfl

/-- Smoothness of the two components of the cut-off field. -/
theorem comp_smooth (u : ℕ → ℝ → ℝ) (hu : ∀ k, ContDiff ℝ ∞ (u k)) (k : ℕ)
    (φ : ℝ × ℝ → Fin 2 → ℝ) (θ : ℝ × ℝ → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ fun x => φ x i)
    (hθ : ContDiff ℝ ∞ θ) (i : Fin 2) :
    ContDiff ℝ ∞ fun y => dfcCut u k φ θ y i := by
  have hdu : ContDiff ℝ ∞ (deriv (u k)) := (contDiff_infty_iff_deriv.mp (hu k)).2
  have hus : ContDiff ℝ ∞ (fun y : ℝ × ℝ => u k y.2) := (hu k).comp contDiff_snd
  have hdus : ContDiff ℝ ∞ (fun y : ℝ × ℝ => deriv (u k) y.2) := hdu.comp contDiff_snd
  have h0 : ContDiff ℝ ∞ fun y : ℝ × ℝ => dfcCut u k φ θ y 0 := by
    show ContDiff ℝ ∞ fun y : ℝ × ℝ => u k y.2 * φ y 0 + deriv (u k) y.2 * θ y
    exact (hus.mul (hφ 0)).add (hdus.mul hθ)
  have h1 : ContDiff ℝ ∞ fun y : ℝ × ℝ => dfcCut u k φ θ y 1 := by
    show ContDiff ℝ ∞ fun y : ℝ × ℝ => u k y.2 * φ y 1
    exact hus.mul (hφ 1)
  fin_cases i
  · exact h0
  · exact h1

end DfcCutFlatAux

/-- **The cut-off fields are spatial flat tests** (`PartIII-a:T18/3/1/1/10`). Proves `DfcCutFlat`. -/
theorem dfcCutFlat : UnforcedLeray.Short.IIIa.DfcCutFlat := by
  unfold UnforcedLeray.Short.IIIa.DfcCutFlat
  intro c hc u hu φ θ hφ hθ k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact fun i => DfcCutFlatAux.comp_smooth u hu.smooth k φ θ hφ.smooth hθ.smooth i
  · -- c-periodicity in q
    intro x i
    fin_cases i
    · show u k x.2 * φ (x.1 + c, x.2) 0 + deriv (u k) x.2 * θ (x.1 + c, x.2) =
        u k x.2 * φ x 0 + deriv (u k) x.2 * θ x
      rw [hφ.periodic x 0, hθ.periodic x]
    · show u k x.2 * φ (x.1 + c, x.2) 1 = u k x.2 * φ x 1
      rw [hφ.periodic x 1]
  · -- flatness in η
    refine ⟨2 * ((k : ℝ) + 1), fun x i hx => ?_⟩
    obtain ⟨h0, h1⟩ := hu.vanish k x.2 hx
    fin_cases i
    · show u k x.2 * φ x 0 + deriv (u k) x.2 * θ x = 0
      rw [h0, h1]
      ring
    · show u k x.2 * φ x 1 = 0
      rw [h0]
      ring
  · -- divergence free
    intro x
    obtain ⟨e00, -, -, e11⟩ := dfcCutPd u hu.smooth φ θ hφ.smooth hθ.smooth k x
    rw [e00, e11, hθ.pd0 x]
    linear_combination (u k x.2) * hφ.divFree x

end UnforcedLeray.Short.IIIa
