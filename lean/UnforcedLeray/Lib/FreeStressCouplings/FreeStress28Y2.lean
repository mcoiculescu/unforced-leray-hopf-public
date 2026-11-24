import UnforcedLeray.Lib.FreeStressCouplings.PhaseDrift
import UnforcedLeray.Lib.FreeStressCouplings.FreeStress28

/-!
# `eq:free-stress-28` on `Y₂` with the concrete `A` and `B` (INF10 F1 + F2)


§4 bypass **B9** and §5 Level F, targets **F1**, **F2**; blueprint units **B0459**, **B0473**,
**B0474** (tex 7698-7812, `eq:free-stress-28`).

`free_stress_28_extension` (`FreeStress28.lean`) is stated for abstract concrete
representations.  Here it is instantiated on `Y₂ = Yq P 2` with

* `D₀ = 1 + A`, `A = -νΔ` diagonalised by the fibrewise Fourier transform
  (`phaseD0 P ν hν`, `PhaseLaplacian.lean`);
* `C₀ = 1 + |B|`, `B = T₀ - 3/4` diagonalised through the flow chart and the Fourier transform
  in the chart time (`phaseC0 P`, `PhaseDrift.lean`).

`free_stress_28_Y2` takes the two graph bounds in representation form; `free_stress_28_Y2'`
takes them in the manuscript's form: `B 𝓡_μ v` as the derivative at `t = 0` of the group
`e^{tB}` (phase translation composed with the `L²`-normalised dilation), and `A 𝓡_μ* v` as the
fibrewise distributional `-νΔ`.  The constant `√((‖𝓡_μ‖ + M_A)(‖𝓡_μ‖ + M_B))` is the `C_μ` of
`eq:free-stress-28`.  The graph bounds themselves (tex 7724-7788) are hypotheses here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology SchwartzMap
open scoped Laplacian

namespace UnforcedLeray.FreeStress

open UnforcedLeray.PhaseSpace

variable (P : ℝ) [Fact (0 < P)]

/-- **`eq:free-stress-28` on `Y₂`** (B0474), representation form of the hypotheses. -/
theorem free_stress_28_Y2 (ν : ℝ) (hν : 0 ≤ ν) (R : Yq P 2 →L[ℂ] Yq P 2) {M_A M_B : ℝ}
    (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B)
    (hB : ∀ v, ∃ w, (driftRep P).HasGen (R v) w ∧ ‖w‖ ≤ M_B * ‖v‖)
    (hA : ∀ v, ∃ w, (laplaceRepY P ν hν).HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧
      ‖w‖ ≤ M_A * ‖v‖) :
    ∃ S : Yq P 2 →L[ℂ] Yq P 2, ‖S‖ ≤ Real.sqrt ((‖R‖ + M_A) * (‖R‖ + M_B)) ∧
      ∀ x y, (phaseD0 P ν hν).HasPow (1 / 2) x y → (phaseC0 P).HasPow (1 / 2) (R y) (S x) :=
  free_stress_28_extension (laplaceRepY P ν hν) (driftRep P) R hMA hMB hB hA

/-- **`eq:free-stress-28` on `Y₂`** (B0474), with the graph bounds in the manuscript's form:
`B (R v)` is the derivative at `0` of `t ↦ e^{tB} R v`, and `A (R* v) = -νΔ (R* v)` holds
fibrewise in `𝓢'(ℝ³; ℂ³)` for a.e. phase. -/
theorem free_stress_28_Y2' (ν : ℝ) (hν : 0 ≤ ν) (R : Yq P 2 →L[ℂ] Yq P 2) {M_A M_B : ℝ}
    (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B)
    (hB : ∀ v : Yq P 2, ∃ w : Yq P 2,
      Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (phaseDilation P t (R v) - R v)) (𝓝[≠] 0) (𝓝 w) ∧
        ‖w‖ ≤ M_B * ‖v‖)
    (hA : ∀ v : Yq P 2, ∃ w : Yq P 2, (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        (-(ν : ℂ)) • Δ (((((ContinuousLinearMap.adjoint R) v : Yq P 2) τ :
          Lp CVec3 2 (volume : Measure Space))) : 𝓢'(Space, CVec3)) =
          (((w : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) : 𝓢'(Space, CVec3))) ∧
      ‖w‖ ≤ M_A * ‖v‖) :
    ∃ S : Yq P 2 →L[ℂ] Yq P 2, ‖S‖ ≤ Real.sqrt ((‖R‖ + M_A) * (‖R‖ + M_B)) ∧
      ∀ x y, (phaseD0 P ν hν).HasPow (1 / 2) x y → (phaseC0 P).HasPow (1 / 2) (R y) (S x) := by
  refine free_stress_28_Y2 P ν hν R hMA hMB (fun v => ?_) (fun v => ?_)
  · obtain ⟨w, hw, hwn⟩ := hB v
    exact ⟨w, (driftRep_hasGen_iff P (R v) w).2 hw, hwn⟩
  · obtain ⟨w, hw, hwn⟩ := hA v
    exact ⟨w, (laplaceRepY_hasPow_one_iff P ν hν _ w).2 hw, hwn⟩

end UnforcedLeray.FreeStress
