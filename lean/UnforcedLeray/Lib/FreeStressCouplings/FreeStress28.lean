import UnforcedLeray.Lib.FreeStressCouplings.Interpolation
import UnforcedLeray.Lib.FreeStressCouplings.Shift

/-!
# `eq:free-stress-28` from the graph estimates (INF10 F2, assembly)


§5 Level F, target **F2** (Wave 1, block 1J, bypass B9); blueprint units **B0474**
(`eq:free-stress-28`, tex 7789-7812) and the duality input of **B0473** (tex 7774-7788).

Statement in the manuscript's terms (tex 7789-7802).  `A ≥ 0` is selfadjoint and `B` is
skew-adjoint, each given by a concrete diagonalisation (bypass B9; `A : MulRep`,
`B : SkewRep`, with unrelated unitaries, so no commutation between `A` and `B` is assumed,
tex 7807-7808).  Put `C₀ = 1 + |B|` (`B.onePlusAbs`) and `D₀ = 1 + A` (`A.onePlus`).  The
inputs are the graph estimates the manuscript cites at tex 7790-7793:

* `B 𝓡_μ` bounded by `M_B` (the Hilbert graph bound, tex 7740-7751), giving `C₀ 𝓡_μ` bounded
  by `‖𝓡_μ‖ + M_B`;
* `A 𝓡_μ*` bounded by `M_A` (B0473: "`A𝓡_μ^*` and `B𝓡_μ^*` are bounded", tex 7787-7788),
  giving `D₀ 𝓡_μ*` bounded by `‖𝓡_μ‖ + M_A`, hence `𝓡_μ D₀` by duality.

Conclusion: `‖C₀^{1/2} 𝓡_μ D₀^{1/2}‖ ≤ C_μ` with the explicit constant
`C_μ = √((‖𝓡_μ‖ + M_A)(‖𝓡_μ‖ + M_B))`, both pointwise on `dom D₀^{1/2}` (`free_stress_28`) and as
a bounded extension to all of `Y₂` (`free_stress_28_extension`).  The constant depends only on
`‖𝓡_μ‖` (at most `a^{-1}`, tex 7750) and the two graph constants, so it is uniform on compact
`μ`-sets and in `ν` whenever those are (blueprint note on B0474; scoping note §5 F2).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace

namespace UnforcedLeray.FreeStress

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The `D₀`-endpoint: `‖𝓡 D₀ x‖ ≤ (‖𝓡‖ + M_A) ‖x‖` on `dom D₀`, from the bound for `A 𝓡*`
(tex 7792-7793, B0473). -/
theorem onePlus_endpoint (A : MulRep H μ E) (R : H →L[ℂ] H) {M_A : ℝ} (hMA : 0 ≤ M_A)
    (hA : ∀ v, ∃ w, A.HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧ ‖w‖ ≤ M_A * ‖v‖) :
    ∀ x y, A.onePlus.HasPow 1 x y → ‖R y‖ ≤ (‖R‖ + M_A) * ‖x‖ := by
  intro x y hxy
  have hadj := A.onePlus_comp_bound (ContinuousLinearMap.adjoint R) hA
  rw [LinearIsometryEquiv.norm_map] at hadj
  exact A.onePlus.norm_apply_le_of_adjoint R (add_nonneg (norm_nonneg _) hMA) hadj hxy

/-- **`eq:free-stress-28`** (B0474, tex 7789-7812), pointwise form.  With `C₀ = 1 + |B|` and
`D₀ = 1 + A`: for `x ∈ dom D₀^{1/2}` with `D₀^{1/2} x = y`, `𝓡 y ∈ dom C₀^{1/2}` and
`‖C₀^{1/2} 𝓡 y‖ ≤ √((‖𝓡‖ + M_A)(‖𝓡‖ + M_B)) ‖x‖`. -/
theorem free_stress_28 (A : MulRep H μ E) (B : SkewRep H ν F) (R : H →L[ℂ] H)
    {M_A M_B : ℝ} (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B)
    (hB : ∀ v, ∃ w, B.HasGen (R v) w ∧ ‖w‖ ≤ M_B * ‖v‖)
    (hA : ∀ v, ∃ w, A.HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧ ‖w‖ ≤ M_A * ‖v‖)
    {x y : H} (hxy : A.onePlus.HasPow (1 / 2) x y) :
    ∃ z, B.onePlusAbs.HasPow (1 / 2) (R y) z ∧
      ‖z‖ ≤ Real.sqrt ((‖R‖ + M_A) * (‖R‖ + M_B)) * ‖x‖ :=
  MulRep.exists_hasPow_half_of_endpoints B.onePlusAbs A.onePlus R
    (add_nonneg (norm_nonneg _) hMA) (add_nonneg (norm_nonneg _) hMB)
    (B.onePlusAbs_comp_bound R hB) (onePlus_endpoint A R hMA hA) hxy

/-- **`eq:free-stress-28`** (B0474, tex 7789-7812), bounded-extension form:
`C₀^{1/2} 𝓡 D₀^{1/2}` extends to a bounded operator `S` on `H` with
`‖S‖ ≤ √((‖𝓡‖ + M_A)(‖𝓡‖ + M_B))`. -/
theorem free_stress_28_extension (A : MulRep H μ E) (B : SkewRep H ν F) (R : H →L[ℂ] H)
    {M_A M_B : ℝ} (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B)
    (hB : ∀ v, ∃ w, B.HasGen (R v) w ∧ ‖w‖ ≤ M_B * ‖v‖)
    (hA : ∀ v, ∃ w, A.HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧ ‖w‖ ≤ M_A * ‖v‖) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ Real.sqrt ((‖R‖ + M_A) * (‖R‖ + M_B)) ∧
      ∀ x y, A.onePlus.HasPow (1 / 2) x y → B.onePlusAbs.HasPow (1 / 2) (R y) (S x) :=
  MulRep.exists_bounded_extension B.onePlusAbs A.onePlus R
    (add_nonneg (norm_nonneg _) hMA) (add_nonneg (norm_nonneg _) hMB)
    (B.onePlusAbs_comp_bound R hB) (onePlus_endpoint A R hMA hA)

end UnforcedLeray.FreeStress
