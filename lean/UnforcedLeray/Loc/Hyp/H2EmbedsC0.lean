import UnforcedLeray.Loc.L01Coefficient
import UnforcedLeray.Lib.SobolevC.C0Rep
import UnforcedLeray.Lib.Sobolev.Bridge
import UnforcedLeray.Lib.Sobolev.Complexify

/-!
# The hypothesis `H2EmbedsC0` is a theorem: `H²(ℝ³;ℝ³) ⊂ C₀(ℝ³;ℝ³)`

`paper/main.tex` lines 279–285 (`loc:eq:coefficient-maps`: `r_heat ∈ C_per H²` gives
`U_* ∈ C_per C₀`, line 280, and `‖g‖_∞ ≤ C‖g‖_{H²}` for `g ∈ Z`, line 285); blueprint unit
B0711 (infrastructure INF11, "`H²(ℝ³) ⊂ C₀ ∩ L^∞`"). The hypothesis is the Prop
`UnforcedLeray.Blueprint.H2EmbedsC0` of `Loc/L01Coefficient.lean` (line 50).

## Proof
Transport `F : SobolevGraph.H2` to the Sobolev space `W^{2,2}(ℝ³;ℝ³)` of `Lib/Sobolev`
through the componentwise isometry `Sob.h2Equiv` (`Lib/Sobolev/Bridge.lean`), complexify it
isometrically (`Sob.W.complexify`, `Lib/Sobolev/Complexify.lean`), and apply the Fourier
embedding `Sob.W.exists_C0_rep` (`Lib/SobolevC/C0Rep.lean`: `𝓕x ∈ L¹` with
`‖𝓕x‖₁ ≤ ‖⟨ξ⟩^{-2}‖₂ · 2 · ‖x‖_{H²}` since `3 < 2·2`, then Riemann–Lebesgue for `𝓕⁻¹(𝓕x)`).
The componentwise real part of the complex representative is the real representative; it is
continuous, tends to `0` at infinity, and is pointwise bounded by the complex one.

## Main declaration
* `h2EmbedsC0 : H2EmbedsC0`.

No hypothesis is strengthened: the statement proved is the Prop `H2EmbedsC0` itself, with the
`H²` norm the project's exact ordered-derivative graph norm (`SobolevGraph.H2.norm_sq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Blueprint

namespace H2EmbedsC0Proof

/-- The componentwise real part `ℂ³ → ℝ³` is a contraction. -/
theorem norm_reL_le (w : EuclideanSpace ℂ (Fin 3)) : ‖Sob.reL 3 w‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [Sob.reL_apply, Real.norm_eq_abs, sq_abs]
  have h := Complex.abs_re_le_norm (w i)
  nlinarith [abs_nonneg (w i).re, sq_abs (w i).re]

/-- The real part undoes the complex inclusion. -/
theorem reL_ofRealL (x : EuclideanSpace ℝ (Fin 3)) : Sob.reL 3 (Sob.ofRealL 3 x) = x := by
  ext i
  simp

end H2EmbedsC0Proof

open H2EmbedsC0Proof in
/-- **`H2EmbedsC0` holds** (tex lines 280 and 285; blueprint B0711, INF11): every class
`F ∈ H²(ℝ³;ℝ³)` (the project's `SobolevGraph.H2`) has a representative
`v ∈ C₀(ℝ³;ℝ³)` with `‖v‖_∞ ≤ C‖F‖_{H²}`, with one constant `C` for all `F`. -/
theorem h2EmbedsC0 : H2EmbedsC0 := by
  obtain ⟨C, -, hC⟩ := Sob.W.exists_C0_rep (n := 3) (k := 2)
    (F := EuclideanSpace ℂ (Fin 3)) (by norm_num)
  refine ⟨C, fun F => ?_⟩
  set x := Sob.h2Equiv F with hx
  set z := Sob.W.complexify x with hz
  obtain ⟨g, hgc, hg0, hgae, hgb⟩ := hC z
  -- the real representative
  let v : Space → Space := fun y => Sob.reL 3 (g y)
  have hvc : Continuous v := (Sob.reL 3).continuous.comp hgc
  have hv0 : Tendsto v (cocompact Space) (𝓝 0) := by
    have h := ((Sob.reL 3).continuous.tendsto 0).comp hg0
    rw [map_zero] at h
    exact h
  let V : ZeroAtInftyContinuousMap Space Space :=
    { toFun := v
      continuous_toFun := hvc
      zero_at_infty' := hv0 }
  -- the norms
  have hnz : ‖z‖ = ‖F‖ := by
    rw [hz, Sob.W.norm_complexify, hx, LinearIsometryEquiv.norm_map]
  have hpt : ∀ y, ‖v y‖ ≤ C * ‖F‖ := fun y =>
    (norm_reL_le (g y)).trans ((hgb y).trans_eq (by rw [hnz]))
  have hCF : 0 ≤ C * ‖F‖ := (norm_nonneg _).trans (hpt 0)
  refine ⟨V, ?_, ?_⟩
  · -- `v = F` almost everywhere
    have h1 : ⇑(Sob.W.value (Sob.wholeSpace 3) 1 ℂ (EuclideanSpace ℂ (Fin 3)) 2 2 z)
        =ᵐ[volume] fun y => Sob.ofRealL 3
          (Sob.W.value (Sob.wholeSpace 3) 1 ℝ Space 2 2 x y) := by
      rw [hz, Sob.W.complexify, Sob.W.value_mapCLM]
      exact (Sob.ae_eq_wμ_iff _ _).mp
        ((Sob.ofRealL 3).toContinuousLinearMap.coeFn_compLp' _)
    have h2 := Sob.h2Equiv_value F
    filter_upwards [hgae, h1, h2] with y hy1 hy2 hy3
    change Sob.reL 3 (g y) = (F.value : SpatialField) y
    rw [← hy1, hy2]
    change Sob.reL 3 (Sob.ofRealL 3
      (Sob.W.value (Sob.wholeSpace 3) 1 ℝ Space 2 2 (Sob.h2Equiv F) y)) = _
    rw [reL_ofRealL, hy3]
  · -- the sup bound
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact (BoundedContinuousFunction.norm_le hCF).mpr hpt

/-- **`H² ⊂ L^∞`** (tex line 285, `‖g‖_∞ ≤ C‖g‖_{H²}`; blueprint B0711, B1021 ingredient): the
almost-everywhere form of `h2EmbedsC0`, with a nonnegative constant. -/
theorem h2_ae_norm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobolevGraph.H2,
    ∀ᵐ x ∂(volume : Measure Space), ‖(F.value : SpatialField) x‖ ≤ C * ‖F‖ := by
  obtain ⟨C, hC⟩ := h2EmbedsC0
  refine ⟨max C 0, le_max_right _ _, fun F => ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC F
  filter_upwards [hv] with x hx
  rw [← hx]
  calc ‖(v : SpatialField) x‖ ≤ ‖v‖ := by
        rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact BoundedContinuousFunction.norm_coe_le_norm v.toBCF x
    _ ≤ C * ‖F‖ := hvC
    _ ≤ max C 0 * ‖F‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end UnforcedLeray.Blueprint
