import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound

/-!
# `PartIII-b:C/ward/10`: `WardHBoundL` from the young `L²` bounds of `X₀` and the stream correction

Source of record: `the November 2 reference manuscript` (73 pages).

`wardHBoundL_of : WardXYoungL2 → WardHBoundL` is compiled in `Ward/HBound.lean`.  The only
remaining analytic leaf is `WardXYoungL2` (source 4194-4196).  `X = 𝒞_y X₀ = χ_y X₀ + corr`
(`wardStreamCut`, 4180-4186), and the leaf splits into

* `WardX0YoungL2`: `X₀ = W_μ - W_{μ+1}` and `∂_jX₀` on the young chart region
  (`sep:young` 3633-3648, `p = q = 2`, `b = 1`, `j ≤ 1`, on the cut old source, 4171-4174);
* `WardStreamCorrYoungL2`: the stream-cutoff correction `(χ_y'/r)Ψ_{X₀}e_z` and its first partials
  (translation-invariant majorant, 3687-3713).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The stream-cutoff correction `(χ_y'/r)Ψ_Z e_z` of `𝒞_yZ` (source 4180-4186). -/
def wardStreamCorr (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y * outPrim Z τ (ϱ y) (y 2)) •
    coordinateVector 2

theorem wardX_eq_cut_add_corr (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    wardX ν μ R c χy g τ y =
      χy (ν * age R y) • wardX0 ν μ R c g τ y + wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y :=
  rfl

/-- **`X₀` and `∂_jX₀` on the young support** (source 4171-4174, 4194-4196; `sep:young` 3633-3648
with `p = q = 2`, `b = 1`, `j ≤ 1`, `D = R√ν(1 - √(5/6))`, `inf_K(2μ + 3/2) > 0` for `μ > -1/4`,
applied to the cut old source `oldCutSrc` and transferred by `oldSourceReg_of`/`SepWCongrAE`;
lift identity 2684-2689): for old `L²` data the young chart readings of `X₀` and of its first
partials are bounded by `C‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardX0YoungL2 : Prop :=
  ∀ (ν μ R c : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R C (wardX0 ν μ R c g) g ∧
        ∀ j : Fin 3, YoungL2Le c ν R C (fun τ => physPd (wardX0 ν μ R c g τ) j) g

/-- **The stream-cutoff correction on the young support** (source 4180-4186, 3687-3713): the
correction `(χ_y'/r)Ψ_{X₀}e_z` (supported on the annulus `R√ν ≤ ϱ ≤ R√(1.25ν)`, where
`χ_y' ≠ 0`) and its first partials have young chart readings bounded by `C‖g‖`; `Ψ` is dominated
by the translation-invariant majorant `CD^{-2}(D² + |z - z_src|²)^{-1}1_{|y' - z'_src| ≤ CD}` of
`L¹` norm `CD^{-1}`, so the `sep:young` bound of `X₀` persists. -/
def WardStreamCorrYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R C (wardStreamCorr ν R χy (wardX0 ν μ R c g)) g ∧
        ∀ j : Fin 3, YoungL2Le c ν R C
          (fun τ => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j) g

/-- **Decomposed target**: `WardHBoundL` from the unconditional leaf `WardXYoungL2`
(which follows from `WardX0YoungL2` and `WardStreamCorrYoungL2` by `X = χ_yX₀ + corr`). -/
theorem wardHBoundL_proved_of (h : WardXYoungL2) : WardHBoundL := wardHBoundL_of h

end UnforcedLeray.Short.PartIIIb.Concrete
