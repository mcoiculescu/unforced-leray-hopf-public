import UnforcedLeray.Loc.Hyp.H2ProductBound.Column
import UnforcedLeray.Loc.Hyp.H2EmbedsC0

/-!
# Hypothesis H-H2Prod: the `H²(ℝ³)` product bound

`paper/main.tex` line 504 ("The `H²` product bound and multiplication by `W^{2,∞}` fields, followed
by `loc:eq:inverse-bound`, give affine, linear and bilinear bounds"); blueprint units B1021
(`loc:eq:local-fixed-point`, the bilinear term `𝒩(z) = -𝔓 div(z ⊗ z)`) and B0721
(`unlabeled:463`, the operator `𝓝`), infrastructure INF11. The hypothesis is
`UnforcedLeray.Blueprint.L10.H2ProductBound` (`Loc/L10Nonlinear.lean`): there is `C` with
`‖g_j f‖_{H²} ≤ C ‖f‖_{H²} ‖g‖_{H²}` for the columns `g_j f` of `f ⊗ g` (line 107).

## Files

* `H2ProductBound/L4.lean`: `H¹ ⊂ L⁴` (interpolation `‖f‖₄⁴ ≤ ‖f‖₂‖f‖₆³` and the compiled
  `H¹ ⊂ L⁶`) and the Hölder bound `‖U_j V‖₂ ≤ l4Const² ‖U‖_{H¹}‖V‖_{H¹}`.
* `H2ProductBound/Column.lean`: the weak product rule (`L01.leibniz`) twice, giving
  `∂ₖ(g_j f) = (∂ₖg)_j f + g_j ∂ₖf` and
  `∂ₗ∂ₖ(g_j f) = (∂ₗ∂ₖg)_j f + (∂ₖg)_j ∂ₗf + (∂ₗg)_j ∂ₖf + g_j ∂ₗ∂ₖf`, with the `L²` bounds
  `‖g‖_∞‖·‖₂`, `‖·‖₂‖f‖_∞` and `‖∂ₖg‖₄‖∂ₗf‖₄`; the result is
  `H2Prod.exists_column_H2` (for any `L^∞` constant `A`,
  `‖g_j f‖_{H²} ≤ 13 (A + l4Const²) ‖f‖_{H²}‖g‖_{H²}`) and `h2ProductBound_of`.
* this file: `H² ⊂ L^∞` from `Loc/Hyp/H2EmbedsC0.lean` (`h2EmbedsC0`, blueprint B0711).

Main declaration: `h2ProductBound`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Blueprint.L10

/-- **Hypothesis H-H2Prod holds: the `H²(ℝ³)` product bound** (`paper/main.tex` line 504;
blueprint B1021, B0721, INF11). There is `C` such that for all `f, g ∈ H²(ℝ³;ℝ³)` and every `j`,
the column `g_j f` of `f ⊗ g` is in `H²` with `‖g_j f‖_{H²} ≤ C ‖f‖_{H²} ‖g‖_{H²}`. -/
theorem h2ProductBound : H2ProductBound :=
  h2ProductBound_of h2EmbedsC0

end UnforcedLeray.Blueprint.L10
