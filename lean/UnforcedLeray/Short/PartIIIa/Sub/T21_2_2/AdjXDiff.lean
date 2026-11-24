import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# `PartIII-a:T21/2/2`: differentiability of the adjoint in `X_{-m,c}` (SP 3060-3073)

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073: the
energies `E_0 = ‖φ‖²_{X_{-m}}`, `E_1 = Σ_k ‖∂_kφ‖²_{X_{-m}}` (weight `p_d⁻¹`) are used as classical
quantities of the reverse time, `E_1'` and `E_2` appearing in `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`.

On the fixed physical cylinder `r ↦ φ(r)` and `r ↦ ∂_kφ(r)` are differentiable as maps into
`X_{-m,c}` before the terminal age, with derivatives `∂_rφ(r)` and `∂_k∂_rφ(r)`. This is not a
pointwise-majorant statement (the cell `B0579.cell c` is an infinite strip, and a majorant of
`sup_{r'} |∂_rφ(r')|` would need `∂_r²φ`); it follows from `IsAdjointFlow.higherCont` by the
fundamental theorem of calculus in `r` at each point `x` (`jointSmooth`) and Minkowski's inequality:
`‖φ(r') - φ(r) - (r' - r)∂_rφ(r)‖_X ≤ |∫_r^{r'} ‖∂_rφ(ρ) - ∂_rφ(r)‖_X dρ|`, which is `o(|r' - r|)` by
the continuity of `ρ ↦ ∂_rφ(ρ)` in `X_{-m,c}`. It is the common input of the differentiation of
`E_0` (`PartIII-a:T21/2/2/2/2`) and of `E_1` (`PartIII-a:T21/2/2/3/5`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`r ↦ ∂^wφ(r)` is differentiable in `X_{-m,c}`** (SP 3060-3073), for the words `w` of at most
one spatial derivative: at every `r ∈ (t, s)`, the difference quotient of `∂^wφ` converges in
`X_{-m,c}` to `∂^w∂_rφ(r)` (`adjSpatial w (adjDt t s φ r)`; `∂_k∂_rφ = ∂_r∂_kφ` by `jointSmooth`). -/
def AdjXDiff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ∀ r ∈ Ioo t s, ∀ w : List (Fin 2),
        w.length ≤ 1 →
        Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m)
            ((r' - r)⁻¹ • (adjSpatial w (φ r') - adjSpatial w (φ r)) -
              adjSpatial w (adjDt t s φ r)))
          (𝓝[≠] r) (𝓝 0)

end UnforcedLeray.Short.IIIa
