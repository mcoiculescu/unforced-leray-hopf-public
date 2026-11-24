import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5` (`e1MovingDeriv`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2860-2864
(`d_z/d = -1/(2θ)`), 2945-2957, 3060-3062 and 3137-3139 (Reynolds' term cancels the dilation seam
term; the calculation is made on the fixed physical cylinder and rescaled).

The reverse moving energy `revE1 ν c m φ s ζ'` equals, for `ζ'` in the flow window, the fixed-cell
physical energy `physE1 ν c m φ (revAge ν s ζ')`, `r = revAge ν s ζ'`:
`E_1 = a⁻² Σ_k ∫_{C_c} wh(a,x) |∂_k φ(r,x)|² dx`, `wh(a,x) = p_{c/√a}⁻¹(x/√a)`.
`e1MovingDeriv_of` derives `E1MovingDeriv m` from
* `E1ChangeVar` (rescaling `x = √a y` of the cell integral),
* `RevAgeDeriv` (`dr/dζ = -a²`, SP 2857),
* `E1PhysDeriv` (differentiation of `physE1` in `r` on the FIXED cell under the integral sign,
  via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, and rescaling of the result back to
  `e1Rate`; Reynolds / seam cancellation; the genuinely hard analytic leaf).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- The physical fixed-cell energy `a⁻² Σ_k ∫_{C_c} p_{c/√a}⁻¹(x/√a) |∂_k φ(r,x)|² dx`, `a = a(r)`. -/
def physE1 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  (clockA ν r)⁻¹ ^ 2 * ∑ k : Fin 2, ∫ x in B0579.cell c,
    periodicWeight (-m) (cellLen c (clockA ν r))
      (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)) * ‖pdCx k (φ r) x‖ ^ 2

/-- **Leaf A** (SP 2860-2864; change of variables `x = √a y`, `|∂_kΦ|² = a⁻¹ |∂_kφ|²(√a y)`,
`dy = a⁻¹ dx`, `φ r` smooth for `r ∈ [t, s)` by `IsAdjointFlow.smooth`, `revAge ν s ζ ∈ [t, s)`
for `ζ ∈ (0, Δz)`): `revE1 = physE1 ∘ revAge` on the flow window. -/
def E1ChangeVar (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ = physE1 ν (ν ^ (-2 : ℝ)) m φ (revAge ν s ζ)

/-- **Leaf B** (SP 2857): `revAge ν s ζ = z/(1-νz)`, `z = z_s - ζ`, has derivative
`-1/(1-νz)² = -a(r)²` (`a(r) = 1/(1-νz)`, `1 - νz > 0` since `z < z_s < 1/ν`). -/
def RevAgeDeriv (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    HasDerivAt (revAge ν s) (-(clockA ν (revAge ν s ζ)) ^ 2) ζ

/-- **Leaf C** (SP 2945-2957, 3060-3062, 3137-3139; the hard leaf): under the hypotheses of
`E1MovingDeriv`, `physE1` is differentiable at the age `r = revAge ν s ζ`, with derivative `D`
satisfying `-a(r)² D = e1Rate` (chain rule `dr/dζ = -a²`).  Route (no pointwise majorant: the cell
is an infinite strip and a majorant of `sup_r |∂_r∂_kφ|` needs `∂_r²φ`): `r' ↦ ∂_kφ(r')` is
differentiable in `X_{-m,c}` with derivative `∂_k∂_rφ(r)` (`AdjXDiff`, `w = [k]`, from
`IsAdjointFlow.higherCont`), so the weighted norm `∫ wt(a(r'),x)|∂_kφ(r',x)|²` is differentiable by
the product rule, the moving weight being controlled by `wtRatio_le`, `continuousAt_wtRatio`
(`Sub/T21_2_2_1_F1/WtCore.lean`); then use `∂_r ∂_kφ = -∂_k(ν Δφ + v·∇φ - χ_phys)` (the rescaled
`MovAdjEquation`, the hypothesis `HasDerivAt` of `mvPhi`, integrated by parts on the periodic cell
with `MovAdjHigherReg`), and rescale back `x = √a y`; the Reynolds boundary term of the moving cell
cancels the dilation seam term. -/
def E1PhysDeriv (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    ∀ χ : ℝ × ℝ → ℂ, ContDiff ℝ 1 χ →
      (∀ y : ℝ × ℝ, χ (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2) = χ y) →
      (∀ y : ℝ × ℝ, HasDerivAt (fun ζ' => mvPhi ν φ s ζ' y)
        (adjGen (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y - χ y) ζ) →
      (∀ k : Fin 2, IntegrableOn
        (fun y => periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y * ‖pdCx k χ y‖ ^ 2)
        (B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ))) →
      ∃ D : ℝ, HasDerivAt (physE1 ν (ν ^ (-2 : ℝ)) m φ) D (revAge ν s ζ) ∧
        -(clockA ν (revAge ν s ζ)) ^ 2 * D =
          e1Rate m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ)
            (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) χ

/-- **`E1MovingDeriv` from the three leaves** (chain rule through `revAge`). -/
theorem e1MovingDeriv_of (m : ℝ) (hA : E1ChangeVar m) (hB : RevAgeDeriv m) (hC : E1PhysDeriv m) :
    E1MovingDeriv m := by
  intro ν tr t s φ ζ hζ χ hχ hper hder hint
  obtain ⟨D, hD, hDe⟩ := hC ν tr t s φ ζ hζ χ hχ hper hder hint
  have hcomp : HasDerivAt (physE1 ν (ν ^ (-2 : ℝ)) m φ ∘ revAge ν s)
      ((-(clockA ν (revAge ν s ζ)) ^ 2) • D) ζ :=
    HasDerivAt.scomp ζ hD (hB ν tr t s φ ζ hζ)
  obtain ⟨hν, ht0, hts, hG, hz⟩ := hζ
  have hev : revE1 ν (ν ^ (-2 : ℝ)) m φ s =ᶠ[𝓝 ζ]
      (physE1 ν (ν ^ (-2 : ℝ)) m φ ∘ revAge ν s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with ζ' hz'
    exact hA ν tr t s φ ζ' ⟨hν, ht0, hts, hG, hz'⟩
  have := hcomp.congr_of_eventuallyEq hev
  rw [smul_eq_mul, hDe] at this
  exact this

end UnforcedLeray.Short.IIIa.AdjE1
