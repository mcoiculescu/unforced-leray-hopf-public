import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff

/-!
# `PartIII-a:T21/2/2/2/2`: Reynolds' cancellation for `E_0`, the leaf statements

Source of record: `the November 2 reference manuscript` (SP) lines 2860
(`d_z/d = -1/(2θ)`), 2945-2946 (Reynolds' boundary term cancels the dilation seam term) and
3060-3062 (`E_0' + β_min E_1 ≤ C_b E_0`).

On the fixed physical cell `C_c` (`c = ν⁻²`), with `r = revAge ν s ζ`, `a = a(r)`, `d = c/√a`,
`E_0(ζ) = a⁻³ ∫_{C_c} p_d⁻¹(x/√a) |φ(r, x)|² dx`.  The leaves:

* `ReyPhysDeriv` (R1): `r ↦ ∫_{C_c} a⁻³ p_d⁻¹(x/√a)|φ(r,x)|² dx` is differentiable at every
  `r ∈ (t, s)` with derivative the integral of the pointwise `r`-derivative of the integrand. This is
  NOT a dominated-convergence statement with a pointwise majorant: `B0579.cell c` is an infinite
  strip (`η` unbounded), joint smoothness gives no integrable majorant, and a majorant of the
  `r`-derivative of `|φ|²` needs `∂_r²φ`, which `IsAdjointFlow` does not provide (`IsBUCTrain` bounds
  only spatial derivatives of `v`). It follows from `AdjXDiff` (`r ↦ φ(r)` differentiable in
  `X_{-m,c}`, itself from `IsAdjointFlow.higherCont`, SP 3060-3073) by the product rule for the
  weighted norm, the moving weight being controlled by `wtRatio_le`, `continuousAt_wtRatio`
  (`Sub/T21_2_2_1_F1/WtCore.lean`).
* `ReyChange` (R2): the change of variables to the fixed cell, SP 3036-3037.
* `ReyChain` (R3): `dr/dζ = -a²` and `d(d)/dζ = d/(2θ)`, SP 2860.
* `ReyDeriv` (R5): the same for `ζ ↦ ∫ reyIntegrand`, from R1 by the chain rule through `revAge`.
* `ReyIdent` (R4/R6): integrability of `w Re(Φ̄ Ψ)` (from `AdjWeightEquiv` and `memX`) and the
  identification of the derivative with `rate0` (change of variables back, `∂_ζ[φ(r(ζ),x)] =
  λ⁻²(-θ⁻¹Φ + Ψ)` at `y = λx`, SP 2945-2946).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The integrand of `E_0` on the fixed physical cell:
`a⁻³ p_d⁻¹(x/√a) |φ(r, x)|²`, `r = revAge ν s ζ`, `a = a(r)`, `d = c/√a` (SP 3036-3037, 3060). -/
def reyIntegrand (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ((clockA ν (revAge ν s ζ) ^ 3)⁻¹) *
    periodicWeight (-m) (cellLen c (clockA ν (revAge ν s ζ)))
      (x.1 / Real.sqrt (clockA ν (revAge ν s ζ)), x.2 / Real.sqrt (clockA ν (revAge ν s ζ))) *
    ‖φ (revAge ν s ζ) x‖ ^ 2

/-- The integrand of `E_0` on the fixed physical cell as a function of the age `r`:
`a(r)⁻³ p_d⁻¹(x/√a) |φ(r, x)|²`, `a = a(r)`, `d = c/√a`. -/
def physE0Integrand (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  ((clockA ν r ^ 3)⁻¹) *
    periodicWeight (-m) (cellLen c (clockA ν r)) (x.1 / Real.sqrt (clockA ν r),
      x.2 / Real.sqrt (clockA ν r)) * ‖φ r x‖ ^ 2

/-- The fixed-cell energy `E_0` as a function of the age: `∫_{C_c} physE0Integrand`. -/
def physE0 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  ∫ x in B0579.cell c, physE0Integrand ν c m φ r x

theorem reyIntegrand_eq (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (s ζ : ℝ) (x : ℝ × ℝ) :
    reyIntegrand ν c m φ s ζ x = physE0Integrand ν c m φ (revAge ν s ζ) x := rfl

/-- **R1: differentiation of the fixed-cell energy in the age** (SP 3060-3073; from `AdjXDiff`, the
product rule for `∫ w(a(r), x)|φ(r, x)|²` and the weight bounds, not from a pointwise majorant):
for `r ∈ (t, s)`, `physE0` has derivative `∫_{C_c} ∂_r[a⁻³ p_d⁻¹(x/√a) |φ(r, x)|²]`. -/
def ReyPhysDeriv (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ∀ r ∈ Ioo t s,
        HasDerivAt (physE0 ν (ν ^ (-2 : ℝ)) m φ)
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            deriv (fun r' => physE0Integrand ν (ν ^ (-2 : ℝ)) m φ r' x) r) r

/-- **R2: change of variables to the fixed cell** (SP 3036-3037): `y = x/√a`, `dy = dx/a`,
`Φ = a⁻¹φ(r, √a ·)`, `d = c/√a`. -/
def ReyChange (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        revE0 ν (ν ^ (-2 : ℝ)) m φ s =ᶠ[𝓝 ζ]
          fun ζ' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x

/-- **R3: chain rule** (SP 2860): `dr/dζ = -a(r)²` and `∂_ζ d = d/(2θ)`, for `ζ ∈ (0, Δz)`. -/
def ReyChain : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ t s : ℝ, 0 ≤ t → t < s → ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
    HasDerivAt (revAge ν s) (-(clockA ν (revAge ν s ζ)) ^ 2) ζ ∧
    HasDerivAt (revCell ν (ν ^ (-2 : ℝ)) s)
      (revCell ν (ν ^ (-2 : ℝ)) s ζ / (2 * revTheta ν s ζ)) ζ

/-- **R5: differentiation of `ζ ↦ ∫ reyIntegrand`** on the fixed cell, from `ReyPhysDeriv` by the
chain rule `dr/dζ = -a²` (`ReyChain`) and the pointwise differentiability of the integrand in `r`
(`IsAdjointFlow.jointSmooth`, smoothness of the weight in `a`). -/
def ReyDeriv (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        HasDerivAt (fun ζ' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x)
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x) ζ) ζ

/-- **R4/R6: integrability and identification with `rate0`** (SP 2860, 2945-2946, 3060-3062). -/
def ReyIdent (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        IntegrableOn (wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
            (fun y => revDt ν φ s ζ y +
              (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y))
          (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ)) ∧
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x) ζ) =
          rate0 m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revTheta ν s ζ) (revPhi ν φ s ζ)
            (fun y => revDt ν φ s ζ y +
              (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y)

/-- `E_0` with Reynolds' cancellation from the leaves. -/
theorem adjE0Reynolds_of (m : ℝ) (h2 : ReyChange m) (h5 : ReyDeriv m) (h4 : ReyIdent m) :
    AdjE0Reynolds m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  obtain ⟨hint, heq⟩ := h4 ν hν tr t s ht hts g φ hφ ζ hζ
  refine ⟨hint, ?_⟩
  rw [← heq]
  exact (h5 ν hν tr t s ht hts g φ hφ ζ hζ).congr_of_eventuallyEq
    (h2 ν hν tr t s ht hts g φ hφ ζ hζ)

end UnforcedLeray.Short.IIIa.E0
