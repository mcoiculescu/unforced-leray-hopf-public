import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R2_Change
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R3_Chain

/-!
# `PartIII-a:T21/2/2/2/2/4`: decomposition of `ReyIdent`

Source of record: `the November 2 reference manuscript` (SP) lines 2860, 2945-2946,
3060-3062, 3036-3037.

With `a = a(r)`, `r = revAge ν s ζ`, `d = c/√a`, `θ = revTheta`, `Φ = revPhi`, `Ψ = ∂_ζΦ + (2θ)⁻¹ y·∇Φ`,
the substitution `x = √a y` maps the moving cell `C_d` onto the fixed cell `C_c` with `dx = a dy`
(`integral_cell_scale`).  Three leaf facts are needed:

* `ReyPointwise`: for every `y`, `a · ∂_ζ[reyIntegrand](ζ, √a y) = (d/(2θ) ∂_d w + θ⁻¹ w + (2θ)⁻¹ y·∇w)|Φ|²
  + 2 w Re(Φ̄ Ψ)`.  Pure calculus: `|φ(r,√a y)|² = a²|Φ(y)|²`, `a⁻³·a² = a⁻¹ = 1 - ν z`, `∂_ζ a⁻¹ = ν = a⁻¹... = θ⁻¹ a⁻¹`;
  the fixed-`x` derivative equals the fixed-`y` derivative plus `(∂_ζ y)·∇_y`, `∂_ζ y = y/(2θ)`
  (`∂_ζ a = -ν a²`), and `∂_ζ[w(x/√a; d(ζ))] = ∂_d w · d/(2θ) + (2θ)⁻¹ y·∇w`.  Differentiability of
  `ζ' ↦ a⁻¹ φ(r(ζ'), √a(ζ') y)` and of `φ(r,·)` from `IsAdjointFlow.jointSmooth`, and `ReyChain`.
* `ReyIntegrableRe`: integrability of `w Re(Φ̄ Ψ)` on the moving cell.
* `ReyIntegrableA`: integrability of `(d/(2θ) ∂_d w + θ⁻¹ w + (2θ)⁻¹ y·∇w)|Φ|²` on the moving cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The weight-and-`|Φ|²` part of the rate integrand at `ζ`. -/
def reyAPart (m : ℝ) (ν s ζ : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℝ :=
  (revCell ν (ν ^ (-2 : ℝ)) s ζ / (2 * revTheta ν s ζ) * wDd m (revCell ν (ν ^ (-2 : ℝ)) s ζ) y +
    (revTheta ν s ζ)⁻¹ * periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y +
    (2 * revTheta ν s ζ)⁻¹ * wDil m (revCell ν (ν ^ (-2 : ℝ)) s ζ) y) *
    ‖revPhi ν φ s ζ y‖ ^ 2

/-- `Ψ = ∂_ζΦ + (2θ)⁻¹ y·∇Φ`. -/
def reyPsi (ν s ζ : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  revDt ν φ s ζ y + (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y

/-- **Leaf (pointwise chain rule, SP 2860, 2945-2946).** -/
def ReyPointwise (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∀ y : ℝ × ℝ,
        clockA ν (revAge ν s ζ) *
          deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ'
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
              Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) ζ =
          reyAPart m ν s ζ φ y +
            2 * wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ) (reyPsi ν s ζ φ) y

/-- **Leaf (integrability of `w Re(Φ̄ Ψ)`, SP 2945-2946, 3060-3062).** -/
def ReyIntegrableRe (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        IntegrableOn (wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ) (reyPsi ν s ζ φ))
          (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ))

/-- **Leaf (integrability of the weight part, SP 3044-3050, 3060).** -/
def ReyIntegrableA (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ ζ ∈ Ioo 0 (deltaZ ν t s),
        IntegrableOn (reyAPart m ν s ζ φ) (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ))

/-- **Conditional assembly of `ReyIdent`.** -/
theorem reyIdent_of (m : ℝ) (hm : 8 < m) (hp : ReyPointwise m) (hre : ReyIntegrableRe m)
    (hA : ReyIntegrableA m) : ReyIdent m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  have hs : 0 ≤ s := by linarith
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ.1
  have iRe := hre ν hν tr t s ht hts g φ hφ ζ hζ
  have iA := hA ν hν tr t s ht hts g φ hφ ζ hζ
  refine ⟨iRe, ?_⟩
  set a := clockA ν (revAge ν s ζ) with ha_def
  set F : ℝ × ℝ → ℝ := fun x => deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x) ζ
    with hF
  have hscale := integral_cell_scale (ν ^ (-2 : ℝ)) a ha F
  have hcell : cellLen (ν ^ (-2 : ℝ)) a = revCell ν (ν ^ (-2 : ℝ)) s ζ := rfl
  rw [hcell] at hscale
  have h1 : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), F x) =
      ∫ y in B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ),
        (reyAPart m ν s ζ φ y +
          2 * wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ) (reyPsi ν s ζ φ) y) := by
    have e : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), F x) =
        a * ∫ y in B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ),
          F (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hp ν hν tr t s ht hts g φ hφ ζ hζ y
  rw [h1, integral_add iA (iRe.const_mul 2), integral_const_mul]
  unfold rate0 reyAPart reyPsi
  rfl

end UnforcedLeray.Short.IIIa.E0
