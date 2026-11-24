import UnforcedLeray.Units.B0104.Dyson

/-!
# Joint measurability hypothesis for the Dyson iteration of the relative free evolution

SP 2920-2925, 2962-2982.  `DysonDefined` needs the integrands `r ↦ F t r (A r (V_k r s x))` to be
integrable for every `t`; the iterates `V_{k+1}(r,s)` integrate `F r r'` against the previous one,
so measurability of `σ ↦ F τ σ x` for each `τ` is not enough: the family must also be jointly a.e.
strongly measurable in `(τ, σ)` on the triangle `σ ≤ τ` (a family such as `F t s = 1_N(t) id` with
`N` non-measurable satisfies the slice hypothesis and violates `DysonDefined`).
-/

set_option autoImplicit false

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.DysonJointMeas

/-- Strong measurability of `(τ, σ) ↦ F τ σ x` on the whole plane (the relative free evolution is
strongly continuous in `(t,s)`; outside the triangle use the identity/zero extension). -/
def FJointMeas {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (F : ℝ → ℝ → H →L[ℂ] H) :
    Prop :=
  ∀ x : H, StronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 x)

end UnforcedLeray.Short.IIIa.DysonJointMeas
