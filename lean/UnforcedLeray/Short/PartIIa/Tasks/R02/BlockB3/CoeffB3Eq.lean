import UnforcedLeray.Short.PartIIa.Calc.BlockB3

/-!
# Part II-a, block `B₃`: the leaf `CoeffB3Eq` (task `PartII-a:R02/11/1`)

Target: `coeffB3Eq : CoeffB3Eq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`coeffB₃ ν g x = ν * (-jet 0 0 0 g x - jet 1 0 0 g x + jet 2 0 0 g x + jet 3 0 0 g x)`.

Source of record: `the November 2 reference manuscript` line 1258
(`B₃ = -ν(K+1)²H`, `H = (1-K)ψ`).

Route: with `H = ageDefect g = g + (-1)·Kg` (pointwise), `(K+1)H = g + (-1)·K²g` on `{s > 0}`
(linearity of `K` at points where `g` and `Kg` are differentiable), then `K((K+1)H)` at `x` is
`Kg + (-1)·K³g` by locality and linearity again.  Hence `(K+1)²H = (g - K²g) + (Kg - K³g)` at `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-! ### Smoothness helpers (copied from `Calc/BlockB1.lean`; the B3 organizer does not export them) -/

theorem contDiffOn_ageOperator {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator F) {y : ProfilePoint | 0 < y.2.2} := by
  have h1 := contDiffOn_fderiv_apply hF eηDir
  have h2 := contDiffOn_fderiv_apply hF esDir
  have he : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.1) := by fun_prop
  have hs : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.2) := by fun_prop
  exact (he.contDiffOn.mul h1).add ((contDiffOn_const.mul hs.contDiffOn).mul h2)

theorem differentiableAt_of_late {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ F x :=
  (hF.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem eventuallyEq_of_late {F G : ProfilePoint → ℝ}
    (h : EqOn F G {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    F =ᶠ[𝓝 x] G :=
  Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun z hz => h hz)

/-- **Leaf `CoeffB3Eq`** (source line 1258): `B₃[g] = ν(-g - Kg + K²g + K³g)` on `{s > 0}`. -/
theorem coeffB3Eq : CoeffB3Eq := by
  unfold CoeffB3Eq
  intro ν g hg x hx
  have hK1 : ContDiffOn ℝ ∞ (ageOperator g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hg
  have hK2 : ContDiffOn ℝ ∞ (ageOperator (ageOperator g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hK1
  have dg : DifferentiableAt ℝ g x := differentiableAt_of_late hg hx
  have dK1 : DifferentiableAt ℝ (ageOperator g) x := differentiableAt_of_late hK1 hx
  have dK2 : DifferentiableAt ℝ (ageOperator (ageOperator g)) x := differentiableAt_of_late hK2 hx
  -- pointwise: `(K+1)H = g + (-1) K²g` on `{s > 0}`, where `H = ageDefect g`
  have L1 : ∀ y : ProfilePoint, 0 < y.2.2 →
      ageShift 1 (ageDefect g) y = g y + (-1) * ageOperator (ageOperator g) y := by
    intro y hy
    have hg' : DifferentiableAt ℝ g y := differentiableAt_of_late hg hy
    have hK1' : DifferentiableAt ℝ (ageOperator g) y := differentiableAt_of_late hK1 hy
    have hK2' : DifferentiableAt ℝ (ageOperator (ageOperator g)) y :=
      differentiableAt_of_late hK2 hy
    have hH : ageDefect g = fun X => g X + (-1) * ageOperator g X := by
      funext X
      unfold ageDefect
      ring
    have e : ageOperator (ageDefect g) y =
        ageOperator g y + (-1) * ageOperator (ageOperator g) y := by
      rw [hH]
      exact ageOperator_add_mul hg' hK1' (-1)
    unfold ageShift
    rw [e]
    unfold ageDefect
    ring
  -- locality: `(K+1)H` agrees with `g + (-1) K²g` near `x`
  have hev : ageShift 1 (ageDefect g) =ᶠ[𝓝 x]
      (fun y => g y + (-1) * ageOperator (ageOperator g) y) :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun y hy => L1 y hy)
  have eK : ageOperator (ageShift 1 (ageDefect g)) x =
      ageOperator g x + (-1) * ageOperator (ageOperator (ageOperator g)) x := by
    rw [kx_ageOp_congr hev]
    exact ageOperator_add_mul dg dK2 (-1)
  have hpt : ageShift 1 (ageDefect g) x = g x + (-1) * ageOperator (ageOperator g) x :=
    L1 x hx
  have hfinal : ageShift 1 (ageShift 1 (ageDefect g)) x =
      ageOperator (ageShift 1 (ageDefect g)) x + 1 * ageShift 1 (ageDefect g) x := rfl
  have hj0 : jet 0 0 0 g x = g x := rfl
  have hj1 : jet 1 0 0 g x = ageOperator g x := rfl
  have hj2 : jet 2 0 0 g x = ageOperator (ageOperator g) x := rfl
  have hj3 : jet 3 0 0 g x = ageOperator (ageOperator (ageOperator g)) x := rfl
  unfold coeffB₃
  rw [hfinal, eK, hpt, hj0, hj1, hj2, hj3]
  ring

end UnforcedLeray.Short.PartIIa.BlockB3
