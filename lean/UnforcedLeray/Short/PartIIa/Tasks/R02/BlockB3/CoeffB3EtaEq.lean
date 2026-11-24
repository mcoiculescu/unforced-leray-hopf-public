import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3Eq
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators

/-!
# Part II-a, block `B₃`: the leaf `CoeffB3EtaEq` (task `PartII-a:R02/11/2`)

Target: `coeffB3EtaEq : CoeffB3EtaEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`∂_η(coeffB₃ ν g) x = ν * (4 * jet 1 1 0 g x + 4 * jet 2 1 0 g x + jet 3 1 0 g x)`.

Source of record: `the November 2 reference manuscript` lines 1250-1262.

Route. Write `A = ∂_η g`, `K = ageOperator`. The commutator `∂_η(Kf) = K(∂_η f) + ∂_η f`
(`profileCommutators`, pointwise on `{s > 0}`) gives, by induction on the number of `K`s:
`∂_η Kg = KA + A`, `∂_η K²g = K²A + 2KA + A`, `∂_η K³g = K³A + 3K²A + 3KA + A`
(each pointwise on `{s > 0}`, so locality of `K` transfers them to the next step).
`coeffB3Eq` gives `coeffB₃ ν g = -νg - νKg + νK²g + νK³g` near `x`, and linearity of `∂_η` at `x`
finishes with `ring`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-! ### Linear combinations of derivatives -/

theorem fd_lin2 {F₁ F₂ : ProfilePoint → ℝ} {x : ProfilePoint} (h₁ : DifferentiableAt ℝ F₁ x)
    (h₂ : DifferentiableAt ℝ F₂ x) (a₁ a₂ : ℝ) (v : ProfilePoint) :
    fderiv ℝ (fun y => a₁ * F₁ y + a₂ * F₂ y) x v =
      a₁ * fderiv ℝ F₁ x v + a₂ * fderiv ℝ F₂ x v := by
  have h : HasFDerivAt (fun y => a₁ * F₁ y + a₂ * F₂ y) _ x :=
    (h₁.hasFDerivAt.const_mul a₁).add (h₂.hasFDerivAt.const_mul a₂)
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem fd_lin3 {F₁ F₂ F₃ : ProfilePoint → ℝ} {x : ProfilePoint} (h₁ : DifferentiableAt ℝ F₁ x)
    (h₂ : DifferentiableAt ℝ F₂ x) (h₃ : DifferentiableAt ℝ F₃ x) (a₁ a₂ a₃ : ℝ)
    (v : ProfilePoint) :
    fderiv ℝ (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y) x v =
      a₁ * fderiv ℝ F₁ x v + a₂ * fderiv ℝ F₂ x v + a₃ * fderiv ℝ F₃ x v := by
  have h : HasFDerivAt (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y) _ x :=
    ((h₁.hasFDerivAt.const_mul a₁).add (h₂.hasFDerivAt.const_mul a₂)).add
      (h₃.hasFDerivAt.const_mul a₃)
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem fd_lin4 {F₁ F₂ F₃ F₄ : ProfilePoint → ℝ} {x : ProfilePoint}
    (h₁ : DifferentiableAt ℝ F₁ x) (h₂ : DifferentiableAt ℝ F₂ x)
    (h₃ : DifferentiableAt ℝ F₃ x) (h₄ : DifferentiableAt ℝ F₄ x) (a₁ a₂ a₃ a₄ : ℝ)
    (v : ProfilePoint) :
    fderiv ℝ (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y + a₄ * F₄ y) x v =
      a₁ * fderiv ℝ F₁ x v + a₂ * fderiv ℝ F₂ x v + a₃ * fderiv ℝ F₃ x v +
        a₄ * fderiv ℝ F₄ x v := by
  have h : HasFDerivAt (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y + a₄ * F₄ y) _ x :=
    (((h₁.hasFDerivAt.const_mul a₁).add (h₂.hasFDerivAt.const_mul a₂)).add
      (h₃.hasFDerivAt.const_mul a₃)).add (h₄.hasFDerivAt.const_mul a₄)
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem pEta_lin4 {F₁ F₂ F₃ F₄ : ProfilePoint → ℝ} {x : ProfilePoint}
    (h₁ : DifferentiableAt ℝ F₁ x) (h₂ : DifferentiableAt ℝ F₂ x)
    (h₃ : DifferentiableAt ℝ F₃ x) (h₄ : DifferentiableAt ℝ F₄ x) (a₁ a₂ a₃ a₄ : ℝ) :
    partialEta (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y + a₄ * F₄ y) x =
      a₁ * partialEta F₁ x + a₂ * partialEta F₂ x + a₃ * partialEta F₃ x +
        a₄ * partialEta F₄ x := by
  unfold partialEta
  exact fd_lin4 h₁ h₂ h₃ h₄ a₁ a₂ a₃ a₄ eηDir

theorem K_lin2 {F₁ F₂ : ProfilePoint → ℝ} {x : ProfilePoint} (h₁ : DifferentiableAt ℝ F₁ x)
    (h₂ : DifferentiableAt ℝ F₂ x) (a₁ a₂ : ℝ) :
    ageOperator (fun y => a₁ * F₁ y + a₂ * F₂ y) x =
      a₁ * ageOperator F₁ x + a₂ * ageOperator F₂ x := by
  unfold ageOperator partialEta partialAge
  rw [fd_lin2 h₁ h₂ a₁ a₂ eηDir, fd_lin2 h₁ h₂ a₁ a₂ esDir]
  ring

theorem K_lin3 {F₁ F₂ F₃ : ProfilePoint → ℝ} {x : ProfilePoint} (h₁ : DifferentiableAt ℝ F₁ x)
    (h₂ : DifferentiableAt ℝ F₂ x) (h₃ : DifferentiableAt ℝ F₃ x) (a₁ a₂ a₃ : ℝ) :
    ageOperator (fun y => a₁ * F₁ y + a₂ * F₂ y + a₃ * F₃ y) x =
      a₁ * ageOperator F₁ x + a₂ * ageOperator F₂ x + a₃ * ageOperator F₃ x := by
  unfold ageOperator partialEta partialAge
  rw [fd_lin3 h₁ h₂ h₃ a₁ a₂ a₃ eηDir, fd_lin3 h₁ h₂ h₃ a₁ a₂ a₃ esDir]
  ring

/-! ### The commutator `[K, ∂_η] = -∂_η` on `{s > 0}` -/

theorem contDiffOn_partialEta_of {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (partialEta G) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_fderiv_apply hG eηDir

/-- `∂_η(Kf) = K(∂_η f) + ∂_η f` at each point of `{s > 0}`. -/
theorem commEta_fn {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2}) {y : ProfilePoint} (hy : 0 < y.2.2) :
    partialEta (ageOperator f) y = ageOperator (partialEta f) y + partialEta f y := by
  have h2 : ContDiffAt ℝ 2 f y :=
    (hf.contDiffAt (isOpen_late.mem_nhds hy)).of_le (by norm_num)
  have h := (UnforcedLeray.Short.PartIIa.profileCommutators f y h2).1
  linarith

/-! ### Leaf `CoeffB3EtaEq` -/

/-- **Leaf `CoeffB3EtaEq`** (source lines 1258-1262): `∂_η B₃[g] = ν(4Kg' + 4K²g' + K³g')`
with `g' = ∂_η g`, on `{s > 0}`. -/
theorem coeffB3EtaEq : CoeffB3EtaEq := by
  unfold CoeffB3EtaEq
  intro ν g hg x hx
  have hA : ContDiffOn ℝ ∞ (partialEta g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_of hg
  have hK1 : ContDiffOn ℝ ∞ (ageOperator g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hg
  have hK2 : ContDiffOn ℝ ∞ (ageOperator (ageOperator g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hK1
  have hK3 : ContDiffOn ℝ ∞ (ageOperator (ageOperator (ageOperator g)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hK2
  have hKA : ContDiffOn ℝ ∞ (ageOperator (partialEta g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hA
  have hKKA : ContDiffOn ℝ ∞ (ageOperator (ageOperator (partialEta g)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hKA
  -- (a) `∂_η Kg = KA + A`
  have hEa : ∀ y : ProfilePoint, 0 < y.2.2 →
      partialEta (ageOperator g) y = 1 * ageOperator (partialEta g) y + 1 * partialEta g y := by
    intro y hy
    rw [commEta_fn hg hy]
    ring
  -- (b) `∂_η K²g = K²A + 2KA + A`
  have hEb : ∀ y : ProfilePoint, 0 < y.2.2 →
      partialEta (ageOperator (ageOperator g)) y =
        1 * ageOperator (ageOperator (partialEta g)) y + 2 * ageOperator (partialEta g) y +
          1 * partialEta g y := by
    intro y hy
    rw [commEta_fn hK1 hy]
    have e1 : ageOperator (partialEta (ageOperator g)) y =
        ageOperator (fun X => 1 * ageOperator (partialEta g) X + 1 * partialEta g X) y :=
      kx_ageOp_congr (eventuallyEq_of_late (fun X hX => hEa X hX) hy)
    rw [e1, K_lin2 (differentiableAt_of_late hKA hy) (differentiableAt_of_late hA hy),
      hEa y hy]
    ring
  -- (c) `∂_η K³g = K³A + 3K²A + 3KA + A`
  have hEc : ∀ y : ProfilePoint, 0 < y.2.2 →
      partialEta (ageOperator (ageOperator (ageOperator g))) y =
        1 * ageOperator (ageOperator (ageOperator (partialEta g))) y +
          3 * ageOperator (ageOperator (partialEta g)) y +
          3 * ageOperator (partialEta g) y + 1 * partialEta g y := by
    intro y hy
    rw [commEta_fn hK2 hy]
    have e2 : ageOperator (partialEta (ageOperator (ageOperator g))) y =
        ageOperator (fun X => 1 * ageOperator (ageOperator (partialEta g)) X +
          2 * ageOperator (partialEta g) X + 1 * partialEta g X) y :=
      kx_ageOp_congr (eventuallyEq_of_late (fun X hX => hEb X hX) hy)
    rw [e2, K_lin3 (differentiableAt_of_late hKKA hy) (differentiableAt_of_late hKA hy)
      (differentiableAt_of_late hA hy), hEb y hy]
    ring
  -- the coefficient `coeffB₃` near `x`
  have key : ∀ y : ProfilePoint, 0 < y.2.2 →
      coeffB₃ ν g y = (-ν) * g y + (-ν) * ageOperator g y +
        ν * ageOperator (ageOperator g) y + ν * ageOperator (ageOperator (ageOperator g)) y := by
    intro y hy
    rw [coeffB3Eq ν g hg y hy]
    show ν * (-g y - ageOperator g y + ageOperator (ageOperator g) y +
      ageOperator (ageOperator (ageOperator g)) y) = _
    ring
  have hEv : coeffB₃ ν g =ᶠ[𝓝 x] (fun y => (-ν) * g y + (-ν) * ageOperator g y +
      ν * ageOperator (ageOperator g) y + ν * ageOperator (ageOperator (ageOperator g)) y) :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun y hy => key y hy)
  have hEta : partialEta (coeffB₃ ν g) x = partialEta (fun y => (-ν) * g y +
      (-ν) * ageOperator g y + ν * ageOperator (ageOperator g) y +
      ν * ageOperator (ageOperator (ageOperator g)) y) x := by
    unfold partialEta
    rw [hEv.fderiv_eq]
  have dg : DifferentiableAt ℝ g x := differentiableAt_of_late hg hx
  have d1 : DifferentiableAt ℝ (ageOperator g) x := differentiableAt_of_late hK1 hx
  have d2 : DifferentiableAt ℝ (ageOperator (ageOperator g)) x := differentiableAt_of_late hK2 hx
  have d3 : DifferentiableAt ℝ (ageOperator (ageOperator (ageOperator g))) x :=
    differentiableAt_of_late hK3 hx
  rw [hEta, pEta_lin4 dg d1 d2 d3, hEa x hx, hEb x hx, hEc x hx]
  have j1 : jet 1 1 0 g x = ageOperator (partialEta g) x := rfl
  have j2 : jet 2 1 0 g x = ageOperator (ageOperator (partialEta g)) x := rfl
  have j3 : jet 3 1 0 g x = ageOperator (ageOperator (ageOperator (partialEta g))) x := rfl
  rw [j1, j2, j3]
  ring

end UnforcedLeray.Short.PartIIa.BlockB3
