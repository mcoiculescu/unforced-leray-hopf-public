import UnforcedLeray.Short.PartIIb.Sub.T11_1

/-!
# Part II-b, task `PartII-b:T11/1/2`: the commutator of `flatTranspose ∘ ∇^⊥` with `θ(q)` (proof)

Source of record: `the November 2 reference manuscript`, lines 1923-1927
(`flatTranspose` in `Defs.lean` is the transpose of `μ + S - νsΔ_{q,η}`).

Proves `CellStreamCommutator` (`Sub/T11_1.lean`) with no extra hypotheses. Every auxiliary
declaration is prefixed `scc_`.

Strategy. Write `θ` for `θ(q)`, and `θ', θ'', θ'''` for its derivatives. For a scalar field `F`,
the transpose entry of `flatTranspose` is `(μ-1)F - s ∂_sF - νs(∂_q²F + ∂_η²F)`. Since `∂_sθ = 0`,
`∂_η θ = 0` and `∂_q θ = θ'`, the product rule gives the pointwise values of `∂_s`, `∂_q²`, `∂_η²`
on `θ(q) h` and on sums and negations of such products. Substituting the components of
`streamField (qMul θ ψ)` (namely `θ ∂_ηψ` and `-(θ'ψ + θ∂_qψ)`) gives a polynomial identity in
`θ^{(k)}(q)`, `ν`, `μ`, `s`, `b x i` and the partial derivatives of `ψ` at `x`, which is exactly the
right-hand side `Σ_k θ^{(k)}(q) cellG_k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ### Calculus of `cpd` (directional derivative along `cdir j`) -/

theorem scc_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

/-- A function of `q` alone is smooth as a function on the chart. -/
theorem scc_contDiff_q (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : Coord => F z.2.1) :=
  hF.comp (contDiff_fst.comp contDiff_snd)

/-- The partial derivative of a smooth function is smooth. -/
theorem scc_contDiff_cpd {f : Coord → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun y => cpd j f y) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

/-- Directional derivative of a function of `q` alone. -/
theorem scc_q_cpd (F : ℝ → ℝ) (hF : Differentiable ℝ F) (j : Fin 3) (y : Coord) :
    cpd j (fun z : Coord => F z.2.1) y = (cdir j).2.1 * deriv F y.2.1 := by
  have hL : HasFDerivAt (fun z : Coord => z.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) y :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hF' : HasFDerivAt F (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv F y.2.1))
      y.2.1 :=
    ((hF y.2.1).hasDerivAt).hasFDerivAt
  have hc : HasFDerivAt (fun z : Coord => F z.2.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv F y.2.1)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) y :=
    hF'.comp y hL
  unfold cpd
  rw [hc.fderiv]
  simp [mul_comm]

/-- Product rule for `cpd` (pointwise). -/
theorem scc_cpd_mul (j : Fin 3) {f g : Coord → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Coord) :
    cpd j (fun y => f y * g y) x = f x * cpd j g x + g x * cpd j f x := by
  unfold cpd
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- Pointwise sums: `cpd j (A + B) = cpd j A + cpd j B`. -/
theorem scc_cpd_add (j : Fin 3) {A B : Coord → ℝ} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) (x : Coord) :
    cpd j (fun z => A z + B z) x = cpd j A x + cpd j B x := by
  unfold cpd
  rw [fderiv_fun_add (hA x) (hB x), add_apply]

/-- Pointwise negation: `cpd j (-A) = -cpd j A`. -/
theorem scc_cpd_neg (j : Fin 3) (A : Coord → ℝ) (x : Coord) :
    cpd j (fun z => -A z) x = -cpd j A x := by
  unfold cpd
  rw [fderiv_fun_neg, neg_apply]

/-- The product rule for `θ(q) g` along `cdir j`. -/
theorem scc_pt (j : Fin 3) (F : ℝ → ℝ) (hF : Differentiable ℝ F) {g : Coord → ℝ}
    (hg : Differentiable ℝ g) (y : Coord) :
    cpd j (fun z : Coord => F z.2.1 * g z) y =
      F y.2.1 * cpd j g y + g y * ((cdir j).2.1 * deriv F y.2.1) := by
  have hΘ : Differentiable ℝ (fun z : Coord => F z.2.1) :=
    hF.comp (differentiable_fst.comp differentiable_snd)
  rw [scc_cpd_mul j hΘ hg y, scc_q_cpd F hF j y]

/-- `∂_s (θ(q) g) = θ ∂_s g`. -/
theorem scc_p0 (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (y : Coord) :
    cpd 0 (fun z : Coord => F z.2.1 * g z) y = F y.2.1 * cpd 0 g y := by
  rw [scc_pt 0 F (scc_diff hF) (scc_diff hg) y]
  have h : (cdir 0).2.1 = 0 := rfl
  rw [h]
  ring

/-- `∂_q (θ(q) g) = θ' g + θ ∂_q g`. -/
theorem scc_p1 (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (y : Coord) :
    cpd 1 (fun z : Coord => F z.2.1 * g z) y = deriv F y.2.1 * g y + F y.2.1 * cpd 1 g y := by
  rw [scc_pt 1 F (scc_diff hF) (scc_diff hg) y]
  have h : (cdir 1).2.1 = 1 := rfl
  rw [h]
  ring

/-- `∂_η (θ(q) g) = θ ∂_η g`. -/
theorem scc_p2 (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (y : Coord) :
    cpd 2 (fun z : Coord => F z.2.1 * g z) y = F y.2.1 * cpd 2 g y := by
  rw [scc_pt 2 F (scc_diff hF) (scc_diff hg) y]
  have h : (cdir 2).2.1 = 0 := rfl
  rw [h]
  ring

/-- Second `∂_q` of `θ(q) g`. -/
theorem scc_p11 (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Coord) :
    cpd 1 (cpd 1 (fun z : Coord => F z.2.1 * g z)) x =
      deriv (deriv F) x.2.1 * g x + 2 * (deriv F x.2.1 * cpd 1 g x) +
        F x.2.1 * cpd 1 (cpd 1 g) x := by
  have hF1 : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hg1 : ContDiff ℝ ∞ (cpd 1 g) := scc_contDiff_cpd hg 1
  have hA : Differentiable ℝ (fun z : Coord => deriv F z.2.1 * g z) :=
    scc_diff ((scc_contDiff_q _ hF1).mul hg)
  have hB : Differentiable ℝ (fun z : Coord => F z.2.1 * cpd 1 g z) :=
    scc_diff ((scc_contDiff_q _ hF).mul hg1)
  have e : cpd 1 (fun z : Coord => F z.2.1 * g z) =
      fun y => deriv F y.2.1 * g y + F y.2.1 * cpd 1 g y :=
    funext fun y => scc_p1 F hF hg y
  rw [e, scc_cpd_add 1 hA hB x, scc_p1 (deriv F) hF1 hg x, scc_p1 F hF hg1 x]
  ring

/-- Second `∂_η` of `θ(q) g`. -/
theorem scc_p22 (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Coord) :
    cpd 2 (cpd 2 (fun z : Coord => F z.2.1 * g z)) x = F x.2.1 * cpd 2 (cpd 2 g) x := by
  have hg2 : ContDiff ℝ ∞ (cpd 2 g) := scc_contDiff_cpd hg 2
  have e : cpd 2 (fun z : Coord => F z.2.1 * g z) = fun y => F y.2.1 * cpd 2 g y :=
    funext fun y => scc_p2 F hF hg y
  rw [e]
  exact scc_p2 F hF hg2 x

/-- `∂_s` of a sum of smooth functions. -/
theorem scc_a0 {A B : Coord → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (x : Coord) :
    cpd 0 (fun z => A z + B z) x = cpd 0 A x + cpd 0 B x :=
  scc_cpd_add 0 (scc_diff hA) (scc_diff hB) x

/-- `∂_q²` of a sum of smooth functions. -/
theorem scc_a11 {A B : Coord → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (x : Coord) :
    cpd 1 (cpd 1 (fun z => A z + B z)) x = cpd 1 (cpd 1 A) x + cpd 1 (cpd 1 B) x := by
  have e : cpd 1 (fun z => A z + B z) = fun y => cpd 1 A y + cpd 1 B y :=
    funext fun y => scc_cpd_add 1 (scc_diff hA) (scc_diff hB) y
  rw [e]
  exact scc_cpd_add 1 (scc_diff (scc_contDiff_cpd hA 1)) (scc_diff (scc_contDiff_cpd hB 1)) x

/-- `∂_η²` of a sum of smooth functions. -/
theorem scc_a22 {A B : Coord → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (x : Coord) :
    cpd 2 (cpd 2 (fun z => A z + B z)) x = cpd 2 (cpd 2 A) x + cpd 2 (cpd 2 B) x := by
  have e : cpd 2 (fun z => A z + B z) = fun y => cpd 2 A y + cpd 2 B y :=
    funext fun y => scc_cpd_add 2 (scc_diff hA) (scc_diff hB) y
  rw [e]
  exact scc_cpd_add 2 (scc_diff (scc_contDiff_cpd hA 2)) (scc_diff (scc_contDiff_cpd hB 2)) x

/-- `∂_s` of a negation. -/
theorem scc_n0 (A : Coord → ℝ) (x : Coord) :
    cpd 0 (fun z => -A z) x = -cpd 0 A x :=
  scc_cpd_neg 0 A x

/-- `∂_q²` of a negation. -/
theorem scc_n11 (A : Coord → ℝ) (x : Coord) :
    cpd 1 (cpd 1 (fun z => -A z)) x = -cpd 1 (cpd 1 A) x := by
  have e : cpd 1 (fun z => -A z) = fun y => -cpd 1 A y :=
    funext fun y => scc_cpd_neg 1 A y
  rw [e]
  exact scc_cpd_neg 1 (cpd 1 A) x

/-- `∂_η²` of a negation. -/
theorem scc_n22 (A : Coord → ℝ) (x : Coord) :
    cpd 2 (cpd 2 (fun z => -A z)) x = -cpd 2 (cpd 2 A) x := by
  have e : cpd 2 (fun z => -A z) = fun y => -cpd 2 A y :=
    funext fun y => scc_cpd_neg 2 A y
  rw [e]
  exact scc_cpd_neg 2 (cpd 2 A) x

/-! ### The transpose on a scalar component -/

/-- `flatTranspose` on a component `Ψ · i` that equals the scalar field `F`. -/
theorem scc_ft_of (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) (i : Fin 2) (F : Coord → ℝ)
    (hF : ∀ y, Ψ y i = F y) (x : Coord) :
    flatTranspose ν μ Ψ x i = (μ - 1) * (F x : ℂ) - ((x.1 * cpd 0 F x : ℝ) : ℂ) -
      ((ν * x.1 * (cpd 1 (cpd 1 F) x + cpd 2 (cpd 2 F) x) : ℝ) : ℂ) := by
  have hf : (fun y => Ψ y i) = F := funext hF
  unfold flatTranspose
  rw [hf, hF x]

/-! ### The commutator -/

/-- **Leaf `PartII-b:T11/1/2`.** `Σ_i b_i flatTranspose(∇^⊥(θψ))_i = Σ_k θ^{(k)}(q) G_k`. -/
theorem cellStreamCommutator : CellStreamCommutator := by
  unfold CellStreamCommutator
  intro ν μ b θ ψ hθ hψ x
  have hθ1 : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.mp hθ).2
  have hψ1 : ContDiff ℝ ∞ (cpd 1 ψ) := scc_contDiff_cpd hψ 1
  have hψ2 : ContDiff ℝ ∞ (cpd 2 ψ) := scc_contDiff_cpd hψ 2
  have hA : ContDiff ℝ ∞ (fun z : Coord => deriv θ z.2.1 * ψ z) :=
    (scc_contDiff_q _ hθ1).mul hψ
  have hB : ContDiff ℝ ∞ (fun z : Coord => θ z.2.1 * cpd 1 ψ z) :=
    (scc_contDiff_q _ hθ).mul hψ1
  -- the two components of the stream field of `θψ`
  have hS0 : ∀ y : Coord, streamField (qMul θ ψ) y 0 = θ y.2.1 * cpd 2 ψ y :=
    fun y => scc_p2 θ hθ hψ y
  have hS1 : ∀ y : Coord, streamField (qMul θ ψ) y 1 =
      -(deriv θ y.2.1 * ψ y + θ y.2.1 * cpd 1 ψ y) := by
    intro y
    show -cpd 1 (fun z : Coord => θ z.2.1 * ψ z) y = _
    rw [scc_p1 θ hθ hψ y]
  -- the left-hand side
  rw [Fin.sum_univ_two,
    scc_ft_of ν μ (streamField (qMul θ ψ)) 0 (fun y => θ y.2.1 * cpd 2 ψ y) hS0 x,
    scc_ft_of ν μ (streamField (qMul θ ψ)) 1
      (fun y => -(deriv θ y.2.1 * ψ y + θ y.2.1 * cpd 1 ψ y)) hS1 x]
  -- the right-hand side
  rw [Fin.sum_univ_four]
  have i2 : iteratedDeriv 2 θ = deriv (deriv θ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have i3 : iteratedDeriv 3 θ = deriv (deriv (deriv θ)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  show _ = ((iteratedDeriv 0 θ x.2.1 : ℝ) : ℂ) * cellG0 ν μ b ψ x +
    ((iteratedDeriv 1 θ x.2.1 : ℝ) : ℂ) * cellG1 ν μ b ψ x +
    ((iteratedDeriv 2 θ x.2.1 : ℝ) : ℂ) * cellG2 ν μ b ψ x +
    ((iteratedDeriv 3 θ x.2.1 : ℝ) : ℂ) * cellG3 ν μ b ψ x
  rw [i2, i3, iteratedDeriv_one, iteratedDeriv_zero]
  unfold cellG0 cellG1 cellG2 cellG3
  rw [Fin.sum_univ_two,
    scc_ft_of ν μ (streamField ψ) 0 (cpd 2 ψ) (fun y => rfl) x,
    scc_ft_of ν μ (streamField ψ) 1 (fun y => -cpd 1 ψ y) (fun y => rfl) x]
  -- evaluate the operators on the products `θ(q) g` and on their sums and negations
  simp only [scc_p0 θ hθ hψ2 x, scc_p11 θ hθ hψ2 x, scc_p22 θ hθ hψ2 x,
    scc_n0 (fun z : Coord => deriv θ z.2.1 * ψ z + θ z.2.1 * cpd 1 ψ z) x,
    scc_n11 (fun z : Coord => deriv θ z.2.1 * ψ z + θ z.2.1 * cpd 1 ψ z) x,
    scc_n22 (fun z : Coord => deriv θ z.2.1 * ψ z + θ z.2.1 * cpd 1 ψ z) x,
    scc_a0 hA hB x, scc_a11 hA hB x, scc_a22 hA hB x,
    scc_p0 (deriv θ) hθ1 hψ x, scc_p11 (deriv θ) hθ1 hψ x, scc_p22 (deriv θ) hθ1 hψ x,
    scc_p0 θ hθ hψ1 x, scc_p11 θ hθ hψ1 x, scc_p22 θ hθ hψ1 x,
    scc_n0 (cpd 1 ψ) x, scc_n11 (cpd 1 ψ) x, scc_n22 (cpd 1 ψ) x]
  push_cast
  ring

end UnforcedLeray.Short.IIb
