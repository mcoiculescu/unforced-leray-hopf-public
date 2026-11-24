import UnforcedLeray.Short.PartIIa.Calc.BlockB3

/-!
# Part II-a, block `B₃`: the leaf `JetLinear` (task `PartII-a:R02/11/6`)

Target: `jetLinear : JetLinear`, i.e. for `g₁, g₂` smooth on `{s > 0}`,
`K^ℓ∂_η^a∂_q^b(αg₁ + βg₂) = αK^ℓ∂_η^a∂_q^bg₁ + βK^ℓ∂_η^a∂_q^bg₂` on `{s > 0}`.

Route (calculus only).  Each of `∂_q`, `∂_η`, `K` is linear at points where its argument is
differentiable, respects equality on the open set `{s > 0}`, and maps smooth functions there to
smooth functions.  Generic iterated versions follow by induction on the number of iterations,
and the three iterates are composed.
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

/-- `∂_η` commutes with a constant multiple at points of differentiability. -/
theorem jl_eta_const_mul (c : ℝ) {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) :
    partialEta (fun y => c * f y) x = c * partialEta f x := by
  unfold partialEta
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  simp

/-- `∂_q` commutes with a constant multiple at points of differentiability. -/
theorem jl_q_const_mul (c : ℝ) {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) :
    partialQ (fun y => c * f y) x = c * partialQ f x := by
  unfold partialQ
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  simp

/-- Linearity of `∂_η` on `αF + βG` at points of differentiability. -/
theorem jl_eta_lin (α β : ℝ) {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    partialEta (fun z => α * F z + β * G z) y = α * partialEta F y + β * partialEta G y := by
  have h := partialEta_add_mul (hF.const_mul α) hG β
  rw [jl_eta_const_mul α hF] at h
  exact h

/-- Linearity of `∂_q` on `αF + βG` at points of differentiability. -/
theorem jl_q_lin (α β : ℝ) {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    partialQ (fun z => α * F z + β * G z) y = α * partialQ F y + β * partialQ G y := by
  have h := partialQ_add_mul (hF.const_mul α) hG β
  rw [jl_q_const_mul α hF] at h
  exact h

/-- Linearity of `K` on `αF + βG` at points of differentiability. -/
theorem jl_age_lin (α β : ℝ) {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    ageOperator (fun z => α * F z + β * G z) y = α * ageOperator F y + β * ageOperator G y := by
  have h := ageOperator_add_mul (hF.const_mul α) hG β
  rw [kx_ageOp_const_mul α hF] at h
  exact h

/-- Iterates of a linear operator `D` respect linear combinations on `{s > 0}`. -/
theorem jl_iter_lin (D : (ProfilePoint → ℝ) → ProfilePoint → ℝ)
    (hlin : ∀ (F G : ProfilePoint → ℝ) (α β : ℝ) (y : ProfilePoint), 0 < y.2.2 →
      DifferentiableAt ℝ F y → DifferentiableAt ℝ G y →
      D (fun z => α * F z + β * G z) y = α * D F y + β * D G y)
    (hlift : ∀ F F' : ProfilePoint → ℝ, EqOn F F' {y : ProfilePoint | 0 < y.2.2} →
      EqOn (D F) (D F') {y : ProfilePoint | 0 < y.2.2})
    (hsm : ∀ F : ProfilePoint → ℝ, ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2} →
      ContDiffOn ℝ ∞ (D F) {y : ProfilePoint | 0 < y.2.2})
    (α β : ℝ) {F G : ProfilePoint → ℝ} (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2})
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (n : ℕ) :
    EqOn (D^[n] (fun z => α * F z + β * G z))
      (fun z => α * D^[n] F z + β * D^[n] G z) {y : ProfilePoint | 0 < y.2.2} := by
  induction n with
  | zero =>
    intro y _
    simp
  | succ n ih =>
    intro y hy
    have hDF : ContDiffOn ℝ ∞ (D^[n] F) {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_iterate D hsm hF n
    have hDG : ContDiffOn ℝ ∞ (D^[n] G) {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_iterate D hsm hG n
    have e1 : D^[n + 1] (fun z => α * F z + β * G z) y =
        D (D^[n] (fun z => α * F z + β * G z)) y := by
      rw [Function.iterate_succ_apply']
    have e2 : D^[n + 1] F y = D (D^[n] F) y := by
      rw [Function.iterate_succ_apply']
    have e3 : D^[n + 1] G y = D (D^[n] G) y := by
      rw [Function.iterate_succ_apply']
    show D^[n + 1] (fun z => α * F z + β * G z) y = α * D^[n + 1] F y + β * D^[n + 1] G y
    rw [e1, e2, e3, hlift _ _ ih hy,
      hlin _ _ α β y hy (differentiableAt_of_late hDF hy) (differentiableAt_of_late hDG hy)]

/-- Iterates of a lift-respecting operator respect equality on `{s > 0}`. -/
theorem jl_iter_lift (D : (ProfilePoint → ℝ) → ProfilePoint → ℝ)
    (hlift : ∀ F F' : ProfilePoint → ℝ, EqOn F F' {y : ProfilePoint | 0 < y.2.2} →
      EqOn (D F) (D F') {y : ProfilePoint | 0 < y.2.2})
    {F F' : ProfilePoint → ℝ} (h : EqOn F F' {y : ProfilePoint | 0 < y.2.2}) (n : ℕ) :
    EqOn (D^[n] F) (D^[n] F') {y : ProfilePoint | 0 < y.2.2} := by
  induction n with
  | zero =>
    intro y hy
    simp only [Function.iterate_zero_apply]
    exact h hy
  | succ n ih =>
    intro y hy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hlift _ _ ih hy

theorem jl_eta_lift (F F' : ProfilePoint → ℝ) (h : EqOn F F' {y : ProfilePoint | 0 < y.2.2}) :
    EqOn (partialEta F) (partialEta F') {y : ProfilePoint | 0 < y.2.2} := by
  intro y hy
  unfold partialEta
  rw [(eventuallyEq_of_late h hy).fderiv_eq]

theorem jl_q_lift (F F' : ProfilePoint → ℝ) (h : EqOn F F' {y : ProfilePoint | 0 < y.2.2}) :
    EqOn (partialQ F) (partialQ F') {y : ProfilePoint | 0 < y.2.2} := by
  intro y hy
  unfold partialQ
  rw [(eventuallyEq_of_late h hy).fderiv_eq]

theorem jl_age_lift (F F' : ProfilePoint → ℝ) (h : EqOn F F' {y : ProfilePoint | 0 < y.2.2}) :
    EqOn (ageOperator F) (ageOperator F') {y : ProfilePoint | 0 < y.2.2} := by
  intro y hy
  exact kx_ageOp_congr (eventuallyEq_of_late h hy)

theorem jl_eta_sm (F : ProfilePoint → ℝ) (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (partialEta F) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_fderiv_apply hF eηDir

theorem jl_q_sm (F : ProfilePoint → ℝ) (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (partialQ F) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_fderiv_apply hF eqDir

theorem jl_age_sm (F : ProfilePoint → ℝ) (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator F) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_ageOperator hF

/-- **Leaf `JetLinear`** (calculus): `K^ℓ∂_η^a∂_q^b` is linear on `{s > 0}`. -/
theorem jetLinear : JetLinear := by
  unfold JetLinear
  intro g₁ g₂ h₁ h₂ α β ℓ a b x hx
  -- the three iterates, linear in turn
  have hQ := jl_iter_lin partialQ
    (fun F G α β y _ hF hG => jl_q_lin α β hF hG) jl_q_lift jl_q_sm α β h₁ h₂ b
  have hP₁ : ContDiffOn ℝ ∞ (partialQ^[b] g₁) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialQ_iter h₁ b
  have hP₂ : ContDiffOn ℝ ∞ (partialQ^[b] g₂) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialQ_iter h₂ b
  have hE := jl_iter_lift partialEta jl_eta_lift hQ a
  have hE2 := jl_iter_lin partialEta
    (fun F G α β y _ hF hG => jl_eta_lin α β hF hG) jl_eta_lift jl_eta_sm α β hP₁ hP₂ a
  have hK := jl_iter_lift ageOperator jl_age_lift (hE.trans hE2) ℓ
  have hQ1 : ContDiffOn ℝ ∞ (partialEta^[a] (partialQ^[b] g₁)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hP₁ a
  have hQ2 : ContDiffOn ℝ ∞ (partialEta^[a] (partialQ^[b] g₂)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hP₂ a
  have hK2 := jl_iter_lin ageOperator
    (fun F G α β y _ hF hG => jl_age_lin α β hF hG) jl_age_lift jl_age_sm α β hQ1 hQ2 ℓ
  have e1 := hK hx
  have e2 := hK2 hx
  show ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (fun y => α * g₁ y + β * g₂ y))) x =
    α * ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] g₁)) x +
      β * ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] g₂)) x
  rw [e1, e2]

end UnforcedLeray.Short.PartIIa.BlockB3
