import UnforcedLeray.Short.PartIIb.Sub.T15

/-!
# Part II-b, task `PartII-b:T15/1`: periodic extension of the weak identity for `S`

Source of record: `the November 2 reference manuscript`, lines 1975-1979.
The proof tests `HasWeakVec vS dZero w Sw` with `Ψ(x) = s^a g(q) φ(x)`, where `g` is a smooth
compactly supported cutoff in `q`, and then localises to one cell by the fundamental lemma of the
calculus of variations in the `q`-variable (no partition of unity is needed, since `PeriodicWeakS`
integrates over the cell only).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Calculus along the `s`-line -/

/-- Derivative of a function along the `s`-line through a point, `t ↦ F(s + t, q, η)`. -/
theorem hasDerivAt_line {F : Coord → ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x) :
    HasDerivAt (fun t : ℝ => F (x.1 + t, x.2)) (cpd 0 F x) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1 + t, x.2) : Coord)) (cdir 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.1
    have h2 : HasDerivAt (fun _ : ℝ => x.2) 0 0 := hasDerivAt_const _ _
    have h3 := h1.prodMk h2
    rw [show cdir 0 = (1, 0) by simp [cdir]]
    exact h3
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact hcomp

/-- A function vanishing for `s < σ` has zero `∂_s`-derivative at points with `s < σ`. -/
theorem cpd0_eq_zero_of_lt {F : Coord → ℝ} (hFc : ContDiff ℝ ∞ F) {σ : ℝ}
    (hF : ∀ y : Coord, y.1 < σ → F y = 0) {x : Coord} (hx : x.1 < σ) : cpd 0 F x = 0 := by
  have hdiff : DifferentiableAt ℝ F x := (hFc.differentiable (by simp)).differentiableAt
  have hl := hasDerivAt_line (F := F) hdiff
  have hev : (fun t : ℝ => F (x.1 + t, x.2)) =ᶠ[𝓝 0] (fun _ : ℝ => (0 : ℝ)) := by
    have hopen : ∀ᶠ t in 𝓝 (0 : ℝ), x.1 + t < σ := by
      have hc : ContinuousAt (fun t : ℝ => x.1 + t) 0 := (continuous_const.add continuous_id).continuousAt
      exact hc.eventually_lt continuousAt_const (by simpa using hx)
    filter_upwards [hopen] with t ht
    exact hF _ ht
  have h0 := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  exact hl.unique h0

/-! ## The transpose of `S` and the product tests `s^a g(q) φ` -/

/-- `coordTranspose vS dZero Ψ = -(Ψ + s ∂_s Ψ)` (SP 1651, `S = s∂_s`). -/
theorem coordTranspose_vS_eq {Ψ : Coord → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (x : Coord) :
    coordTranspose vS dZero Ψ x = -(Ψ x + x.1 * cpd 0 Ψ x) := by
  have hd : DifferentiableAt ℝ Ψ x := (hΨ.differentiable (by simp)).differentiableAt
  have hF : DifferentiableAt ℝ (fun y : Coord => y.1 * Ψ y) x :=
    ((contDiff_fst (n := ∞)).differentiable (by simp)).differentiableAt.mul hd
  have hl1 := hasDerivAt_line hF
  have hl2 := hasDerivAt_line hd
  have h1 : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.1
  have hprod := h1.mul hl2
  have hcpd : cpd 0 (fun y : Coord => y.1 * Ψ y) x = Ψ x + x.1 * cpd 0 Ψ x := by
    rw [hl1.unique hprod]
    simp
  have hsum : (∑ j : Fin 3, cpd j (fun y : Coord => vS y j * Ψ y) x) =
      cpd 0 (fun y : Coord => y.1 * Ψ y) x := by
    have e1 : cpd 1 (fun y : Coord => vS y 1 * Ψ y) x = 0 := by
      simp [cpd, vS, cdir]
    have e2 : cpd 2 (fun y : Coord => vS y 2 * Ψ y) x = 0 := by
      simp [cpd, vS, cdir]
    have e0 : cpd 0 (fun y : Coord => vS y 0 * Ψ y) x = cpd 0 (fun y : Coord => y.1 * Ψ y) x := by
      simp [vS]
    simp only [Fin.sum_univ_three]
    rw [e0, e1, e2]
    ring
  unfold coordTranspose
  rw [hsum, hcpd]
  simp [dZero]

/-- Smoothness of the product test `s^a g(q) φ` when `φ` vanishes for `s < σ`, `σ > 0`. -/
theorem contDiff_test (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {φ : Coord → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {σ : ℝ} (hσ : 0 < σ) (hlow : ∀ y : Coord, y.1 < σ → φ y = 0) :
    ContDiff ℝ ∞ (fun x : Coord => x.1 ^ a * g x.2.1 * φ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : σ ≤ x.1
  · have hne : x.1 ≠ 0 := (lt_of_lt_of_le hσ hx).ne'
    have h1 : ContDiffAt ℝ ∞ (fun y : Coord => y.1 ^ a) x :=
      (Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := a) hne).comp x contDiffAt_fst
    have h2 : ContDiffAt ℝ ∞ (fun y : Coord => g y.2.1) x :=
      (hg.comp (contDiff_fst.comp contDiff_snd)).contDiffAt
    exact ((h1.mul h2).mul hφ.contDiffAt)
  · have hx' : x.1 < σ := lt_of_not_ge hx
    have hev : (fun _ : Coord => (0 : ℝ)) =ᶠ[𝓝 x]
        (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hx'] with y hy
      simp [hlow y hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm

/-- Support of the product test: compact, and `tsupport ⊆ {s > 0}`. -/
theorem support_test (a : ℝ) {g : ℝ → ℝ} (hgc : HasCompactSupport g) {φ : Coord → ℝ}
    {σ H L : ℝ} (hσ : 0 < σ)
    (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0) :
    HasCompactSupport (fun x : Coord => x.1 ^ a * g x.2.1 * φ x) ∧
      tsupport (fun x : Coord => x.1 ^ a * g x.2.1 * φ x) ⊆ Ioi (0 : ℝ) ×ˢ univ := by
  have hsub : ∀ x : Coord, x.1 ^ a * g x.2.1 * φ x ≠ 0 →
      x ∈ Icc σ H ×ˢ (tsupport g ×ˢ Icc (-L) L) := by
    intro x hne
    have hφ0 : φ x ≠ 0 := fun h => hne (by simp [h])
    have hg0 : g x.2.1 ≠ 0 := fun h => hne (by simp [h])
    have hbox : σ ≤ x.1 ∧ x.1 ≤ H ∧ |x.2.2| ≤ L := by
      by_contra hc
      apply hφ0
      apply hzero
      by_cases h1 : x.1 < σ
      · exact Or.inl h1
      by_cases h2 : H < x.1
      · exact Or.inr (Or.inl h2)
      by_cases h3 : L < |x.2.2|
      · exact Or.inr (Or.inr h3)
      exact (hc ⟨not_lt.1 h1, not_lt.1 h2, not_lt.1 h3⟩).elim
    exact ⟨⟨hbox.1, hbox.2.1⟩, subset_tsupport g (Function.mem_support.2 hg0), abs_le.1 hbox.2.2⟩
  have hK : IsCompact (Icc σ H ×ˢ (tsupport g ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (hgc.isCompact.prod isCompact_Icc)
  refine ⟨HasCompactSupport.intro hK (fun x hx => ?_), ?_⟩
  · by_contra hne
    exact hx (hsub x hne)
  · have hsupp2 : Function.support (fun x : Coord => x.1 ^ a * g x.2.1 * φ x) ⊆ Ici σ ×ˢ univ := by
      intro x hx'
      have hne := Function.mem_support.1 hx'
      have hσx : σ ≤ x.1 := by
        by_contra hcon
        apply hne
        simp [hzero x (Or.inl (not_le.1 hcon))]
      exact ⟨hσx, mem_univ _⟩
    exact (closure_minimal hsupp2 (isClosed_Ici.prod isClosed_univ)).trans
      (prod_mono (fun s hs => lt_of_lt_of_le hσ hs) subset_rfl)

/-- Derivative of the product test in `s`, for `s > 0`. -/
theorem cpd0_test {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : ℝ) {x : Coord} (hx : 0 < x.1) :
    cpd 0 (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) x =
      a * x.1 ^ (a - 1) * (g x.2.1 * φ x) + x.1 ^ a * (g x.2.1 * cpd 0 φ x) := by
  have hne : x.1 ≠ 0 := hx.ne'
  have hA : DifferentiableAt ℝ (fun y : Coord => y.1 ^ a) x :=
    ((Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := a) hne).comp x contDiffAt_fst).differentiableAt
      (by simp)
  have hG : DifferentiableAt ℝ (fun y : Coord => g y.2.1) x :=
    ((hg.comp (contDiff_fst.comp contDiff_snd)).differentiable (by simp)).differentiableAt
  have hP : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
  have hΨd : DifferentiableAt ℝ (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) x :=
    (hA.mul hG).mul hP
  have hl := hasDerivAt_line hΨd
  have h1 : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.1
  have hA' : HasDerivAt (fun t : ℝ => (x.1 + t) ^ a) (1 * a * (x.1 + 0) ^ (a - 1)) 0 :=
    h1.rpow_const (Or.inl (by simpa using hne))
  have hG' : HasDerivAt (fun _ : ℝ => g x.2.1) 0 0 := hasDerivAt_const _ _
  have hP' := hasDerivAt_line hP
  have hprod := (hA'.mul hG').mul hP'
  rw [hl.unique hprod]
  simp only [add_zero, mul_zero, Pi.mul_apply, Prod.mk.eta]
  ring

/-- The coordinate transpose of the product test, in closed form. -/
theorem coordTranspose_test (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {φ : Coord → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {σ : ℝ} (hσ : 0 < σ) (hlow : ∀ y : Coord, y.1 < σ → φ y = 0)
    (x : Coord) :
    coordTranspose vS dZero (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) x =
      -(g x.2.1 * (x.1 ^ a * ((1 + a) * φ x + x.1 * cpd 0 φ x))) := by
  have hΨ := contDiff_test a hg hφ hσ hlow
  rw [coordTranspose_vS_eq hΨ x]
  by_cases hx : x.1 < σ
  · have hΨz : ∀ y : Coord, y.1 < σ → (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) y = 0 :=
      fun y hy => by simp [hlow y hy]
    rw [cpd0_eq_zero_of_lt hΨ hΨz hx, cpd0_eq_zero_of_lt hφ hlow hx]
    simp [hlow x hx]
  · have hpos : 0 < x.1 := lt_of_lt_of_le hσ (not_lt.1 hx)
    rw [cpd0_test hφ hg a hpos]
    have key : x.1 * x.1 ^ (a - 1) = x.1 ^ a := by
      rw [Real.rpow_sub_one hpos.ne']
      field_simp
    linear_combination (-(a * g x.2.1 * φ x)) * key

/-! ## Reordering the coordinates and the Fubini identity -/

/-- The measurable equivalence `(s, (q, η)) ↦ (q, (s, η))`. -/
def reorderEquiv : Coord ≃ᵐ ℝ × (ℝ × ℝ) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun z := (z.2.1, (z.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  measurable_invFun := (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem measurePreserving_reorderEquiv :
    MeasurePreserving reorderEquiv (volume : Measure Coord)
      (volume : Measure (ℝ × (ℝ × ℝ))) := by
  have hA := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)).symm
  have hB := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hC := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)
  exact hC.comp (hB.comp hA)

/-- Fubini on `Coord` with the `q`-variable as the outer integral. -/
theorem coord_fubini {H : Coord → ℂ} (hH : Integrable H) :
    Integrable (fun q : ℝ => ∫ p : ℝ × ℝ, H (p.1, (q, p.2))) ∧
      ∫ x : Coord, H x = ∫ q : ℝ, ∫ p : ℝ × ℝ, H (p.1, (q, p.2)) := by
  let H' : ℝ × (ℝ × ℝ) → ℂ := fun z => H (z.2.1, (z.1, z.2.2))
  have hfun : H' ∘ reorderEquiv = H := by
    funext x
    rfl
  have hmp := measurePreserving_reorderEquiv
  have hint' : Integrable H' (volume : Measure (ℝ × (ℝ × ℝ))) :=
    (hmp.integrable_comp_emb reorderEquiv.measurableEmbedding).1 (by rw [hfun]; exact hH)
  have hcomp : ∫ x : Coord, H x = ∫ z : ℝ × (ℝ × ℝ), H' z := by
    rw [← hfun]
    exact hmp.integral_comp' H'
  have hint2 : Integrable H' ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hint'
  refine ⟨hint2.integral_prod_left, ?_⟩
  rw [hcomp]
  exact integral_prod H' hint2

/-! ## The integrand and its `q`-marginal -/

/-- The integrand `s^a (S w_i φ + w_i ((1+a)φ + s∂_sφ))` of the periodic identity. -/
def Fx (a : ℝ) (φ : Coord → ℝ) (w Sw : CProf) (i : Fin 2) (x : Coord) : ℂ :=
  ((x.1 ^ a : ℝ) : ℂ) *
    (Sw x i * (φ x : ℂ) + w x i * (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ))

/-- The weak identity tested with `s^a g(q) φ` says `∫ g(q) Fx = 0`. -/
theorem Fx_test (a : ℝ) {w Sw : CProf} (i : Fin 2) (hWeak : HasWeakVec vS dZero w Sw)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {σ H L : ℝ} (hσ : 0 < σ)
    (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (fun x : Coord => ((g x.2.1 : ℝ) : ℂ) * Fx a φ w Sw i x) ∧
      ∫ x : Coord, ((g x.2.1 : ℝ) : ℂ) * Fx a φ w Sw i x = 0 := by
  have hlow : ∀ y : Coord, y.1 < σ → φ y = 0 := fun y hy => hzero y (Or.inl hy)
  have hΨ := contDiff_test a hg hφ hσ hlow
  have hcT : IsCoordTest (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) :=
    ⟨hΨ, (support_test a hgc hσ hzero).1, (support_test a hgc hσ hzero).2⟩
  have hW := hWeak i
  have hint := hW.1 _ hcT
  have hid := hW.2 _ hcT
  have hpt : (fun x : Coord => ((g x.2.1 : ℝ) : ℂ) * Fx a φ w Sw i x) =
      fun x : Coord => Sw x i * ((x.1 ^ a * g x.2.1 * φ x : ℝ) : ℂ) -
        w x i * ((coordTranspose vS dZero (fun y : Coord => y.1 ^ a * g y.2.1 * φ y) x : ℝ) : ℂ) := by
    funext x
    rw [coordTranspose_test a hg hφ hσ hlow x]
    simp only [Fx]
    push_cast
    ring
  have hI : Integrable (fun x : Coord => ((g x.2.1 : ℝ) : ℂ) * Fx a φ w Sw i x) := by
    rw [hpt]
    exact hint.2.sub hint.1
  refine ⟨hI, ?_⟩
  rw [hpt, integral_sub hint.2 hint.1]
  exact sub_eq_zero.2 hid

/-- The `q`-marginal `G(q) = ∫_{(s,η)} Fx(s, q, η)`. -/
def Gq (a : ℝ) (φ : Coord → ℝ) (w Sw : CProf) (i : Fin 2) (q : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, Fx a φ w Sw i (p.1, (q, p.2))

/-- A smooth compactly supported cutoff equal to `1` on `[-c/2, c/2]`. -/
theorem cutoff_props (c : ℝ) (hc : 0 < c) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ q : ℝ, -c / 2 ≤ q → q ≤ c / 2 → g q = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨c, 2 * c, hc, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, fun q h1 h2 => f.one_of_mem_closedBall ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  show |q| ≤ c
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The `q`-integral of `g(q) G(q)` vanishes for every product test. -/
theorem integral_mul_Gq (a : ℝ) {w Sw : CProf} {i : Fin 2} (hWeak : HasWeakVec vS dZero w Sw)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {σ H L : ℝ} (hσ : 0 < σ)
    (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ q : ℝ, ((g q : ℝ) : ℂ) * Gq a φ w Sw i q = 0 := by
  have hF := Fx_test a i hWeak hφ hσ hzero hg hgc
  have h := (coord_fubini hF.1).2
  have h1 : ∫ q : ℝ, ∫ p : ℝ × ℝ, ((g q : ℝ) : ℂ) * Fx a φ w Sw i (p.1, (q, p.2)) = 0 :=
    h.symm.trans hF.2
  have key : ∫ q : ℝ, ∫ p : ℝ × ℝ, ((g q : ℝ) : ℂ) * Fx a φ w Sw i (p.1, (q, p.2)) =
      ∫ q : ℝ, ((g q : ℝ) : ℂ) * Gq a φ w Sw i q := by
    congr 1
    funext q
    rw [Gq, integral_const_mul]
  rw [← key]
  exact h1

/-- The fundamental lemma in the `q`-variable: `G = 0` a.e. on the open cell `(-c/2, c/2)`. -/
theorem Gq_ae_zero (a : ℝ) {w Sw : CProf} {i : Fin 2} (hWeak : HasWeakVec vS dZero w Sw)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {σ H L : ℝ} (hσ : 0 < σ)
    (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ q ∂(volume : Measure ℝ), q ∈ Ioo (-c / 2) (c / 2) → Gq a φ w Sw i q = 0 := by
  obtain ⟨g0, hg0c, hg0k, hg0one⟩ := cutoff_props c hc
  have hF := Fx_test a i hWeak hφ hσ hzero hg0c hg0k
  have hint := (coord_fubini hF.1).1
  have hint2 : Integrable (fun q : ℝ => ((g0 q : ℝ) : ℂ) * Gq a φ w Sw i q) := by
    have e : (fun q : ℝ => ∫ p : ℝ × ℝ, ((g0 q : ℝ) : ℂ) * Fx a φ w Sw i (p.1, (q, p.2))) =
        fun q : ℝ => ((g0 q : ℝ) : ℂ) * Gq a φ w Sw i q := by
      funext q
      rw [Gq, integral_const_mul]
    rw [← e]
    exact hint
  have hloc : LocallyIntegrableOn (Gq a φ w Sw i) (Ioo (-c / 2) (c / 2)) := by
    apply IntegrableOn.locallyIntegrableOn
    refine (hint2.integrableOn).congr_fun (fun q hq => ?_) measurableSet_Ioo
    simp only
    rw [hg0one q hq.1.le hq.2.le, Complex.ofReal_one, one_mul]
  have h : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo (-c / 2) (c / 2) → ∫ x, g x • Gq a φ w Sw i x = 0 := by
    intro g hg hgc _
    simp only [Complex.real_smul]
    exact integral_mul_Gq a hWeak hφ hσ hzero hg hgc
  exact isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc h

/-- The cell integral of the `Fx` integrand vanishes. -/
theorem integral_cell_Fx (a : ℝ) {w Sw : CProf} {i : Fin 2}
    (hWeak : HasWeakVec vS dZero w Sw)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {σ H L : ℝ} (hσ : 0 < σ)
    (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0) {c : ℝ} (hc : 0 < c) :
    ∫ x : Coord, (Ico (-c / 2) (c / 2)).indicator (fun _ : ℝ => (1 : ℂ)) x.2.1 *
      Fx a φ w Sw i x = 0 := by
  obtain ⟨g0, hg0c, hg0k, hg0one⟩ := cutoff_props c hc
  have hS : MeasurableSet {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} :=
    measurableSet_Ico.preimage (measurable_fst.comp measurable_snd)
  have hQ : ∀ x : Coord, (Ico (-c / 2) (c / 2)).indicator (fun _ : ℝ => (1 : ℂ)) x.2.1 *
      Fx a φ w Sw i x = ({x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}.indicator
        (fun x : Coord => ((g0 x.2.1 : ℝ) : ℂ) * Fx a φ w Sw i x)) x := by
    intro x
    by_cases hx : x.2.1 ∈ Ico (-c / 2) (c / 2)
    · have hx' : x.2.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self hx
      have hxS : x ∈ {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxS, hg0one _ hx'.1 hx'.2]
      simp
    · have hxS : x ∉ {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxS]
      simp
  have hgF := (Fx_test a i hWeak hφ hσ hzero hg0c hg0k).1
  have hHint : Integrable (fun x : Coord => (Ico (-c / 2) (c / 2)).indicator (fun _ : ℝ => (1 : ℂ))
      x.2.1 * Fx a φ w Sw i x) := by
    refine (hgF.indicator hS).congr (Filter.Eventually.of_forall fun x => (hQ x).symm)
  have hfub := (coord_fubini hHint).2
  have hG : ∀ q : ℝ, ∫ p : ℝ × ℝ, (Ico (-c / 2) (c / 2)).indicator (fun _ : ℝ => (1 : ℂ)) q *
      Fx a φ w Sw i (p.1, (q, p.2)) =
      (Ico (-c / 2) (c / 2)).indicator (Gq a φ w Sw i) q := by
    intro q
    rw [integral_const_mul]
    by_cases hq : q ∈ Ico (-c / 2) (c / 2)
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, one_mul, Gq]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, zero_mul]
  rw [hfub]
  simp only [hG]
  rw [integral_indicator measurableSet_Ico]
  rw [setIntegral_congr_set Ioo_ae_eq_Ico.symm]
  rw [setIntegral_congr_ae measurableSet_Ioo (Gq_ae_zero a hWeak hφ hσ hzero hc)]
  simp

/-! ## The age-weighted measure as a density, and the periodic identity -/

/-- Density of `ageμ c a` with respect to Lebesgue measure on `Coord`:
`c⁻¹ s^a` on `(0,∞) × cell`, zero elsewhere. -/
def dens (c a : ℝ) (x : Coord) : ℝ≥0∞ :=
  ENNReal.ofReal (c⁻¹ * x.1 ^ a) * (Ioi (0 : ℝ) ×ˢ Axi.qCell c).indicator 1 x

theorem measurableSet_halfCell' (c : ℝ) : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
  measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)

theorem measurable_dens (c a : ℝ) : Measurable (dens c a) :=
  (ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const a).const_mul c⁻¹)).mul
    (measurable_one.indicator (measurableSet_halfCell' c))

theorem dens_lt_top (c a : ℝ) (x : Coord) : dens c a x < ⊤ := by
  by_cases h : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
  · simp [dens, Set.indicator_of_mem h]
  · simp [dens, Set.indicator_of_notMem h]

theorem dens_toReal {c : ℝ} (hc : 0 < c) (a : ℝ) (x : Coord) :
    (dens c a x).toReal =
      (Ioi (0 : ℝ) ×ˢ Axi.qCell c).indicator (fun y : Coord => c⁻¹ * y.1 ^ a) x := by
  by_cases h : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
  · rw [Set.indicator_of_mem h]
    simp only [dens, Set.indicator_of_mem h, Pi.one_apply, mul_one]
    exact ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hc.le)
      (Real.rpow_nonneg (show (0 : ℝ) < x.1 from h.1).le a))
  · rw [Set.indicator_of_notMem h]
    simp only [dens, Set.indicator_of_notMem h, mul_zero, ENNReal.toReal_zero]

/-- `ageμ c a` is the Lebesgue measure with density `dens c a`. -/
theorem ageμ_eq_withDensity {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Axi.ageμ c a = (volume : Measure Coord).withDensity (dens c a) := by
  refine Measure.ext fun A hA => ?_
  rw [withDensity_apply _ hA, ← lintegral_indicator_one (μ := Axi.ageμ c a) hA,
    Axi.lintegral_ageμ hc a (measurable_one.indicator hA),
    ← lintegral_indicator (measurableSet_halfCell' c), ← lintegral_indicator hA]
  congr 1
  funext p
  unfold dens
  by_cases hpA : p ∈ A <;> by_cases hpE : p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c <;>
    simp [Set.indicator_apply, hpA, hpE]

/-- `Fx` vanishes for `s < σ`, since `φ` and `∂_sφ` do. -/
theorem Fx_eq_zero_of_lt (a : ℝ) (φ : Coord → ℝ) (w Sw : CProf) (i : Fin 2)
    (hφc : ContDiff ℝ ∞ φ) {σ : ℝ} (hlow : ∀ y : Coord, y.1 < σ → φ y = 0)
    {x : Coord} (hx : x.1 < σ) : Fx a φ w Sw i x = 0 := by
  have h1 : φ x = 0 := hlow x hx
  have h2 : cpd 0 φ x = 0 := cpd0_eq_zero_of_lt hφc hlow hx
  simp [Fx, h1, h2]

/-- The periodic weak identity at a fixed component, for the age-weighted measure. -/
theorem periodic_identity {c : ℝ} (hc : 0 < c) (a : ℝ) {w Sw : CProf}
    (hWeak : HasWeakVec vS dZero w Sw) {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) {σ H L : ℝ}
    (hσ : 0 < σ) (hzero : ∀ y : Coord, (y.1 < σ ∨ H < y.1 ∨ L < |y.2.2|) → φ y = 0)
    (i : Fin 2) :
    ∫ x, Sw x i * (φ x : ℂ) ∂(Axi.ageμ c a) =
      -∫ x, w x i * (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ) ∂(Axi.ageμ c a) := by
  have hlow : ∀ y : Coord, y.1 < σ → φ y = 0 := fun y hy => hzero y (Or.inl hy)
  obtain ⟨g0, hg0c, hg0k, hg0one⟩ := cutoff_props c hc
  have hEm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) := measurableSet_halfCell' c
  have hΨ := contDiff_test a hg0c hφ hσ hlow
  have hcT : IsCoordTest (fun y : Coord => y.1 ^ a * g0 y.2.1 * φ y) :=
    ⟨hΨ, (support_test a hg0k hσ hzero).1, (support_test a hg0k hσ hzero).2⟩
  have hW := hWeak i
  have hint0 := hW.1 _ hcT
  have hmeas := measurable_dens c a
  have hfin : ∀ᵐ x ∂(volume : Measure Coord), dens c a x < ⊤ :=
    Filter.Eventually.of_forall (dens_lt_top c a)
  -- cell point facts
  have hcell : ∀ x : Coord, x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c → g0 x.2.1 = 1 := by
    intro x hx
    have hq : x.2.1 ∈ Ico (-c / 2) (c / 2) := hx.2.1
    exact hg0one _ (Ico_subset_Icc_self hq).1 (Ico_subset_Icc_self hq).2
  -- the first integrand is integrable against the density
  have hI1 : Integrable (fun x : Coord => Sw x i * (φ x : ℂ))
      ((volume : Measure Coord).withDensity (dens c a)) := by
    rw [integrable_withDensity_iff_integrable_smul' hmeas hfin]
    refine ((hint0.2.const_mul ((c⁻¹ : ℝ) : ℂ)).indicator hEm).congr
      (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [dens_toReal hc a x]
    by_cases hx : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hcell x hx]
      simp only [Complex.real_smul]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  -- the second integrand
  have hI2 : Integrable (fun x : Coord => w x i *
      (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ))
      ((volume : Measure Coord).withDensity (dens c a)) := by
    rw [integrable_withDensity_iff_integrable_smul' hmeas hfin]
    refine ((hW.1 _ hcT).1.const_mul (-(c⁻¹ : ℝ) : ℂ)).indicator hEm |>.congr
      (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [dens_toReal hc a x]
    by_cases hx : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        coordTranspose_test a hg0c hφ hσ hlow x, hcell x hx]
      simp only [Complex.real_smul]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  -- the sum integrates to zero
  have hsum : ∫ x, (Sw x i * (φ x : ℂ) + w x i *
      (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ))
      ∂((volume : Measure Coord).withDensity (dens c a)) = 0 := by
    rw [integral_withDensity_eq_integral_toReal_smul hmeas hfin]
    have hpt : ∀ x : Coord, (dens c a x).toReal • (Sw x i * (φ x : ℂ) + w x i *
        (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ)) =
        (c⁻¹ : ℂ) * ((Ico (-c / 2) (c / 2)).indicator (fun _ : ℝ => (1 : ℂ)) x.2.1 *
          Fx a φ w Sw i x) := by
      intro x
      rw [dens_toReal hc a x]
      by_cases hx : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c
      · have hq : x.2.1 ∈ Ico (-c / 2) (c / 2) := hx.2.1
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hq]
        simp only [Fx, Complex.real_smul]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hx, zero_smul]
        by_cases hq : x.2.1 ∈ Ico (-c / 2) (c / 2)
        · have hxle : x.1 ≤ 0 := by
            by_contra hcon
            exact hx ⟨not_le.1 hcon, Set.mem_univ _ |> fun h => ⟨hq, h⟩⟩
          rw [Set.indicator_of_mem hq, Fx_eq_zero_of_lt a φ w Sw i hφ hlow
            (show x.1 < σ from lt_of_le_of_lt hxle hσ), mul_zero, mul_zero]
        · rw [Set.indicator_of_notMem hq, zero_mul, mul_zero]
    simp_rw [hpt]
    rw [integral_const_mul, integral_cell_Fx a hWeak hφ hσ hzero hc, mul_zero]
  rw [ageμ_eq_withDensity hc a]
  have hadd := integral_add hI1 hI2
  exact eq_neg_of_add_eq_zero_left (hadd.symm.trans hsum)

/-- **Leaf `PartII-b:T15/1`** (SP 1975-1979): the weak identity for `S` extends to
`c`-periodic tests, `PeriodicWeakS c (-3/2) w Sw`. -/
theorem weakSPeriodicExtension : WeakSPeriodicExtension := by
  unfold WeakSPeriodicExtension PeriodicWeakS
  intro c w Sw hc _hw _hSw hWeak φ hφ _hper hsupp i
  obtain ⟨σ, H, L, hσ, hzero⟩ := hsupp
  exact periodic_identity hc (-3 / 2) hWeak hφ hσ hzero i

end UnforcedLeray.Short.IIb
