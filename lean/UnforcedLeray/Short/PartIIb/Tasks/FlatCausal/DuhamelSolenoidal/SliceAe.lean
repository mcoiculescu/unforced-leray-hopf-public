import UnforcedLeray.Short.PartIIb.Sub.T12_6

/-!
# Part II-b, task `PartII-b:T12/6` helper: slice solenoidality of the Duhamel integrand, fixed test

Source of record: `the November 2 reference manuscript`, SP 1924 ("the heat flow
preserves solenoidality, `P_0 G = G`"). Target: `DuhamelSolenoidal` (`Sub/T12.lean:193`).


`dsolF` now lives in `Sub/T12_6.lean`) proves the first reduction of the target (step (1) of the plan). For a tensor test
`φ(s, y) = g(s) ψ(y)` with `g ∈ C_c^∞(0,∞)` and `ψ ∈ C_c^∞(ℝ²)`, the weak solenoidality of `G`
gives `∫ g(s) A_ψ(s) ds = 0` with `A_ψ(s) = ∫_y G(s,y)·∇ψ(y) dy`, and the fundamental lemma in `s`
gives `A_ψ(s) = 0` for almost every `s > 0`, for each fixed `ψ` (`dsol_slice_ae`).

The remaining pieces are the leaves of `Sub/T12_6.lean` (`DsolSliceAll`, `DsolSliceGauss`, ...).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `∂_q` of the tensor test `g(s) ψ(q, η)`. -/
theorem dsol_cpd_one (g : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g)
    (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 1 (fun y : Coord => g y.1 * ψ y.2) x = g x.1 * fderiv ℝ ψ x.2 (1, 0) := by
  have hf1 : HasFDerivAt (fun y : Coord => g y.1)
      (deriv g x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (hg x.1).hasDerivAt.comp_hasFDerivAt x hasFDerivAt_fst
  have hf2 : HasFDerivAt (fun y : Coord => ψ y.2)
      ((fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    (hψ x.2).hasFDerivAt.comp x hasFDerivAt_snd
  have hprod : HasFDerivAt (fun y : Coord => g y.1 * ψ y.2)
      (g x.1 • (fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        ψ x.2 • (deriv g x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) x :=
    hf1.mul hf2
  unfold cpd
  rw [hprod.fderiv]
  simp [cdir]

/-- `∂_η` of the tensor test `g(s) ψ(q, η)`. -/
theorem dsol_cpd_two (g : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g)
    (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 2 (fun y : Coord => g y.1 * ψ y.2) x = g x.1 * fderiv ℝ ψ x.2 (0, 1) := by
  have hf1 : HasFDerivAt (fun y : Coord => g y.1)
      (deriv g x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (hg x.1).hasDerivAt.comp_hasFDerivAt x hasFDerivAt_fst
  have hf2 : HasFDerivAt (fun y : Coord => ψ y.2)
      ((fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    (hψ x.2).hasFDerivAt.comp x hasFDerivAt_snd
  have hprod : HasFDerivAt (fun y : Coord => g y.1 * ψ y.2)
      (g x.1 • (fderiv ℝ ψ x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        ψ x.2 • (deriv g x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) x :=
    hf1.mul hf2
  unfold cpd
  rw [hprod.fderiv]
  simp [cdir]

/-- The tensor test `g(s) ψ(q, η)` is an admissible coordinate test when `g` lives in `s > 0`. -/
theorem dsol_tensor_isCoordTest {g : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi (0 : ℝ))
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    IsCoordTest (fun y : Coord => g y.1 * ψ y.2) := by
  have hsub : tsupport (fun y : Coord => g y.1 * ψ y.2) ⊆ tsupport g ×ˢ tsupport ψ := by
    apply closure_minimal
    · intro x hx
      have h0 : g x.1 * ψ x.2 ≠ 0 := hx
      exact ⟨subset_tsupport g (left_ne_zero_of_mul h0),
        subset_tsupport ψ (right_ne_zero_of_mul h0)⟩
    · exact (isClosed_tsupport g).prod (isClosed_tsupport ψ)
  refine ⟨(hg.comp contDiff_fst).mul (hψ.comp contDiff_snd), ?_,
    hsub.trans (prod_mono hgs (subset_univ _))⟩
  refine HasCompactSupport.intro (hgc.isCompact.prod hψc.isCompact) ?_
  intro x hx
  by_cases h1 : x.1 ∈ tsupport g
  · have h2 : x.2 ∉ tsupport ψ := fun h => hx ⟨h1, h⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

/-- The integrand of the weak solenoidality identity for a tensor test is `g(s)` times `F`. -/
theorem dsol_integrand_eq (G : CProf) {g : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g)
    (hψ : Differentiable ℝ ψ) (x : Coord) :
    G x 0 * (cpd 1 (fun y : Coord => g y.1 * ψ y.2) x : ℂ) +
        G x 1 * (cpd 2 (fun y : Coord => g y.1 * ψ y.2) x : ℂ) =
      (g x.1 : ℂ) * dsolF G ψ x := by
  rw [dsol_cpd_one g ψ hg hψ x, dsol_cpd_two g ψ hg hψ x]
  unfold dsolF
  push_cast
  ring

/-- Integrability and vanishing of the tensor pairing `∫ g(s) F(s, y)`, from `WeakSolenoidal G`. -/
theorem dsol_joint {G : CProf} (hW : WeakSolenoidal G) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi (0 : ℝ)) :
    Integrable (fun x : Coord => (g x.1 : ℂ) * dsolF G ψ x) ∧
      ∫ x : Coord, (g x.1 : ℂ) * dsolF G ψ x = 0 := by
  have hφ := dsol_tensor_isCoordTest hg hgc hgs hψ hψc
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcongr : (fun x : Coord => G x 0 * (cpd 1 (fun y : Coord => g y.1 * ψ y.2) x : ℂ) +
      G x 1 * (cpd 2 (fun y : Coord => g y.1 * ψ y.2) x : ℂ)) =
      fun x : Coord => (g x.1 : ℂ) * dsolF G ψ x :=
    funext fun x => dsol_integrand_eq G hdg hdψ x
  obtain ⟨h1, h2⟩ := hW _ hφ
  rw [hcongr] at h1 h2
  exact ⟨h1, h2⟩

/-- Local integrability of the slice integral `s ↦ ∫_y F(s, y)` on `s > 0`. -/
theorem dsol_locInt {G : CProf} (hW : WeakSolenoidal G) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    LocallyIntegrableOn (fun s : ℝ => ∫ y : ℝ × ℝ, dsolF G ψ (s, y)) (Ioi 0) := by
  intro s0 hs0
  have hs0' : (0 : ℝ) < s0 := hs0
  set bump : ContDiffBump s0 := ⟨s0 / 4, s0 / 2, by positivity, by linarith⟩ with hbump
  have hr : bump.rOut = s0 / 2 := rfl
  have hsupp : tsupport bump ⊆ Ioi (0 : ℝ) := by
    rw [bump.tsupport_eq, hr]
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    show (0 : ℝ) < s
    linarith [hs.1]
  have hjoint := (dsol_joint hW hψ hψc bump.contDiff bump.hasCompactSupport hsupp).1
  have hjoint' : Integrable (fun x : Coord => ((bump x.1 : ℝ) : ℂ) * dsolF G ψ x)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hjoint
  have hint := hjoint'.integral_prod_left
  have hint2 : Integrable (fun s : ℝ => (bump s : ℂ) *
      ∫ y : ℝ × ℝ, dsolF G ψ (s, y)) volume := by
    refine hint.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [integral_const_mul]
  refine ⟨Metric.closedBall s0 (s0 / 4),
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds s0 (by positivity)), ?_⟩
  refine IntegrableOn.congr_fun (hint2.integrableOn) ?_ measurableSet_closedBall
  intro s hs
  simp only
  rw [bump.one_of_mem_closedBall hs, Complex.ofReal_one, one_mul]

/-- **Step (1) of `DuhamelSolenoidal`.** For a fixed planar test `ψ ∈ C_c^∞(ℝ²)` and a weakly
solenoidal `G`, the slice integral `∫_y G(s,y)·∇ψ(y)` vanishes for almost every `s > 0`. -/
theorem dsol_slice_ae {G : CProf} (hW : WeakSolenoidal G) {ψ : ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ s : ℝ, s ∈ Ioi (0 : ℝ) → ∫ y : ℝ × ℝ, dsolF G ψ (s, y) = 0 := by
  refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioi
    (dsol_locInt hW hψ hψc) ?_
  intro g hg hgc hgs
  obtain ⟨_, h2⟩ := dsol_joint hW hψ hψc hg hgc hgs
  have hjoint := (dsol_joint hW hψ hψc hg hgc hgs).1
  have hjoint' : Integrable (fun x : Coord => (g x.1 : ℂ) * dsolF G ψ x)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hjoint
  have h2' : ∫ x : Coord, (g x.1 : ℂ) * dsolF G ψ x
      ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) = 0 := h2
  rw [integral_prod _ hjoint'] at h2'
  simp only [integral_const_mul] at h2'
  simp only [Complex.real_smul]
  exact h2'

end UnforcedLeray.Short.IIb
