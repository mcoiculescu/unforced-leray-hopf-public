import UnforcedLeray.Short.PartIIa.Sub.F05_1

/-!
# Part II-a, task `PartII-a:F05a`: smoothness of parameter integrals

Target: `ParamIntegralSmooth` (defined in `Short/PartII-a/Sub/F05_1.lean`). This is pure analysis;
no heat-flow input is used. The Prop is not a step of the 73-page proof, so there are no source
lines to cite.

Proof outline.
* `pm_hasFDerivAt`: first-order differentiation under the integral for an arbitrary normed target
  `F`, from Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
* `pm_deriv_formula`: by induction on `k`, for every target `F` and every family `G`,
  `iteratedFDeriv k` of the integral is the integral of `iteratedFDeriv k (G x)`. The step applies
  the first-order lemma, then the induction hypothesis to the family `x ↦ fderiv (G x)` with target
  `E →L[ℝ] F`, then pulls the currying isometry through the integral.
* `pm_contDiff`: `C^∞` from `contDiff_of_differentiable_iteratedFDeriv`, using the first-order
  lemma for the family `x ↦ iteratedFDeriv k (G x)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace ParamIntegralSmoothAux

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The hypotheses of `ParamFamilyHyp`, for an arbitrary normed target `F`. -/
abbrev GenHyp {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace X]
    (m : Measure X) (G : X → E → F) : Prop :=
  (∀ᵐ x ∂m, ContDiff ℝ ∞ (G x)) ∧
  (∀ (k : ℕ) (p : E), AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (G x) p) m) ∧
  (∀ k : ℕ, ∃ b : X → ℝ, Integrable b m ∧
    ∀ᵐ x ∂m, ∀ p : E, ‖iteratedFDeriv ℝ k (G x) p‖ ≤ b x)

/-! ### Currying identities -/

/-- `fderiv` as the curried first iterated derivative. -/
theorem pm_fderiv_curry1 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (q : E) :
    fderiv ℝ g q = continuousMultilinearCurryFin1 ℝ E F (iteratedFDeriv ℝ 1 g q) := by
  ext v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  rfl

theorem pm_norm_fderiv_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F)
    (q : E) : ‖fderiv ℝ g q‖ = ‖iteratedFDeriv ℝ 1 g q‖ := by
  rw [pm_fderiv_curry1 g q, LinearIsometryEquiv.norm_map]

/-- `fderiv` of the `k`-th derivative, curried into the `(k+1)`-th derivative. -/
theorem pm_fderiv_curryLeft {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (g : E → F) (q : E) :
    fderiv ℝ (iteratedFDeriv ℝ k g) q
      = continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F
          (iteratedFDeriv ℝ (k + 1) g q) := by
  rw [iteratedFDeriv_succ_eq_comp_left]
  simp

theorem pm_norm_fderiv_of_iter {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (g : E → F) (q : E) :
    ‖fderiv ℝ (iteratedFDeriv ℝ k g) q‖ = ‖iteratedFDeriv ℝ (k + 1) g q‖ := by
  rw [pm_fderiv_curryLeft, LinearIsometryEquiv.norm_map]

/-- The `k`-th derivative of `fderiv g`, curried into the `(k+1)`-th derivative of `g`. -/
theorem pm_iter_fderiv_curryRight {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (g : E → F) (q : E) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ g y) q
      = continuousMultilinearCurryRightEquiv' ℝ k E F (iteratedFDeriv ℝ (k + 1) g q) := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem pm_norm_fderiv_iter {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (g : E → F) (q : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ g y) q‖ = ‖iteratedFDeriv ℝ (k + 1) g q‖ := by
  rw [pm_iter_fderiv_curryRight, LinearIsometryEquiv.norm_map]

/-! ### Measurability transfer from iterated derivatives to values and first derivatives -/

theorem pm_aesm0 {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → E → F} (q : E)
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (G x) q) m) :
    AEStronglyMeasurable (fun x => G x q) m := by
  refine ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable h).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp [iteratedFDeriv_zero_eq_comp]

theorem pm_aesm1 {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → E → F} (q : E)
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 1 (G x) q) m) :
    AEStronglyMeasurable (fun x => fderiv ℝ (G x) q) m := by
  refine ((continuousMultilinearCurryFin1 ℝ E F).continuous.comp_aestronglyMeasurable h).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (pm_fderiv_curry1 (G x) q).symm

/-! ### First-order differentiation under the integral -/

/-- Differentiation under the integral sign, first order, for an arbitrary normed target. -/
theorem pm_hasFDerivAt {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → E → F} {b : X → ℝ} (p : E)
    (hdiff : ∀ᵐ x ∂m, Differentiable ℝ (G x))
    (hmeas : ∀ q : E, AEStronglyMeasurable (fun x => G x q) m)
    (hint : Integrable (fun x => G x p) m)
    (hD : ∀ q : E, AEStronglyMeasurable (fun x => fderiv ℝ (G x) q) m)
    (hb : Integrable b m) (hbd : ∀ᵐ x ∂m, ∀ q : E, ‖fderiv ℝ (G x) q‖ ≤ b x) :
    HasFDerivAt (fun q => ∫ x, G x q ∂m) (∫ x, fderiv ℝ (G x) p ∂m) p := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun q x => G x q)
    (F' := fun q x => fderiv ℝ (G x) q) (bound := b) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas) hint (hD p) ?_ hb ?_
  · filter_upwards [hbd] with a ha
    intro q _
    exact ha q
  · filter_upwards [hdiff] with a ha
    intro q _
    exact (ha q).hasFDerivAt

/-- The first-order statement for a `GenHyp` family, at every point. -/
theorem pm_hasFDerivAt_gen {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → E → F} (hG : GenHyp m G) (q : E) :
    HasFDerivAt (fun q' => ∫ x, G x q' ∂m) (∫ x, fderiv ℝ (G x) q ∂m) q := by
  obtain ⟨b, hb, hbd⟩ := hG.2.2 1
  obtain ⟨c, hc, hcd⟩ := hG.2.2 0
  refine pm_hasFDerivAt q ?_ (fun q' => pm_aesm0 q' (hG.2.1 0 q')) ?_
    (fun q' => pm_aesm1 q' (hG.2.1 1 q')) hb ?_
  · filter_upwards [hG.1] with x hx
    exact hx.differentiable (by simp)
  · refine Integrable.mono' hc (pm_aesm0 q (hG.2.1 0 q)) ?_
    filter_upwards [hcd] with x hx
    have := hx q
    rwa [norm_iteratedFDeriv_zero] at this
  · filter_upwards [hbd] with x hx
    intro q'
    rw [pm_norm_fderiv_one]
    exact hx q'

/-! ### The family of first derivatives satisfies the same hypotheses -/

theorem pm_genHyp_fderiv {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : X → E → F} (hG : GenHyp m G) :
    GenHyp m (fun x q => fderiv ℝ (G x) q) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hG.1] with x hx
    exact (contDiff_infty_iff_fderiv.1 hx).2
  · intro k p
    refine ((continuousMultilinearCurryRightEquiv' ℝ k E F).continuous.comp_aestronglyMeasurable
      (hG.2.1 (k + 1) p)).congr (Filter.Eventually.of_forall fun x => ?_)
    exact (pm_iter_fderiv_curryRight k (G x) p).symm
  · intro k
    obtain ⟨b, hb, hbd⟩ := hG.2.2 (k + 1)
    refine ⟨b, hb, ?_⟩
    filter_upwards [hbd] with x hx
    intro q
    exact (pm_norm_fderiv_iter k (G x) q).trans_le (hx q)

/-! ### Derivative formula and smoothness -/

/-- For every target `F` and every family, `iteratedFDeriv k` of the integral is the integral of
`iteratedFDeriv k (G x)`. -/
theorem pm_deriv_formula : ∀ (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (X : Type) [MeasurableSpace X] (m : Measure X) (G : X → E → F), GenHyp m G →
    ∀ p : E, iteratedFDeriv ℝ k (fun q => ∫ x, G x q ∂m) p
      = ∫ x, iteratedFDeriv ℝ k (G x) p ∂m := by
  intro k
  induction k with
  | zero =>
    intro F _ _ _ X _ m G _ p
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.integral_comp_comm
      (fun x => G x p)).symm
  | succ k ih =>
    intro F _ _ _ X _ m G hG p
    have hG' : GenHyp m (fun x q => fderiv ℝ (G x) q) := pm_genHyp_fderiv hG
    have hfun : (fun q => fderiv ℝ (fun q' => ∫ x, G x q' ∂m) q)
        = fun q => ∫ x, fderiv ℝ (G x) q ∂m :=
      funext fun q => (pm_hasFDerivAt_gen hG q).fderiv
    have h2 : iteratedFDeriv ℝ k (fun q => ∫ x, fderiv ℝ (G x) q ∂m) p
        = ∫ x, iteratedFDeriv ℝ k (fun q => fderiv ℝ (G x) q) p ∂m :=
      ih (E →L[ℝ] F) X m (fun x q => fderiv ℝ (G x) q) hG' p
    calc iteratedFDeriv ℝ (k + 1) (fun q => ∫ x, G x q ∂m) p
        = (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
            (iteratedFDeriv ℝ k (fun q => fderiv ℝ (fun q' => ∫ x, G x q' ∂m) q) p) := by
          simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      _ = (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
            (iteratedFDeriv ℝ k (fun q => ∫ x, fderiv ℝ (G x) q ∂m) p) := by
          rw [hfun]
      _ = (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
            (∫ x, iteratedFDeriv ℝ k (fun q => fderiv ℝ (G x) q) p ∂m) := by
          rw [h2]
      _ = ∫ x, (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
            (iteratedFDeriv ℝ k (fun q => fderiv ℝ (G x) q) p) ∂m :=
          ((continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toLinearIsometry.integral_comp_comm
            (fun x => iteratedFDeriv ℝ k (fun q => fderiv ℝ (G x) q) p)).symm
      _ = ∫ x, iteratedFDeriv ℝ (k + 1) (G x) p ∂m := by
          congr 1
          funext x
          rw [pm_iter_fderiv_curryRight, LinearIsometryEquiv.symm_apply_apply]

/-- A `GenHyp` family has a `C^∞` parameter integral. -/
theorem pm_contDiff {X : Type} [MeasurableSpace X] {m : Measure X} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : X → E → F} (hG : GenHyp m G) :
    ContDiff ℝ ∞ (fun q => ∫ x, G x q ∂m) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro k _
  have hfun : iteratedFDeriv ℝ k (fun q => ∫ x, G x q ∂m)
      = fun q => ∫ x, iteratedFDeriv ℝ k (G x) q ∂m :=
    funext fun q => pm_deriv_formula k F X m G hG q
  rw [hfun]
  obtain ⟨b, hb, hbd⟩ := hG.2.2 (k + 1)
  obtain ⟨c, hc, hcd⟩ := hG.2.2 k
  intro q
  refine HasFDerivAt.differentiableAt (pm_hasFDerivAt (G := fun x => iteratedFDeriv ℝ k (G x))
    (b := b) q ?_ ?_ ?_ ?_ hb ?_)
  · filter_upwards [hG.1] with x hx
    exact ContDiff.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k) hx
  · exact fun q' => hG.2.1 k q'
  · refine Integrable.mono' hc (hG.2.1 k q) ?_
    filter_upwards [hcd] with x hx
    exact hx q
  · intro q'
    refine ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).continuous.comp_aestronglyMeasurable
      (hG.2.1 (k + 1) q')).congr (Filter.Eventually.of_forall fun x => ?_)
    exact (pm_fderiv_curryLeft k (G x) q').symm
  · filter_upwards [hbd] with x hx
    intro q'
    exact (pm_norm_fderiv_of_iter k (G x) q').trans_le (hx q')

end ParamIntegralSmoothAux

/-- **Smoothness of parameter integrals** (`ParamIntegralSmooth`). -/
theorem paramIntegralSmooth_proof : UnforcedLeray.Short.PartIIa.ParamIntegralSmooth := by
  intro E _ _ X _ m G hG
  have hG' : ParamIntegralSmoothAux.GenHyp m G := hG
  refine ⟨ParamIntegralSmoothAux.pm_contDiff hG', fun k p => ?_⟩
  exact ParamIntegralSmoothAux.pm_deriv_formula k CVec3 X m G hG' p

end UnforcedLeray.Short.PartIIa
