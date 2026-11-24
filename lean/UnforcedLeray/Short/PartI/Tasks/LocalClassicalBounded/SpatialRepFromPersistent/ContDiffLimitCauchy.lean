import UnforcedLeray.Short.PartI.Sub.T02_1_3

/-!
# Part I, task `PartI:T02/1/3/5`: `ContDiffLimitCauchy` (Mathlib gap)

Source of record: `the November 2 reference manuscript`, lines 261-288. The density
argument for the Sobolev embedding on the cylinder needs limits of uniformly Cauchy `C^m` sequences.

Target: `theorem contDiffLimitCauchy : ContDiffLimitCauchy`, where `ContDiffLimitCauchy` is the
`Prop` of `Short/PartI/Sub/T02_1_3.lean` (line 123).

## Route

`ContDiffLimitCauchyAux.contDiffLimitCauchy_aux` proves the statement for arbitrary real normed
spaces `E`, `F : Type` with `F` complete, by induction on `m`, generalising over the sequence and
the target space:

* base `m = 0`: uniform Cauchy plus pointwise convergence gives uniform convergence, and a uniform
  limit of continuous maps is continuous;
* step `m + 1`: the derivatives `fderiv ℝ (f n)` are `C^m` and their `j`-th derivatives are uniformly
  Cauchy (the curry isometry `continuousMultilinearCurryRightEquiv'` relates `iteratedFDeriv (j+1)`
  to `iteratedFDeriv j` of the derivative). Completeness of `E →L[ℝ] F` gives a uniform limit `G`
  of the derivatives; the induction hypothesis applies to `fun n y => fderiv ℝ (f n) y`, and
  `hasFDerivAt_of_tendstoUniformly` shows that `g` has derivative `G`, whence `C^(m+1)`.
-/

open Set Filter
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

namespace ContDiffLimitCauchyAux

/-- Uniform Cauchy property descends along an isometry on the codomain. -/
lemma uc_of_isometry {α β γ : Type*} [PseudoMetricSpace β] [PseudoMetricSpace γ]
    (Φ : β → γ) (hΦ : Isometry Φ) (F : ℕ → α → β) (s : Set α)
    (h : UniformCauchySeqOn (fun i => Φ ∘ F i) atTop s) : UniformCauchySeqOn F atTop s := by
  rw [Metric.uniformCauchySeqOn_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  have := hN m hm n hn x hx
  simpa only [Function.comp_apply, hΦ.dist_eq] using this

/-- Uniform convergence is transported along an isometry on the codomain. -/
lemma tu_of_isometry {α β γ : Type*} [PseudoMetricSpace β] [PseudoMetricSpace γ]
    (Φ : β → γ) (hΦ : Isometry Φ) (F : ℕ → α → β) (G : α → β)
    (h : TendstoUniformly F G atTop) : TendstoUniformly (fun i => Φ ∘ F i) (Φ ∘ G) atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi x
  simpa only [Function.comp_apply, hΦ.dist_eq] using hi x

/-- Order zero: uniform Cauchy plus pointwise convergence gives uniform convergence. -/
lemma tendstoUniform_of_uc_zero {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℕ → E → F) (g : E → F)
    (hc : UniformCauchySeqOn (fun n => iteratedFDeriv ℝ 0 (f n)) atTop univ)
    (hg : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    TendstoUniformly f g atTop := by
  have hc' : UniformCauchySeqOn f atTop univ :=
    uc_of_isometry _ (continuousMultilinearCurryFin0 ℝ E F).symm.isometry f univ
      (by simpa only [iteratedFDeriv_zero_eq_comp] using hc)
  exact tendstoUniformlyOn_univ.mp (hc'.tendstoUniformlyOn_of_tendsto (fun z _ => hg z))

/-- The `0`-th derivative of a uniformly convergent sequence converges uniformly. -/
lemma tendstoUniform_iteratedFDeriv_zero {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℕ → E → F) (g : E → F)
    (h : TendstoUniformly f g atTop) :
    TendstoUniformly (fun n => iteratedFDeriv ℝ 0 (f n)) (iteratedFDeriv ℝ 0 g) atTop := by
  simp only [iteratedFDeriv_zero_eq_comp]
  exact tu_of_isometry _ (continuousMultilinearCurryFin0 ℝ E F).symm.isometry f g h

/-- Splitting off one derivative: `D^(j+1) f = curry ∘ D^j (Df)`. -/
lemma iteratedFDeriv_succ_eq_iso {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (j : ℕ) :
    iteratedFDeriv ℝ (j + 1) f =
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm ∘
        iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) := by
  funext x
  exact iteratedFDeriv_succ_eq_comp_right

/-- The generic statement over complete real normed target spaces, by induction on `m`. -/
theorem contDiffLimitCauchy_aux (m : ℕ) :
    ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : ℕ → E → F) (g : E → F),
      (∀ n, ContDiff ℝ (m : WithTop ℕ∞) (f n)) →
      (∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) →
      (∀ j : ℕ, j ≤ m → UniformCauchySeqOn (fun n => iteratedFDeriv ℝ j (f n)) atTop univ) →
      ContDiff ℝ (m : WithTop ℕ∞) g ∧
        ∀ j : ℕ, j ≤ m →
          TendstoUniformly (fun n => iteratedFDeriv ℝ j (f n)) (iteratedFDeriv ℝ j g) atTop := by
  induction m with
  | zero =>
    intro E F _ _ _ _ _ f g hf hg hc
    have hcont : ∀ n, Continuous (f n) := fun n =>
      (contDiff_zero (𝕜 := ℝ)).mp (by simpa using hf n)
    have hu : TendstoUniformly f g atTop :=
      tendstoUniform_of_uc_zero f g (hc 0 (Nat.zero_le _)) hg
    have hgc : Continuous g := hu.continuous (Filter.Eventually.of_forall hcont).frequently
    refine ⟨by simpa using (contDiff_zero (𝕜 := ℝ)).mpr hgc, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    exact tendstoUniform_iteratedFDeriv_zero f g hu
  | succ m ih =>
    intro E F _ _ _ _ _ f g hf hg hc
    -- `C^(m+1)` approximants written as `C^(m+1)` with the cast in the form `↑m + 1`
    have hf' : ∀ n, ContDiff ℝ ((m : WithTop ℕ∞) + 1) (f n) := fun n => by
      rw [← Nat.cast_succ]
      exact hf n
    have hdiff : ∀ n, Differentiable ℝ (f n) := fun n => (contDiff_succ_iff_fderiv.mp (hf' n)).1
    have hD : ∀ n, ContDiff ℝ (m : WithTop ℕ∞) (fun y => fderiv ℝ (f n) y) := fun n =>
      (contDiff_succ_iff_fderiv.mp (hf' n)).2.2
    -- uniform Cauchy property of the `j`-th derivatives of the derivatives
    have hUC : ∀ j : ℕ, j ≤ m →
        UniformCauchySeqOn (fun n => iteratedFDeriv ℝ j (fun y => fderiv ℝ (f n) y)) atTop univ := by
      intro j hj
      refine uc_of_isometry _ (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.isometry _ univ ?_
      have h1 := hc (j + 1) (by omega)
      simpa only [iteratedFDeriv_succ_eq_iso] using h1
    -- uniform Cauchy property of the derivatives themselves
    have hUCD : UniformCauchySeqOn (fun n y => fderiv ℝ (f n) y) atTop univ :=
      uc_of_isometry _ (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).symm.isometry _ univ
        (by simpa only [iteratedFDeriv_zero_eq_comp] using hUC 0 (Nat.zero_le _))
    -- pointwise limit of the derivatives, and its uniform convergence
    have hcau : ∀ x : E, CauchySeq (fun n => fderiv ℝ (f n) x) := fun x =>
      hUCD.cauchySeq (mem_univ x)
    choose G hG using fun x : E => cauchySeq_tendsto_of_complete (hcau x)
    have hTU : TendstoUniformly (fun n y => fderiv ℝ (f n) y) G atTop :=
      tendstoUniformlyOn_univ.mp (hUCD.tendstoUniformlyOn_of_tendsto (fun x _ => hG x))
    -- induction hypothesis for the derivatives
    obtain ⟨hGc, hGu⟩ := ih E (E →L[ℝ] F) (fun n y => fderiv ℝ (f n) y) G hD (fun x => hG x) hUC
    -- the limit `g` is differentiable with derivative `G`
    have hfd : ∀ n x, HasFDerivAt (f n) (fderiv ℝ (f n) x) x := fun n x =>
      ((hdiff n) x).hasFDerivAt
    have hgd : ∀ x, HasFDerivAt g (G x) x := fun x =>
      hasFDerivAt_of_tendstoUniformly hTU hfd hg x
    have hfg : fderiv ℝ g = G := funext fun x => (hgd x).fderiv
    have hgdiff : Differentiable ℝ g := fun x => (hgd x).differentiableAt
    have hu0 : TendstoUniformly f g atTop :=
      tendstoUniform_of_uc_zero f g (hc 0 (Nat.zero_le _)) hg
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨hgdiff, fun h => absurd h (by simp), ?_⟩
      rw [hfg]
      exact hGc
    · intro j hj
      cases j with
      | zero => exact tendstoUniform_iteratedFDeriv_zero f g hu0
      | succ j =>
        have hj' : j ≤ m := by omega
        have hT := hGu j hj'
        simp only [iteratedFDeriv_succ_eq_iso]
        rw [hfg]
        exact tu_of_isometry _ (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.isometry _ _ hT

end ContDiffLimitCauchyAux

open ContDiffLimitCauchyAux in
/-- **`ContDiffLimitCauchy`**: uniformly Cauchy `C^m` sequences on the plane converge to a `C^m`
limit, with uniform convergence of all derivatives of order `≤ m`. -/
theorem contDiffLimitCauchy : ContDiffLimitCauchy := by
  unfold ContDiffLimitCauchy
  intro m f g hf hg hc
  exact contDiffLimitCauchy_aux m UnforcedLeray.Cyl.Plane UnforcedLeray.Train.Vec f g hf hg hc

end UnforcedLeray.Short.PartI
