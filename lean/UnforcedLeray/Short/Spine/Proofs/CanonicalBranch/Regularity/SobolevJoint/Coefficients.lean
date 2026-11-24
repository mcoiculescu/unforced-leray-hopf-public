import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4

/-!
# Spine: `CoefficientBounds` (leaf 3 of `Spine:SP-CAN/4/4`)

Proves `CoefficientBounds` (`Sub/SP_CAN4_4.lean`) exactly as stated, with no extra hypotheses.

Source of record: `the November 2 reference manuscript` line 1086 and lines
1134-1140 (Hermite decomposition; `X_{G,j}` is the Gaussian-weighted Sobolev space).

Route. Let `U_j` be the `C^∞` witness of `IsSmoothAllXGj V` at level `j`. For `θ > 0`,
`⟪e_n, U_j θ⟫ = (1+n)^{j/2} ⟪e_n, V θ⟫` (`B0123.inner_IDpow`), so the coefficient
`θ ↦ ⟪e_n, V θ⟫` is the scalar multiple `((1+n)^{j/2})⁻¹` of the `C^∞` curve `θ ↦ ⟪e_n, U_j θ⟫`.
Its `k`-th derivative is `((1+n)^{j/2})⁻¹ ⟪e_n, U_j^{(k)} θ⟫`, so
`(1+n)^j ‖c_n^{(k)} θ‖² = ‖⟪e_n, U_j^{(k)} θ⟫‖²`. Parseval (`B0123.hasSum_norm_inner_sq`) gives
summability with sum `‖U_j^{(k)} θ‖²`, which is bounded on `[a, b] ⊂ (0, ∞)` by continuity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- The multiplier `(1+n)^s` of `(I - D)^s` is nonzero. -/
theorem coefBounds_idMult_ne_zero (s : ℝ) (n : ℕ) : B0123.idMult s n ≠ 0 := by
  unfold B0123.idMult
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) s).ne'

/-- Composition with the continuous linear functional `⟪e, ·⟫` preserves `C^∞` on any set. -/
theorem coefBounds_inner_comp_contDiffOn (e : XG) (U : ℝ → XG) (s : Set ℝ)
    (hU : ContDiffOn ℝ ∞ U s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => inner ℂ e (U t)) s := by
  have hL : ContDiff ℝ ∞ ((innerSL ℂ e).restrictScalars ℝ : XG →L[ℝ] ℂ) :=
    ContinuousLinearMap.contDiff _
  exact hL.comp_contDiffOn hU

/-- The `k`-th derivative commutes with `⟪e, ·⟫` for a curve that is `C^∞` at `θ`. -/
theorem coefBounds_iteratedDeriv_inner_comp (e : XG) (U : ℝ → XG) {θ : ℝ} (k : ℕ)
    (hU : ContDiffAt ℝ ∞ U θ) :
    iteratedDeriv k (fun t : ℝ => inner ℂ e (U t)) θ = inner ℂ e (iteratedDeriv k U θ) := by
  set g : XG →L[ℝ] ℂ := (innerSL ℂ e).restrictScalars ℝ with hg
  have h1 : iteratedFDeriv ℝ k (g ∘ U) θ = g.compContinuousMultilinearMap (iteratedFDeriv ℝ k U θ) :=
    g.iteratedFDeriv_comp_left hU (mod_cast le_top)
  have h2 : iteratedDeriv k (g ∘ U) θ = g (iteratedDeriv k U θ) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, h1, iteratedDeriv_eq_iteratedFDeriv]
    simp
  exact h2

/-- On a witness `U` of level `j`, `⟪e_n, U θ⟫ = (1+n)^{j/2} ⟪e_n, V θ⟫` for `θ > 0`. -/
theorem coefBounds_inner_witness (V U : ℝ → XG) (j : ℕ)
    (hU : ∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j,
      B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ)
    (n : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    inner ℂ (B0094.oscBasis n) (U θ) =
      B0123.idMult ((j : ℝ) / 2) n * inner ℂ (B0094.oscBasis n) (V θ) := by
  obtain ⟨h, hh⟩ := hU θ hθ
  rw [← hh]
  exact B0123.inner_IDpow _ ⟨V θ, h⟩ n

/-- The coefficient is `((1+n)^{j/2})⁻¹` times the coefficient of the witness. -/
theorem coefBounds_coeff_eq (V U : ℝ → XG) (j : ℕ)
    (hU : ∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j,
      B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ)
    (n : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    inner ℂ (B0094.oscBasis n) (V θ) =
      (B0123.idMult ((j : ℝ) / 2) n)⁻¹ * inner ℂ (B0094.oscBasis n) (U θ) := by
  rw [coefBounds_inner_witness V U j hU n θ hθ, ← mul_assoc,
    inv_mul_cancel₀ (coefBounds_idMult_ne_zero _ _), one_mul]

/-- Smoothness of the coefficient `θ ↦ ⟪e_n, V θ⟫` on `(0, ∞)`. -/
theorem coefBounds_coeff_contDiffOn (V U : ℝ → XG) (j : ℕ)
    (hU : ∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j,
      B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ)
    (hUs : ContDiffOn ℝ ∞ U (Ioi 0)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => inner ℂ (B0094.oscBasis n) (V θ)) (Ioi 0) := by
  have hmul : ContDiffOn ℝ ∞
      (fun t : ℝ => (B0123.idMult ((j : ℝ) / 2) n)⁻¹ * inner ℂ (B0094.oscBasis n) (U t))
      (Ioi 0) :=
    contDiffOn_const.mul (coefBounds_inner_comp_contDiffOn _ U _ hUs)
  exact hmul.congr (fun θ hθ => coefBounds_coeff_eq V U j hU n θ hθ)

/-- The `k`-th derivative of the coefficient on `(0, ∞)`. -/
theorem coefBounds_coeff_iteratedDeriv (V U : ℝ → XG) (j : ℕ)
    (hU : ∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j,
      B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ)
    (hUs : ContDiffOn ℝ ∞ U (Ioi 0)) (n k : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    iteratedDeriv k (fun t : ℝ => inner ℂ (B0094.oscBasis n) (V t)) θ =
      (B0123.idMult ((j : ℝ) / 2) n)⁻¹ * inner ℂ (B0094.oscBasis n) (iteratedDeriv k U θ) := by
  have hUθ : ContDiffAt ℝ ∞ U θ := hUs.contDiffAt (Ioi_mem_nhds hθ)
  have hLθ : ContDiffAt ℝ ∞ (fun t : ℝ => inner ℂ (B0094.oscBasis n) (U t)) θ :=
    (coefBounds_inner_comp_contDiffOn _ U _ hUs).contDiffAt (Ioi_mem_nhds hθ)
  have hev : (fun t : ℝ => inner ℂ (B0094.oscBasis n) (V t)) =ᶠ[𝓝 θ]
      (fun t : ℝ => (B0123.idMult ((j : ℝ) / 2) n)⁻¹ * inner ℂ (B0094.oscBasis n) (U t)) := by
    filter_upwards [Ioi_mem_nhds hθ] with t ht
    exact coefBounds_coeff_eq V U j hU n t ht
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_mul _ (hLθ.of_le (mod_cast le_top)),
    coefBounds_iteratedDeriv_inner_comp _ U k hUθ]

/-- Local boundedness of `‖U^{(k)}‖` on `[a, b] ⊂ (0, ∞)`. -/
theorem coefBounds_iteratedDeriv_bound (U : ℝ → XG) (hUs : ContDiffOn ℝ ∞ U (Ioi 0)) (k : ℕ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, ∀ θ ∈ Icc a b, ‖iteratedDeriv k U θ‖ ≤ M := by
  have hcont : ContinuousOn (iteratedDeriv k U) (Icc a b) := by
    have h1 : ContinuousOn (iteratedDerivWithin k U (Ioi 0)) (Ioi 0) :=
      hUs.continuousOn_iteratedDerivWithin (mod_cast le_top) isOpen_Ioi.uniqueDiffOn
    have h2 : ContinuousOn (iteratedDeriv k U) (Ioi 0) :=
      h1.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)
    exact h2.mono (fun x hx => lt_of_lt_of_le ha hx.1)
  exact isCompact_Icc.exists_bound_of_continuousOn hcont

/-- **`CoefficientBounds`**: for `V` with `IsSmoothAllXGj V`, the coefficients
`θ ↦ ⟪e_n, V θ⟫` are `C^∞` on `(0, ∞)`, and for all `k, j` and `0 < a < b` the weighted
`ℓ²` sums `∑ₙ (1+n)^j ‖c_n^{(k)}(θ)‖²` are summable with a uniform bound on `[a, b]`. -/
theorem coefficientBounds_proof : UnforcedLeray.Short.Spine.CoefficientBounds := by
  intro V hV
  obtain ⟨U0, hU0, hU0s⟩ := hV 0
  refine ⟨fun n => coefBounds_coeff_contDiffOn V U0 0 hU0 hU0s n, ?_⟩
  intro k j a b ha _hab
  obtain ⟨U, hUw, hUs⟩ := hV j
  obtain ⟨M, hM⟩ := coefBounds_iteratedDeriv_bound U hUs k ha
  refine ⟨M ^ 2, fun θ hθ => ?_⟩
  have hθpos : 0 < θ := lt_of_lt_of_le ha hθ.1
  have hX : ‖iteratedDeriv k U θ‖ ≤ M := hM θ hθ
  have hfun : (fun n : ℕ => (1 + (n : ℝ)) ^ j *
        ‖iteratedDeriv k (fun t : ℝ => inner ℂ (B0094.oscBasis n) (V t)) θ‖ ^ 2) =
      fun n : ℕ => ‖inner ℂ (B0094.oscBasis n) (iteratedDeriv k U θ)‖ ^ 2 := by
    funext n
    rw [coefBounds_coeff_iteratedDeriv V U j hUw hUs n k hθpos, norm_mul, norm_inv,
      B0123.norm_idMult]
    have hx : (1 + (n : ℝ)) ^ ((j : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    rw [← B0123.one_add_rpow_half_sq j n]
    field_simp
  have hs := B0123.hasSum_norm_inner_sq B0094.oscBasis (iteratedDeriv k U θ)
  rw [hfun]
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) hX 2

end UnforcedLeray.Short.Spine
