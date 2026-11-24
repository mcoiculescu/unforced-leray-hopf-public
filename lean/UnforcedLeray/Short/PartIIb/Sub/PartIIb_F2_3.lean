import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2

/-!
# `PartII-b:F2/3` (`Sub/PartII-b_F2_3.lean`): Decomposition of `FrozenEulerSplittingStep`

Source of record: `the November 2 reference manuscript` (SP), lines 931–953,
2104–2115, 2145–2171, 2347–2358 (`short-sp:dichotomy`).

This module provides:
1. `PartIIbF23Sub`:
   * 2×2 Euclidean rotation-scaling operator calculus on `E2 = EuclideanSpace ℝ (Fin 2)`
     (`rotScaleMat`, `rotScaleCLM`, `rotScaleCLM_inv_mul`, `rotScaleCLM_mul_inv`,
     `norm_rotScaleCLM_le`);
   * Block-length threshold selection (`exists_L₀_frozen_dichotomy`);
   * (`frozenOmega` and `frozenRadialFlow`, the frozen radial transport flow at slow age `σ`,
     are defined in `Sub/PartII-b_F2.lean` in the same namespace.)
2. The two leaf propositions of `PartII-b:F2/3`:
   * `PlanarFrozenEulerStep` (`PartII-b:F2/3/1`, SP 931–953, 2104–2115, 2145–2171),
   * `PeriodizedCylinderCoordStep` (`PartII-b:F2/3/2`, SP 2167–2171, 2347–2358),
   and the unconditional assembly theorem `frozenEulerSplittingStep_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace PartIIbF23Sub

/-! ## 1. 2×2 Euclidean rotation-scaling operator calculus on `E2` -/

/-- The 2×2 real rotation-scaling matrix `![![r * cos θ, -r * sin θ], ![r * sin θ, r * cos θ]]`. -/
def rotScaleMat (r θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![r * Real.cos θ, -r * Real.sin θ],
    ![r * Real.sin θ,  r * Real.cos θ]]

/-- Continuous linear map on `E2 = EuclideanSpace ℝ (Fin 2)` induced by `rotScaleMat r θ`. -/
def rotScaleCLM (r θ : ℝ) : E2 →L[ℝ] E2 :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (rotScaleMat r θ))

theorem rotScaleCLM_apply_zero (r θ : ℝ) (v : E2) :
    rotScaleCLM r θ v 0 = r * Real.cos θ * v 0 - r * Real.sin θ * v 1 := by
  change (Matrix.mulVec (rotScaleMat r θ) v) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rotScaleMat]
  ring

theorem rotScaleCLM_apply_one (r θ : ℝ) (v : E2) :
    rotScaleCLM r θ v 1 = r * Real.sin θ * v 0 + r * Real.cos θ * v 1 := by
  change (Matrix.mulVec (rotScaleMat r θ) v) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rotScaleMat]

theorem rotScaleCLM_comp (r₁ θ₁ r₂ θ₂ : ℝ) :
    (rotScaleCLM r₁ θ₁).comp (rotScaleCLM r₂ θ₂) =
      rotScaleCLM (r₁ * r₂) (θ₁ + θ₂) := by
  ext1 v
  ext i
  fin_cases i
  · simp only [ContinuousLinearMap.comp_apply, Fin.zero_eta,
      rotScaleCLM_apply_zero, rotScaleCLM_apply_one, Real.cos_add, Real.sin_add]
    ring
  · simp only [ContinuousLinearMap.comp_apply, Fin.mk_one,
      rotScaleCLM_apply_zero, rotScaleCLM_apply_one, Real.cos_add, Real.sin_add]
    ring

theorem rotScaleCLM_one_zero :
    rotScaleCLM 1 0 = ContinuousLinearMap.id ℝ E2 := by
  ext1 v
  ext i
  fin_cases i
  · simp [rotScaleCLM_apply_zero]
  · simp [rotScaleCLM_apply_one]

theorem rotScaleCLM_inv_mul {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    rotScaleCLM r⁻¹ (-θ) * rotScaleCLM r θ = 1 := by
  change (rotScaleCLM r⁻¹ (-θ)).comp (rotScaleCLM r θ) = ContinuousLinearMap.id ℝ E2
  rw [rotScaleCLM_comp, inv_mul_cancel₀ hr, neg_add_cancel, rotScaleCLM_one_zero]

theorem rotScaleCLM_mul_inv {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    rotScaleCLM r θ * rotScaleCLM r⁻¹ (-θ) = 1 := by
  change (rotScaleCLM r θ).comp (rotScaleCLM r⁻¹ (-θ)) = ContinuousLinearMap.id ℝ E2
  rw [rotScaleCLM_comp, mul_inv_cancel₀ hr, add_neg_cancel, rotScaleCLM_one_zero]

theorem norm_sq_e2 (v : E2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_rotScaleCLM_apply {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (v : E2) :
    ‖rotScaleCLM r θ v‖ = r * ‖v‖ := by
  have h_sq : ‖rotScaleCLM r θ v‖ ^ 2 = (r * ‖v‖) ^ 2 := by
    rw [norm_sq_e2, mul_pow, norm_sq_e2, rotScaleCLM_apply_zero, rotScaleCLM_apply_one]
    have h_trig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    calc (r * Real.cos θ * v 0 - r * Real.sin θ * v 1) ^ 2 +
          (r * Real.sin θ * v 0 + r * Real.cos θ * v 1) ^ 2
        = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by ring
      _ = r ^ 2 * 1 * (v 0 ^ 2 + v 1 ^ 2) := by rw [h_trig]
      _ = r ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
  have h_nn_lhs : 0 ≤ ‖rotScaleCLM r θ v‖ := norm_nonneg _
  have h_nn_rhs : 0 ≤ r * ‖v‖ := mul_nonneg hr (norm_nonneg _)
  nlinarith [sq_nonneg (‖rotScaleCLM r θ v‖ - r * ‖v‖)]

theorem norm_rotScaleCLM_le {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖rotScaleCLM r θ‖ ≤ r :=
  ContinuousLinearMap.opNorm_le_bound _ hr fun v => (norm_rotScaleCLM_apply hr θ v).le

/-! ## 2. Block-length threshold `L₀` and frozen radial transport flow -/

/-- Exponential decay helper: for `δ > 0` and `C > 0`, there is `L₁ ≥ 1` such that for all
`L ≥ L₁`, `C * Real.exp (-δ * L) ≤ 1 / 4`. -/
theorem exists_L_exp_neg_le_quarter {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L → C * Real.exp (-δ * L) ≤ 1 / 4 := by
  set L₁ : ℝ := max 1 ((4 * C) / δ)
  have hL₁_ge : 1 ≤ L₁ := le_max_left _ _
  refine ⟨L₁, hL₁_ge, fun L hL => ?_⟩
  have hL_bound : (4 * C) / δ ≤ L := (le_max_right _ _).trans hL
  have hδL : 4 * C ≤ δ * L := by
    have := (div_le_iff₀ hδ).mp hL_bound
    linarith [mul_comm L δ]
  have h_one_lt : 1 + δ * L ≤ Real.exp (δ * L) := by
    linarith [Real.add_one_le_exp (δ * L)]
  have h_exp_ge : 4 * C ≤ Real.exp (δ * L) := by linarith
  have h_inv : Real.exp (-δ * L) = (Real.exp (δ * L))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [h_inv]
  have h1 : C * (Real.exp (δ * L))⁻¹ ≤ C * (4 * C)⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    exact inv_anti₀ (by positivity) h_exp_ge
  have h2 : C * (4 * C)⁻¹ = 1 / 4 := by
    field_simp [hC.ne']
  linarith

/-- Given `Sig > 0`, `0 < a' < b' < lam.re / (1 + Sig) ^ 2`, and `C_compl > 0`, there exists
`L₀ ≥ 1` such that for all `σ ∈ Icc 0 Sig` and `L ≥ L₀`:
1. `Real.exp (-(lam.re * L / (1 + σ) ^ 2)) ≤ (1 / 4 : ℝ) * Real.exp (-b' * L)`, and
2. `C_compl * Real.exp ((a' / 2) * L) ≤ (1 / 4 : ℝ) * Real.exp (a' * L)`. -/
theorem exists_L₀_frozen_dichotomy
    {Sig : ℝ} {lam : ℂ} {a' b' C_compl : ℝ}
    (_hSig : 0 < Sig) (ha' : 0 < a') (hab' : a' < b')
    (hb' : b' < lam.re / (1 + Sig) ^ 2) (hC_compl : 0 < C_compl) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ σ ∈ Icc 0 Sig, ∀ L : ℝ, L₀ ≤ L →
        Real.exp (-(lam.re * L / (1 + σ) ^ 2)) ≤ (1 / 4 : ℝ) * Real.exp (-b' * L) ∧
        C_compl * Real.exp ((a' / 2) * L) ≤ (1 / 4 : ℝ) * Real.exp (a' * L) := by
  set γ_min : ℝ := lam.re / (1 + Sig) ^ 2
  have hδ₁ : 0 < γ_min - b' := sub_pos.mpr hb'
  have hδ₂ : 0 < a' / 2 := half_pos ha'
  obtain ⟨L₁, hL₁_1, hL₁⟩ := exists_L_exp_neg_le_quarter hδ₁ zero_lt_one
  obtain ⟨L₂, hL₂_1, hL₂⟩ := exists_L_exp_neg_le_quarter hδ₂ hC_compl
  refine ⟨max L₁ L₂, hL₁_1.trans (le_max_left _ _), fun σ hσ L hL => ?_⟩
  have hL_pos : 0 ≤ L := zero_le_one.trans (hL₁_1.trans ((le_max_left _ _).trans hL))
  have hlam_pos : 0 < lam.re := by
    have h1 : 0 < γ_min := (ha'.trans hab').trans hb'
    have h2 : 0 < (1 + Sig) ^ 2 := by positivity
    have h3 : 0 < γ_min * (1 + Sig) ^ 2 := mul_pos h1 h2
    dsimp [γ_min] at h3
    rwa [div_mul_cancel₀ _ h2.ne'] at h3
  have h_rate_ge : γ_min ≤ lam.re / (1 + σ) ^ 2 := by
    dsimp [γ_min]
    have h1σ : 0 < 1 + σ := by linarith [hσ.1]
    refine div_le_div_of_nonneg_left hlam_pos.le (sq_pos_of_pos h1σ) ?_
    nlinarith [hσ.1, hσ.2]
  constructor
  · have h_exp_le : Real.exp (-(lam.re * L / (1 + σ) ^ 2)) ≤ Real.exp (-γ_min * L) := by
      apply Real.exp_le_exp.mpr
      have h_mul : γ_min * L ≤ (lam.re / (1 + σ) ^ 2) * L :=
        mul_le_mul_of_nonneg_right h_rate_ge hL_pos
      have h_eq : (lam.re / (1 + σ) ^ 2) * L = lam.re * L / (1 + σ) ^ 2 := div_mul_eq_mul_div _ _ _
      linarith
    have h_split : Real.exp (-γ_min * L) =
        (1 * Real.exp (-(γ_min - b') * L)) * Real.exp (-b' * L) := by
      rw [one_mul, ← Real.exp_add]
      congr 1; ring
    have h_q := hL₁ L ((le_max_left _ _).trans hL)
    calc Real.exp (-(lam.re * L / (1 + σ) ^ 2))
        ≤ Real.exp (-γ_min * L) := h_exp_le
      _ = (1 * Real.exp (-(γ_min - b') * L)) * Real.exp (-b' * L) := h_split
      _ ≤ (1 / 4 : ℝ) * Real.exp (-b' * L) :=
          mul_le_mul_of_nonneg_right h_q (Real.exp_pos _).le
  · have h_split : C_compl * Real.exp ((a' / 2) * L) =
        (C_compl * Real.exp (-(a' / 2) * L)) * Real.exp (a' * L) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2; ring
    have h_q := hL₂ L ((le_max_right _ _).trans hL)
    rw [h_split]
    exact mul_le_mul_of_nonneg_right h_q (Real.exp_pos _).le

/-! The frozen angular velocity `frozenOmega` and the radial transport flow `frozenRadialFlow`
(SP 841–852, 931–953, 2104–2115) are defined in `Sub/PartII-b_F2.lean` (same namespace
`PartIIbF23Sub`), where `IsFrozenRadialTransport` and `IsFrozenEulerPackage.euler_duhamel` use them. -/

end PartIIbF23Sub

/-! ## 3. Leaf propositions (`PartII-b:F2/3/1` and `PartII-b:F2/3/2`) and assembly -/

/-- The unperiodized planar frozen direct modes `(2 Re J_a q, -2 Im J_a q)` (the `c = ∞`
profile of `frozenDirectMode`, SP 2167-2171, 2347-2358). -/
def planarFrozenDirectMode (q : Blueprint.Planar.Profile) (a : ℝ) (i : Fin 2)
    (x : B0579.Plane) : ℝ :=
  ![2 * (dilPlanarMode q a x).re, -2 * (dilPlanarMode q a x).im] i

/-- **Leaf 1 (`PartII-b:F2/3/1`, `PlanarFrozenEulerStep`, SP 931–953, 2104–2115, 2145–2171)**:
for every `m > 8`, `Sig > 0`, and growing eigenpair `IsGrowingEigenpair lam q`, there exist a
coordinate bound `M_pl ≥ 1`, continuous planar coordinate maps
`ι_pl : ℝ → (E2 →L[ℝ] Xm m)` and `π_pl : ℝ → (Xm m →L[ℝ] E2)` on `Icc 0 Sig`, and the frozen
planar Euler semigroup family `E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)` such that:
* `(π_pl σ).comp (ι_pl σ) = id` and `‖ι_pl σ‖, ‖π_pl σ‖ ≤ M_pl` on `Icc 0 Sig`;
* `E_pl σ` is a strongly continuous semigroup on `Xm m` for `σ ∈ Icc 0 Sig`;
* `E_pl σ τ` acts on `ι_pl σ` by `rotScaleCLM (exp(lam.re * τ / (1 + σ)²)) (lam.im * τ / (1 + σ)²)`;
* `E_pl σ τ` commutes with the spectral projection `P_σ = (ι_pl σ).comp (π_pl σ)`;
* for every `η > 0`, there is `C_η > 0` such that on the complementary subspace `I - P_σ`,
  `‖(E_pl σ τ).comp (id - (ι_pl σ).comp (π_pl σ))‖ ≤ C_η * exp(η * τ)` uniformly in
  `σ ∈ Icc 0 Sig` and `τ ≥ 0`;
* `ι_pl σ α` is a.e. the combination `∑ i, α i * planarFrozenDirectMode q (1 + σ) i`
  (the frozen plane direct vectors, SP 2167-2171);
* `E_pl σ` is the mild Duhamel evolution of the frozen planar radial transport group `T_pl σ`
  (`PartIIbF23Sub.frozenRadialFlow σ`) perturbed by the planar interaction operator
  `IsPlanarInteractionOp m σ A`. -/
def PlanarFrozenEulerStep : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (M_pl : ℝ)
      (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2))
      (E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)),
      1 ≤ M_pl ∧
      (ContinuousOn ι_pl (Icc 0 Sig) ∧ ContinuousOn π_pl (Icc 0 Sig)) ∧
      (∀ σ ∈ Icc 0 Sig,
        (π_pl σ).comp (ι_pl σ) = ContinuousLinearMap.id ℝ E2 ∧
          ‖ι_pl σ‖ ≤ M_pl ∧ ‖π_pl σ‖ ≤ M_pl) ∧
      (∀ σ ∈ Icc 0 Sig, ∀ α : E2,
        (ι_pl σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
          fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x) ∧
      (∀ σ ∈ Icc 0 Sig,
        E_pl σ 0 = ContinuousLinearMap.id ℝ (Xm m) ∧
        (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → 0 ≤ τ₂ → E_pl σ (τ₁ + τ₂) = (E_pl σ τ₁).comp (E_pl σ τ₂)) ∧
        ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0)) ∧
      (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
        let θ : ℝ := lam.im * τ / (1 + σ) ^ 2
        let r : ℝ := Real.exp (lam.re * τ / (1 + σ) ^ 2)
        (E_pl σ τ).comp (ι_pl σ) =
          (ι_pl σ).comp
            (LinearMap.toContinuousLinearMap
              (Matrix.toEuclideanLin ![![r * Real.cos θ, -r * Real.sin θ],
                                       ![r * Real.sin θ,  r * Real.cos θ]]))) ∧
      (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
        (E_pl σ τ).comp ((ι_pl σ).comp (π_pl σ)) =
          ((ι_pl σ).comp (π_pl σ)).comp (E_pl σ τ)) ∧
      (∀ η : ℝ, 0 < η → ∃ C_η : ℝ, 0 < C_η ∧
        ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
          ‖(E_pl σ τ).comp (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ))‖ ≤
            C_η * Real.exp (η * τ)) ∧
      (∃ T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m),
        (∀ σ ∈ Icc 0 Sig,
          T_pl σ 0 = ContinuousLinearMap.id ℝ (Xm m) ∧
          (∀ τ₁ τ₂ : ℝ, T_pl σ (τ₁ + τ₂) = (T_pl σ τ₁).comp (T_pl σ τ₂)) ∧
          (∀ τ : ℝ, ∀ f : Xm m, ‖T_pl σ τ f‖ = ‖f‖) ∧
          (∀ f : Xm m, Continuous (fun τ => T_pl σ τ f)) ∧
          (∀ τ : ℝ, ∀ f : Xm m,
            (T_pl σ τ f : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
              fun x => f (PartIIbF23Sub.frozenRadialFlow σ τ x))) ∧
        (∀ σ ∈ Icc 0 Sig, ∀ A : Xm m →L[ℝ] Xm m, IsPlanarInteractionOp m σ A →
          ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
            IntervalIntegrable (fun r => T_pl σ (τ - r) (A (E_pl σ r f))) volume 0 τ ∧
            E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (A (E_pl σ r f))))

/-- **Leaf 2 (`PartII-b:F2/3/2`, `PeriodizedCylinderCoordStep`, SP 2167–2171, 2347–2358)**:
for every `m > 8`, `Sig > 0`, growing eigenpair `IsGrowingEigenpair lam q`, and planar coordinate
maps `(ι_pl, π_pl)` from `PlanarFrozenEulerStep` (with `ι_pl σ` the planar frozen direct modes;
`π_pl` needs no extra tie, being a bounded functional on the Hilbert space `Xm m`, continuous in
`σ`, hence uniformly approximated by its restrictions to cells), there exist a period threshold `c₀ ≥ 1`, a
uniform bound `M_c ≥ 1`, and periodized cylinder coordinate maps
`ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m)` and `π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)` such that for
all `c ≥ c₀` and `σ ∈ Icc 0 Sig`:
* `ι_c c σ α` realizes `∑ i, α i * frozenDirectMode q c (1 + σ) i` a.e. on `B0579.cellMeasure c m`
  and has zero circulation (`HasZeroCirculationR c (ι_c c σ α)`);
* `(π_c c σ).comp (ι_c c σ) = id` and `‖ι_c c σ‖, ‖π_c c σ‖ ≤ M_c`;
* `(Jc c m).comp (ι_c c σ) → ι_pl σ` and `(π_c c σ).comp (Rc c m) → π_pl σ` uniformly on
  `σ ∈ Icc 0 Sig` as `c → ∞`. -/
def PeriodizedCylinderCoordStep : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2)),
    ContinuousOn ι_pl (Icc 0 Sig) → ContinuousOn π_pl (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, (π_pl σ).comp (ι_pl σ) = ContinuousLinearMap.id ℝ E2) →
    (∀ σ ∈ Icc 0 Sig, ∀ α : E2,
      (ι_pl σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
        fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x) →
    ∃ (c₀ M_c : ℝ)
      (ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m))
      (π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)),
      1 ≤ c₀ ∧ 1 ≤ M_c ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig, ∀ α : E2,
        (ι_c c σ α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
          fun x => ∑ i : Fin 2, α i * frozenDirectMode q c (1 + σ) i x) ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig, ∀ α : E2,
        HasZeroCirculationR c (ι_c c σ α)) ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig,
        (π_c c σ).comp (ι_c c σ) = ContinuousLinearMap.id ℝ E2) ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ σ ∈ Icc 0 Sig,
        ‖ι_c c σ‖ ≤ M_c ∧ ‖π_c c σ‖ ≤ M_c) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c₁ : ℝ, c₀ ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c →
        ∀ σ ∈ Icc 0 Sig,
          ‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖ ≤ ε ∧
          ‖(π_c c σ).comp (Rc c m) - π_pl σ‖ ≤ ε)

/-- **Full assembly of `FrozenEulerSplittingStep` (`PartII-b:F2/3`)** from `PlanarFrozenEulerStep`
(`PartII-b:F2/3/1`) and `PeriodizedCylinderCoordStep` (`PartII-b:F2/3/2`). -/
theorem frozenEulerSplittingStep_of
    (hPl : PlanarFrozenEulerStep)
    (hCyl : PeriodizedCylinderCoordStep) :
    FrozenEulerSplittingStep := by
  intro m hm Sig lam q hSig hEig a' b' ha' hab' hb'
  obtain ⟨M_pl, ι_pl, π_pl, E_pl, hM_pl_1, hPl_cont, hPl_proj, hPl_ae, hE_semi, hE_eigen,
    hE_comm, hE_compl, hE_duh⟩ := hPl m hm Sig lam q hSig hEig
  obtain ⟨c₀, M_c, ι_c, π_c, hc₀_1, hM_c_1, hCyl_ae, hCyl_circ, hCyl_id, hCyl_norm, hCyl_conv⟩ :=
    hCyl m hm Sig lam q hSig hEig ι_pl π_pl hPl_cont.1 hPl_cont.2
      (fun σ hσ => (hPl_proj σ hσ).1) hPl_ae
  obtain ⟨C_η, hC_η, hCompl_bd⟩ := hE_compl (a' / 2) (half_pos ha')
  set C_compl : ℝ := (1 + M_pl * M_pl) * C_η
  have hC_compl_pos : 0 < C_compl := by
    dsimp [C_compl]
    have : 0 ≤ M_pl * M_pl := mul_nonneg (zero_le_one.trans hM_pl_1) (zero_le_one.trans hM_pl_1)
    positivity
  obtain ⟨L₀, hL₀_1, hL₀_bd⟩ :=
    PartIIbF23Sub.exists_L₀_frozen_dichotomy hSig ha' hab' hb' hC_compl_pos
  set M_E : ℝ := max M_pl M_c
  have hM_E_1 : 1 ≤ M_E := hM_pl_1.trans (le_max_left _ _)
  refine ⟨L₀, M_E, c₀, ι_pl, π_pl, E_pl, ι_c, π_c, ?_, ?_⟩
  · refine
      { L₀_ge_one := hL₀_1
        M_E_ge_one := hM_E_1
        c₀_ge_one := hc₀_1
        cyl_direct_ae := hCyl_ae
        cyl_zeroCirc := hCyl_circ
        cyl_proj_id := hCyl_id
        cyl_norm := fun c hc σ hσ =>
          ⟨(hCyl_norm c hc σ hσ).1.trans (le_max_right _ _),
           (hCyl_norm c hc σ hσ).2.trans (le_max_right _ _)⟩
        pl_cont := hPl_cont
        pl_proj_id := fun σ hσ =>
          ⟨(hPl_proj σ hσ).1,
           (hPl_proj σ hσ).2.1.trans (le_max_left _ _),
           (hPl_proj σ hσ).2.2.trans (le_max_left _ _)⟩
        coord_conv := hCyl_conv
        euler_semigroup := hE_semi
        euler_eigen := hE_eigen
        euler_comm := hE_comm
        euler_duhamel := by
          obtain ⟨T_pl, hT, hD⟩ := hE_duh
          exact ⟨T_pl,
            { zero := fun σ hσ => (hT σ hσ).1
              add := fun σ hσ => (hT σ hσ).2.1
              isometry := fun σ hσ => (hT σ hσ).2.2.1
              cont := fun σ hσ => (hT σ hσ).2.2.2.1
              flow := fun σ hσ => (hT σ hσ).2.2.2.2 }, hD⟩ }
  · intro σ hσ L hL
    have hL_ge_L₀ : L₀ ≤ L := hL.1
    have hL_pos : 0 ≤ L := zero_le_one.trans (hL₀_1.trans hL_ge_L₀)
    obtain ⟨h_grow_exp, h_compl_exp⟩ := hL₀_bd σ hσ L hL_ge_L₀
    have h_proj_id : (π_pl σ).comp (ι_pl σ) = ContinuousLinearMap.id ℝ E2 :=
      (hPl_proj σ hσ).1
    set θ : ℝ := lam.im * L / (1 + σ) ^ 2
    set r : ℝ := Real.exp (lam.re * L / (1 + σ) ^ 2)
    have hr_pos : 0 < r := Real.exp_pos _
    have h_eigen_L : (E_pl σ L).comp (ι_pl σ) = (ι_pl σ).comp (PartIIbF23Sub.rotScaleCLM r θ) :=
      hE_eigen σ hσ L hL_pos
    have h_a_eq : (π_pl σ).comp ((E_pl σ L).comp (ι_pl σ)) = PartIIbF23Sub.rotScaleCLM r θ := by
      rw [h_eigen_L, ← ContinuousLinearMap.comp_assoc, h_proj_id, ContinuousLinearMap.id_comp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨PartIIbF23Sub.rotScaleCLM r⁻¹ (-θ), ?_, ?_, ?_⟩
      · rw [h_a_eq]
        exact PartIIbF23Sub.rotScaleCLM_inv_mul hr_pos.ne' θ
      · rw [h_a_eq]
        exact PartIIbF23Sub.rotScaleCLM_mul_inv hr_pos.ne' θ
      · have hr_inv : r⁻¹ = Real.exp (-(lam.re * L / (1 + σ) ^ 2)) := by
          dsimp [r]
          rw [← Real.exp_neg]
        calc ‖PartIIbF23Sub.rotScaleCLM r⁻¹ (-θ)‖
            ≤ r⁻¹ := PartIIbF23Sub.norm_rotScaleCLM_le (inv_pos.mpr hr_pos).le (-θ)
          _ = Real.exp (-(lam.re * L / (1 + σ) ^ 2)) := hr_inv
          _ ≤ (1 / 4 : ℝ) * Real.exp (-b' * L) := h_grow_exp
    · set Q_σ : Xm m →L[ℝ] Xm m := ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)
      have hQ_norm : ‖Q_σ‖ ≤ 1 + M_pl * M_pl := by
        dsimp [Q_σ]
        calc ‖ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)‖
            ≤ ‖ContinuousLinearMap.id ℝ (Xm m)‖ + ‖(ι_pl σ).comp (π_pl σ)‖ := norm_sub_le _ _
          _ ≤ 1 + ‖ι_pl σ‖ * ‖π_pl σ‖ :=
              add_le_add ContinuousLinearMap.norm_id_le (ContinuousLinearMap.opNorm_comp_le _ _)
          _ ≤ 1 + M_pl * M_pl :=
              add_le_add le_rfl
                (mul_le_mul (hPl_proj σ hσ).2.1 (hPl_proj σ hσ).2.2
                  (norm_nonneg _) (zero_le_one.trans hM_pl_1))
      have h_sem_bd := hCompl_bd σ hσ L hL_pos
      calc ‖Q_σ.comp ((E_pl σ L).comp Q_σ)‖
          ≤ ‖Q_σ‖ * ‖(E_pl σ L).comp Q_σ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (1 + M_pl * M_pl) * (C_η * Real.exp ((a' / 2) * L)) :=
            mul_le_mul hQ_norm h_sem_bd (norm_nonneg _) (by positivity)
        _ = C_compl * Real.exp ((a' / 2) * L) := by dsimp [C_compl]; ring
        _ ≤ (1 / 4 : ℝ) * Real.exp (a' * L) := h_compl_exp
    · have h_comm := hE_comm σ hσ L hL_pos
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.comp_sub, h_comm,
        ← ContinuousLinearMap.comp_assoc (π_pl σ) ((ι_pl σ).comp (π_pl σ)) (E_pl σ L),
        ← ContinuousLinearMap.comp_assoc (π_pl σ) (ι_pl σ) (π_pl σ),
        h_proj_id, ContinuousLinearMap.id_comp, sub_self]
    · rw [h_eigen_L, ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_assoc (ι_pl σ) (π_pl σ)
          ((ι_pl σ).comp (PartIIbF23Sub.rotScaleCLM r θ)),
        ← ContinuousLinearMap.comp_assoc (π_pl σ) (ι_pl σ) (PartIIbF23Sub.rotScaleCLM r θ),
        h_proj_id, ContinuousLinearMap.id_comp, sub_self]

end UnforcedLeray.Short.IIb

end
