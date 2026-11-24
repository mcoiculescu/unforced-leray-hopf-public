import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# `PartII-b_S3_1_1_2_1`: Sub-module for `PartII-b:S3/1/1/2/1` (`BgFirstRadialDriftL4`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523, 2543-2562, and 2594-2610.

## Proved here (zero `sorry`)

1. **All-order coordinate-word reduction for `iteratedFDeriv` and `eLpNorm · 4`
   (`coordWord_length`, `coordWord_norm_prod`, `eLpNorm_dirSpatialJet_coordWord_le`,
   `norm_iteratedFDeriv_le_sum_coordWord`, `eLpNorm_iteratedFDeriv_le_sum_coordWord`)**:
   * Every coordinate direction word `PhaseDerivStepSub.coordWord α` (`α : Fin k → Fin 3`) has
     length `k` and unit direction-norm product `((coordWord α).map norm).prod = 1`.
   * Iterating `SmoothLeraySliceSub.norm_iteratedFDeriv_succ_le_sum_dirSpatialJet` along
     `PhaseDerivStepSub.coordWord_snoc` bounds `‖iteratedFDeriv ℝ k g y‖` pointwise and in `L⁴(ℝ³)`
     by the finite sum over `α : Fin k → Fin 3` of `dirSpatialJet g (coordWord α)`.
2. **All-order radial-drift commutator estimate in `L⁴(ℝ³)`
   (`eLpNorm_dirSpatialJet_spatialRadialDrift_coordWord_le`,
   `eLpNorm_iteratedFDeriv_spatialRadialDrift_le`,
   `exists_iteratedFDeriv_spatialRadialDrift_l4_of_coordJet`)**:
   * Combining `PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift`
     (`D_ws((y · ∇)F) = (y · ∇)(D_ws F) + |ws| • D_ws F`) with `eLpNorm_dirSpatialJet_coordWord_le`
     reduces the order-`k` `L⁴(ℝ³)` norm of `iteratedFDeriv ℝ k (spatialRadialDrift (U₀ τ))` to
     the order-`0` `L⁴(ℝ³)` norms of `spatialRadialDrift (dirSpatialJet (U₀ τ) (coordWord α))`
     plus `(3 : ℝ≥0∞) ^ k * k * eLpNorm (iteratedFDeriv ℝ k (U₀ τ)) 4 volume`.
3. **Background piece decomposition for `spatialRadialDrift ∘ dirSpatialJet`
   (`contDiff_infty_corr_of_bgField`, `dirSpatialJet_bgField_eq`,
   `spatialRadialDrift_dirSpatialJet_bgField_eq`,
   `eLpNorm_spatialRadialDrift_dirSpatialJet_bgField_le`)**:
   * Decomposes `spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)` into the sum of the
     radial drifts of the `p.raw`, `p.inlet i`, and `p.corr z` coordinate jets and bounds its
     `L⁴(ℝ³)` norm by the sum of the piece `L⁴(ℝ³)` norms.
4. **Inverse-square derivative decay to `L⁴(ℝ³)` radial-drift bound
   (`memLp_decay1`, `eLpNorm_le_of_decay`,
   `norm_spatialRadialDrift_dirSpatialJet_coordWord_le`,
   `eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay`)**:
   * Pointwise bound `‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) F y‖ * ‖y‖`.
   * If `‖iteratedFDeriv ℝ (k + 1) F y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`, then
     `‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖ ≤ C * (1 + ‖y‖)⁻¹` and hence
     `eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume ≤ ENNReal.ofReal (C * decayK)`.
5. **Atomic leaf definitions and conditional assembly of `BgFirstRadialDriftL4`
   (`BgCoordJetRadialDriftL4`, `RawAndInletCoordJetRadialDriftL4`, `CorrCoordJetRadialDriftL4`,
   `bgCoordJetRadialDriftL4_of_pieces`, `bgFirstRadialDriftL4_of`,
   `bgFirstRadialDriftL4_of_pieces`)**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

local instance fact_one_le_four_rad : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace RadialDriftL4Sub

open PhaseDerivStepSub SmoothLeraySliceSub ProjectedEvolutionSub

/-! ## 1. Coordinate-word properties and all-order `iteratedFDeriv` reduction -/

/-- Every coordinate direction word `coordWord α` (`α : Fin k → Fin 3`) has length `k`. -/
@[simp]
theorem coordWord_length {k : ℕ} (α : Fin k → Fin 3) :
    (coordWord α).length = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [coordWord_succ, List.length_append, ih, List.length_singleton]

/-- Every standard basis vector `coordinateVector j` (`j : Fin 3`) has unit norm in `Space`. -/
@[simp]
theorem norm_coordinateVector (j : Fin 3) :
    ‖coordinateVector j‖ = 1 := by
  change ‖(EuclideanSpace.single j (1 : ℝ) : Space)‖ = 1
  simp

/-- The product of the direction norms in `coordWord α` is `1`. -/
@[simp]
theorem coordWord_norm_prod {k : ℕ} (α : Fin k → Fin 3) :
    ((coordWord α).map norm).prod = 1 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [coordWord_succ, List.map_append, List.prod_append, ih, one_mul,
        List.map_singleton, List.prod_singleton, norm_coordinateVector]

/-- Pointwise bound `‖dirSpatialJet F (coordWord α) y‖ ≤ ‖iteratedFDeriv ℝ k F y‖` for any smooth
spatial field `F` and multi-index `α : Fin k → Fin 3`. -/
theorem norm_dirSpatialJet_coordWord_le {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    {k : ℕ} (α : Fin k → Fin 3) (y : Space) :
    ‖dirSpatialJet F (coordWord α) y‖ ≤ ‖iteratedFDeriv ℝ k F y‖ := by
  have h := JointSmoothSub.norm_dirSpatialJet_le hF (coordWord α) y
  rwa [coordWord_length, coordWord_norm_prod, mul_one] at h

/-- `L⁴(ℝ³)` bound on `dirSpatialJet F (coordWord α)` by `eLpNorm (iteratedFDeriv ℝ k F) 4 volume`. -/
theorem eLpNorm_dirSpatialJet_coordWord_le {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    {k : ℕ} (α : Fin k → Fin 3) :
    eLpNorm (dirSpatialJet F (coordWord α)) 4 volume ≤
      eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume := by
  have h := SmoothLeraySliceSub.eLpNorm_dirSpatialJet_le hF (coordWord α)
  rwa [coordWord_length, coordWord_norm_prod, ENNReal.ofReal_one, one_mul] at h

/-- Reindexing a sum over `Fin (k + 1) → Fin 3` by `Fin.snoc α j` (`α : Fin k → Fin 3`, `j : Fin 3`). -/
theorem sum_fin_succ_snoc {M : Type*} [AddCommMonoid M] (k : ℕ)
    (f : (Fin (k + 1) → Fin 3) → M) :
    (∑ β : Fin (k + 1) → Fin 3, f β) =
      ∑ j : Fin 3, ∑ α : Fin k → Fin 3, f (Fin.snoc α j) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin 3)) f).symm

/-- Pointwise bound on `‖iteratedFDeriv ℝ k g y‖` by the sum over all coordinate words
`coordWord α` (`α : Fin k → Fin 3`). -/
theorem norm_iteratedFDeriv_le_sum_coordWord {g : SpatialField} (hg : ContDiff ℝ ∞ g) :
    ∀ (k : ℕ) (y : Space),
      ‖iteratedFDeriv ℝ k g y‖ ≤
        ∑ α : Fin k → Fin 3, ‖dirSpatialJet g (coordWord α) y‖
  | 0, y => by
      rw [norm_iteratedFDeriv_zero, Fintype.sum_unique]
      rfl
  | k + 1, y => by
      have hstep := SmoothLeraySliceSub.norm_iteratedFDeriv_succ_le_sum_dirSpatialJet hg k y
      refine hstep.trans ?_
      rw [sum_fin_succ_snoc]
      refine Finset.sum_le_sum fun j _ => ?_
      have hgj : ContDiff ℝ ∞ (dirSpatialJet g [coordinateVector j]) :=
        JointSmoothSub.contDiff_infty_dirSpatialJet hg [coordinateVector j]
      have hih := norm_iteratedFDeriv_le_sum_coordWord hgj k y
      refine hih.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [HigherPhaseSub.dirSpatialJet_append g (coordWord α) [coordinateVector j],
        coordWord_snoc]

/-- `L⁴(ℝ³)` bound on `iteratedFDeriv ℝ k g` by the sum over all coordinate words `coordWord α`
(`α : Fin k → Fin 3`). -/
theorem eLpNorm_iteratedFDeriv_le_sum_coordWord {g : SpatialField} (hg : ContDiff ℝ ∞ g)
    (k : ℕ) :
    eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume ≤
      ∑ α : Fin k → Fin 3, eLpNorm (dirSpatialJet g (coordWord α)) 4 volume := by
  have hpt : ∀ y : Space,
      ‖iteratedFDeriv ℝ k g y‖ ≤
        ‖(∑ α : Fin k → Fin 3, fun y' => ‖dirSpatialJet g (coordWord α) y'‖) y‖ := by
    intro y
    rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact norm_iteratedFDeriv_le_sum_coordWord hg k y
  have hmeas : ∀ α ∈ (Finset.univ : Finset (Fin k → Fin 3)),
      AEStronglyMeasurable (fun y : Space => ‖dirSpatialJet g (coordWord α) y‖) volume := by
    intro α _
    exact (JointSmoothSub.contDiff_infty_dirSpatialJet hg
      (coordWord α)).continuous.norm.aestronglyMeasurable
  calc eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume
      ≤ eLpNorm (∑ α : Fin k → Fin 3, fun y => ‖dirSpatialJet g (coordWord α) y‖) 4 volume :=
        eLpNorm_mono hpt
    _ ≤ ∑ α : Fin k → Fin 3,
          eLpNorm (fun y => ‖dirSpatialJet g (coordWord α) y‖) 4 volume :=
        eLpNorm_sum_le hmeas (by norm_num)
    _ = ∑ α : Fin k → Fin 3, eLpNorm (dirSpatialJet g (coordWord α)) 4 volume := by
        simp_rw [eLpNorm_norm]

/-! ## 2. All-order radial-drift commutator estimate in `L⁴(ℝ³)` -/

/-- Pointwise commutator bound for `dirSpatialJet (spatialRadialDrift F) (coordWord α)`. -/
theorem norm_dirSpatialJet_spatialRadialDrift_coordWord_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3) (y : Space) :
    ‖dirSpatialJet (spatialRadialDrift F) (coordWord α) y‖ ≤
      ‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖ +
        (k : ℝ) * ‖iteratedFDeriv ℝ k F y‖ := by
  have hcomm := congrFun (PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift hF (coordWord α)) y
  rw [hcomm, coordWord_length, Pi.add_apply, Pi.smul_apply]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg k)]
  exact mul_le_mul_of_nonneg_left (norm_dirSpatialJet_coordWord_le hF α y) (Nat.cast_nonneg k)

/-- `L⁴(ℝ³)` commutator bound for `dirSpatialJet (spatialRadialDrift F) (coordWord α)`:
`eLpNorm (dirSpatialJet (spatialRadialDrift F) (coordWord α)) 4 volume ≤ eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume + ENNReal.ofReal k * eLpNorm (iteratedFDeriv ℝ k F) 4 volume`. -/
theorem eLpNorm_dirSpatialJet_spatialRadialDrift_coordWord_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3) :
    eLpNorm (dirSpatialJet (spatialRadialDrift F) (coordWord α)) 4 volume ≤
      eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume +
        ENNReal.ofReal (k : ℝ) * eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume := by
  let g₁ : Space → ℝ := fun y => ‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖
  let g₂ : Space → ℝ := fun y => ‖iteratedFDeriv ℝ k F y‖
  have hpt : ∀ y : Space,
      ‖dirSpatialJet (spatialRadialDrift F) (coordWord α) y‖ ≤ ‖(g₁ + (k : ℝ) • g₂) y‖ := by
    intro y
    have hnonneg : 0 ≤ g₁ y + (k : ℝ) * g₂ y :=
      add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _))
    change ‖dirSpatialJet (spatialRadialDrift F) (coordWord α) y‖ ≤ |g₁ y + (k : ℝ) * g₂ y|
    rw [abs_of_nonneg hnonneg]
    exact norm_dirSpatialJet_spatialRadialDrift_coordWord_le hF α y
  have hjet : ContDiff ℝ ∞ (dirSpatialJet F (coordWord α)) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF (coordWord α)
  have hg₁_meas : AEStronglyMeasurable g₁ volume :=
    (HigherPhaseSub.contDiff_infty_spatialRadialDrift hjet).continuous.norm.aestronglyMeasurable
  have hg₂_meas : AEStronglyMeasurable g₂ volume :=
    (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable
  calc eLpNorm (dirSpatialJet (spatialRadialDrift F) (coordWord α)) 4 volume
      ≤ eLpNorm (g₁ + (k : ℝ) • g₂) 4 volume := eLpNorm_mono hpt
    _ ≤ eLpNorm g₁ 4 volume + eLpNorm ((k : ℝ) • g₂) 4 volume :=
        eLpNorm_add_le hg₁_meas (hg₂_meas.const_smul (k : ℝ)) (by norm_num)
    _ = eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume +
          ENNReal.ofReal (k : ℝ) * eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg (Nat.cast_nonneg k)]
        simp only [g₁, g₂, eLpNorm_norm]

/-- All-order `L⁴(ℝ³)` bound on `iteratedFDeriv ℝ k (spatialRadialDrift F)` in terms of the
order-`0` radial drifts `spatialRadialDrift (dirSpatialJet F (coordWord α))` (`α : Fin k → Fin 3`)
and `eLpNorm (iteratedFDeriv ℝ k F) 4 volume`. -/
theorem eLpNorm_iteratedFDeriv_spatialRadialDrift_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    eLpNorm (fun y => iteratedFDeriv ℝ k (spatialRadialDrift F) y) 4 volume ≤
      (∑ α : Fin k → Fin 3,
        eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume) +
        (3 : ℝ≥0∞) ^ k * ENNReal.ofReal (k : ℝ) *
          eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume := by
  have hrad : ContDiff ℝ ∞ (spatialRadialDrift F) :=
    HigherPhaseSub.contDiff_infty_spatialRadialDrift hF
  calc eLpNorm (fun y => iteratedFDeriv ℝ k (spatialRadialDrift F) y) 4 volume
      ≤ ∑ α : Fin k → Fin 3,
          eLpNorm (dirSpatialJet (spatialRadialDrift F) (coordWord α)) 4 volume :=
        eLpNorm_iteratedFDeriv_le_sum_coordWord hrad k
    _ ≤ ∑ α : Fin k → Fin 3,
          (eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume +
            ENNReal.ofReal (k : ℝ) * eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume) :=
        Finset.sum_le_sum fun α _ =>
          eLpNorm_dirSpatialJet_spatialRadialDrift_coordWord_le hF α
    _ = (∑ α : Fin k → Fin 3,
          eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume) +
          (3 : ℝ≥0∞) ^ k * ENNReal.ofReal (k : ℝ) *
            eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

/-- If `U₀ ∈ IsUniformSmoothL4SliceFamily` and for every `k : ℕ` and `α : Fin k → Fin 3` the
order-`0` radial drift of `dirSpatialJet (U₀ τ) (coordWord α)` is uniformly bounded in `L⁴(ℝ³)`,
then for every `k : ℕ`, `iteratedFDeriv ℝ k (spatialRadialDrift (U₀ τ))` is uniformly bounded in
`L⁴(ℝ³)` across `τ : ℝ`. -/
theorem exists_iteratedFDeriv_spatialRadialDrift_l4_of_coordJet
    {U₀ : ℝ → SpatialField} (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hJet : ∀ (k : ℕ) (α : Fin k → Fin 3), ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (spatialRadialDrift (dirSpatialJet (U₀ τ) (coordWord α))) 4 volume ≤
        ENNReal.ofReal M) :
    ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (spatialRadialDrift (U₀ τ)) y) 4 volume ≤
        ENNReal.ofReal M := by
  intro k
  choose M_α hM_α using hJet k
  obtain ⟨M_k, hM_k⟩ := hU₀.l4_bounded k
  let M_α' : (Fin k → Fin 3) → ℝ := fun α => max (M_α α) 0
  let M_k' : ℝ := max M_k 0
  refine ⟨(∑ α : Fin k → Fin 3, M_α' α) + (3 : ℝ) ^ k * (k : ℝ) * M_k', ?_⟩
  intro τ
  have hF : ContDiff ℝ ∞ (U₀ τ) := HigherPhaseSub.sliceFamily_contDiff_infty hU₀ τ
  have h1 := eLpNorm_iteratedFDeriv_spatialRadialDrift_le hF k
  have hsum :
      (∑ α : Fin k → Fin 3,
        eLpNorm (spatialRadialDrift (dirSpatialJet (U₀ τ) (coordWord α))) 4 volume) ≤
        ENNReal.ofReal (∑ α : Fin k → Fin 3, M_α' α) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => le_max_right (M_α α) 0)]
    refine Finset.sum_le_sum fun α _ => ?_
    exact (hM_α α τ).trans (ENNReal.ofReal_le_ofReal (le_max_left (M_α α) 0))
  have hrem :
      (3 : ℝ≥0∞) ^ k * ENNReal.ofReal (k : ℝ) *
          eLpNorm (fun y => iteratedFDeriv ℝ k (U₀ τ) y) 4 volume ≤
        ENNReal.ofReal ((3 : ℝ) ^ k * (k : ℝ) * M_k') := by
    have hpow : (3 : ℝ≥0∞) ^ k = ENNReal.ofReal ((3 : ℝ) ^ k) := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [hpow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    exact (hM_k τ).trans (ENNReal.ofReal_le_ofReal (le_max_left M_k 0))
  have hadd_ofReal :
      ENNReal.ofReal (∑ α : Fin k → Fin 3, M_α' α) +
        ENNReal.ofReal ((3 : ℝ) ^ k * (k : ℝ) * M_k') =
      ENNReal.ofReal ((∑ α : Fin k → Fin 3, M_α' α) + (3 : ℝ) ^ k * (k : ℝ) * M_k') := by
    rw [← ENNReal.ofReal_add
      (Finset.sum_nonneg fun α _ => le_max_right (M_α α) 0)
      (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg k)) (le_max_right M_k 0))]
  exact h1.trans ((add_le_add hsum hrem).trans (le_of_eq hadd_ofReal))

/-! ## 3. Piece decomposition of `spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)` -/

/-- Since `p.corr z τ = bgField p z τ - (p.raw τ + ∑ i, p.coord z i • p.inlet i τ)`, `p.corr z τ` is
`C^∞` on `Space` whenever `bgField p z τ`, `p.raw τ`, and `p.inlet i τ` are `C^∞`. -/
theorem contDiff_infty_corr_of_bgField (p : Params) (z : p.Z) (τ : ℝ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ))
    (hBg : ContDiff ℝ ∞ (bgField p z τ)) :
    ContDiff ℝ ∞ (p.corr z τ) := by
  have heq : p.corr z τ =
      bgField p z τ - (p.raw τ + fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) := by
    funext y
    simp [bgField]
  rw [heq]
  exact hBg.sub (hRaw.add (ContDiff.sum fun i _ => (hInlet i).const_smul (p.coord z i)))

/-- Piece decomposition of `dirSpatialJet (bgField p z τ) ws`. -/
theorem dirSpatialJet_bgField_eq (p : Params) (z : p.Z) (τ : ℝ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) :
    dirSpatialJet (bgField p z τ) ws =
      dirSpatialJet (p.raw τ) ws +
        (fun y => ∑ i : Fin 2, p.coord z i • dirSpatialJet (p.inlet i τ) ws y) +
        dirSpatialJet (p.corr z τ) ws := by
  let sumIn : SpatialField := fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y
  have hBgEq : bgField p z τ = (p.raw τ + sumIn) + p.corr z τ := by
    funext y
    rfl
  have hSumSmooth : ContDiff ℝ ∞ sumIn :=
    ContDiff.sum fun i _ => (hInlet i).const_smul (p.coord z i)
  have hRawSumSmooth : ContDiff ℝ ∞ (p.raw τ + sumIn) := hRaw.add hSumSmooth
  rw [hBgEq, HigherPhaseSub.dirSpatialJet_add hRawSumSmooth hCorr ws,
    HigherPhaseSub.dirSpatialJet_add hRaw hSumSmooth ws]
  congr 2
  rw [HigherPhaseSub.dirSpatialJet_sum Finset.univ
    (F := fun i y => p.coord z i • p.inlet i τ y)
    (fun i _ => (hInlet i).const_smul (p.coord z i)) ws]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrFun (HigherPhaseSub.dirSpatialJet_smul (p.coord z i) (hInlet i) ws) y

/-- Piece decomposition of `spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)`. -/
theorem spatialRadialDrift_dirSpatialJet_bgField_eq (p : Params) (z : p.Z) (τ : ℝ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) :
    spatialRadialDrift (dirSpatialJet (bgField p z τ) ws) =
      spatialRadialDrift (dirSpatialJet (p.raw τ) ws) +
        (fun y => ∑ i : Fin 2,
          p.coord z i • spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws) y) +
        spatialRadialDrift (dirSpatialJet (p.corr z τ) ws) := by
  let sumInJet : SpatialField := fun y => ∑ i : Fin 2, p.coord z i • dirSpatialJet (p.inlet i τ) ws y
  have hRawJet : ContDiff ℝ ∞ (dirSpatialJet (p.raw τ) ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hRaw ws
  have hInJet : ∀ i : Fin 2, ContDiff ℝ ∞ (dirSpatialJet (p.inlet i τ) ws) :=
    fun i => JointSmoothSub.contDiff_infty_dirSpatialJet (hInlet i) ws
  have hSumJet : ContDiff ℝ ∞ sumInJet :=
    ContDiff.sum fun i _ => (hInJet i).const_smul (p.coord z i)
  have hRawSumJet : ContDiff ℝ ∞ (dirSpatialJet (p.raw τ) ws + sumInJet) :=
    hRawJet.add hSumJet
  have hCorrJet : ContDiff ℝ ∞ (dirSpatialJet (p.corr z τ) ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hCorr ws
  have hJetEq : dirSpatialJet (bgField p z τ) ws =
      (dirSpatialJet (p.raw τ) ws + sumInJet) + dirSpatialJet (p.corr z τ) ws :=
    dirSpatialJet_bgField_eq p z τ hRaw hInlet hCorr ws
  rw [hJetEq,
    ProjectedEvolutionSub.spatialRadialDrift_add hRawSumJet hCorrJet,
    ProjectedEvolutionSub.spatialRadialDrift_add hRawJet hSumJet]
  congr 2
  rw [ProjectedEvolutionSub.spatialRadialDrift_sum Finset.univ
    (F := fun i y => p.coord z i • dirSpatialJet (p.inlet i τ) ws y)
    (fun i _ => (hInJet i).const_smul (p.coord z i))]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrFun (ProjectedEvolutionSub.spatialRadialDrift_smul (p.coord z i) (hInJet i)) y

/-- Pointwise triangle inequality for `spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)`
across the raw, inlet, and correction pieces. -/
theorem norm_spatialRadialDrift_dirSpatialJet_bgField_le (p : Params) (z : p.Z) (τ : ℝ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) (y : Space) :
    ‖spatialRadialDrift (dirSpatialJet (bgField p z τ) ws) y‖ ≤
      ‖spatialRadialDrift (dirSpatialJet (p.raw τ) ws) y‖ +
        (∑ i : Fin 2, |p.coord z i| * ‖spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws) y‖) +
        ‖spatialRadialDrift (dirSpatialJet (p.corr z τ) ws) y‖ := by
  have hEq := congrFun (spatialRadialDrift_dirSpatialJet_bgField_eq p z τ hRaw hInlet hCorr ws) y
  rw [hEq, Pi.add_apply, Pi.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]

/-- `L⁴(ℝ³)` triangle inequality for `spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)` across
the raw, inlet, and correction pieces. -/
theorem eLpNorm_spatialRadialDrift_dirSpatialJet_bgField_le (p : Params) (z : p.Z) (τ : ℝ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) :
    eLpNorm (spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)) 4 volume ≤
      eLpNorm (spatialRadialDrift (dirSpatialJet (p.raw τ) ws)) 4 volume +
        (∑ i : Fin 2, ENNReal.ofReal |p.coord z i| *
          eLpNorm (spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws)) 4 volume) +
        eLpNorm (spatialRadialDrift (dirSpatialJet (p.corr z τ) ws)) 4 volume := by
  let gRaw : Space → ℝ := fun y => ‖spatialRadialDrift (dirSpatialJet (p.raw τ) ws) y‖
  let gIn : Fin 2 → Space → ℝ :=
    fun i y => ‖spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws) y‖
  let gSum : Space → ℝ := ∑ i : Fin 2, |p.coord z i| • gIn i
  let gCorr : Space → ℝ := fun y => ‖spatialRadialDrift (dirSpatialJet (p.corr z τ) ws) y‖
  have hpt : ∀ y : Space,
      ‖spatialRadialDrift (dirSpatialJet (bgField p z τ) ws) y‖ ≤
        ‖((gRaw + gSum) + gCorr) y‖ := by
    intro y
    have hSumNonneg : 0 ≤ ∑ i : Fin 2, |p.coord z i| * gIn i y :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hTotNonneg : 0 ≤ (gRaw y + ∑ i : Fin 2, |p.coord z i| * gIn i y) + gCorr y :=
      add_nonneg (add_nonneg (norm_nonneg _) hSumNonneg) (norm_nonneg _)
    have hval : ((gRaw + gSum) + gCorr) y =
        (gRaw y + ∑ i : Fin 2, |p.coord z i| * gIn i y) + gCorr y := by
      simp [gSum, smul_eq_mul]
    rw [hval, Real.norm_of_nonneg hTotNonneg]
    exact norm_spatialRadialDrift_dirSpatialJet_bgField_le p z τ hRaw hInlet hCorr ws y
  have hRawMeas : AEStronglyMeasurable gRaw volume :=
    (HigherPhaseSub.contDiff_infty_spatialRadialDrift
      (JointSmoothSub.contDiff_infty_dirSpatialJet hRaw ws)).continuous.norm.aestronglyMeasurable
  have hInMeas : ∀ i : Fin 2, AEStronglyMeasurable (gIn i) volume :=
    fun i => (HigherPhaseSub.contDiff_infty_spatialRadialDrift
      (JointSmoothSub.contDiff_infty_dirSpatialJet (hInlet i) ws)).continuous.norm.aestronglyMeasurable
  have hSumMeas : AEStronglyMeasurable gSum volume :=
    Finset.aestronglyMeasurable_sum Finset.univ fun i _ => (hInMeas i).const_smul |p.coord z i|
  have hCorrMeas : AEStronglyMeasurable gCorr volume :=
    (HigherPhaseSub.contDiff_infty_spatialRadialDrift
      (JointSmoothSub.contDiff_infty_dirSpatialJet hCorr ws)).continuous.norm.aestronglyMeasurable
  have htri1 := eLpNorm_add_le (hRawMeas.add hSumMeas) hCorrMeas (by norm_num) (p := (4 : ℝ≥0∞))
  have htri2 := eLpNorm_add_le hRawMeas hSumMeas (by norm_num) (p := (4 : ℝ≥0∞))
  have htri_sum :
      eLpNorm gSum 4 volume ≤
        ∑ i : Fin 2, ENNReal.ofReal |p.coord z i| *
          eLpNorm (spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws)) 4 volume := by
    refine (eLpNorm_sum_le (fun i _ => (hInMeas i).const_smul |p.coord z i|) (by norm_num)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (abs_nonneg _)]
    simp [gIn, eLpNorm_norm]
  calc eLpNorm (spatialRadialDrift (dirSpatialJet (bgField p z τ) ws)) 4 volume
      ≤ eLpNorm ((gRaw + gSum) + gCorr) 4 volume := eLpNorm_mono hpt
    _ ≤ (eLpNorm gRaw 4 volume + eLpNorm gSum 4 volume) + eLpNorm gCorr 4 volume :=
        htri1.trans (add_le_add htri2 le_rfl)
    _ ≤ (eLpNorm (spatialRadialDrift (dirSpatialJet (p.raw τ) ws)) 4 volume +
          ∑ i : Fin 2, ENNReal.ofReal |p.coord z i| *
            eLpNorm (spatialRadialDrift (dirSpatialJet (p.inlet i τ) ws)) 4 volume) +
        eLpNorm (spatialRadialDrift (dirSpatialJet (p.corr z τ) ws)) 4 volume := by
        simp only [gRaw, gCorr, eLpNorm_norm]
        exact add_le_add (add_le_add le_rfl htri_sum) le_rfl

/-! ## 4. Inverse-square derivative decay to `L⁴(ℝ³)` radial-drift bound -/

/-- The model decay profile `(1 + ‖y‖)⁻¹` on `Space = ℝ³`. -/
def decay1 : Space → ℝ := fun y => (1 + ‖y‖)⁻¹

/-- `decay1 = (1 + ‖·‖)⁻¹` belongs to `L⁴(ℝ³)` since `3 < 4`. -/
theorem memLp_decay1 : MemLp decay1 4 (volume : Measure Space) := by
  have hm : AEStronglyMeasurable decay1 (volume : Measure Space) :=
    Measurable.aestronglyMeasurable (by unfold decay1; fun_prop)
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) (volume : Measure Space) := by
    apply integrable_one_add_norm
    simp [finrank_euclideanSpace]
    norm_num
  have h1 : MemLp (fun x : Space => ‖decay1 x‖ ^ (4 : ℝ≥0∞).toReal) (4 / 4)
      (volume : Measure Space) := by
    rw [ENNReal.div_self (by norm_num) (by norm_num), memLp_one_iff_integrable]
    refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
    have hp : 0 < 1 + ‖y‖ := by positivity
    simp only [decay1, norm_inv, Real.norm_eq_abs, abs_of_pos hp, ENNReal.toReal_ofNat]
    rw [Real.rpow_neg hp.le, Real.inv_rpow hp.le]
  exact (memLp_norm_rpow_iff hm (by norm_num) (by norm_num)).mp h1

/-- Universal constant `‖(1 + ‖·‖)⁻¹‖_{L⁴(ℝ³)}`. -/
def decayK : ℝ := (eLpNorm decay1 4 (volume : Measure Space)).toReal

/-- Nonnegativity of `decayK`. -/
theorem decayK_nonneg : 0 ≤ decayK := ENNReal.toReal_nonneg

/-- Any field `G : Space → V` satisfying `‖G y‖ ≤ C * (1 + ‖y‖)⁻¹` has `L⁴(ℝ³)` norm at most
`C * decayK`. -/
theorem eLpNorm_le_of_decay {V : Type*} [NormedAddCommGroup V] (G : Space → V)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, ‖G y‖ ≤ C * (1 + ‖y‖)⁻¹) :
    eLpNorm G 4 (volume : Measure Space) ≤ ENNReal.ofReal (C * decayK) := by
  have hle : eLpNorm G 4 volume ≤ eLpNorm (C • decay1) 4 volume := by
    apply eLpNorm_mono
    intro y
    simp only [Pi.smul_apply, smul_eq_mul, decay1, norm_mul, Real.norm_eq_abs, norm_inv]
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [abs_of_pos hp, abs_of_nonneg hC]
    exact h y
  refine hle.trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hC, decayK,
    ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal memLp_decay1.eLpNorm_lt_top.ne]

/-- Pointwise bound `‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) F y‖ * ‖y‖`. -/
theorem norm_spatialRadialDrift_dirSpatialJet_coordWord_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3) (y : Space) :
    ‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) F y‖ * ‖y‖ := by
  have heq : spatialRadialDrift (dirSpatialJet F (coordWord α)) y =
      dirSpatialJet F ([y] ++ coordWord α) y := by
    rw [← HigherPhaseSub.dirSpatialJet_append F [y] (coordWord α)]
    rfl
  rw [heq]
  have h := JointSmoothSub.norm_dirSpatialJet_le hF ([y] ++ coordWord α) y
  rwa [List.length_append, List.length_singleton, coordWord_length, add_comm 1 k,
    List.map_append, List.prod_append, coordWord_norm_prod, mul_one,
    List.map_singleton, List.prod_singleton] at h

/-- If `F` is smooth and its `(k + 1)`-st iterated derivative satisfies the inverse-square decay
`‖iteratedFDeriv ℝ (k + 1) F y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹`, then
`eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume ≤ ENNReal.ofReal (C * decayK)`. -/
theorem eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3)
    {C : ℝ} (hC : 0 ≤ C)
    (hDecay : ∀ y : Space, ‖iteratedFDeriv ℝ (k + 1) F y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹) :
    eLpNorm (spatialRadialDrift (dirSpatialJet F (coordWord α))) 4 volume ≤
      ENNReal.ofReal (C * decayK) := by
  refine eLpNorm_le_of_decay _ hC fun y => ?_
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hy : ‖y‖ ≤ 1 + ‖y‖ := by linarith
  calc ‖spatialRadialDrift (dirSpatialJet F (coordWord α)) y‖
      ≤ ‖iteratedFDeriv ℝ (k + 1) F y‖ * ‖y‖ :=
        norm_spatialRadialDrift_dirSpatialJet_coordWord_le hF α y
    _ ≤ (C * ((1 + ‖y‖) ^ 2)⁻¹) * (1 + ‖y‖) := by
        gcongr
        exact hDecay y
    _ = C * (1 + ‖y‖)⁻¹ := by
        rw [sq, mul_inv, mul_assoc, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]

end RadialDriftL4Sub

/-! ## 5. Atomic leaf definitions and conditional assembly of `BgFirstRadialDriftL4` -/

/-- **Order-`0` radial-drift `L⁴(ℝ³)` bound on coordinate spatial jets of `bgField p z`**:
under the hypotheses of `BgFirstRadialDriftL4`, for every multi-index `α : Fin k → Fin 3`,
`spatialRadialDrift (dirSpatialJet (bgField p z τ) (PhaseDerivStepSub.coordWord α))` is bounded in
`L⁴(ℝ³)` uniformly across `τ : ℝ`. -/
def BgCoordJetRadialDriftL4 : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ (k : ℕ) (α : Fin k → Fin 3), ∃ M : ℝ, ∀ τ : ℝ,
        eLpNorm (spatialRadialDrift
          (dirSpatialJet (bgField p z τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
          ENNReal.ofReal M

/-- **Leaf 1 (`PartII-b:S3/1/1/2/1/1`, `RawAndInletCoordJetRadialDriftL4`)**
(SP 2543-2559, 2594-2610: from the all-age inverse-distance bounds `|D^{k+1} V(τ, y)| ≲ ⟨y⟩^{-2-k}`
for `p.raw` and `p.inlet i`, `|(y · ∇) D^α V(τ, y)| ≲ ⟨y⟩^{-1-k} ∈ L⁴(ℝ³)` uniformly in `τ`,
supplied via `RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_le_of_inv_sq_decay`).
Composed by task `PartII-b:S3/1/1/2/1` via `bgFirstRadialDriftL4_of_pieces`. -/
def RawAndInletCoordJetRadialDriftL4 : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ (k : ℕ) (α : Fin k → Fin 3), ∃ M_V : ℝ, 0 ≤ M_V ∧ ∀ τ : ℝ,
        eLpNorm (spatialRadialDrift
          (dirSpatialJet (p.raw τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
          ENNReal.ofReal M_V ∧
        ∀ i : Fin 2,
          eLpNorm (spatialRadialDrift
            (dirSpatialJet (p.inlet i τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
            ENNReal.ofReal M_V

/-- **Leaf 2 (`PartII-b:S3/1/1/2/1/2`, `CorrCoordJetRadialDriftL4`)**
(SP 2519-2523, 2552-2562: for a solution `z` of `ProjectedEquation p z` with all iterated spatial
derivatives `g α` in the maximal graph `B0411.D p.period p.ν q0E`, the radial drift of each
coordinate jet of `p.corr z τ` is uniformly bounded in `L⁴(ℝ³)` across `τ : ℝ`).
Composed by task `PartII-b:S3/1/1/2/1` via `bgFirstRadialDriftL4_of_pieces`. -/
def CorrCoordJetRadialDriftL4 : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ (k : ℕ) (α : Fin k → Fin 3), ∃ M_w : ℝ, 0 ≤ M_w ∧ ∀ τ : ℝ,
        eLpNorm (spatialRadialDrift
          (dirSpatialJet (p.corr z τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
          ENNReal.ofReal M_w

/-- Assembly of `BgCoordJetRadialDriftL4` from `RawAndInletCoordJetRadialDriftL4` and
`CorrCoordJetRadialDriftL4` via `RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_bgField_le`. -/
theorem bgCoordJetRadialDriftL4_of_pieces
    (hV : RawAndInletCoordJetRadialDriftL4)
    (hW : CorrCoordJetRadialDriftL4) :
    BgCoordJetRadialDriftL4 := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hV'⟩ := hV Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₂, hν₂, hW'⟩ := hW Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRaw hInlet k α
  obtain ⟨M_V, hMV0, hMV⟩ :=
    hV' p d hReg (hν.trans (min_le_left _ _)) hAge hMode hRawCD hInCD hRaw hInlet k α
  obtain ⟨M_w, hMw0, hMw⟩ :=
    hW' p d hReg (hν.trans (min_le_right _ _)) hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRaw hInlet k α
  refine ⟨M_V + (∑ i : Fin 2, |p.coord z i| * M_V) + M_w, ?_⟩
  intro τ
  have hRawSlice : ContDiff ℝ ∞ (p.raw τ) :=
    PhaseDerivStepSub.contDiff_slice_of_joint (F := p.raw) hRawCD τ
  have hInSlice : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ) :=
    fun i => PhaseDerivStepSub.contDiff_slice_of_joint (F := p.inlet i) (hInCD i) τ
  have hBgSlice : ContDiff ℝ ∞ (bgField p z τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty hBg τ
  have hCorrSlice : ContDiff ℝ ∞ (p.corr z τ) :=
    RadialDriftL4Sub.contDiff_infty_corr_of_bgField p z τ hRawSlice hInSlice hBgSlice
  have htri := RadialDriftL4Sub.eLpNorm_spatialRadialDrift_dirSpatialJet_bgField_le
    p z τ hRawSlice hInSlice hCorrSlice (PhaseDerivStepSub.coordWord α)
  have hsum :
      (∑ i : Fin 2, ENNReal.ofReal |p.coord z i| *
        eLpNorm (spatialRadialDrift
          (dirSpatialJet (p.inlet i τ) (PhaseDerivStepSub.coordWord α))) 4 volume) ≤
        ENNReal.ofReal (∑ i : Fin 2, |p.coord z i| * M_V) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (abs_nonneg _) hMV0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((hMV τ).2 i) zero_le
  have htot := add_le_add (add_le_add (hMV τ).1 hsum) (hMw τ)
  have hsum0 : 0 ≤ ∑ i : Fin 2, |p.coord z i| * M_V :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) hMV0
  rw [← ENNReal.ofReal_add hMV0 hsum0, ← ENNReal.ofReal_add (add_nonneg hMV0 hsum0) hMw0] at htot
  exact htri.trans htot

/-- Complete reduction of `BgFirstRadialDriftL4` (`PartII-b:S3/1/1/2/1`) to the order-`0`
coordinate-jet radial-drift bound `BgCoordJetRadialDriftL4` via the all-order commutator reduction
`RadialDriftL4Sub.exists_iteratedFDeriv_spatialRadialDrift_l4_of_coordJet`. -/
theorem bgFirstRadialDriftL4_of
    (hJet : BgCoordJetRadialDriftL4) :
    BgFirstRadialDriftL4 := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, hJ⟩ := hJet Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRaw hInlet
  exact RadialDriftL4Sub.exists_iteratedFDeriv_spatialRadialDrift_l4_of_coordJet hBg
    (hJ p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRaw hInlet)

/-- Assembly of `BgFirstRadialDriftL4` (`PartII-b:S3/1/1/2/1`) from the raw/inlet and correction
coordinate-jet radial-drift `L⁴(ℝ³)` bounds. -/
theorem bgFirstRadialDriftL4_of_pieces
    (hV : RawAndInletCoordJetRadialDriftL4)
    (hW : CorrCoordJetRadialDriftL4) :
    BgFirstRadialDriftL4 :=
  bgFirstRadialDriftL4_of (bgCoordJetRadialDriftL4_of_pieces hV hW)

end UnforcedLeray.Short.IIb

end
