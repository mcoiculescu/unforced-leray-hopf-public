import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1
import UnforcedLeray.Analysis.SobolevEmbedding.Smooth

/-!
# `PartII-b:S3/1/1` decomposition (`Sub/PartII-b_S3_1_1.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. Slice regularity and piece bounds for `bgField p z`:
   - `bgField_slice_contDiff`, `bgField_slice_contDiff_infty`, `bgField_l4_bounded`,
     `corr_iteratedFDeriv_bounded`, `bgField_norm_bounded`,
     `isUniformSmoothL4SliceFamily_bgField_of_iteratedFDeriv_bounded`.
2. Multilinear coordinate reduction of 3D Morrey (`FirstOrderPhaseDerivSub`):
   - `FirstOrderPhaseDerivSub.opNorm_le_sum_coordinates`: operator norm of any continuous linear
     map `Space →L[ℝ] E` is bounded by the sum over the 3 coordinate vectors `coordinateVector i`;
   - `FirstOrderPhaseDerivSub.exists_finite_coord_bound`: for every `k : ℕ`, there is a finite
     index type `ι` of `k`-tuples of unit vectors in `Space` such that for every continuous
     `k`-multilinear map `A`, `‖A‖ ≤ ∑ a : ι, ‖A (v a)‖` (by induction on `k` via
     `ContinuousMultilinearMap.curryLeft`);
   - `smoothMorreyL4Bound_of_field`: reduces the all-order `SmoothMorreyL4Bound` on
     `iteratedFDeriv ℝ k F` for all `k : ℕ` to the single first-order (`k = 0`) vector-field Morrey
     inequality `SmoothMorreyL4FieldBound` (`W^{1,4}(ℝ³) ↪ L^∞(ℝ³)` on `SpatialField`);
   - `isUniformSmoothL4SliceFamily_of_morreyL4` and
     `isUniformSmoothL4SliceFamily_bgField_of_morreyL4`: upgrades `W^{k,4}(ℝ³)` bounds on any
     slice-smooth family `V : ℝ → SpatialField` to `IsUniformSmoothL4SliceFamily V`.
3. `bgFirstOrderPhaseDeriv_of`: conditional assembly of `BgFirstOrderPhaseDeriv` (`PartII-b:S3/1/1`)
   from `SmoothMorreyL4FieldBound` (`PartII-b:S3/1/1/1`) and `BgFirstPhaseDerivStep`
   (`PartII-b:S3/1/1/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint

/-! ## 1. Slice regularity and piece bounds for `bgField p z` -/

/-- From the slice regularity package `hSlice`, every spatial slice `bgField p z τ` is `C^k` on
`Space` for every `k : ℕ`. -/
theorem bgField_slice_contDiff (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) :
    ∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (bgField p z τ) := by
  intro k τ
  obtain ⟨M, hM⟩ := hSlice k
  exact (hM τ).1

/-- From the slice regularity package `hSlice`, every spatial slice `bgField p z τ` is `C^∞` on
`Space`. -/
theorem bgField_slice_contDiff_infty (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) :
    ∀ τ : ℝ, ContDiff ℝ ∞ (bgField p z τ) := by
  intro τ
  exact contDiff_infty.mpr fun k => bgField_slice_contDiff p z hSlice k τ

/-- From the slice regularity package `hSlice`, every spatial derivative order `k` of
`bgField p z τ` is bounded in `L^4(ℝ³)` uniformly in `τ`. -/
theorem bgField_l4_bounded (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) :
    ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M := by
  intro k
  obtain ⟨M, hM⟩ := hSlice k
  exact ⟨M, fun τ => (hM τ).2.2⟩

/-- From `hSlice`, every spatial derivative order `k` of `p.corr z τ` is bounded in `L^∞(ℝ³)`
uniformly in `(τ, y)`. -/
theorem corr_iteratedFDeriv_bounded (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) :
    ∀ k : ℕ, ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M := by
  intro k
  obtain ⟨M, hM⟩ := hSlice k
  exact ⟨M, fun τ y => (hM τ).2.1 y⟩

/-- Pointwise `L^∞` bound on `bgField p z τ y` uniformly in `(τ, y)` from `hSlice`, `hRaw`, and
`hInlet`. -/
theorem bgField_norm_bounded (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M)
    (hRaw : Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ))
    (hInlet : ∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
      ∀ τ, IsSolenoidal (p.inlet i τ)) :
    ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖bgField p z τ y‖ ≤ M := by
  obtain ⟨Craw, hCraw⟩ := hRaw.1.bounded
  obtain ⟨C0, hC0⟩ := (hInlet 0).1.bounded
  obtain ⟨C1, hC1⟩ := (hInlet 1).1.bounded
  obtain ⟨M0, hM0⟩ := hSlice 0
  refine ⟨Craw + (|p.coord z 0| * C0 + |p.coord z 1| * C1) + M0, fun τ y => ?_⟩
  have hcorr : ‖p.corr z τ y‖ ≤ M0 := by
    have h := (hM0 τ).2.1 y
    rwa [norm_iteratedFDeriv_zero] at h
  have hraw : ‖p.raw τ y‖ ≤ Craw := (hCraw τ y).1
  have hin0 : ‖p.coord z 0 • p.inlet 0 τ y‖ ≤ |p.coord z 0| * C0 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hC0 τ y).1) (abs_nonneg _)
  have hin1 : ‖p.coord z 1 • p.inlet 1 τ y‖ ≤ |p.coord z 1| * C1 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hC1 τ y).1) (abs_nonneg _)
  dsimp [bgField]
  rw [Fin.sum_univ_two]
  have h1 := norm_add_le
    (p.raw τ y + (p.coord z 0 • p.inlet 0 τ y + p.coord z 1 • p.inlet 1 τ y))
    (p.corr z τ y)
  have h2 := norm_add_le (p.raw τ y)
    (p.coord z 0 • p.inlet 0 τ y + p.coord z 1 • p.inlet 1 τ y)
  have h3 := norm_add_le (p.coord z 0 • p.inlet 0 τ y) (p.coord z 1 • p.inlet 1 τ y)
  linarith

/-- Assembles `IsUniformSmoothL4SliceFamily (bgField p z)` from `hSlice` and uniform pointwise
bounds on `iteratedFDeriv ℝ k (bgField p z τ)`. -/
theorem isUniformSmoothL4SliceFamily_bgField_of_iteratedFDeriv_bounded (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M)
    (hBdd : ∀ k : ℕ, ∃ M : ℝ, ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ k (bgField p z τ) y‖ ≤ M) :
    IsUniformSmoothL4SliceFamily (bgField p z) where
  slice_contDiff := bgField_slice_contDiff p z hSlice
  iteratedFDeriv_bounded := hBdd
  l4_bounded := bgField_l4_bounded p z hSlice

/-! ## 2. Multilinear coordinate reduction of 3D Morrey (`W^{1,4}(ℝ³) ↪ L^∞(ℝ³)`) -/

/-- **`PartII-b:S3/1/1/1` (`SmoothMorreyL4FieldBound`)**
(`the November 2 reference manuscript`,
lines 2557-2562: 3D Morrey/Sobolev embedding `W^{1,4}(ℝ³) ↪ L^∞(ℝ³)` on smooth spatial vector
fields): there exists a universal constant `C ≥ 0` such that for every smooth spatial vector field
`F : SpatialField` (`ContDiff ℝ ∞ F`) and bounds `M₀, M₁ ≥ 0` with
`eLpNorm F 4 volume ≤ ENNReal.ofReal M₀` and `eLpNorm (fderiv ℝ F) 4 volume ≤ ENNReal.ofReal M₁`,
at every point `y : Space`, `‖F y‖ ≤ C * (M₀ + M₁)`.
Composed by `smoothMorreyL4Bound_of_field` and `bgFirstOrderPhaseDeriv_of` in task
`PartII-b:S3/1/1`. -/
def SmoothMorreyL4FieldBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SpatialField, ContDiff ℝ ∞ F →
    ∀ M₀ M₁ : ℝ, 0 ≤ M₀ → 0 ≤ M₁ →
      eLpNorm F 4 volume ≤ ENNReal.ofReal M₀ →
      eLpNorm (fderiv ℝ F) 4 volume ≤ ENNReal.ofReal M₁ →
      ∀ y : Space, ‖F y‖ ≤ C * (M₀ + M₁)

/-- All-order 3D Morrey/Sobolev `W^{1,4}(ℝ³) ↪ L^∞(ℝ³)` inequality on smooth spatial fields: for
every derivative order `k : ℕ`, `‖iteratedFDeriv ℝ k F y‖` is controlled by the `L^4` norms of
`iteratedFDeriv ℝ k F` and `iteratedFDeriv ℝ (k + 1) F`. Proved below in
`smoothMorreyL4Bound_of_field` from `SmoothMorreyL4FieldBound`. -/
def SmoothMorreyL4Bound : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SpatialField, ContDiff ℝ ∞ F →
    ∀ M₀ M₁ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k F y) 4 volume ≤ ENNReal.ofReal M₀ →
      eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) F y) 4 volume ≤ ENNReal.ofReal M₁ →
      ∀ y : Space, ‖iteratedFDeriv ℝ k F y‖ ≤ C * (max M₀ 0 + max M₁ 0)

namespace FirstOrderPhaseDerivSub

/-- Operator norm of any continuous linear map `Space →L[ℝ] E` is bounded by the sum of its norms
on the three standard basis vectors `coordinateVector i`. -/
theorem opNorm_le_sum_coordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (coordinateVector i)‖ := by
  have hrepr (v : Space) : ∑ i : Fin 3, v i • coordinateVector i = v := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  calc
    ‖A v‖ = ‖A (∑ i : Fin 3, v i • coordinateVector i)‖ := by rw [hrepr]
    _ = ‖∑ i : Fin 3, v i • A (coordinateVector i)‖ := by simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • A (coordinateVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (coordinateVector i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (coordinateVector i)‖) * ‖v‖ := by
      rw [← Finset.mul_sum, mul_comm]

theorem norm_coordinateVector_le_one (i : Fin 3) : ‖coordinateVector i‖ ≤ 1 := by
  unfold coordinateVector
  simp

/-- For every `k : ℕ`, there is a finite family `v : ι → Fin k → Space` of tuples of vectors of
norm `≤ 1` such that for any normed space `E` and any continuous `k`-multilinear map
`A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) E`, `‖A‖ ≤ ∑ a : ι, ‖A (v a)‖`. -/
theorem exists_finite_coord_bound (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → Fin k → Space),
      (∀ (a : ι) (j : Fin k), ‖v a j‖ ≤ 1) ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) E),
        ‖A‖ ≤ ∑ a : ι, ‖A (v a)‖ := by
  induction k with
  | zero =>
      refine ⟨Unit, inferInstance, fun _ _ => 0, fun _ j => Fin.elim0 j, ?_⟩
      intro E _ _ A
      rw [Fintype.sum_unique]
      refine A.opNorm_le_bound (norm_nonneg (A 0)) fun m => ?_
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      simp
  | succ k ih =>
      obtain ⟨ι, hι, v, hv1, hAb⟩ := ih
      let _ : Fintype ι := hι
      refine ⟨Fin 3 × ι, inferInstance,
        fun p => Fin.cons (coordinateVector p.1) (v p.2), ?_, ?_⟩
      · intro p j
        refine Fin.cases ?_ ?_ j
        · simpa using norm_coordinateVector_le_one p.1
        · intro m
          simpa using hv1 p.2 m
      · intro E _ _ A
        rw [← A.curryLeft_norm]
        calc ‖A.curryLeft‖
            ≤ ∑ i : Fin 3, ‖A.curryLeft (coordinateVector i)‖ :=
              opNorm_le_sum_coordinates A.curryLeft
          _ ≤ ∑ i : Fin 3, ∑ a : ι, ‖A.curryLeft (coordinateVector i) (v a)‖ :=
              Finset.sum_le_sum fun i _ => hAb (A.curryLeft (coordinateVector i))
          _ = ∑ p : Fin 3 × ι, ‖A (Fin.cons (coordinateVector p.1) (v p.2))‖ := by
              rw [Fintype.sum_prod_type]
              rfl

/-- Evaluation of a continuous `k`-multilinear map at a tuple `w : Fin k → Space` of vectors of
norm `≤ 1` is a continuous linear map of operator norm at most `1`. -/
theorem norm_apply_clm_le_one {k : ℕ} (w : Fin k → Space) (hw : ∀ j : Fin k, ‖w j‖ ≤ 1) :
    ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space) Space w‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  rw [one_mul]
  change ‖A w‖ ≤ ‖A‖
  have hprod : ∏ j : Fin k, ‖w j‖ ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg (w j)) (fun j _ => hw j)
  calc ‖A w‖
      ≤ ‖A‖ * ∏ j : Fin k, ‖w j‖ := A.le_opNorm w
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg A)
    _ = ‖A‖ := mul_one ‖A‖

end FirstOrderPhaseDerivSub

/-- Reduction of the all-order `SmoothMorreyL4Bound` to the first-order (`k = 0`) vector-field
Morrey inequality `SmoothMorreyL4FieldBound` (`PartII-b:S3/1/1/1`). -/
theorem smoothMorreyL4Bound_of_field (hField : SmoothMorreyL4FieldBound) :
    SmoothMorreyL4Bound := by
  obtain ⟨C, hC0, hC⟩ := hField
  intro k
  obtain ⟨ι, hι, v, hv1, hAb⟩ := FirstOrderPhaseDerivSub.exists_finite_coord_bound k
  let _ : Fintype ι := hι
  refine ⟨(Fintype.card ι : ℝ) * C, by positivity, ?_⟩
  intro F hF M₀ M₁ hM₀ hM₁ y
  let G : Space → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space :=
    iteratedFDeriv ℝ k F
  have hG : ContDiff ℝ ∞ G := hF.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hG_diff : Differentiable ℝ G := hG.differentiable (by simp)
  have hM₀_le : ENNReal.ofReal M₀ ≤ ENNReal.ofReal (max M₀ 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left M₀ 0)
  have hM₁_le : ENNReal.ofReal M₁ ≤ ENNReal.ofReal (max M₁ 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left M₁ 0)
  have hterm : ∀ a : ι, ‖G y (v a)‖ ≤ C * (max M₀ 0 + max M₁ 0) := by
    intro a
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space →L[ℝ] Space :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space) Space (v a)
    have hL1 : ‖L‖ ≤ 1 := FirstOrderPhaseDerivSub.norm_apply_clm_le_one (v a) (hv1 a)
    let Fa : SpatialField := fun y' => L (G y')
    have hFa : ContDiff ℝ ∞ Fa := L.contDiff.comp hG
    have hFa0 : ∀ y' : Space, ‖Fa y'‖ ≤ ‖G y'‖ := fun y' => by
      calc ‖L (G y')‖
          ≤ ‖L‖ * ‖G y'‖ := L.le_opNorm (G y')
        _ ≤ 1 * ‖G y'‖ := mul_le_mul_of_nonneg_right hL1 (norm_nonneg (G y'))
        _ = ‖G y'‖ := one_mul _
    have hFa1 : ∀ y' : Space, ‖fderiv ℝ Fa y'‖ ≤ ‖iteratedFDeriv ℝ (k + 1) F y'‖ := fun y' => by
      have hfd : fderiv ℝ Fa y' = L.comp (fderiv ℝ G y') :=
        (L.hasFDerivAt.comp y' (hG_diff y').hasFDerivAt).fderiv
      rw [hfd]
      calc ‖L.comp (fderiv ℝ G y')‖
          ≤ ‖L‖ * ‖fderiv ℝ G y'‖ := ContinuousLinearMap.opNorm_comp_le L (fderiv ℝ G y')
        _ ≤ 1 * ‖fderiv ℝ G y'‖ := mul_le_mul_of_nonneg_right hL1 (norm_nonneg (fderiv ℝ G y'))
        _ = ‖fderiv ℝ (iteratedFDeriv ℝ k F) y'‖ := one_mul _
        _ = ‖iteratedFDeriv ℝ (k + 1) F y'‖ := norm_fderiv_iteratedFDeriv
    have hLp0 : eLpNorm Fa 4 volume ≤ ENNReal.ofReal (max M₀ 0) :=
      (eLpNorm_mono_ae (Eventually.of_forall hFa0)).trans (hM₀.trans hM₀_le)
    have hLp1 : eLpNorm (fderiv ℝ Fa) 4 volume ≤ ENNReal.ofReal (max M₁ 0) :=
      (eLpNorm_mono_ae (Eventually.of_forall hFa1)).trans (hM₁.trans hM₁_le)
    exact hC Fa hFa (max M₀ 0) (max M₁ 0) (le_max_right M₀ 0) (le_max_right M₁ 0) hLp0 hLp1 y
  calc ‖iteratedFDeriv ℝ k F y‖
      ≤ ∑ a : ι, ‖G y (v a)‖ := hAb (G y)
    _ ≤ ∑ _a : ι, C * (max M₀ 0 + max M₁ 0) := Finset.sum_le_sum fun a _ => hterm a
    _ = (Fintype.card ι : ℝ) * C * (max M₀ 0 + max M₁ 0) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- Any slice-smooth family `V : ℝ → SpatialField` with uniform `W^{k,4}(ℝ³)` bounds satisfies
`IsUniformSmoothL4SliceFamily V` once `SmoothMorreyL4Bound` is available. -/
theorem isUniformSmoothL4SliceFamily_of_morreyL4
    (hMorrey : SmoothMorreyL4Bound) (V : ℝ → SpatialField)
    (hSmooth : ∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (V τ))
    (hL4 : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (V τ) y) 4 volume ≤ ENNReal.ofReal M) :
    IsUniformSmoothL4SliceFamily V where
  slice_contDiff := hSmooth
  iteratedFDeriv_bounded := by
    intro k
    obtain ⟨C, _, hC⟩ := hMorrey k
    obtain ⟨M₀, hM₀⟩ := hL4 k
    obtain ⟨M₁, hM₁⟩ := hL4 (k + 1)
    exact ⟨C * (max M₀ 0 + max M₁ 0), fun τ y =>
      hC (V τ) (contDiff_infty.mpr fun j => hSmooth j τ) M₀ M₁ (hM₀ τ) (hM₁ τ) y⟩
  l4_bounded := hL4

/-- Specialization of `isUniformSmoothL4SliceFamily_of_morreyL4` to `bgField p z` using `hSlice`. -/
theorem isUniformSmoothL4SliceFamily_bgField_of_morreyL4
    (hMorrey : SmoothMorreyL4Bound) (p : Params) (z : p.Z)
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) :
    IsUniformSmoothL4SliceFamily (bgField p z) :=
  isUniformSmoothL4SliceFamily_of_morreyL4 hMorrey (bgField p z)
    (bgField_slice_contDiff p z hSlice) (bgField_l4_bounded p z hSlice)

/-! ## 3. First-order comoving derivative step and conditional assembly -/

/-- **`PartII-b:S3/1/1/2` (`BgFirstPhaseDerivStep`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562: "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$
with zero residual. ... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$
regularity and the projected equation give all time derivatives"): under the regime and all-order
spatial regularity hypotheses of `BgFirstOrderPhaseDeriv`, given
`IsUniformSmoothL4SliceFamily (bgField p z)`, there exists a slice-smooth `W^{k,4}` family
`U₁ : ℝ → SpatialField` (`U₁ = T₀U = νΔU + ½U - 𝔓(U · ∇U)`, `T₀ = ∂_τ - ½ y · ∇_y`) which is the
comoving derivative of `bgField p z` on every spatial jet along every comoving ray
`t ↦ (τ + t, e^{-t/2} y)`: `HasComovingJetDeriv (bgField p z) U₁`. (The maximal graph controls
`T₀w`, not `∂_τ w` or `(y · ∇)w` separately, so no fixed-`y` phase derivative is used.)
Composed by `bgFirstOrderPhaseDeriv_of` in task `PartII-b:S3/1/1`; decomposed by
`bgFirstPhaseDerivStep_of_comoving` (`Sub/PartII-b_S3_1_comoving.lean`). -/
def BgFirstPhaseDerivStep : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∃ U₁ : ℝ → SpatialField,
        (∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (U₁ τ)) ∧
        (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
          eLpNorm (fun y => iteratedFDeriv ℝ k (U₁ τ) y) 4 volume ≤ ENNReal.ofReal M) ∧
        HasComovingJetDeriv (bgField p z) U₁

/-- Conditional assembly of `BgFirstOrderPhaseDeriv` (`PartII-b:S3/1/1`, SP 2519-2523, 2559-2562)
from `SmoothMorreyL4FieldBound` (`PartII-b:S3/1/1/1`) and `BgFirstPhaseDerivStep`
(`PartII-b:S3/1/1/2`). -/
theorem bgFirstOrderPhaseDeriv_of
    (hField : SmoothMorreyL4FieldBound)
    (hFirstDeriv : BgFirstPhaseDerivStep) :
    BgFirstOrderPhaseDeriv := by
  have hMorrey : SmoothMorreyL4Bound := smoothMorreyL4Bound_of_field hField
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, hStep⟩ := hFirstDeriv Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, fun p d hReg hν hAge hMode z hProj hz hGraph hSlice hRaw hInlet => ?_⟩
  have hBg : IsUniformSmoothL4SliceFamily (bgField p z) :=
    isUniformSmoothL4SliceFamily_bgField_of_morreyL4 hMorrey p z hSlice
  obtain ⟨U₁, hU₁Smooth, hU₁L4, hU₁Deriv⟩ :=
    hStep p d hReg hν hAge hMode z hProj hz hGraph hSlice hBg hRaw hInlet
  exact ⟨hBg, U₁, isUniformSmoothL4SliceFamily_of_morreyL4 hMorrey U₁ hU₁Smooth hU₁L4, hU₁Deriv⟩

end UnforcedLeray.Short.IIb

end
