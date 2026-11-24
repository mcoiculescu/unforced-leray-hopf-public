import UnforcedLeray.Loc.L10Nonlinear.Pairing

/-!
# L12 helper: the group `𝒪` acting on `L²`, `L²_div`, `H¹_div` and `H²_div`

`paper/main.tex` lines 112–115 (the action `(g·f)(x) = g f(g⁻¹x)` of `𝒪`) and 563–572 (step
L12, blueprint unit B1025: "Each action is an isometry of `𝒵_β`"). For a linear isometry
`g` of `ℝ³` this file builds

* `rotL2 g` on `L²(ℝ³;ℝ³)`, with `⟪rotL2 g F, rotL2 g G⟫ = ⟪F, G⟫` and inverse `rotL2 g⁻¹`
  (the operator is adapted from `rotL2` in

* the solenoidal subspace is invariant and the Leray projection commutes with `rotL2 g`;
* weak derivatives rotate: `∂ᵢ(g·F) = ∑ⱼ gᵢⱼ (g·∂ⱼF)` (`mem_derivativeGraph_rot`);
* isometries `rotH1`, `rotH2` of the graph spaces, and the continuous linear maps
  `rotL` on `L²_div`, `rotX` on `X = H¹_div`, `rotZ` on `Z = H²_div`, all acting on values
  by `rotL2 g`; `rotZ g` is an isometry and `ι_Z ∘ rotZ g = rotX g ∘ ι_Z`.

Nothing here uses `FixesAxis`: every linear isometry of `ℝ³` acts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L12

open SobolevGraph
open UnforcedLeray.Blueprint.L10 (toL2_coeFn toL2_of_ae_eq_coeFn toL2_congr coeFn_finsetSum
  space_sum_single)

/-! ## Coordinates -/

theorem inner_coord_left (i : Fin 3) (v : Space) : inner ℝ (coordinateVector i) v = v i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem space_eq_sum (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j :=
  (space_sum_single v).symm

theorem inner_eq_sum (a b : Space) : inner ℝ a b = ∑ i : Fin 3, a i * b i := by
  conv_lhs => rw [space_eq_sum a]
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_smul_left, inner_coord_left]

/-- `∑ᵢ L(eᵢ) eᵢ`, the vector representing a linear functional. -/
def gradVec (L : Space →L[ℝ] ℝ) : Space := ∑ i : Fin 3, L (coordinateVector i) • coordinateVector i

theorem inner_gradVec (L : Space →L[ℝ] ℝ) (v : Space) : inner ℝ (gradVec L) v = L v := by
  rw [gradVec, sum_inner]
  simp_rw [real_inner_smul_left, inner_coord_left]
  conv_rhs => rw [space_eq_sum v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

variable (g : Space ≃ₗᵢ[ℝ] Space)

/-- The matrix of `g`: `rc g i j = (g eⱼ)ᵢ`. -/
def rc (i j : Fin 3) : ℝ := g (coordinateVector j) i

theorem map_eq_sum (w : Space) : g w = ∑ j : Fin 3, w j • g (coordinateVector j) := by
  conv_lhs => rw [space_eq_sum w]
  rw [map_sum]
  simp_rw [map_smul]

theorem apply_coord (w : Space) (i : Fin 3) : g w i = ∑ j : Fin 3, rc g i j * w j := by
  rw [← inner_coord_left i (g w), map_eq_sum g w, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_right, inner_coord_left, rc, mul_comm]

theorem inner_symm_left (a b : Space) : inner ℝ (g.symm a) b = inner ℝ a (g b) := by
  rw [← g.inner_map_map, g.apply_symm_apply]

/-- `∑ⱼ gᵢⱼ eⱼ = g⁻¹ eᵢ`. -/
theorem sum_rc_smul (i : Fin 3) :
    ∑ j : Fin 3, rc g i j • coordinateVector j = g.symm (coordinateVector i) := by
  apply ext_inner_right ℝ
  intro v
  rw [sum_inner, inner_symm_left, inner_coord_left, apply_coord]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left, inner_coord_left]

/-- The columns of the matrix of `g` are orthonormal. -/
theorem sum_rc_mul_rc (j k : Fin 3) :
    ∑ i : Fin 3, rc g i j * rc g i k = if j = k then 1 else 0 := by
  rw [show (∑ i : Fin 3, rc g i j * rc g i k) =
      inner ℝ (g (coordinateVector j)) (g (coordinateVector k)) from
    (inner_eq_sum _ _).symm, g.inner_map_map, inner_coord_left]
  simp [coordinateVector]

/-- `g⁻¹ ∇L = ∇(L ∘ g)`. -/
theorem symm_gradVec (L : Space →L[ℝ] ℝ) :
    g.symm (gradVec L) = gradVec (L.comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_symm_left, inner_gradVec, inner_gradVec]
  rfl

/-- An orthogonal change of frame preserves sums of squares. -/
theorem sum_norm_sq_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : Fin 3 → Fin 3 → ℝ) (ha : ∀ j k, ∑ i : Fin 3, a i j * a i k = if j = k then 1 else 0)
    (H : Fin 3 → E) : ∑ i : Fin 3, ‖∑ j : Fin 3, a i j • H j‖ ^ 2 = ∑ j : Fin 3, ‖H j‖ ^ 2 := by
  have h1 : ∀ i, ‖∑ j : Fin 3, a i j • H j‖ ^ 2 =
      ∑ j : Fin 3, ∑ k : Fin 3, a i j * a i k * inner ℝ (H j) (H k) := by
    intro i
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ k, ∑ i : Fin 3, a i j * a i k * inner ℝ (H j) (H k) =
      (if j = k then 1 else 0) * inner ℝ (H j) (H k) := by
    intro k
    rw [← ha j k, Finset.sum_mul]
  simp_rw [h2]
  simp

theorem sum_norm_sq_rc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Fin 3 → E) : ∑ i : Fin 3, ‖∑ j : Fin 3, rc g i j • H j‖ ^ 2 = ∑ j : Fin 3, ‖H j‖ ^ 2 :=
  sum_norm_sq_orth (rc g) (sum_rc_mul_rc g) H

/-! ## Fields -/

theorem rotateField_apply (f : SpatialField) (x : Space) :
    rotateField g f x = g (f (g.symm x)) := rfl

theorem rotateField_congr {f f' : SpatialField} (h : f =ᵐ[volume] f') :
    rotateField g f =ᵐ[volume] rotateField g f' := by
  have h2 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h2] with x hx
  simp only [Function.comp_apply] at hx
  simp only [rotateField, hx]

theorem rotateField_rotateField_symm (f : SpatialField) :
    rotateField g (rotateField g.symm f) = f := by
  funext x
  simp [rotateField]

theorem memLp_rotateField {f : SpatialField} {p : ℝ≥0∞} (hf : MemLp f p volume) :
    MemLp (rotateField g f) p volume := by
  have h1 : MemLp (f ∘ g.symm) p volume := hf.comp_measurePreserving g.symm.measurePreserving
  exact (g.toLinearIsometry.toContinuousLinearMap.comp_memLp' h1)

/-! ## The action on `L²` -/

/-- `F ↦ g F(g⁻¹ ·)` on `L²(ℝ³;ℝ³)` (adapted from `rotL2` in
-/
def rotL2 : L2Space →L[ℝ] L2Space :=
  (g.toLinearIsometry.toContinuousLinearMap.compLpL 2 volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (g.symm : Space → Space)
      g.symm.measurePreserving).toContinuousLinearMap

theorem rotL2_ae (F : L2Space) :
    (rotL2 g F : SpatialField) =ᵐ[volume] rotateField g (F : SpatialField) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := volume) (p := 2)
    g.toLinearIsometry.toContinuousLinearMap
    (Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F)
  have h2 := Lp.coeFn_compMeasurePreserving F g.symm.measurePreserving
  have h3 : (fun x => g.toLinearIsometry.toContinuousLinearMap
      ((Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F) x))
        =ᵐ[volume] rotateField g (F : SpatialField) := by
    filter_upwards [h2] with x hx
    simp only [rotateField, hx, Function.comp_apply]
    rfl
  exact h1.trans h3

theorem rotL2_toL2 {f : SpatialField} (hf : MemLp f 2 volume) :
    rotL2 g (toL2 f) = toL2 (rotateField g f) := by
  symm
  apply toL2_of_ae_eq_coeFn
  refine (rotL2_ae g _).trans ?_
  exact rotateField_congr g (coeFn_toL2 hf)

theorem inner_rotL2 (F G : L2Space) : inner ℝ (rotL2 g F) (rotL2 g G) = inner ℝ F G := by
  rw [L2.inner_def, L2.inner_def]
  have h1 : (fun x => inner ℝ ((rotL2 g F : SpatialField) x) ((rotL2 g G : SpatialField) x))
      =ᵐ[volume] fun x =>
        inner ℝ ((F : SpatialField) (g.symm x)) ((G : SpatialField) (g.symm x)) := by
    filter_upwards [rotL2_ae g F, rotL2_ae g G] with x hF hG
    rw [hF, hG]
    simp only [rotateField, LinearIsometryEquiv.inner_map_map]
  rw [integral_congr_ae h1]
  exact MeasureTheory.integral_comp g.symm
    (fun y => inner ℝ ((F : SpatialField) y) ((G : SpatialField) y))

theorem norm_rotL2 (F : L2Space) : ‖rotL2 g F‖ = ‖F‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_rotL2]

theorem rotL2_rotL2_symm (F : L2Space) : rotL2 g (rotL2 g.symm F) = F := by
  apply Lp.ext
  filter_upwards [rotL2_ae g (rotL2 g.symm F), rotateField_congr g (rotL2_ae g.symm F)]
    with x h1 h2
  rw [h1, h2, rotateField_rotateField_symm]

theorem rotL2_symm_rotL2 (F : L2Space) : rotL2 g.symm (rotL2 g F) = F := by
  have h := rotL2_rotL2_symm g.symm F
  rwa [LinearIsometryEquiv.symm_symm] at h

/-- The adjoint of `rotL2 g` is `rotL2 g⁻¹`. -/
theorem inner_rotL2_left (F G : L2Space) :
    inner ℝ (rotL2 g F) G = inner ℝ F (rotL2 g.symm G) := by
  conv_lhs => rw [← rotL2_rotL2_symm g G]
  rw [inner_rotL2]

theorem inner_rotL2_right (F G : L2Space) :
    inner ℝ F (rotL2 g G) = inner ℝ (rotL2 g.symm F) G := by
  rw [real_inner_comm, inner_rotL2_left, real_inner_comm]

/-! ## Tests -/

theorem isSpatialTest_comp {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) :
    IsSpatialTest (fun x => ψ (g x)) :=
  ⟨hψ.smooth.comp g.contDiff, hψ.compact.comp_homeomorph g.toHomeomorph⟩

theorem rotL2_testVector (ψ : Space → ℝ) (hψ : IsSpatialTest ψ) (v : Space) :
    rotL2 g (testVector ψ hψ v) =
      testVector (fun x => ψ (g.symm x)) (isSpatialTest_comp g.symm hψ) (g v) := by
  apply Lp.ext
  filter_upwards [rotL2_ae g (testVector ψ hψ v),
    rotateField_congr g (coeFn_testVector ψ hψ v),
    coeFn_testVector (fun x => ψ (g.symm x)) (isSpatialTest_comp g.symm hψ) (g v)]
    with x h1 h2 h3
  rw [h1, h2, h3]
  simp [rotateField, map_smul]

/-- The chain rule `fderiv (φ ∘ g) x = fderiv φ (g x) ∘ g`. -/
theorem fderiv_comp_rot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : Space → E)
    (x : Space) :
    fderiv ℝ (fun y => φ (g y)) x =
      (fderiv ℝ φ (g x)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space) := by
  have h := g.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := φ) (x := x)
  exact h

theorem spatialTestDerivative_comp (φ : Space → ℝ) (i : Fin 3) (x : Space) :
    spatialTestDerivative i φ (g x) =
      ∑ j : Fin 3, rc g i j * spatialTestDerivative j (fun y => φ (g y)) x := by
  simp only [spatialTestDerivative, fderiv_comp_rot g φ x, ContinuousLinearMap.comp_apply]
  have e : ∀ j, (g.toContinuousLinearEquiv : Space →L[ℝ] Space) (coordinateVector j) =
      g (coordinateVector j) := fun j => rfl
  simp_rw [e]
  have e2 : coordinateVector i = g (g.symm (coordinateVector i)) := (g.apply_symm_apply _).symm
  conv_lhs => rw [e2, ← sum_rc_smul g i]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem testVector_comp_derivative (φ : Space → ℝ) (hφ : IsSpatialTest φ) (i : Fin 3)
    (h' : IsSpatialTest (fun x => spatialTestDerivative i φ (g x))) (w : Space) :
    testVector (fun x => spatialTestDerivative i φ (g x)) h' w =
      ∑ j : Fin 3, rc g i j • testVector (spatialTestDerivative j (fun y => φ (g y)))
        ((isSpatialTest_comp g hφ).derivative j) w := by
  apply Lp.ext
  filter_upwards [coeFn_testVector _ h' w,
    coeFn_finsetSum Finset.univ (fun j : Fin 3 => rc g i j • testVector
      (spatialTestDerivative j (fun y => φ (g y))) ((isSpatialTest_comp g hφ).derivative j) w),
    ae_all_iff.mpr (fun j : Fin 3 => Lp.coeFn_smul (rc g i j) (testVector
      (spatialTestDerivative j (fun y => φ (g y))) ((isSpatialTest_comp g hφ).derivative j) w)),
    ae_all_iff.mpr (fun j : Fin 3 => coeFn_testVector
      (spatialTestDerivative j (fun y => φ (g y))) ((isSpatialTest_comp g hφ).derivative j) w)]
    with x h1 h2 h3 h4
  rw [h1, h2]
  simp only [Pi.smul_apply] at h3
  simp_rw [h3, h4]
  rw [spatialTestDerivative_comp g φ i x, Finset.sum_smul]
  simp_rw [smul_smul]

/-! ## The Leray projection commutes with rotations -/

theorem rotL2_testGradient (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    rotL2 g.symm (Leray.testGradient φ hφ) =
      Leray.testGradient (fun x => φ (g x)) (isSpatialTest_comp g hφ) := by
  apply Lp.ext
  filter_upwards [rotL2_ae g.symm (Leray.testGradient φ hφ),
    rotateField_congr g.symm (Leray.coeFn_testGradient φ hφ),
    Leray.coeFn_testGradient (fun x => φ (g x)) (isSpatialTest_comp g hφ)] with x h1 h2 h3
  rw [h1, h2, h3]
  simp only [rotateField, LinearIsometryEquiv.symm_symm]
  have e1 : (∑ i : Fin 3, spatialTestDerivative i φ (g x) • coordinateVector i) =
      gradVec (fderiv ℝ φ (g x)) := rfl
  have e2 : (∑ i : Fin 3, spatialTestDerivative i (fun y => φ (g y)) x • coordinateVector i) =
      gradVec (fderiv ℝ (fun y => φ (g y)) x) := rfl
  rw [e1, e2, symm_gradVec, fderiv_comp_rot]

theorem rotL2_mem_solenoidal {F : L2Space} (hF : F ∈ Leray.solenoidalSubspace) :
    rotL2 g F ∈ Leray.solenoidalSubspace := by
  simp only [Leray.solenoidalSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hF ⊢
  intro φ
  have h := hF ⟨fun x => φ.1 (g x), isSpatialTest_comp g φ.2⟩
  simp only [Leray.divergenceFunctional, innerSL_apply_apply] at h ⊢
  rw [inner_rotL2_right, rotL2_testGradient g φ.1 φ.2]
  exact h

theorem projection_rotL2 (F : L2Space) :
    Leray.projection (rotL2 g F) = rotL2 g (Leray.projection F) := by
  unfold Leray.projection
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact rotL2_mem_solenoidal g (Leray.solenoidalSubspace.starProjection_apply_mem F)
  · intro w hw
    rw [← map_sub, inner_rotL2_left]
    exact Submodule.starProjection_inner_eq_zero F _ (rotL2_mem_solenoidal g.symm hw)

/-! ## Weak derivatives rotate -/

/-- If `∂ⱼF = Gⱼ` weakly for all `j`, then `∂ᵢ(g·F) = ∑ⱼ gᵢⱼ (g·Gⱼ)` weakly. -/
theorem mem_derivativeGraph_rot {F : L2Space} {G : Fin 3 → L2Space}
    (hG : ∀ j, (F, G j) ∈ derivativeGraph j) (i : Fin 3) :
    (rotL2 g F, ∑ j : Fin 3, rc g i j • rotL2 g (G j)) ∈ derivativeGraph i := by
  simp only [derivativeGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hG ⊢
  intro φ v
  have hψ : IsSpatialTest (fun x => φ.1 (g x)) := isSpatialTest_comp g φ.2
  have key : ∀ (ψ : Space → ℝ) (hψ : IsSpatialTest ψ) (w : Space) (H : L2Space),
      pairing ψ hψ w H = inner ℝ (testVector ψ hψ w) H := fun _ _ _ _ => rfl
  have hfun : ∀ (j : Fin 3) (φ' : SpatialTest) (w : Space) (P : L2Space × L2Space),
      derivativeFunctional j φ' w P =
        pairing (spatialTestDerivative j φ'.1) (φ'.2.derivative j) w P.1 +
          pairing φ'.1 φ'.2 w P.2 := fun _ _ _ _ => rfl
  rw [hfun, key, key]
  dsimp only
  rw [inner_rotL2_right]
  have hd : IsSpatialTest (fun x => spatialTestDerivative i φ.1 (g x)) :=
    isSpatialTest_comp g (φ.2.derivative i)
  have e1 : rotL2 g.symm (testVector (spatialTestDerivative i φ.1) (φ.2.derivative i) v) =
      testVector (fun x => spatialTestDerivative i φ.1 (g x)) hd (g.symm v) := by
    rw [rotL2_testVector]
    simp only [LinearIsometryEquiv.symm_symm]
  rw [e1, testVector_comp_derivative g φ.1 φ.2 i hd, sum_inner]
  have e2 : ∀ j : Fin 3, inner ℝ (rc g i j • testVector (spatialTestDerivative j
      (fun y => φ.1 (g y))) ((isSpatialTest_comp g φ.2).derivative j) (g.symm v)) F =
      -(rc g i j * inner ℝ (testVector φ.1 φ.2 v) (rotL2 g (G j))) := by
    intro j
    have h := hG j ⟨fun x => φ.1 (g x), hψ⟩ (g.symm v)
    rw [hfun, key, key] at h
    dsimp only at h
    rw [real_inner_smul_left, inner_rotL2_right]
    have e3 : rotL2 g.symm (testVector φ.1 φ.2 v) =
        testVector (fun x => φ.1 (g x)) hψ (g.symm v) := by
      rw [rotL2_testVector]
      simp only [LinearIsometryEquiv.symm_symm]
    rw [e3]
    have h' : inner ℝ (testVector (spatialTestDerivative j (fun y => φ.1 (g y)))
        ((isSpatialTest_comp g φ.2).derivative j) (g.symm v)) F =
        -inner ℝ (testVector (fun x => φ.1 (g x)) hψ (g.symm v)) (G j) :=
      eq_neg_of_add_eq_zero_left h
    rw [h']
    ring
  simp_rw [e2, inner_sum, real_inner_smul_right]
  simp [Finset.sum_neg_distrib]

/-! ## `H¹` and `H²` -/

theorem mem_graph_of_H1 (F : H1) (j : Fin 3) : (F.value, F.derivative j) ∈ derivativeGraph j :=
  (mem_derivativeGraph_iff j _ _).mpr (F.hasWeakDerivative j)

/-- The rotated `H¹` field. -/
def rotH1 (F : H1) : H1 :=
  H1.ofWeakDerivatives (rotL2 g F.value)
    (fun i => ∑ j : Fin 3, rc g i j • rotL2 g (F.derivative j))
    (fun i => (mem_derivativeGraph_iff i _ _).mp
      (mem_derivativeGraph_rot g (mem_graph_of_H1 F) i))

@[simp] theorem rotH1_value (F : H1) : (rotH1 g F).value = rotL2 g F.value := rfl

theorem norm_rotH1 (F : H1) : ‖rotH1 g F‖ = ‖F‖ := by
  have h : ‖rotH1 g F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [H1.norm_sq, H1.norm_sq]
    simp only [rotH1, H1.value_ofWeakDerivatives, H1.derivative_ofWeakDerivatives]
    rw [sum_norm_sq_rc, norm_rotL2]
    simp_rw [norm_rotL2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `rotH1 g` as a continuous linear map. -/
def rotH1L : H1 →L[ℝ] H1 :=
  LinearMap.mkContinuous
    { toFun := rotH1 g
      map_add' := fun F G => H1.value_injective (by
        show rotL2 g (H1.valueCLM (F + G)) = H1.valueCLM (rotH1 g F + rotH1 g G)
        rw [map_add, map_add, map_add]
        rfl)
      map_smul' := fun a F => H1.value_injective (by
        show rotL2 g (H1.valueCLM (a • F)) = H1.valueCLM (a • rotH1 g F)
        rw [map_smul, map_smul, map_smul]
        rfl) } 1
    (fun F => by
      show ‖rotH1 g F‖ ≤ 1 * ‖F‖
      rw [one_mul, norm_rotH1])

@[simp] theorem rotH1L_apply (F : H1) : rotH1L g F = rotH1 g F := rfl

theorem mem_graph_first_of_H2 (F : H2) (j : Fin 3) :
    (F.value, F.first j) ∈ derivativeGraph j :=
  (mem_derivativeGraph_iff j _ _).mpr (F.hasWeakFirst j)

theorem mem_graph_second_of_H2 (F : H2) (j k : Fin 3) :
    (F.first j, F.second j k) ∈ derivativeGraph k :=
  (mem_derivativeGraph_iff k _ _).mpr (F.hasWeakSecond j k)

theorem mem_graph_second_rot (F : H2) (i l : Fin 3) :
    (∑ j : Fin 3, rc g i j • rotL2 g (F.first j),
      ∑ j : Fin 3, rc g i j • ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k)) ∈
      derivativeGraph l := by
  have h : ∑ j : Fin 3, rc g i j • (rotL2 g (F.first j),
      ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k)) ∈ derivativeGraph l :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (mem_derivativeGraph_rot g (mem_graph_second_of_H2 F j) l))
  have e : ∑ j : Fin 3, rc g i j • (rotL2 g (F.first j),
      ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k)) =
      (∑ j : Fin 3, rc g i j • rotL2 g (F.first j),
        ∑ j : Fin 3, rc g i j • ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k)) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rwa [e] at h

/-- The rotated `H²` field. -/
def rotH2 (F : H2) : H2 :=
  H2.ofWeakDerivatives (rotL2 g F.value)
    (fun i => ∑ j : Fin 3, rc g i j • rotL2 g (F.first j))
    (fun i l => ∑ j : Fin 3, rc g i j • ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k))
    (fun i => (mem_derivativeGraph_iff i _ _).mp
      (mem_derivativeGraph_rot g (mem_graph_first_of_H2 F) i))
    (fun i l => (mem_derivativeGraph_iff l _ _).mp (mem_graph_second_rot g F i l))

@[simp] theorem rotH2_value (F : H2) : (rotH2 g F).value = rotL2 g F.value := rfl

theorem norm_rotH2 (F : H2) : ‖rotH2 g F‖ = ‖F‖ := by
  have h : ‖rotH2 g F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [H2.norm_sq, H2.norm_sq]
    simp only [rotH2, H2.value_ofWeakDerivatives, H2.first_ofWeakDerivatives,
      H2.second_ofWeakDerivatives]
    rw [sum_norm_sq_rc, norm_rotL2]
    simp_rw [norm_rotL2]
    congr 1
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun l _ => sum_norm_sq_rc g
      (fun j => ∑ k : Fin 3, rc g l k • rotL2 g (F.second j k))), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sum_norm_sq_rc]
    simp_rw [norm_rotL2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `rotH2 g` as a continuous linear map. -/
def rotH2L : H2 →L[ℝ] H2 :=
  LinearMap.mkContinuous
    { toFun := rotH2 g
      map_add' := fun F G => H2.value_injective (by
        show rotL2 g (H2.valueCLM (F + G)) = H2.valueCLM (rotH2 g F + rotH2 g G)
        rw [map_add, map_add, map_add]
        rfl)
      map_smul' := fun a F => H2.value_injective (by
        show rotL2 g (H2.valueCLM (a • F)) = H2.valueCLM (a • rotH2 g F)
        rw [map_smul, map_smul, map_smul]
        rfl) } 1
    (fun F => by
      show ‖rotH2 g F‖ ≤ 1 * ‖F‖
      rw [one_mul, norm_rotH2])

@[simp] theorem rotH2L_apply (F : H2) : rotH2L g F = rotH2 g F := rfl

/-! ## `L²_div`, `X = H¹_div`, `Z = H²_div` -/

/-- The action on `L²_div`. -/
def rotL : L2div →L[ℝ] L2div :=
  ((rotL2 g).comp Leray.solenoidalSubspace.subtypeL).codRestrict Leray.solenoidalSubspace
    (fun F => rotL2_mem_solenoidal g F.2)

/-- The action on `X = H¹_div`. -/
def rotX : X →L[ℝ] X :=
  ((rotH1L g).comp Xincl).codRestrict Xsub (fun f => by
    show H1.valueCLM (rotH1 g f.toH1) ∈ Leray.solenoidalSubspace
    exact rotL2_mem_solenoidal g (X.mem f))

/-- The action on `Z = H²_div`. -/
def rotZ : Z →L[ℝ] Z :=
  ((rotH2L g).comp Zincl).codRestrict Zsub (fun f => by
    show H2.valueCLM (rotH2 g f.toH2) ∈ Leray.solenoidalSubspace
    exact rotL2_mem_solenoidal g (Z.mem f))

theorem Lclass_rotL (F : L2div) : Lclass (rotL g F) = rotL2 g (Lclass F) := rfl
theorem Xclass_rotX (f : X) : Xclass (rotX g f) = rotL2 g (Xclass f) := rfl
theorem Zclass_rotZ (f : Z) : Zclass (rotZ g f) = rotL2 g (Zclass f) := rfl

theorem norm_rotZ (f : Z) : ‖rotZ g f‖ = ‖f‖ := norm_rotH2 g f.toH2

theorem Lval_rotL (F : L2div) : Lval (rotL g F) =ᵐ[volume] rotateField g (Lval F) :=
  rotL2_ae g (Lclass F)
theorem Xval_rotX (f : X) : Xval (rotX g f) =ᵐ[volume] rotateField g (Xval f) :=
  rotL2_ae g (Xclass f)
theorem Zval_rotZ (f : Z) : Zval (rotZ g f) =ᵐ[volume] rotateField g (Zval f) :=
  rotL2_ae g (Zclass f)

theorem Lclass_injective : Function.Injective Lclass := fun _ _ h => Subtype.ext h

theorem Zclass_injective : Function.Injective Zclass :=
  fun _ _ h => Subtype.ext (H2.value_injective h)

theorem ιZ_rotZ (f : Z) : ιZ (rotZ g f) = rotX g (ιZ f) := L10.Xclass_injective rfl

theorem ιX_rotX (f : X) : ιX (rotX g f) = rotL g (ιX f) := Lclass_injective rfl

end UnforcedLeray.Blueprint.L12
