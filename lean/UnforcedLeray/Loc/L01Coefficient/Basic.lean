import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Analysis.SobolevEmbedding.H1
import UnforcedLeray.Analysis.LerayProjection.Mollifier.SmoothApproximation
import UnforcedLeray.Analysis.WeakDerivative
import UnforcedLeray.Analysis.SobolevGraph.Functions
import UnforcedLeray.Analysis.SobolevGraph.Pairing
import Mathlib.MeasureTheory.Function.Holder

/-!
# Step L1, helpers: exponents, tests, embeddings and operator families

Support for `Loc/L01Coefficient.lean` (step L1 `CoefficientStep`, `paper/main.tex` lines
267–290, `loc:eq:coefficient-maps`, blueprint units B0709, B0711).

* Hölder exponents `1/6 + 1/3 = 1/2` (line 282: `‖∇U_*‖₃‖f‖₆`).
* Scalar tests times `Lᵠ` coefficients lie in `L²`.
* `toLinf : C₀ → L^∞` and `h1ToL3 : H¹ → L³` (line 280: `∇U_* ∈ C_per L³`; `H¹ ⊂ L³` by
  interpolation between `L²` and the compiled `H¹ ⊂ L⁶`).
* Uniqueness of locally integrable weak derivatives.
* The vector-test integration by parts `⟨F, ∂ⱼφ⟩ = -⟨∂ⱼF, φ⟩` for `F ∈ H¹`.
* Continuity of `codRestrict` and `pi` families of operators.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

open SobolevGraph

/-! ## Exponents and spaces -/

instance holderTriple_six_three_two : ENNReal.HolderTriple 6 3 2 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff]

/-- `L^∞(ℝ³;ℝ³)`. -/
abbrev LinfSpace := Lp Space ∞ (volume : Measure Space)

/-- `L³(ℝ³;ℝ³)`. -/
abbrev L3Space := Lp Space 3 (volume : Measure Space)

/-! ## Tests -/

/-- A smooth compactly supported scalar test times an `L^q` field is in `L²` whenever
`1/s + 1/q = 1/2`. -/
theorem test_smul_memLp {φ : Space → ℝ} (hφ : IsSpatialTest φ) {a : SpatialField}
    {s q : ℝ≥0∞} [ENNReal.HolderTriple s q 2] (ha : MemLp a q volume) :
    MemLp (fun x => φ x • a x) 2 volume :=
  ha.smul (hφ.memLp s)

/-- The components of a vector test. -/
def testComponent (φ : Space → Space) (m : Fin 3) : Space → ℝ := fun x => φ x m

theorem testComponent_eq (φ : Space → Space) (m : Fin 3) :
    testComponent φ m = (EuclideanSpace.proj m : Space →L[ℝ] ℝ) ∘ φ := rfl

theorem isSpatialTest_testComponent {φ : Space → Space} (hφ : IsVectorTest φ) (m : Fin 3) :
    IsSpatialTest (testComponent φ m) := by
  rw [testComponent_eq]
  exact ⟨(EuclideanSpace.proj m : Space →L[ℝ] ℝ).contDiff.comp hφ.smooth,
    hφ.compact.comp_left (by simp)⟩

theorem spatialTestDerivative_testComponent {φ : Space → Space} (hφ : IsVectorTest φ)
    (m j : Fin 3) (x : Space) :
    spatialTestDerivative j (testComponent φ m) x = testPartial φ j x m := by
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.smooth.differentiable (by simp) x).hasFDerivAt
  have hc := (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp x hd
  unfold spatialTestDerivative
  rw [testComponent_eq, hc.fderiv]
  rfl

theorem space_sum_single (v : Space) :
    ∑ m : Fin 3, v m • EuclideanSpace.single m (1 : ℝ) = v := by
  ext i
  simp [Pi.single_apply]

/-- `⇑(∑ Fᵢ) = ∑ ⇑Fᵢ` almost everywhere, for a finite sum in `Lᵖ`. -/
theorem coeFn_finsetSum {ι : Type*} {p : ℝ≥0∞} (s : Finset ι)
    (F : ι → Lp Space p (volume : Measure Space)) :
    ⇑(∑ i ∈ s, F i) =ᵐ[volume] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero Space p volume
  | insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x h1 h2
    rw [Finset.sum_insert hi, h1, Pi.add_apply, h2, Finset.sum_insert hi]

theorem vectorTest_memLp {φ : Space → Space} (hφ : IsVectorTest φ) (p : ℝ≥0∞) :
    MemLp φ p volume :=
  hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact

theorem testPartial_memLp {φ : Space → Space} (hφ : IsVectorTest φ) (j : Fin 3) (p : ℝ≥0∞) :
    MemLp (testPartial φ j) p volume := by
  have hs : ContDiff ℝ ∞ (testPartial φ j) :=
    (ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).clm_apply contDiff_const
  exact hs.continuous.memLp_of_hasCompactSupport (hφ.compact.fderiv_apply ℝ _)

/-- `toL2 φ = ∑ₘ φₘ eₘ` in `L²`. -/
theorem toL2_vectorTest_eq_sum {φ : Space → Space} (hφ : IsVectorTest φ) :
    toL2 φ = ∑ m : Fin 3, testVector (testComponent φ m) (isSpatialTest_testComponent hφ m)
      (EuclideanSpace.single m 1) := by
  apply Lp.ext
  have hsum := coeFn_finsetSum Finset.univ (fun m : Fin 3 => testVector (testComponent φ m)
    (isSpatialTest_testComponent hφ m) (EuclideanSpace.single m 1))
  have hall : ∀ m ∈ (Finset.univ : Finset (Fin 3)),
      (testVector (testComponent φ m) (isSpatialTest_testComponent hφ m)
        (EuclideanSpace.single m 1) : SpatialField) =ᵐ[volume]
        fun x => testComponent φ m x • EuclideanSpace.single m (1 : ℝ) :=
    fun m _ => coeFn_testVector _ _ _
  have hall' := (ae_ball_iff (Finset.univ : Finset (Fin 3)).countable_toSet).mpr
    (fun m hm => hall m hm)
  filter_upwards [coeFn_toL2 (vectorTest_memLp hφ 2), hsum, hall'] with x hx hs ha
  rw [hx, hs]
  rw [Finset.sum_congr rfl (fun m hm => ha m hm)]
  exact (space_sum_single (φ x)).symm

/-- `toL2 ∂ⱼφ = ∑ₘ (∂ⱼφₘ) eₘ` in `L²`. -/
theorem toL2_testPartial_eq_sum {φ : Space → Space} (hφ : IsVectorTest φ) (j : Fin 3) :
    toL2 (testPartial φ j) = ∑ m : Fin 3,
      testVector (spatialTestDerivative j (testComponent φ m))
        ((isSpatialTest_testComponent hφ m).derivative j) (EuclideanSpace.single m 1) := by
  apply Lp.ext
  have hsum := coeFn_finsetSum Finset.univ (fun m : Fin 3 => testVector
    (spatialTestDerivative j (testComponent φ m))
    ((isSpatialTest_testComponent hφ m).derivative j) (EuclideanSpace.single m 1))
  have hall : ∀ m ∈ (Finset.univ : Finset (Fin 3)),
      (testVector (spatialTestDerivative j (testComponent φ m))
        ((isSpatialTest_testComponent hφ m).derivative j)
        (EuclideanSpace.single m 1) : SpatialField) =ᵐ[volume]
        fun x => spatialTestDerivative j (testComponent φ m) x •
          EuclideanSpace.single m (1 : ℝ) :=
    fun m _ => coeFn_testVector _ _ _
  have hall' := (ae_ball_iff (Finset.univ : Finset (Fin 3)).countable_toSet).mpr
    (fun m hm => hall m hm)
  filter_upwards [coeFn_toL2 (testPartial_memLp hφ j 2), hsum, hall'] with x hx hs ha
  rw [hx, hs]
  rw [Finset.sum_congr rfl (fun m hm => ha m hm)]
  simp_rw [spatialTestDerivative_testComponent hφ]
  exact (space_sum_single (testPartial φ j x)).symm

/-- Integration by parts against a vector test: `⟨F, ∂ⱼφ⟩ = -⟨∂ⱼF, φ⟩` for `F ∈ H¹`. -/
theorem H1_inner_testPartial (F : H1) {φ : Space → Space} (hφ : IsVectorTest φ) (j : Fin 3) :
    inner ℝ F.value (toL2 (testPartial φ j)) = -inner ℝ (F.derivative j) (toL2 φ) := by
  have hgraph : (F.value, F.derivative j) ∈ derivativeGraph j :=
    (mem_derivativeGraph_iff j _ _).mpr (F.hasWeakDerivative j)
  rw [toL2_testPartial_eq_sum hφ j, toL2_vectorTest_eq_sum hφ, inner_sum, inner_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hgraph
    ⟨testComponent φ m, isSpatialTest_testComponent hφ m⟩) (EuclideanSpace.single m 1)
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h
  change pairing (spatialTestDerivative j (testComponent φ m)) _ _ F.value +
    pairing (testComponent φ m) _ _ (F.derivative j) = 0 at h
  change inner ℝ F.value (testVector _ _ _) = -inner ℝ (F.derivative j) (testVector _ _ _)
  rw [real_inner_comm, real_inner_comm _ (F.derivative j)]
  exact eq_neg_of_add_eq_zero_left h

/-! ## `C₀ → L^∞` -/

theorem c0_memLp_top (v : ZeroAtInftyContinuousMap Space Space) :
    MemLp (v : SpatialField) ∞ volume :=
  memLp_top_of_bound v.continuous.aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun x => by
      simpa using (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := v)) ▸
        BoundedContinuousFunction.norm_coe_le_norm v.toBCF x)

/-- The `L^∞` class of a `C₀` field. -/
def toLinfFun (v : ZeroAtInftyContinuousMap Space Space) : LinfSpace := (c0_memLp_top v).toLp v

theorem coeFn_toLinfFun (v : ZeroAtInftyContinuousMap Space Space) :
    (toLinfFun v : SpatialField) =ᵐ[volume] v := (c0_memLp_top v).coeFn_toLp

theorem norm_toLinfFun_le (v : ZeroAtInftyContinuousMap Space Space) : ‖toLinfFun v‖ ≤ ‖v‖ := by
  have hb : ∀ᵐ x ∂(volume : Measure Space), ‖(v : SpatialField) x‖ ≤ ‖v‖ :=
    Eventually.of_forall fun x => by
      simpa using (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := v)) ▸
        BoundedContinuousFunction.norm_coe_le_norm v.toBCF x
  rw [toLinfFun, Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNormEssSup_le_of_ae_bound hb)

/-- `C₀ → L^∞` as a linear map. -/
def toLinfLinear : ZeroAtInftyContinuousMap Space Space →ₗ[ℝ] LinfSpace where
  toFun := toLinfFun
  map_add' v w := by
    apply Lp.ext
    filter_upwards [coeFn_toLinfFun (v + w), coeFn_toLinfFun v, coeFn_toLinfFun w,
      Lp.coeFn_add (toLinfFun v) (toLinfFun w)] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    rfl
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [coeFn_toLinfFun (c • v), coeFn_toLinfFun v,
      Lp.coeFn_smul c (toLinfFun v)] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2]
    rfl

/-- The bounded inclusion `C₀(ℝ³;ℝ³) → L^∞(ℝ³;ℝ³)`. -/
def toLinf : ZeroAtInftyContinuousMap Space Space →L[ℝ] LinfSpace :=
  toLinfLinear.mkContinuous 1 (fun v => by
    rw [one_mul]
    exact norm_toLinfFun_le v)

theorem coeFn_toLinf (v : ZeroAtInftyContinuousMap Space Space) :
    (toLinf v : SpatialField) =ᵐ[volume] v := coeFn_toLinfFun v

/-! ## `H¹ ⊂ L³` by interpolation

The two interpolation inequalities follow the template of

copied here because that draft is not compiled into the overlay. -/

/-- `‖f‖₄⁴ ≤ ‖f‖₂ ‖f‖₆³` (copied from `SobolevEmbedding/L4.lean`). -/
theorem eLpNorm_four_pow_le' {f : SpatialField} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 4 volume ^ 4 ≤ eLpNorm f 2 volume * eLpNorm f 6 volume ^ 3 := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (f := fun x : Space => ‖f x‖ₑ ^ (2 : ℝ))
    (g := fun x : Space => ‖f x‖ₑ ^ (6 : ℝ))
    (hf.enorm.pow_const _) (hf.enorm.pow_const _)
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have he (x : Space) :
      (‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (‖f x‖ₑ ^ (6 : ℝ)) ^ (1 / 2 : ℝ) = ‖f x‖ₑ ^ (4 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have ea := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 2) (by norm_num)
  have eb := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 6) (by norm_num)
  have ec := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 4) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at ea eb ec
  simp only [he] at h
  rw [← ea, ← eb, ← ec] at h
  norm_num only [ENNReal.coe_ofNat, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    show (6 : ℝ) * (1 / 2) = 3 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h
  calc eLpNorm f 4 volume ^ (4 : ℕ) = eLpNorm f 4 volume ^ (4 : ℝ) := by
        rw [← ENNReal.rpow_natCast]; norm_num
    _ ≤ _ := h.trans (le_of_eq (by norm_num))

/-- `‖f‖₃³ ≤ ‖f‖₂ ‖f‖₄²`. -/
theorem eLpNorm_three_pow_le {f : SpatialField} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 3 volume ^ 3 ≤ eLpNorm f 2 volume * eLpNorm f 4 volume ^ 2 := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (f := fun x : Space => ‖f x‖ₑ ^ (2 : ℝ))
    (g := fun x : Space => ‖f x‖ₑ ^ (4 : ℝ))
    (hf.enorm.pow_const _) (hf.enorm.pow_const _)
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have he (x : Space) :
      (‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (‖f x‖ₑ ^ (4 : ℝ)) ^ (1 / 2 : ℝ) = ‖f x‖ₑ ^ (3 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have ea := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 2) (by norm_num)
  have eb := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 4) (by norm_num)
  have ec := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 3) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at ea eb ec
  simp only [he] at h
  rw [← ea, ← eb, ← ec] at h
  norm_num only [ENNReal.coe_ofNat, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    show (4 : ℝ) * (1 / 2) = 2 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h
  calc eLpNorm f 3 volume ^ (3 : ℕ) = eLpNorm f 3 volume ^ (3 : ℝ) := by
        rw [← ENNReal.rpow_natCast]; norm_num
    _ ≤ _ := h.trans (le_of_eq (by norm_num))

/-- The constant of `H¹ ⊂ L³`. -/
def l3Constant : ℝ := 1 + 3 * (SobolevEmbedding.sobolevConstant : ℝ)

theorem one_le_l3Constant : 1 ≤ l3Constant := by
  unfold l3Constant
  have : (0 : ℝ) ≤ (SobolevEmbedding.sobolevConstant : ℝ) := NNReal.coe_nonneg _
  linarith

/-- The value of an `H¹` field and its `L⁶` norm are bounded by `l3Constant ‖F‖`. -/
theorem h1_l2_l6_le (F : H1) :
    (eLpNorm (F.value : SpatialField) 2 volume).toReal ≤ l3Constant * ‖F‖ ∧
      (eLpNorm (F.value : SpatialField) 6 volume).toReal ≤ l3Constant * ‖F‖ := by
  have hv : ‖F.value‖ ≤ ‖F‖ := PiLp.norm_apply_le (F : H1Ambient) 0
  have h1 : ‖F‖ ≤ l3Constant * ‖F‖ := by
    nlinarith [one_le_l3Constant, norm_nonneg F]
  constructor
  · rw [← Lp.norm_def]
    exact hv.trans h1
  · apply (SobolevEmbedding.h1_l6Norm_le F).trans
    unfold l3Constant
    nlinarith [norm_nonneg F]

theorem h1_memLp_three (F : H1) : MemLp (F.value : SpatialField) 3 volume := by
  have h2 := Lp.memLp F.value
  have h6 := SobolevEmbedding.h1_memLp_six F
  have h4 : eLpNorm (F.value : SpatialField) 4 volume < ⊤ := by
    have hb : eLpNorm (F.value : SpatialField) 4 volume ^ 4 < ⊤ :=
      (eLpNorm_four_pow_le' h2.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top h2.2 (ENNReal.pow_lt_top (n := 3) h6.2))
    by_contra hn
    have he : eLpNorm (F.value : SpatialField) 4 volume = ⊤ := top_unique (not_lt.mp hn)
    simp [he] at hb
  refine ⟨h2.aestronglyMeasurable, ?_⟩
  have hb : eLpNorm (F.value : SpatialField) 3 volume ^ 3 < ⊤ :=
    (eLpNorm_three_pow_le h2.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top h2.2 (ENNReal.pow_lt_top (n := 2) h4))
  by_contra hn
  have he : eLpNorm (F.value : SpatialField) 3 volume = ⊤ := top_unique (not_lt.mp hn)
  simp [he] at hb

theorem h1_l3Norm_le (F : H1) :
    (eLpNorm (F.value : SpatialField) 3 volume).toReal ≤ l3Constant * ‖F‖ := by
  obtain ⟨h2b, h6b⟩ := h1_l2_l6_le F
  have h2 := Lp.memLp F.value
  have h6 := SobolevEmbedding.h1_memLp_six F
  have h3 := h1_memLp_three F
  set K := l3Constant * ‖F‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by linarith [one_le_l3Constant]) (norm_nonneg F)
  have h4fin : eLpNorm (F.value : SpatialField) 4 volume ≠ ⊤ := by
    have hb : eLpNorm (F.value : SpatialField) 4 volume ^ 4 < ⊤ :=
      (eLpNorm_four_pow_le' h2.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top h2.2 (ENNReal.pow_lt_top (n := 3) h6.2))
    intro he
    simp [he] at hb
  have h4r : (eLpNorm (F.value : SpatialField) 4 volume).toReal ^ 4 ≤
      (eLpNorm (F.value : SpatialField) 2 volume).toReal *
        (eLpNorm (F.value : SpatialField) 6 volume).toReal ^ 3 := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top h2.2.ne (ENNReal.pow_ne_top h6.2.ne))
      (eLpNorm_four_pow_le' h2.aestronglyMeasurable)
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul] using h
  have h3r : (eLpNorm (F.value : SpatialField) 3 volume).toReal ^ 3 ≤
      (eLpNorm (F.value : SpatialField) 2 volume).toReal *
        (eLpNorm (F.value : SpatialField) 4 volume).toReal ^ 2 := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top h2.2.ne (ENNReal.pow_ne_top h4fin))
      (eLpNorm_three_pow_le h2.aestronglyMeasurable)
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul] using h
  have h4K : (eLpNorm (F.value : SpatialField) 4 volume).toReal ≤ K := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hK0
    calc _ ≤ _ := h4r
      _ ≤ K * K ^ 3 := by gcongr
      _ = K ^ 4 := by ring
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hK0
  calc _ ≤ _ := h3r
    _ ≤ K * K ^ 2 := by gcongr
    _ = K ^ 3 := by ring

/-- The `L³` class of an `H¹` field. -/
def h1ToL3Fun (F : H1) : L3Space := (h1_memLp_three F).toLp (F.value : SpatialField)

theorem coeFn_h1ToL3Fun (F : H1) :
    (h1ToL3Fun F : SpatialField) =ᵐ[volume] (F.value : SpatialField) :=
  (h1_memLp_three F).coeFn_toLp

/-- `H¹ → L³` as a linear map. -/
def h1ToL3Linear : H1 →ₗ[ℝ] L3Space where
  toFun := h1ToL3Fun
  map_add' F G := by
    apply Lp.ext
    filter_upwards [coeFn_h1ToL3Fun (F + G), coeFn_h1ToL3Fun F, coeFn_h1ToL3Fun G,
      Lp.coeFn_add (h1ToL3Fun F) (h1ToL3Fun G), Lp.coeFn_add F.value G.value]
      with x hsum hF hG hLp hval
    rw [hsum, hLp, Pi.add_apply, hF, hG]
    exact hval
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [coeFn_h1ToL3Fun (c • F), coeFn_h1ToL3Fun F,
      Lp.coeFn_smul c (h1ToL3Fun F), Lp.coeFn_smul c F.value] with x hs hF hLp hval
    rw [hs, RingHom.id_apply, hLp, Pi.smul_apply, hF]
    exact hval

/-- The bounded inclusion `H¹(ℝ³;ℝ³) → L³(ℝ³;ℝ³)`. -/
def h1ToL3 : H1 →L[ℝ] L3Space :=
  h1ToL3Linear.mkContinuous l3Constant (fun F => by
    change ‖h1ToL3Fun F‖ ≤ _
    rw [h1ToL3Fun, Lp.norm_toLp]
    exact h1_l3Norm_le F)

theorem coeFn_h1ToL3 (F : H1) :
    (h1ToL3 F : SpatialField) =ᵐ[volume] (F.value : SpatialField) := coeFn_h1ToL3Fun F

/-! ## Uniqueness of weak derivatives -/

theorem weakDerivative_ae_eq {i : Fin 3} {f g₁ g₂ : SpatialField}
    (h₁ : HasWeakSpatialDerivative i f g₁) (h₂ : HasWeakSpatialDerivative i f g₂)
    (hg₁ : LocallyIntegrable g₁ volume) (hg₂ : LocallyIntegrable g₂ volume) :
    g₁ =ᵐ[volume] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq hg₁ hg₂
  intro φ hs hc
  have hφ : IsSpatialTest φ := ⟨hs, hc⟩
  apply neg_injective
  exact (h₁.identity φ hφ).symm.trans (h₂.identity φ hφ)

/-- Two `Lᵖ` classes (`p ≥ 1`) that are weak derivatives of the same field are equal. -/
theorem Lp_eq_of_weakDerivative {p : ℝ≥0∞} [Fact (1 ≤ p)] {i : Fin 3} {f : SpatialField}
    {g₁ g₂ : Lp Space p (volume : Measure Space)}
    (h₁ : HasWeakSpatialDerivative i f (g₁ : SpatialField))
    (h₂ : HasWeakSpatialDerivative i f (g₂ : SpatialField)) : g₁ = g₂ :=
  Lp.ext (weakDerivative_ae_eq h₁ h₂ ((Lp.memLp g₁).locallyIntegrable Fact.out)
    ((Lp.memLp g₂).locallyIntegrable Fact.out))

/-! ## Continuity of operator families -/

section Families

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_codRestrict_sub_le (S : Submodule ℝ F) (A A' : E →L[ℝ] F)
    (h : ∀ x, A x ∈ S) (h' : ∀ x, A' x ∈ S) :
    ‖A.codRestrict S h - A'.codRestrict S h'‖ ≤ ‖A - A'‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have : ‖(A.codRestrict S h - A'.codRestrict S h') x‖ = ‖(A - A') x‖ := rfl
  rw [this]
  exact (A - A').le_opNorm x

theorem continuous_codRestrict_family {α : Type*} [TopologicalSpace α] (S : Submodule ℝ F)
    (A : α → E →L[ℝ] F) (hA : Continuous A) (h : ∀ a x, A a x ∈ S) :
    Continuous (fun a => (A a).codRestrict S (h a)) := by
  rw [continuous_iff_continuousAt]
  intro a₀
  refine (tendsto_iff_norm_sub_tendsto_zero
    (f := fun a => (A a).codRestrict S (h a))).mpr ?_
  have h0 : Tendsto (fun a => ‖A a - A a₀‖) (𝓝 a₀) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (hA.tendsto a₀)
  exact squeeze_zero (fun _ => by positivity)
    (fun a => norm_codRestrict_sub_le S (A a) (A a₀) (h a) (h a₀)) h0

theorem continuous_pi_family {ι : Type*} [Fintype ι] {α : Type*} [TopologicalSpace α]
    (A : ι → α → E →L[ℝ] F) (hA : ∀ i, Continuous (A i)) :
    Continuous (fun a => ContinuousLinearMap.pi (fun i => A i a)) := by
  rw [continuous_iff_continuousAt]
  intro a₀
  refine (tendsto_iff_norm_sub_tendsto_zero
    (f := fun a => ContinuousLinearMap.pi (fun i => A i a))).mpr ?_
  have h0 : Tendsto (fun a => ∑ i, ‖A i a - A i a₀‖) (𝓝 a₀) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun i _ => (tendsto_iff_norm_sub_tendsto_zero).mp ((hA i).tendsto a₀))
    simpa using this
  refine squeeze_zero (fun _ => by positivity) (fun a => ?_) h0
  have heq : ContinuousLinearMap.pi (fun i => A i a) - ContinuousLinearMap.pi (fun i => A i a₀) =
      ContinuousLinearMap.pi (fun i => A i a - A i a₀) := by
    ext x i
    simp
  rw [heq]
  exact ContinuousLinearMap.norm_pi_le_of_le
    (fun i => Finset.single_le_sum (f := fun i => ‖A i a - A i a₀‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end Families

end UnforcedLeray.Blueprint.L01
