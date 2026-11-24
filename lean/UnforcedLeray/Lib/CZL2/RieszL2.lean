import UnforcedLeray.Lib.CZL2.TestProjection

/-!
# The Riesz pairs `R_iR_k` on L² through the Newton Hessian (INF01 level L0, T2–T4)

Blueprint: INF01 targets T2, T3, T4 (scoping note `INF01-CZ.md` §4.2, §5); decision D5 of
`scoping/README.md` §3. Manuscript: `R_j = ∂_j(-Δ)^{-1/2}`, so
`R_iR_k = ∂_i∂_k(-Δ)^{-1}` and `-R_iR_k` is the `(i,k)` entry of `I - 𝔓`
(`paper/main.tex` lines 107–111; the L² uses of §1d of the note).

* `rieszPairTest i k f = ∂ᵢ∂ₖ(N ∗ f)` on compact smooth tests (T2), with the
  identities `∂ᵢ∂ₖ(N ∗ f) = N ∗ ∂ᵢ∂ₖf`, symmetry in `(i,k)`, `Σₖ T_kk f = -f`.
* T3: `Σᵢₖ ‖T_ik f‖₂² = ‖f‖₂²` and `∫ T_ik f · g = ∫ f · T_ik g` for tests `f, g`.
* T4: the bounded operator `rieszPairL2 i k` on scalar L² (norm `≤ 1`) agreeing with
  `T_ik` on every test, and `lerayNewtonL2 F = F + Σᵢₖ T_ik Fₖ eᵢ`, which equals the
  compiled orthogonal projection `Leray.projection` (`lerayNewtonL2_eq_projection`).

`rieszPairL2 i k` is built as `-(eᵢ-component) ∘ (I - 𝔓) ∘ (· eₖ)`; the content is the
theorem `rieszPairL2_toLp` that it is the Newton Hessian `∂ᵢ∂ₖ(N ∗ ·)` on tests, proved
from the test-level identity `(I - 𝔓)φ = -∇(N ∗ div φ)` (`TestProjection.lean`).
No Fourier transform is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-! ### T2: the Newton Hessian on tests -/

/-- `T_ik f = ∂ᵢ∂ₖ(N ∗ f)` for a compact smooth test `f` (INF01 T2, `rieszPairTest`). -/
def rieszPairTest (i k : Fin 3) (f : Space → ℝ) : Space → ℝ :=
  spatialTestDerivative i (spatialTestDerivative k (newtonConv f))

theorem rieszPairTest_eq_newtonConv {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    rieszPairTest i k f = newtonConv (spatialTestDerivative i (spatialTestDerivative k f)) := by
  rw [rieszPairTest, spatialTestDerivative_newtonConv hf k,
    spatialTestDerivative_newtonConv (hf.derivative k) i]

theorem rieszPairTest_comm {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    rieszPairTest i k f = rieszPairTest k i f := by
  rw [rieszPairTest_eq_newtonConv hf, rieszPairTest_eq_newtonConv hf,
    SobolevGraph.spatialTestDerivative_comm hf i k]

theorem rieszPairTest_contDiff {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    ContDiff ℝ ∞ (rieszPairTest i k f) := by
  rw [rieszPairTest_eq_newtonConv hf]
  exact newtonConv_contDiff ((hf.derivative k).derivative i)

/-- `Σₖ T_kk f = Δ(N ∗ f) = -f`. -/
theorem sum_rieszPairTest_diag {f : Space → ℝ} (hf : IsSpatialTest f) (x : Space) :
    ∑ k : Fin 3, rieszPairTest k k f x = -f x :=
  congrFun (laplacian_newtonConv hf) x

/-- The component family of the vector test `f eₖ`. -/
def singleFamily (k : Fin 3) (f : Space → ℝ) : Fin 3 → Space → ℝ :=
  fun j x => if j = k then f x else 0

theorem isSpatialTest_singleFamily {f : Space → ℝ} (hf : IsSpatialTest f) (k j : Fin 3) :
    IsSpatialTest (singleFamily k f j) := by
  unfold singleFamily
  by_cases h : j = k
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact ⟨contDiff_const, HasCompactSupport.zero⟩

theorem divTest_singleFamily {f : Space → ℝ} (k : Fin 3) :
    divTest (singleFamily k f) = spatialTestDerivative k f := by
  funext x
  unfold divTest
  rw [Finset.sum_eq_single k]
  · have h0 : singleFamily k f k = f := by
      funext y; simp [singleFamily]
    rw [h0]
  · intro j _ hj
    have h0 : singleFamily k f j = fun _ => 0 := by
      funext y; simp [singleFamily, hj]
    rw [spatialTestDerivative, h0]
    simp
  · simp

theorem vecField_singleFamily (k : Fin 3) (f : Space → ℝ) (x : Space) :
    vecField (singleFamily k f) x = f x • coordinateVector k := by
  unfold vecField
  rw [Finset.sum_eq_single k]
  · simp [singleFamily]
  · intro j _ hj; simp [singleFamily, hj]
  · simp

theorem lerayPotential_singleFamily {f : Space → ℝ} (hf : IsSpatialTest f) (k : Fin 3) :
    lerayPotential (singleFamily k f) = spatialTestDerivative k (newtonConv f) := by
  rw [lerayPotential, divTest_singleFamily, spatialTestDerivative_newtonConv hf k]

theorem spatialTestDerivative_lerayPotential_singleFamily {f : Space → ℝ}
    (hf : IsSpatialTest f) (i k : Fin 3) :
    spatialTestDerivative i (lerayPotential (singleFamily k f)) = rieszPairTest i k f := by
  rw [lerayPotential_singleFamily hf k]; rfl

/-- `T_ik f ∈ L²` (it is bounded by `M (1+|x|)⁻²`). -/
theorem memLp_rieszPairTest {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    MemLp (rieszPairTest i k f) 2 volume := by
  have hfam := isSpatialTest_singleFamily hf k
  obtain ⟨M, -, hM⟩ := lerayPotential_decay hfam
  rw [← spatialTestDerivative_lerayPotential_singleFamily hf i k]
  exact memLp_two_of_norm_le
    (contDiff_spatialTestDerivative (lerayPotential_contDiff hfam) i).continuous.aestronglyMeasurable
    (M := M) fun y => (Real.norm_eq_abs _).trans_le (hM i y)

/-- Differentiating a finite sum of smooth functions differentiates each summand. -/
theorem spatialTestDerivative_sum' {ι : Type*} (s : Finset ι) {a : ι → Space → ℝ}
    (ha : ∀ j, ContDiff ℝ ∞ (a j)) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => ∑ j ∈ s, a j y) x =
      ∑ j ∈ s, spatialTestDerivative i (a j) x := by
  unfold spatialTestDerivative
  rw [(HasFDerivAt.fun_sum (fun j (_ : j ∈ s) =>
    (((ha j).differentiable (by simp)).differentiableAt).hasFDerivAt)).fderiv]
  simp

/-- The Newton formula for the potential: `∂ᵢ(N ∗ div φ) = Σₖ T_ik φₖ`. -/
theorem spatialTestDerivative_lerayPotential_eq_sum {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (lerayPotential f) x = ∑ k : Fin 3, rieszPairTest i k (f k) x := by
  have hsum := newtonConv_sum Finset.univ (f := fun k => spatialTestDerivative k (f k))
    (fun k => (hf k).derivative k)
  have he : lerayPotential f = fun y => ∑ k : Fin 3, spatialTestDerivative k (newtonConv (f k)) y := by
    rw [lerayPotential, show divTest f = fun x => ∑ k : Fin 3, spatialTestDerivative k (f k) x
      from rfl, hsum]
    funext y
    exact Finset.sum_congr rfl fun k _ => by rw [spatialTestDerivative_newtonConv (hf k) k]
  rw [he, spatialTestDerivative_sum' Finset.univ
    (fun k => contDiff_spatialTestDerivative (newtonConv_contDiff (hf k)) k) i x]
  rfl

/-! ### Inner products of the test fields -/

theorem inner_vecField_vecField (a b : Fin 3 → Space → ℝ) (x : Space) :
    inner ℝ (vecField a x) (vecField b x) = ∑ i : Fin 3, a i x * b i x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecField_apply, vecField_apply, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

theorem gradField_eq_vecField (ψ : Space → ℝ) :
    gradField ψ = vecField fun i => spatialTestDerivative i ψ := rfl

theorem sum_singleFamily_mul (k : Fin 3) (f : Space → ℝ) (a : Fin 3 → ℝ) (x : Space) :
    ∑ j : Fin 3, a j * singleFamily k f j x = a k * f x := by
  rw [Finset.sum_eq_single k]
  · simp [singleFamily]
  · intro j _ hj; simp [singleFamily, hj]
  · simp

/-- `(eLpNorm a 2).toReal² = ∫ a²` for real `a ∈ L²`. -/
theorem eLpNorm_two_toReal_sq {a : Space → ℝ} (ha : MemLp a 2 volume) :
    (eLpNorm a 2 volume).toReal ^ 2 = ∫ x, a x ^ 2 := by
  rw [ha.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hI : 0 ≤ ∫ x, ‖a x‖ ^ (ENNReal.toReal 2) := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast,
    ← Real.rpow_mul hI]
  norm_num

/-- Inner product of a test field with the L² class of `∇ψ` for a potential of a test. -/
private theorem toL2_inner_toL2 {A B : SpatialField} (hA : MemLp A 2 volume)
    (hB : MemLp B 2 volume) :
    inner ℝ (toL2 A) (toL2 B) = ∫ x, inner ℝ (A x) (B x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hA, coeFn_toL2 hB] with x h1 h2
  rw [h1, h2]

/-! ### T3: the L² identity and the symmetry on tests -/

/-- For each `k`: `Σᵢ ∫ (T_ik f)² = -∫ T_kk f · f`. -/
theorem sum_integral_sq_rieszPairTest_col {f : Space → ℝ} (hf : IsSpatialTest f) (k : Fin 3) :
    ∑ i : Fin 3, ∫ x, rieszPairTest i k f x ^ 2 = -∫ x, rieszPairTest k k f x * f x := by
  have hfam := isSpatialTest_singleFamily hf k
  set V := vecField (singleFamily k f) with hVdef
  set ψ := lerayPotential (singleFamily k f) with hψdef
  have hV := memLp_vecField hfam 2
  have hW := memLp_gradField_lerayPotential hfam
  set w := toL2 V - Leray.projection (toL2 V) with hwdef
  have hw : w = -toL2 (gradField ψ) := toL2_sub_projection_vecField hfam
  have hdψ : ∀ i, spatialTestDerivative i ψ = rieszPairTest i k f := fun i =>
    spatialTestDerivative_lerayPotential_singleFamily hf i k
  -- `‖∇ψ‖² = Σᵢ ∫ (∂ᵢψ)²`
  have h1 : inner ℝ (toL2 (gradField ψ)) (toL2 (gradField ψ)) =
      ∑ i : Fin 3, ∫ x, rieszPairTest i k f x ^ 2 := by
    rw [toL2_inner_toL2 hW hW, ← integral_finsetSum _ fun i _ =>
      (memLp_rieszPairTest hf i k).integrable_sq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [gradField_eq_vecField, inner_vecField_vecField]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdψ i, sq]
  -- `⟨w, w⟩ = ⟨w, V⟩`
  have h2 : inner ℝ w w = inner ℝ w (toL2 V) := by
    have h0 : inner ℝ w (Leray.projection (toL2 V)) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Leray.projection_mem _)
        (Leray.residual_mem_orthogonal _)
    calc inner ℝ w w = inner ℝ w (toL2 V) - inner ℝ w (Leray.projection (toL2 V)) := by
          rw [hwdef, inner_sub_right]
      _ = inner ℝ w (toL2 V) := by rw [h0, sub_zero]
  -- `⟨∇ψ, V⟩ = ∫ ∂ₖψ f`
  have h3 : inner ℝ (toL2 (gradField ψ)) (toL2 V) = ∫ x, rieszPairTest k k f x * f x := by
    rw [toL2_inner_toL2 hW hV]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [gradField_eq_vecField, inner_vecField_vecField, sum_singleFamily_mul, hdψ k]
  rw [← h1, ← inner_neg_neg, ← hw, h2, hw, inner_neg_left, h3]

/-- **INF01 T3** (integral form): `Σᵢₖ ∫ (T_ik f)² = ∫ f²`. -/
theorem sum_integral_sq_rieszPairTest {f : Space → ℝ} (hf : IsSpatialTest f) :
    ∑ i : Fin 3, ∑ k : Fin 3, ∫ x, rieszPairTest i k f x ^ 2 = ∫ x, f x ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [sum_integral_sq_rieszPairTest_col hf]
  have hint : ∀ k, Integrable (fun x => rieszPairTest k k f x * f x) volume := fun k =>
    memLp_one_iff_integrable.mp ((hf.memLp 2).mul' (memLp_rieszPairTest hf k k))
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun k _ => hint k]
  simp_rw [← Finset.sum_mul, sum_rieszPairTest_diag hf]
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **INF01 T3.** `Σᵢₖ ‖∂ᵢ∂ₖ(N ∗ f)‖₂² = ‖f‖₂²` for every compact smooth test `f`. -/
theorem sum_sq_l2_rieszPairTest {f : Space → ℝ} (hf : IsSpatialTest f) :
    ∑ i : Fin 3, ∑ k : Fin 3, (eLpNorm (rieszPairTest i k f) 2 volume).toReal ^ 2 =
      (eLpNorm f 2 volume).toReal ^ 2 := by
  simp_rw [eLpNorm_two_toReal_sq (memLp_rieszPairTest hf _ _), eLpNorm_two_toReal_sq (hf.memLp 2)]
  exact sum_integral_sq_rieszPairTest hf

/-- **INF01 T3.** Symmetry: `∫ T_ik f · g = ∫ f · T_ik g` for compact smooth tests. -/
theorem integral_rieszPairTest_mul_symm {f g : Space → ℝ} (hf : IsSpatialTest f)
    (hg : IsSpatialTest g) (i k : Fin 3) :
    ∫ x, rieszPairTest i k f x * g x = ∫ x, f x * rieszPairTest i k g x := by
  have hF := isSpatialTest_singleFamily hf k
  have hG := isSpatialTest_singleFamily hg i
  set Vf := vecField (singleFamily k f)
  set Vg := vecField (singleFamily i g)
  have hVf := memLp_vecField hF 2
  have hVg := memLp_vecField hG 2
  have hWf := memLp_gradField_lerayPotential hF
  have hWg := memLp_gradField_lerayPotential hG
  have hself : inner ℝ (toL2 Vf - Leray.projection (toL2 Vf)) (toL2 Vg) =
      inner ℝ (toL2 Vf) (toL2 Vg - Leray.projection (toL2 Vg)) := by
    rw [inner_sub_left, inner_sub_right, Leray.projection_selfadjoint]
  rw [toL2_sub_projection_vecField hF, toL2_sub_projection_vecField hG,
    inner_neg_left, inner_neg_right, neg_inj, toL2_inner_toL2 hWf hVg,
    toL2_inner_toL2 hVf hWg] at hself
  have e1 : ∫ x, inner ℝ (gradField (lerayPotential (singleFamily k f)) x) (Vg x) =
      ∫ x, rieszPairTest i k f x * g x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [gradField_eq_vecField, inner_vecField_vecField, sum_singleFamily_mul,
      spatialTestDerivative_lerayPotential_singleFamily hf i k]
  have e2 : ∫ x, inner ℝ (Vf x) (gradField (lerayPotential (singleFamily i g)) x) =
      ∫ x, f x * rieszPairTest i k g x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [real_inner_comm, gradField_eq_vecField, inner_vecField_vecField, sum_singleFamily_mul,
      spatialTestDerivative_lerayPotential_singleFamily hg k i, rieszPairTest_comm hg k i,
      mul_comm]
  rw [← e1, ← e2, hself]

/-! ### T4: the bounded L² operators -/

/-- Scalar `L²(R³)`. -/
abbrev ScalarL2 := Lp ℝ 2 (volume : Measure Space)

/-- `f ↦ f eₖ`, scalar L² into vector L². -/
def embedL2 (k : Fin 3) : ScalarL2 →L[ℝ] L2Space :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector k)).compLpL 2 volume

/-- `F ↦ Fᵢ`, vector L² onto scalar L². -/
def coordL2 (i : Fin 3) : L2Space →L[ℝ] ScalarL2 :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).compLpL 2 volume

/-- The complementary projection `I - 𝔓` onto the closed gradient subspace. -/
def complementL2 : L2Space →L[ℝ] L2Space := ContinuousLinearMap.id ℝ L2Space - Leray.projection

/-- **INF01 T4.** The Riesz pair `R_iR_k = ∂ᵢ∂ₖ(-Δ)^{-1}` on scalar L²:
`-(eᵢ-component of (I - 𝔓)(f eₖ))`. It is the Newton Hessian on tests
(`rieszPairL2_toLp`) and has norm `≤ 1` (`norm_rieszPairL2_le`). -/
def rieszPairL2 (i k : Fin 3) : ScalarL2 →L[ℝ] ScalarL2 :=
  -((coordL2 i).comp (complementL2.comp (embedL2 k)))

/-- **INF01 T4.** The Leray projection written through the Newton Hessian:
`(𝔓F)ᵢ = Fᵢ + Σₖ T_ik Fₖ`. -/
def lerayNewtonL2 : L2Space →L[ℝ] L2Space :=
  ContinuousLinearMap.id ℝ L2Space +
    ∑ i : Fin 3, ∑ k : Fin 3, (embedL2 i).comp ((rieszPairL2 i k).comp (coordL2 k))

theorem coeFn_embedL2 (k : Fin 3) (f : ScalarL2) :
    (embedL2 k f : SpatialField) =ᵐ[volume] fun x => f x • coordinateVector k := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector k)) f] with x hx
  rw [embedL2, hx]
  simp

theorem coeFn_coordL2 (i : Fin 3) (F : L2Space) :
    (coordL2 i F : Space → ℝ) =ᵐ[volume] fun x => F x i := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ) F] with x hx
  rw [coordL2, hx]
  rfl

theorem complementL2_apply (F : L2Space) : complementL2 F = F - Leray.projection F := rfl

theorem norm_complementL2_apply_le (F : L2Space) : ‖complementL2 F‖ ≤ ‖F‖ := by
  rw [complementL2_apply, Leray.projection,
    ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ F

theorem norm_complementL2_le : ‖complementL2‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => by
    rw [one_mul]; exact norm_complementL2_apply_le F

theorem norm_embedL2_le (k : Fin 3) : ‖embedL2 k‖ ≤ 1 := by
  refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_coordinateVector, mul_one]
  exact ContinuousLinearMap.norm_id_le

theorem norm_coordL2_le (i : Fin 3) : ‖coordL2 i‖ ≤ 1 := by
  refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact PiLp.norm_apply_le x i

/-- **INF01 T4.** `‖R_iR_k‖_{L²→L²} ≤ 1`. -/
theorem norm_rieszPairL2_le (i k : Fin 3) : ‖rieszPairL2 i k‖ ≤ 1 := by
  rw [rieszPairL2, norm_neg]
  calc ‖(coordL2 i).comp (complementL2.comp (embedL2 k))‖
      ≤ ‖coordL2 i‖ * (‖complementL2‖ * ‖embedL2 k‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by
        gcongr
        · exact norm_coordL2_le i
        · exact norm_complementL2_le
        · exact norm_embedL2_le k
    _ = 1 := by norm_num

theorem embedL2_toLp {f : Space → ℝ} (hf : IsSpatialTest f) (k : Fin 3) :
    embedL2 k ((hf.memLp 2).toLp f) = toL2 (vecField (singleFamily k f)) := by
  have hV := memLp_vecField (isSpatialTest_singleFamily hf k) 2
  apply Lp.ext
  filter_upwards [coeFn_embedL2 k ((hf.memLp 2).toLp f), (hf.memLp 2).coeFn_toLp,
    coeFn_toL2 hV] with x h1 h2 h3
  rw [h1, h3, h2, vecField_singleFamily]

/-- **INF01 T4.** On every compact smooth test, `rieszPairL2 i k` is the Newton Hessian
`∂ᵢ∂ₖ(N ∗ f)`. -/
theorem rieszPairL2_toLp {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    rieszPairL2 i k ((hf.memLp 2).toLp f) =
      (memLp_rieszPairTest hf i k).toLp (rieszPairTest i k f) := by
  have hfam := isSpatialTest_singleFamily hf k
  have hW := memLp_gradField_lerayPotential hfam
  have h1 : complementL2 (embedL2 k ((hf.memLp 2).toLp f)) =
      -toL2 (gradField (lerayPotential (singleFamily k f))) := by
    rw [embedL2_toLp hf k, complementL2_apply, toL2_sub_projection_vecField hfam]
  have h2 : rieszPairL2 i k ((hf.memLp 2).toLp f) =
      coordL2 i (toL2 (gradField (lerayPotential (singleFamily k f)))) := by
    rw [rieszPairL2, neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, h1, map_neg, neg_neg]
  rw [h2]
  apply Lp.ext
  filter_upwards [coeFn_coordL2 i (toL2 (gradField (lerayPotential (singleFamily k f)))),
    coeFn_toL2 hW, (memLp_rieszPairTest hf i k).coeFn_toLp] with x h1 h2 h3
  rw [h1, h3, h2, gradField_apply, spatialTestDerivative_lerayPotential_singleFamily hf i k]

/-- Every vector L² class is the sum of its embedded components. -/
theorem sum_embedL2_coordL2 (F : L2Space) : ∑ k : Fin 3, embedL2 k (coordL2 k F) = F := by
  apply Lp.ext
  have hk : ∀ᵐ x ∂volume, ∀ k : Fin 3,
      (embedL2 k (coordL2 k F) : SpatialField) x = (coordL2 k F) x • coordinateVector k :=
    ae_all_iff.mpr fun k => coeFn_embedL2 k (coordL2 k F)
  have hc : ∀ᵐ x ∂volume, ∀ k : Fin 3, (coordL2 k F) x = F x k :=
    ae_all_iff.mpr fun k => coeFn_coordL2 k F
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun k : Fin 3 => embedL2 k (coordL2 k F)), hk, hc] with x h1 h2 h3
  rw [h1]
  simp_rw [h2, h3]
  exact (eq_sum_coordinateVector (F x)).symm

/-- **INF01 T4.** The Newton–Hessian Leray operator is the compiled orthogonal Leray
projection (`LerayProjection/Basic.lean`). -/
theorem lerayNewtonL2_eq_projection : lerayNewtonL2 = Leray.projection := by
  ext1 F
  have hrow : ∀ i : Fin 3, ∑ k : Fin 3, (embedL2 i).comp ((rieszPairL2 i k).comp (coordL2 k)) F =
      -embedL2 i (coordL2 i (complementL2 F)) := by
    intro i
    simp only [ContinuousLinearMap.comp_apply, rieszPairL2, neg_apply,
      map_neg]
    rw [Finset.sum_neg_distrib, ← map_sum, ← map_sum, ← map_sum, sum_embedL2_coordL2]
  simp only [lerayNewtonL2, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sum_apply]
  simp_rw [hrow]
  rw [Finset.sum_neg_distrib, sum_embedL2_coordL2, complementL2_apply]
  abel

/-- On a compact smooth vector test, the Newton formula `(𝔓φ)ᵢ = φᵢ + Σₖ ∂ᵢ∂ₖ(N ∗ φₖ)`
holds for the compiled Leray projection. -/
theorem projection_toL2_vecField_newton {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) :
    Leray.projection (toL2 (vecField f)) =
      toL2 (vecField fun i x => f i x + ∑ k : Fin 3, rieszPairTest i k (f k) x) := by
  rw [projection_toL2_vecField hf]
  congr 1
  funext x
  ext i
  rw [Pi.add_apply, PiLp.add_apply, vecField_apply, gradField_apply, vecField_apply,
    spatialTestDerivative_lerayPotential_eq_sum hf i x]

end UnforcedLeray.RieszLp
