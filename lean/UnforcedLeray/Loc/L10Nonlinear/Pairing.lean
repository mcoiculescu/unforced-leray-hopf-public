import UnforcedLeray.Blueprint.Localization.Nonlinear
import UnforcedLeray.Analysis.SobolevGraph.Pairing
import UnforcedLeray.Analysis.SobolevGraph.Functions
import UnforcedLeray.Analysis.SobolevGraph.H2Functions
import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Step L10, helpers: the weak `-𝔓 div` of a tensor

Support for `Loc/L10Nonlinear.lean` (step L10 `NonlinearStep`, `paper/main.tex` lines 462–491,
blueprint units B0721, B0722). The three maps of L10 (`𝓝`, `𝓒(K_loc,·)`, `G_*`) are all of the
form `-𝔓 div 𝕋` (lines 464–466), characterized by `IsMinusLerayDiv` of
`Blueprint/Localization/Spaces.lean`. This file proves:

* the algebra of `IsMinusLerayDiv`: a.e. congruence of the columns, sums, scalar multiples;
* uniqueness: `IsMinusLerayDiv col F₁ → IsMinusLerayDiv col F₂ → F₁ = F₂` (smooth compactly
  supported fields separate `L²`);
* existence for tensors with `H²` columns: if `𝕋_{·j} = P_j ∈ H²`, then
  `-𝔓 ∑ⱼ ∂ⱼ P_j ∈ X = H¹_div` is `-𝔓 div 𝕋`, with `X`-norm at most `∑ⱼ ‖P_j‖_{H²}`
  (the compiled `h1Projection` contracts `H¹`, line 489);
* bounded (bi)linear operators into `X` from a.e.-(bi)linear tensors with bounded `H²` columns,
  obtained from uniqueness.

The vector-test integration by parts `⟨F, ∂ⱼφ⟩ = -⟨∂ⱼF, φ⟩` is copied (with its helper lemmas)

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L10

open SobolevGraph

/-! ## `toL2` algebra -/

theorem toL2_add' {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f + g) = toL2 f + toL2 g := by
  rw [toL2_of_memLp (hf.add hg), toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_add hg

theorem toL2_smul' (a : ℝ) {f : SpatialField} (hf : MemLp f 2 volume) :
    toL2 (a • f) = a • toL2 f := by
  rw [toL2_of_memLp (hf.const_smul a), toL2_of_memLp hf]
  exact hf.toLp_const_smul a

theorem toL2_congr {f g : SpatialField} (hf : MemLp f 2 volume) (h : f =ᵐ[volume] g) :
    toL2 f = toL2 g := by
  have hg : MemLp g 2 volume := (memLp_congr_ae h).mp hf
  rw [toL2_of_memLp hf, toL2_of_memLp hg]
  exact (hf.toLp_eq_toLp_iff hg).mpr h

theorem toL2_coeFn (F : L2Space) : toL2 (F : SpatialField) = F := by
  rw [toL2_of_memLp (Lp.memLp F)]
  exact Lp.toLp_coeFn F (Lp.memLp F)

theorem toL2_of_ae_eq_coeFn {f : SpatialField} {F : L2Space}
    (h : (F : SpatialField) =ᵐ[volume] f) : toL2 f = F := by
  rw [← toL2_congr (Lp.memLp F) h, toL2_coeFn]

theorem l2Norm_coeFn (F : L2Space) : l2Norm (F : SpatialField) = ‖F‖ := by
  unfold l2Norm
  rw [Lp.norm_def]

/-! ## The algebra of `IsMinusLerayDiv` -/

theorem lerayDivPairing_congr {c₁ c₂ : Fin 3 → SpatialField} (h₁ : ColumnsL2 c₁)
    (h : ∀ j, c₁ j =ᵐ[volume] c₂ j) (φ : Space → Space) :
    lerayDivPairing c₁ φ = lerayDivPairing c₂ φ := by
  unfold lerayDivPairing
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toL2_congr (h₁ j) (h j)]

theorem IsMinusLerayDiv.congr {c₁ c₂ : Fin 3 → SpatialField} {F : L2Space}
    (hF : IsMinusLerayDiv c₁ F) (h : ∀ j, c₁ j =ᵐ[volume] c₂ j) : IsMinusLerayDiv c₂ F :=
  ⟨fun j => (memLp_congr_ae (h j)).mp (hF.1 j),
    fun φ hφ => by rw [hF.2 φ hφ, lerayDivPairing_congr hF.1 h]⟩

theorem IsMinusLerayDiv.congr_F {c : Fin 3 → SpatialField} {F G : L2Space}
    (hF : IsMinusLerayDiv c F) (h : F = G) : IsMinusLerayDiv c G := h ▸ hF

theorem IsMinusLerayDiv.add {c₁ c₂ : Fin 3 → SpatialField} {F₁ F₂ : L2Space}
    (h₁ : IsMinusLerayDiv c₁ F₁) (h₂ : IsMinusLerayDiv c₂ F₂) :
    IsMinusLerayDiv (addColumns c₁ c₂) (F₁ + F₂) := by
  refine ⟨fun j => (h₁.1 j).add (h₂.1 j), fun φ hφ => ?_⟩
  rw [inner_add_left, h₁.2 φ hφ, h₂.2 φ hφ]
  unfold lerayDivPairing addColumns
  have e : ∀ j, toL2 (c₁ j + c₂ j) = toL2 (c₁ j) + toL2 (c₂ j) :=
    fun j => toL2_add' (h₁.1 j) (h₂.1 j)
  simp only [e, inner_add_left, Finset.sum_add_distrib]
  ring

theorem IsMinusLerayDiv.smul {c : Fin 3 → SpatialField} {F : L2Space}
    (h : IsMinusLerayDiv c F) (a : ℝ) :
    IsMinusLerayDiv (fun j => a • c j) (a • F) := by
  refine ⟨fun j => (h.1 j).const_smul a, fun φ hφ => ?_⟩
  rw [real_inner_smul_left, h.2 φ hφ]
  unfold lerayDivPairing
  have e : ∀ j, toL2 (a • c j) = a • toL2 (c j) := fun j => toL2_smul' a (h.1 j)
  simp only [e, real_inner_smul_left, ← Finset.mul_sum]
  ring

theorem IsMinusLerayDiv.neg {c : Fin 3 → SpatialField} {F : L2Space}
    (h : IsMinusLerayDiv c F) : IsMinusLerayDiv (fun j => -c j) (-F) := by
  have := IsMinusLerayDiv.smul h (-1)
  simpa only [neg_one_smul] using this

theorem IsMinusLerayDiv.sub {c₁ c₂ : Fin 3 → SpatialField} {F₁ F₂ : L2Space}
    (h₁ : IsMinusLerayDiv c₁ F₁) (h₂ : IsMinusLerayDiv c₂ F₂) :
    IsMinusLerayDiv (fun j => c₁ j - c₂ j) (F₁ - F₂) := by
  have := IsMinusLerayDiv.add h₁ (IsMinusLerayDiv.neg h₂)
  rw [← sub_eq_add_neg] at this
  refine IsMinusLerayDiv.congr this (fun j => Eventually.of_forall (fun x => ?_))
  simp [addColumns, sub_eq_add_neg]

/-! ## Uniqueness -/

/-- Smooth compactly supported vector fields separate `L²(ℝ³;ℝ³)`. -/
theorem eq_zero_of_forall_vectorTest {F : L2Space}
    (h : ∀ φ, IsVectorTest φ → inner ℝ F (toL2 φ) = 0) : F = 0 := by
  have hint : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (F : SpatialField) x = 0 := by
    intro ψ hs hc
    have hψ : IsSpatialTest ψ := ⟨hs, hc⟩
    apply ext_inner_left ℝ
    intro v
    rw [inner_zero_right, ← pairing_apply ψ hψ v F]
    change inner ℝ (testVector ψ hψ v) F = 0
    have hφ : IsVectorTest (fun x => ψ x • v) :=
      ⟨hs.smul contDiff_const, hc.smul_right⟩
    have hm : MemLp (fun x => ψ x • v) 2 volume :=
      hφ.smooth.continuous.memLp_of_hasCompactSupport hφ.compact
    have heq : toL2 (fun x => ψ x • v) = testVector ψ hψ v := by
      rw [toL2_of_memLp hm]
      rfl
    rw [real_inner_comm, ← heq]
    exact h _ hφ
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp F).locallyIntegrable (by norm_num)) hint
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae

theorem IsMinusLerayDiv.unique {c : Fin 3 → SpatialField} {F₁ F₂ : L2Space}
    (h₁ : IsMinusLerayDiv c F₁) (h₂ : IsMinusLerayDiv c F₂) : F₁ = F₂ := by
  have : F₁ - F₂ = 0 := eq_zero_of_forall_vectorTest (fun φ hφ => by
    rw [inner_sub_left, h₁.2 φ hφ, h₂.2 φ hφ, sub_self])
  exact sub_eq_zero.mp this

/-! ## `X` and its `L²` classes -/

/-- `Xclass` as a bounded operator `X → L²`. -/
def XclassCLM : X →L[ℝ] L2Space := H1.valueCLM.comp Xincl

theorem XclassCLM_apply (f : X) : XclassCLM f = Xclass f := rfl

theorem Xclass_add (f g : X) : Xclass (f + g) = Xclass f + Xclass g := map_add XclassCLM f g
theorem Xclass_sub (f g : X) : Xclass (f - g) = Xclass f - Xclass g := map_sub XclassCLM f g
theorem Xclass_neg (f : X) : Xclass (-f) = -Xclass f := map_neg XclassCLM f
theorem Xclass_smul (a : ℝ) (f : X) : Xclass (a • f) = a • Xclass f := map_smul XclassCLM a f
theorem Xclass_zero : Xclass 0 = 0 := map_zero XclassCLM

theorem Xclass_injective : Function.Injective Xclass := by
  intro f g h
  have h1 : f.toH1 = g.toH1 := H1.value_injective h
  exact Subtype.ext h1

theorem norm_mk_X (F : H1) (hF : F ∈ Xsub) : ‖(show X from ⟨F, hF⟩)‖ = ‖F‖ := rfl

/-! ## Vector-test integration by parts (copied from `Loc/L01Coefficient/Basic.lean`) -/

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

/-! ## Existence for tensors with `H²` columns -/

/-- An `H²` field as an `H¹` field. -/
def h2AsH1 (P : H2) : H1 :=
  H1.ofWeakDerivatives P.value (fun i => P.first i) (fun i => P.hasWeakFirst i)

/-- The `H¹` field `∂ⱼ P` of an `H²` field `P`. -/
def h2PartialH1 (P : H2) (j : Fin 3) : H1 :=
  H1.ofWeakDerivatives (P.first j) (fun i => P.second j i) (fun i => P.hasWeakSecond j i)

theorem norm_h2PartialH1_le (P : H2) (j : Fin 3) : ‖h2PartialH1 P j‖ ≤ ‖P‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [H1.norm_sq, H2.norm_sq]
  simp only [h2PartialH1, H1.value_ofWeakDerivatives, H1.derivative_ofWeakDerivatives]
  have h1 : ‖P.first j‖ ^ 2 ≤ ∑ i : Fin 3, ‖P.first i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖P.first i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ i : Fin 3, ‖P.second j i‖ ^ 2 ≤ ∑ k : Fin 3, ∑ i : Fin 3, ‖P.second k i‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ∑ i : Fin 3, ‖P.second k i‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ j)
  nlinarith [sq_nonneg ‖P.value‖]

/-- `div 𝕋 = ∑ⱼ ∂ⱼ P_j ∈ H¹` for a tensor with `H²` columns `P_j`. -/
def h2DivH1 (P : Fin 3 → H2) : H1 := ∑ j : Fin 3, h2PartialH1 (P j) j

theorem h2DivH1_value (P : Fin 3 → H2) :
    (h2DivH1 P).value = ∑ j : Fin 3, (P j).first j := by
  rw [h2DivH1, ← H1.valueCLM_apply, map_sum]
  rfl

theorem norm_h2DivH1_le (P : Fin 3 → H2) : ‖h2DivH1 P‖ ≤ ∑ j : Fin 3, ‖P j‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_h2PartialH1_le (P j) j))

theorem h1Projection_mem_Xsub (F : H1) : Leray.h1Projection F ∈ Xsub := by
  change H1.valueCLM (Leray.h1Projection F) ∈ Leray.solenoidalSubspace
  rw [H1.valueCLM_apply, Leray.value_h1Projection]
  exact Leray.projection_mem _

/-- `-𝔓 div 𝕋 = -𝔓 ∑ⱼ ∂ⱼ P_j ∈ X` for a tensor with `H²` columns `P_j`. -/
def minusLerayDivX (P : Fin 3 → H2) : X :=
  -(show X from ⟨Leray.h1Projection (h2DivH1 P), h1Projection_mem_Xsub _⟩)

theorem Xclass_minusLerayDivX (P : Fin 3 → H2) :
    Xclass (minusLerayDivX P) = -Leray.projection (∑ j : Fin 3, (P j).first j) := by
  rw [minusLerayDivX, Xclass_neg]
  change -(Leray.h1Projection (h2DivH1 P)).value = _
  rw [Leray.value_h1Projection, h2DivH1_value]

theorem norm_minusLerayDivX_le (P : Fin 3 → H2) : ‖minusLerayDivX P‖ ≤ ∑ j : Fin 3, ‖P j‖ := by
  rw [minusLerayDivX, norm_neg, norm_mk_X]
  exact (Leray.norm_h1Project_le _).trans (norm_h2DivH1_le P)

/-- **Existence for `H²` columns.** If the columns of `𝕋` are (a.e.) the `H²` fields `P_j`,
then `-𝔓 div 𝕋` exists in `X`, with norm at most `∑ⱼ ‖P_j‖_{H²}`. -/
theorem isMinusLerayDiv_minusLerayDivX (P : Fin 3 → H2) (col : Fin 3 → SpatialField)
    (hP : ∀ j, ((P j).value : SpatialField) =ᵐ[volume] col j) :
    IsMinusLerayDiv col (Xclass (minusLerayDivX P)) := by
  have hcol : ColumnsL2 col := fun j => (memLp_congr_ae (hP j)).mp (Lp.memLp _)
  refine ⟨hcol, fun φ hφ => ?_⟩
  rw [Xclass_minusLerayDivX]
  unfold lerayDivPairing
  rw [neg_neg, inner_neg_left, map_sum, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toL2_of_ae_eq_coeFn (hP j), ← Leray.projection_selfadjoint]
  have hval : Leray.projection (P j).value = (Leray.h1Projection (h2AsH1 (P j))).value := rfl
  rw [hval, H1_inner_testPartial _ hφ j, Leray.derivative_h1Projection]
  rfl

/-! ## Bounded operators into `X` from uniqueness -/

/-- **Bounded linear operators.** A tensor depending a.e.-linearly on `x ∈ E`, whose
`-𝔓 div` exists in `X` with norm `≤ C‖x‖`, defines a bounded operator `E → X`. -/
theorem exists_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (col : E → Fin 3 → SpatialField)
    (hadd : ∀ x y j, col (x + y) j =ᵐ[volume] fun z => col x j z + col y j z)
    (hsmul : ∀ (a : ℝ) x j, col (a • x) j =ᵐ[volume] fun z => a • col x j z)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ∃ F : X, IsMinusLerayDiv (col x) (Xclass F) ∧ ‖F‖ ≤ C * ‖x‖) :
    ∃ T : E →L[ℝ] X, (∀ x, IsMinusLerayDiv (col x) (Xclass (T x))) ∧ ‖T‖ ≤ C := by
  choose f hf hfb using h
  let L : E →ₗ[ℝ] X :=
    { toFun := f
      map_add' := fun x y => by
        apply Xclass_injective
        rw [Xclass_add]
        refine IsMinusLerayDiv.unique (hf (x + y)) ?_
        exact IsMinusLerayDiv.congr (IsMinusLerayDiv.add (hf x) (hf y))
          (fun j => (hadd x y j).symm)
      map_smul' := fun a x => by
        apply Xclass_injective
        rw [RingHom.id_apply, Xclass_smul]
        refine IsMinusLerayDiv.unique (hf (a • x)) ?_
        exact IsMinusLerayDiv.congr (IsMinusLerayDiv.smul (hf x) a)
          (fun j => (hsmul a x j).symm) }
  refine ⟨L.mkContinuous C hfb, fun x => hf x, ?_⟩
  exact LinearMap.mkContinuous_norm_le L hC hfb

/-- **Bounded bilinear operators**, as in `exists_clm`. -/
theorem exists_clm₂ {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (col : E → E' → Fin 3 → SpatialField)
    (hadd₁ : ∀ x x' y j, col (x + x') y j =ᵐ[volume] fun z => col x y j z + col x' y j z)
    (hsmul₁ : ∀ (a : ℝ) x y j, col (a • x) y j =ᵐ[volume] fun z => a • col x y j z)
    (hadd₂ : ∀ x y y' j, col x (y + y') j =ᵐ[volume] fun z => col x y j z + col x y' j z)
    (hsmul₂ : ∀ (a : ℝ) x y j, col x (a • y) j =ᵐ[volume] fun z => a • col x y j z)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ∃ F : X, IsMinusLerayDiv (col x y) (Xclass F) ∧ ‖F‖ ≤ C * ‖x‖ * ‖y‖) :
    ∃ T : E →L[ℝ] E' →L[ℝ] X, ∀ x y, IsMinusLerayDiv (col x y) (Xclass (T x y)) := by
  have hrow : ∀ x, ∃ T : E' →L[ℝ] X,
      (∀ y, IsMinusLerayDiv (col x y) (Xclass (T y))) ∧ ‖T‖ ≤ C * ‖x‖ := by
    intro x
    refine exists_clm (col x) (hadd₂ x) (fun a y j => hsmul₂ a x y j)
      (mul_nonneg hC (norm_nonneg x)) (fun y => ?_)
    obtain ⟨F, hF, hFb⟩ := h x y
    exact ⟨F, hF, hFb⟩
  choose T hT hTb using hrow
  let L : E →ₗ[ℝ] (E' →L[ℝ] X) :=
    { toFun := T
      map_add' := fun x x' => by
        ext y
        apply Xclass_injective
        rw [ContinuousLinearMap.add_apply, Xclass_add]
        refine IsMinusLerayDiv.unique (hT (x + x') y) ?_
        exact IsMinusLerayDiv.congr (IsMinusLerayDiv.add (hT x y) (hT x' y))
          (fun j => (hadd₁ x x' y j).symm)
      map_smul' := fun a x => by
        ext y
        apply Xclass_injective
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, Xclass_smul]
        refine IsMinusLerayDiv.unique (hT (a • x) y) ?_
        exact IsMinusLerayDiv.congr (IsMinusLerayDiv.smul (hT x y) a)
          (fun j => (hsmul₁ a x y j).symm) }
  exact ⟨L.mkContinuous C hTb, fun x y => hT x y⟩

end UnforcedLeray.Blueprint.L10
