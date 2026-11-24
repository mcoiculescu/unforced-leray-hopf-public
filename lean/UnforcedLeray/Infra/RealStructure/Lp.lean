import UnforcedLeray.Infra.RealStructure.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete conjugations: `ℂ`, invariant subspaces, `PiLp` products and `L^p` fields

This file builds the conjugations used for complexified velocity fields.

* `Conjugation.complex`: complex conjugation on `ℂ`;
* `Conjugation.restrict`: the restriction of a conjugation to a `J`-invariant complex subspace
  (for instance a divergence-free or Sobolev subspace of an `L²` space), with
  `mem_fixedSubmodule_restrict_iff`;
* `Conjugation.piLp`: the componentwise conjugation on a finite `PiLp p` product (the ambient
  space `PiLp 2 (fun _ : Fin 4 => L²)` of an `H¹` graph norm, or `EuclideanSpace ℂ ι`), with
  `mem_fixedSubmodule_piLp_iff`;
* `Conjugation.euclidean ι`: pointwise complex conjugation on `EuclideanSpace ℂ ι`; its real
  vectors are those with real coordinates (`mem_fixedSubmodule_euclidean_iff`);
* `Conjugation.lp J p μ`: the pointwise conjugation `f ↦ J ∘ f` on `Lp E p μ`, with
  `coeFn_lp` and `mem_fixedSubmodule_lp_iff` (`f` is real iff `f a` is real for a.e. `a`);
* `Conjugation.lpEuclidean ι p μ` on `Lp (EuclideanSpace ℂ ι) p μ` (the case
  `ι = Fin 3`, `p = 2` is complex-valued `L²` velocity fields): a field is real iff its
  coordinates are a.e. real (`mem_fixedSubmodule_lpEuclidean_iff`), and the real fields are
  exactly the complexifications of real-valued fields `Lp (EuclideanSpace ℝ ι) p μ`
  (`mem_fixedSubmodule_lpEuclidean_iff_exists`, `complexifyLp`, `norm_complexifyLp`,
  `complexifyLp_injective`, and the real-linear isometric equivalence `realFieldsEquiv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate NNReal

namespace UnforcedLeray.Infra.RealStructure

namespace Conjugation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

@[simp] theorem nnnorm_apply (J : Conjugation X) (x : X) : ‖J x‖₊ = ‖x‖₊ :=
  NNReal.eq (J.norm_apply x)

/-- The conjugation as a continuous conjugate-linear map. -/
def toCLM (J : Conjugation X) : X →SL[starRingEnd ℂ] X :=
  (J.toLinearIsometryEquiv.toContinuousLinearEquiv : X →SL[starRingEnd ℂ] X)

@[simp] theorem toCLM_apply (J : Conjugation X) (x : X) : J.toCLM x = J x := rfl

/-! ### Complex conjugation on `ℂ` -/

/-- Complex conjugation on `ℂ`. -/
def complex : Conjugation ℂ :=
  mk' { toFun := fun z => conj z
        map_add' := map_add _
        map_smul' := fun c z => by simp [smul_eq_mul] }
    (fun z => Complex.conj_conj z) (fun z => le_of_eq (Complex.norm_conj z))

@[simp] theorem complex_apply (z : ℂ) : complex z = conj z := rfl

theorem mem_fixedSubmodule_complex_iff {z : ℂ} : z ∈ complex.fixedSubmodule ↔ z.im = 0 := by
  rw [mem_fixedSubmodule, complex_apply, Complex.conj_eq_iff_im]

/-! ### Restriction to an invariant subspace -/

/-- The conjugate-linear map underlying `Conjugation.restrict`. -/
def restrictₛₗ (J : Conjugation X) (V : Submodule ℂ X) (hV : ∀ x ∈ V, J x ∈ V) :
    V →ₛₗ[starRingEnd ℂ] V where
  toFun x := ⟨J (x : X), hV (x : X) x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp [J.map_smul_conj]

/-- The restriction of a conjugation to a `J`-invariant complex subspace. -/
def restrict (J : Conjugation X) (V : Submodule ℂ X) (hV : ∀ x ∈ V, J x ∈ V) :
    Conjugation V :=
  mk' (J.restrictₛₗ V hV)
    (fun x => Subtype.ext (J.apply_apply (x : X)))
    (fun x => le_of_eq (by
      change ‖J (x : X)‖ = ‖(x : X)‖
      exact J.norm_apply x))

@[simp] theorem coe_restrict_apply (J : Conjugation X) (V : Submodule ℂ X)
    (hV : ∀ x ∈ V, J x ∈ V) (x : V) : (J.restrict V hV x : X) = J x := rfl

theorem mem_fixedSubmodule_restrict_iff (J : Conjugation X) (V : Submodule ℂ X)
    (hV : ∀ x ∈ V, J x ∈ V) (x : V) :
    x ∈ (J.restrict V hV).fixedSubmodule ↔ (x : X) ∈ J.fixedSubmodule := by
  rw [mem_fixedSubmodule, mem_fixedSubmodule, ← Subtype.coe_inj, coe_restrict_apply]

/-- The restriction of an operator to an invariant closed or non-closed complex subspace. -/
def restrictOp (V : Submodule ℂ X) (T : X →L[ℂ] X) (hT : ∀ x ∈ V, T x ∈ V) : V →L[ℂ] V :=
  (T.comp V.subtypeL).codRestrict V fun x => hT x x.2

@[simp] theorem coe_restrictOp_apply (V : Submodule ℂ X) (T : X →L[ℂ] X)
    (hT : ∀ x ∈ V, T x ∈ V) (x : V) : (restrictOp V T hT x : X) = T x := rfl

/-- An operator commuting with `J` and preserving a `J`-invariant subspace `V` restricts to an
operator on `V` commuting with the restricted conjugation. -/
theorem CommutesWith.restrictOp {J : Conjugation X} {T : X →L[ℂ] X} (hJT : J.CommutesWith T)
    (V : Submodule ℂ X) (hV : ∀ x ∈ V, J x ∈ V) (hT : ∀ x ∈ V, T x ∈ V) :
    (J.restrict V hV).CommutesWith (Conjugation.restrictOp V T hT) := fun x => by
  apply Subtype.ext
  simp only [coe_restrict_apply, coe_restrictOp_apply]
  exact hJT x

/-! ### Finite `PiLp` products -/

section PiLp

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
  [∀ i, NormedSpace ℂ (β i)]

/-- The componentwise conjugation is isometric on `PiLp p β`. -/
theorem norm_piLp_map (p : ℝ≥0∞) [Fact (1 ≤ p)] (J : ∀ i, Conjugation (β i)) (x : PiLp p β) :
    ‖WithLp.toLp p (fun i => J i (x i))‖ = ‖x‖ := by
  obtain ⟨y, rfl⟩ := (WithLp.equiv p (∀ i, β i)).symm.surjective x
  obtain rfl | hp := p.dichotomy
  · simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, PiLp.norm_toLp, Pi.norm_def,
      nnnorm_apply]
  · have : 0 < p.toReal := zero_lt_one.trans_le hp
    simp only [PiLp.norm_eq_sum this, WithLp.equiv_symm_apply, PiLp.toLp_apply, norm_apply]

/-- The componentwise conjugation on a finite `PiLp p` product. -/
def piLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (J : ∀ i, Conjugation (β i)) : Conjugation (PiLp p β) :=
  mk' { toFun := fun x => WithLp.toLp p (fun i => J i (x i))
        map_add' := fun x y => by ext i; simp
        map_smul' := fun c x => by ext i; simp [map_smul_conj] }
    (fun x => by ext i; simp)
    (fun x => le_of_eq (norm_piLp_map p J x))

@[simp] theorem piLp_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (J : ∀ i, Conjugation (β i))
    (x : PiLp p β) (i : ι) : piLp p J x i = J i (x i) := rfl

theorem mem_fixedSubmodule_piLp_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] (J : ∀ i, Conjugation (β i))
    (x : PiLp p β) : x ∈ (piLp p J).fixedSubmodule ↔ ∀ i, x i ∈ (J i).fixedSubmodule := by
  simp only [mem_fixedSubmodule]
  constructor
  · intro h i
    have := congrArg (fun y : PiLp p β => y i) h
    simpa using this
  · intro h
    ext i
    simpa using h i

end PiLp

/-! ### Euclidean space -/

section Euclidean

variable (ι : Type*) [Fintype ι]

/-- Pointwise complex conjugation on `EuclideanSpace ℂ ι`. -/
def euclidean : Conjugation (EuclideanSpace ℂ ι) :=
  piLp 2 (fun _ => complex)

variable {ι}

@[simp] theorem euclidean_apply (x : EuclideanSpace ℂ ι) (i : ι) :
    euclidean ι x i = conj (x i) := rfl

/-- The real vectors of `EuclideanSpace ℂ ι` are those with real coordinates. -/
theorem mem_fixedSubmodule_euclidean_iff (x : EuclideanSpace ℂ ι) :
    x ∈ (euclidean ι).fixedSubmodule ↔ ∀ i, (x i).im = 0 := by
  rw [euclidean, mem_fixedSubmodule_piLp_iff]
  simp only [mem_fixedSubmodule_complex_iff]

end Euclidean

/-! ### `L^p` fields -/

section Lp

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The pointwise conjugation `f ↦ J ∘ f` on `Lp E p μ`. -/
def lp (J : Conjugation E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) :
    Conjugation (Lp E p μ) :=
  mk' (J.toCLM.compLpₗ p μ)
    (fun f => by
      apply Lp.ext
      simp only [ContinuousLinearMap.compLpₗ_apply]
      filter_upwards [J.toCLM.coeFn_compLp (J.toCLM.compLp f), J.toCLM.coeFn_compLp f]
        with a h1 h2
      rw [h1, toCLM_apply, h2, toCLM_apply, apply_apply])
    (fun f => by
      simp only [ContinuousLinearMap.compLpₗ_apply]
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [J.toCLM.coeFn_compLp f] with a h1
      rw [h1, toCLM_apply, norm_apply])

variable (J : Conjugation E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)

/-- `J.lp p μ f = J ∘ f` almost everywhere. -/
theorem coeFn_lp (f : Lp E p μ) : ⇑(J.lp p μ f) =ᵐ[μ] fun a => J (f a) :=
  J.toCLM.coeFn_compLp f

/-- A field is real for the pointwise conjugation iff its values are a.e. real. -/
theorem mem_fixedSubmodule_lp_iff (f : Lp E p μ) :
    f ∈ (J.lp p μ).fixedSubmodule ↔ ∀ᵐ a ∂μ, f a ∈ J.fixedSubmodule := by
  rw [mem_fixedSubmodule]
  constructor
  · intro h
    have h' : ⇑(J.lp p μ f) =ᵐ[μ] f := by rw [h]
    filter_upwards [J.coeFn_lp p μ f, h'] with a h1 h2
    rw [mem_fixedSubmodule, ← h1, h2]
  · intro h
    apply Lp.ext
    filter_upwards [J.coeFn_lp p μ f, h] with a h1 h2
    rw [h1, (mem_fixedSubmodule J).1 h2]

end Lp

/-! ### Complex-valued vector fields `Lp (EuclideanSpace ℂ ι) p μ` -/

section LpEuclidean

variable {α : Type*} [MeasurableSpace α] (ι : Type*) [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (μ : Measure α)

/-- Pointwise complex conjugation of complex vector fields `Lp (EuclideanSpace ℂ ι) p μ`. -/
def lpEuclidean : Conjugation (Lp (EuclideanSpace ℂ ι) p μ) :=
  (euclidean ι).lp p μ

variable {ι p μ}

theorem coeFn_lpEuclidean (f : Lp (EuclideanSpace ℂ ι) p μ) :
    ∀ᵐ a ∂μ, ∀ i, lpEuclidean ι p μ f a i = conj (f a i) := by
  filter_upwards [(euclidean ι).coeFn_lp p μ f] with a h i
  rw [lpEuclidean, h, euclidean_apply]

/-- A complex vector field is real (fixed by pointwise conjugation) iff its coordinates are
a.e. real. -/
theorem mem_fixedSubmodule_lpEuclidean_iff (f : Lp (EuclideanSpace ℂ ι) p μ) :
    f ∈ (lpEuclidean ι p μ).fixedSubmodule ↔ ∀ᵐ a ∂μ, ∀ i, (f a i).im = 0 := by
  rw [lpEuclidean, mem_fixedSubmodule_lp_iff]
  simp only [mem_fixedSubmodule_euclidean_iff]

variable (ι) in
/-- The complexification `x ↦ x + 0 i` of real vectors. -/
def ofRealEuclidean : EuclideanSpace ℝ ι →+ EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype ι] in
@[simp] theorem ofRealEuclidean_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    ofRealEuclidean ι x i = (x i : ℂ) := rfl

theorem norm_ofRealEuclidean (x : EuclideanSpace ℝ ι) : ‖ofRealEuclidean ι x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [ofRealEuclidean_apply, Complex.norm_real]

/-- The real part of complex vectors, coordinatewise. -/
def reEuclidean : EuclideanSpace ℂ ι →+ EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => (x i).re)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype ι] in
@[simp] theorem reEuclidean_apply (x : EuclideanSpace ℂ ι) (i : ι) :
    reEuclidean x i = (x i).re := rfl

theorem norm_reEuclidean_le (x : EuclideanSpace ℂ ι) : ‖reEuclidean x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [reEuclidean_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

theorem lipschitzWith_ofRealEuclidean : LipschitzWith 1 (ofRealEuclidean ι) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (ofRealEuclidean ι) 1 fun x => by
    rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, norm_ofRealEuclidean]

theorem lipschitzWith_reEuclidean : LipschitzWith 1 (reEuclidean (ι := ι)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (reEuclidean (ι := ι)) 1 fun x => by
    rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    exact norm_reEuclidean_le x

/-- The complexification of a real vector field `g ∈ Lp (EuclideanSpace ℝ ι) p μ`. -/
def complexifyLp (g : Lp (EuclideanSpace ℝ ι) p μ) : Lp (EuclideanSpace ℂ ι) p μ :=
  lipschitzWith_ofRealEuclidean.compLp (map_zero _) g

/-- The coordinatewise real part of a complex vector field. -/
def reLp (f : Lp (EuclideanSpace ℂ ι) p μ) : Lp (EuclideanSpace ℝ ι) p μ :=
  lipschitzWith_reEuclidean.compLp (map_zero _) f

omit [Fact (1 ≤ p)] in
theorem coeFn_complexifyLp (g : Lp (EuclideanSpace ℝ ι) p μ) :
    complexifyLp g =ᵐ[μ] fun a => ofRealEuclidean ι (g a) :=
  LipschitzWith.coeFn_compLp _ _ _

omit [Fact (1 ≤ p)] in
theorem coeFn_reLp (f : Lp (EuclideanSpace ℂ ι) p μ) :
    reLp f =ᵐ[μ] fun a => reEuclidean (f a) :=
  LipschitzWith.coeFn_compLp _ _ _

omit [Fact (1 ≤ p)] in
/-- Complexification is isometric. -/
theorem norm_complexifyLp (g : Lp (EuclideanSpace ℝ ι) p μ) : ‖complexifyLp g‖ = ‖g‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [coeFn_complexifyLp g] with a h
    rw [h, norm_ofRealEuclidean]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [coeFn_complexifyLp g] with a h
    rw [h, norm_ofRealEuclidean]

omit [Fact (1 ≤ p)] in
theorem reLp_complexifyLp (g : Lp (EuclideanSpace ℝ ι) p μ) : reLp (complexifyLp g) = g := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (complexifyLp g), coeFn_complexifyLp g] with a h1 h2
  rw [h1, h2]
  ext i
  simp

omit [Fact (1 ≤ p)] in
theorem complexifyLp_injective :
    Function.Injective (complexifyLp : Lp (EuclideanSpace ℝ ι) p μ → _) :=
  Function.LeftInverse.injective reLp_complexifyLp

omit [Fact (1 ≤ p)] in
theorem complexifyLp_add (g h : Lp (EuclideanSpace ℝ ι) p μ) :
    complexifyLp (g + h) = complexifyLp g + complexifyLp h := by
  apply Lp.ext
  filter_upwards [coeFn_complexifyLp (g + h), coeFn_complexifyLp g, coeFn_complexifyLp h,
    Lp.coeFn_add g h, Lp.coeFn_add (complexifyLp g) (complexifyLp h)] with a h1 h2 h3 h4 h5
  rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, map_add]

/-- Complexified real fields are real. -/
theorem complexifyLp_mem_fixedSubmodule (g : Lp (EuclideanSpace ℝ ι) p μ) :
    complexifyLp g ∈ (lpEuclidean ι p μ).fixedSubmodule := by
  rw [mem_fixedSubmodule_lpEuclidean_iff]
  filter_upwards [coeFn_complexifyLp g] with a h i
  rw [h, ofRealEuclidean_apply, Complex.ofReal_im]

/-- A real complex field is the complexification of its real part. -/
theorem complexifyLp_reLp {f : Lp (EuclideanSpace ℂ ι) p μ}
    (hf : f ∈ (lpEuclidean ι p μ).fixedSubmodule) : complexifyLp (reLp f) = f := by
  rw [mem_fixedSubmodule_lpEuclidean_iff] at hf
  apply Lp.ext
  filter_upwards [coeFn_complexifyLp (reLp f), coeFn_reLp f, hf] with a h1 h2 h3
  rw [h1, h2]
  ext i
  rw [ofRealEuclidean_apply, reEuclidean_apply]
  exact Complex.ext rfl (by rw [Complex.ofReal_im, h3 i])

/-- **Real fields are the fixed points of pointwise conjugation.** A complex vector field
`f ∈ Lp (EuclideanSpace ℂ ι) p μ` is fixed by pointwise complex conjugation iff it is the
complexification of a real vector field `g ∈ Lp (EuclideanSpace ℝ ι) p μ`; this `g` is unique
(`complexifyLp_injective`) and `‖complexifyLp g‖ = ‖g‖`. -/
theorem mem_fixedSubmodule_lpEuclidean_iff_exists (f : Lp (EuclideanSpace ℂ ι) p μ) :
    f ∈ (lpEuclidean ι p μ).fixedSubmodule ↔ ∃ g : Lp (EuclideanSpace ℝ ι) p μ,
      complexifyLp g = f := by
  constructor
  · intro hf
    exact ⟨reLp f, complexifyLp_reLp hf⟩
  · rintro ⟨g, rfl⟩
    exact complexifyLp_mem_fixedSubmodule g

variable (ι p μ) in
/-- **Real fields as a real Banach space.** The real-valued fields `Lp (EuclideanSpace ℝ ι) p μ`
are real-linearly isometrically equivalent, by complexification, to the fixed points of
pointwise complex conjugation on `Lp (EuclideanSpace ℂ ι) p μ`. -/
def realFieldsEquiv :
    Lp (EuclideanSpace ℝ ι) p μ ≃ₗᵢ[ℝ] (lpEuclidean ι p μ).fixedSubmodule where
  toFun g := ⟨complexifyLp g, complexifyLp_mem_fixedSubmodule g⟩
  invFun f := reLp (f : Lp (EuclideanSpace ℂ ι) p μ)
  map_add' g h := Subtype.ext (complexifyLp_add g h)
  map_smul' r g := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Submodule.coe_smul]
    rw [← Complex.coe_smul]
    apply Lp.ext
    filter_upwards [coeFn_complexifyLp (r • g), Lp.coeFn_smul r g,
      Lp.coeFn_smul (r : ℂ) (complexifyLp g), coeFn_complexifyLp g] with a h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, Pi.smul_apply, h4]
    ext i
    simp
  left_inv g := reLp_complexifyLp g
  right_inv f := Subtype.ext (complexifyLp_reLp f.2)
  norm_map' g := norm_complexifyLp g

@[simp] theorem coe_realFieldsEquiv_apply (g : Lp (EuclideanSpace ℝ ι) p μ) :
    (realFieldsEquiv ι p μ g : Lp (EuclideanSpace ℂ ι) p μ) = complexifyLp g := rfl

end LpEuclidean

end Conjugation

end UnforcedLeray.Infra.RealStructure
