import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import UnforcedLeray.Infra.RealStructure.Basic
import UnforcedLeray.Infra.AnalyticFredholm.FiniteRank

/-!
# The complexification of a real Hilbert space, for operators

`paper/main.tex`, lines 331-332 and 359-361 (blueprint units B0715, B0716, B1014): the
localization takes the spectrum, the Riesz projection and the exterior inverse of the real period
map `𝓜` on the complexification of `X`, and "both projections preserve real fields". Mathlib has
no complexification of a real normed space. This file builds the one needed for step L6
(`Blueprint/Localization/Linear.lean`, `SpectralSplittingStep`).

For a real inner product space `E`, `Cx E` is `E × E` with the `ℓ²` norm
`‖(x, y)‖² = ‖x‖² + ‖y‖²` and the complex structure `(a + ib)(x, y) = (ax - by, ay + bx)`;
the inner product of `E` makes the norm complex-homogeneous.

## Main declarations
* `Cx E`: a complex normed space, complete when `E` is;
* `cx A : Cx E →L[ℂ] Cx E`, the complexification `A(x + iy) = Ax + iAy` of a real operator;
  it is an injective unital ring homomorphism with `‖cx A‖ ≤ ‖A‖`;
* `cxConj : Conjugation (Cx E)`, `x + iy ↦ x - iy`, with which every `cx A` commutes;
* `rePart B : E →L[ℝ] E`, `x ↦ Re B(x + i0)`, with `‖rePart B‖ ≤ ‖B‖`, `rePart (cx A) = A`,
  and `cx (rePart B) = B` whenever `B` commutes with `cxConj` (`cx_rePart`);
* `isFiniteRank_cx`: the complexification of a real finite-rank operator has finite complex
  rank (used in `L06SpectralSplitting/Outer.lean` to approximate complexified compact operators).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ComplexConjugate

namespace UnforcedLeray.Loc.L06

open UnforcedLeray.Infra.RealStructure UnforcedLeray.Infra.AnalyticFredholm

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The complexification `E ⊕ iE` of a real inner product space, as `E × E` with the `ℓ²` norm
(`paper/main.tex`, line 332). -/
def Cx : Type _ := WithLp 2 (E × E)

instance : NormedAddCommGroup (Cx E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [CompleteSpace E] : CompleteSpace (Cx E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

variable {E}

namespace Cx

/-- `x + iy`. -/
def mk (x y : E) : Cx E := WithLp.toLp 2 (x, y)

/-- The real part. -/
def re (z : Cx E) : E := (WithLp.ofLp (z : WithLp 2 (E × E))).1

/-- The imaginary part. -/
def im (z : Cx E) : E := (WithLp.ofLp (z : WithLp 2 (E × E))).2

@[simp] theorem re_mk (x y : E) : re (mk x y) = x := rfl
@[simp] theorem im_mk (x y : E) : im (mk x y) = y := rfl

theorem mk_re_im (z : Cx E) : mk (re z) (im z) = z := rfl

@[ext] theorem ext {z w : Cx E} (h1 : re z = re w) (h2 : im z = im w) : z = w := by
  rw [← mk_re_im z, ← mk_re_im w, h1, h2]

@[simp] theorem re_add (z w : Cx E) : re (z + w) = re z + re w := rfl
@[simp] theorem im_add (z w : Cx E) : im (z + w) = im z + im w := rfl
@[simp] theorem re_neg (z : Cx E) : re (-z) = -re z := rfl
@[simp] theorem im_neg (z : Cx E) : im (-z) = -im z := rfl
@[simp] theorem re_sub (z w : Cx E) : re (z - w) = re z - re w := rfl
@[simp] theorem im_sub (z w : Cx E) : im (z - w) = im z - im w := rfl
@[simp] theorem re_zero : re (0 : Cx E) = 0 := rfl
@[simp] theorem im_zero : im (0 : Cx E) = 0 := rfl

theorem norm_sq (z : Cx E) : ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (z : WithLp 2 (E × E))

theorem norm_re_le (z : Cx E) : ‖re z‖ ≤ ‖z‖ := by
  have h := norm_sq z
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg ‖im z‖])

theorem norm_mk_zero (x : E) : ‖mk x (0 : E)‖ = ‖x‖ := by
  have h := norm_sq (mk x (0 : E))
  rw [re_mk, im_mk, norm_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)

/-! ### The complex structure -/

instance : SMul ℂ (Cx E) :=
  ⟨fun c z => mk (c.re • re z - c.im • im z) (c.re • im z + c.im • re z)⟩

@[simp] theorem re_smul (c : ℂ) (z : Cx E) : re (c • z) = c.re • re z - c.im • im z := rfl
@[simp] theorem im_smul (c : ℂ) (z : Cx E) : im (c • z) = c.re • im z + c.im • re z := rfl

instance instModule : Module ℂ (Cx E) where
  one_smul z := by ext <;> simp
  mul_smul a b z := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [re_smul, im_smul, re_add, im_add] <;> module
  add_smul a b z := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add, Complex.add_re, Complex.add_im] <;>
      module
  zero_smul z := by ext <;> simp

theorem norm_smul_sq (c : ℂ) (z : Cx E) : ‖c • z‖ ^ 2 = ‖c‖ ^ 2 * ‖z‖ ^ 2 := by
  have hxy : inner ℝ (im z) (re z) = inner ℝ (re z) (im z) := real_inner_comm _ _
  rw [norm_sq, norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real, norm_smul,
    norm_smul, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, hxy, Complex.sq_norm, Complex.normSq_apply,
    Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  ring

instance instNormedSpace : NormedSpace ℂ (Cx E) where
  norm_smul_le c z := by
    have h := norm_smul_sq c z
    rw [← mul_pow] at h
    exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h).le

theorem real_smul_eq (r : ℝ) (z : Cx E) : r • z = mk (r • re z) (r • im z) := by
  have h : r • z = (r : ℂ) • z := (Complex.coe_smul r z).symm
  rw [h]
  ext <;> simp only [re_smul, im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul,
    sub_zero, add_zero, re_mk, im_mk]

@[simp] theorem re_real_smul (r : ℝ) (z : Cx E) : re (r • z) = r • re z := by
  rw [real_smul_eq]; rfl

@[simp] theorem im_real_smul (r : ℝ) (z : Cx E) : im (r • z) = r • im z := by
  rw [real_smul_eq]; rfl

theorem mk_eq_add (x y : E) : mk x y = mk x 0 + Complex.I • mk y 0 := by
  ext <;> simp

/-- The real-linear inclusion `x ↦ x + i0`. -/
def ofReal : E →ₗ[ℝ] Cx E where
  toFun x := mk x 0
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

@[simp] theorem ofReal_apply (x : E) : ofReal x = mk x (0 : E) := rfl

/-! ### Complexified operators -/

/-- The complexification `A(x + iy) = Ax + iAy` of a real operator, as a linear map. -/
def cxₗ (A : E →L[ℝ] E) : Cx E →ₗ[ℂ] Cx E where
  toFun z := mk (A (re z)) (A (im z))
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp [map_sub, map_add, map_smul]

theorem norm_cxₗ_le (A : E →L[ℝ] E) (z : Cx E) : ‖cxₗ A z‖ ≤ ‖A‖ * ‖z‖ := by
  have h1 : ‖cxₗ A z‖ ^ 2 ≤ (‖A‖ * ‖z‖) ^ 2 := by
    rw [norm_sq, mul_pow, norm_sq]
    change ‖A (re z)‖ ^ 2 + ‖A (im z)‖ ^ 2 ≤ ‖A‖ ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
    have ha := A.le_opNorm (re z)
    have hb := A.le_opNorm (im z)
    have ha2 : ‖A (re z)‖ ^ 2 ≤ (‖A‖ * ‖re z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hb2 : ‖A (im z)‖ ^ 2 ≤ (‖A‖ * ‖im z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- The complexification of a real operator (`paper/main.tex`, line 332). -/
def cx (A : E →L[ℝ] E) : Cx E →L[ℂ] Cx E :=
  (cxₗ A).mkContinuous ‖A‖ (norm_cxₗ_le A)

@[simp] theorem re_cx (A : E →L[ℝ] E) (z : Cx E) : re (cx A z) = A (re z) := rfl
@[simp] theorem im_cx (A : E →L[ℝ] E) (z : Cx E) : im (cx A z) = A (im z) := rfl

theorem norm_cx_le (A : E →L[ℝ] E) : ‖cx A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

@[simp] theorem cx_one : cx (1 : E →L[ℝ] E) = 1 := by
  ext z <;> rfl

@[simp] theorem cx_mul (A B : E →L[ℝ] E) : cx (A * B) = cx A * cx B := by
  ext z <;> rfl

@[simp] theorem cx_add (A B : E →L[ℝ] E) : cx (A + B) = cx A + cx B := by
  ext z <;> rfl

@[simp] theorem cx_sub (A B : E →L[ℝ] E) : cx (A - B) = cx A - cx B := by
  ext z <;> rfl

@[simp] theorem cx_pow (A : E →L[ℝ] E) (n : ℕ) : cx (A ^ n) = cx A ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, cx_mul, ih, pow_succ]

theorem cx_injective : Function.Injective (cx : (E →L[ℝ] E) → (Cx E →L[ℂ] Cx E)) := by
  intro A B h
  ext x
  have := congrArg (fun T => re (T (mk x 0))) h
  simpa using this

/-! ### The conjugation and real parts of complex operators -/

/-- `x + iy ↦ x - iy`, as a conjugate-linear map. -/
def conjₛₗ : Cx E →ₛₗ[starRingEnd ℂ] Cx E where
  toFun z := mk (re z) (-im z)
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' c z := by
    ext <;> simp only [re_smul, im_smul, re_mk, im_mk, starRingEnd_apply] <;> simp <;> module

/-- The conjugation `x + iy ↦ x - iy` of the complexification (`paper/main.tex`, line 361). -/
def cxConj : Conjugation (Cx E) :=
  Conjugation.mk' conjₛₗ (fun z => by ext <;> simp [conjₛₗ]) (fun z => by
    refine le_of_eq ?_
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_sq, norm_sq]
    simp [conjₛₗ])

@[simp] theorem cxConj_apply (z : Cx E) : cxConj z = mk (re z) (-im z) := rfl

theorem cx_commutesWith (A : E →L[ℝ] E) : cxConj.CommutesWith (cx A) := by
  intro z
  ext <;> simp

/-- The real part `x ↦ Re B(x + i0)` of a complex operator. -/
def rePartₗ (B : Cx E →L[ℂ] Cx E) : E →ₗ[ℝ] E where
  toFun x := re (B (mk x 0))
  map_add' x y := by
    have : mk (x + y) (0 : E) = mk x 0 + mk y 0 := by ext <;> simp
    rw [this, map_add, re_add]
  map_smul' r x := by
    have : mk (r • x) (0 : E) = (r : ℂ) • mk x 0 := by ext <;> simp
    rw [this, map_smul, re_smul]
    simp

theorem norm_rePartₗ_le (B : Cx E →L[ℂ] Cx E) (x : E) : ‖rePartₗ B x‖ ≤ ‖B‖ * ‖x‖ := by
  change ‖re (B (mk x 0))‖ ≤ ‖B‖ * ‖x‖
  calc ‖re (B (mk x 0))‖ ≤ ‖B (mk x 0)‖ := norm_re_le _
    _ ≤ ‖B‖ * ‖mk x (0 : E)‖ := B.le_opNorm _
    _ = ‖B‖ * ‖x‖ := by rw [norm_mk_zero]

/-- The real part of a complex operator, a real operator. -/
def rePart (B : Cx E →L[ℂ] Cx E) : E →L[ℝ] E :=
  (rePartₗ B).mkContinuous ‖B‖ (norm_rePartₗ_le B)

theorem rePart_apply (B : Cx E →L[ℂ] Cx E) (x : E) : rePart B x = re (B (mk x 0)) := rfl

theorem norm_rePart_le (B : Cx E →L[ℂ] Cx E) : ‖rePart B‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

@[simp] theorem rePart_cx (A : E →L[ℝ] E) : rePart (cx A) = A := by
  ext x
  rfl

/-- An operator commuting with the conjugation is the complexification of its real part. -/
theorem cx_rePart {B : Cx E →L[ℂ] Cx E} (hB : cxConj.CommutesWith B) : cx (rePart B) = B := by
  have him : ∀ x : E, im (B (mk x 0)) = 0 := by
    intro x
    have h := hB (mk x 0)
    have hc : cxConj (mk x (0 : E)) = mk x 0 := by ext <;> simp
    rw [hc] at h
    have h2 := congrArg im h
    simp only [cxConj_apply, im_mk] at h2
    have : (2 : ℝ) • im (B (mk x 0)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h2]
      simp
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hreal : ∀ x : E, B (mk x 0) = mk (rePart B x) 0 := by
    intro x
    ext
    · rfl
    · simp [him x]
  ext z : 1
  rw [← mk_re_im z, mk_eq_add]
  simp only [map_add, map_smul, hreal]
  ext <;> simp

/-- Real operators whose complexifications agree are equal; used with `cx_rePart`. -/
theorem rePart_eq_of_cx_eq {A : E →L[ℝ] E} {B : Cx E →L[ℂ] Cx E} (h : cx A = B) :
    rePart B = A := by
  rw [← h, rePart_cx]

/-! ### Approximability of complexified compact operators -/

/-- The complexification of a real finite-rank operator has finite complex rank. -/
theorem isFiniteRank_cx {F : E →L[ℝ] E}
    (hF : FiniteDimensional ℝ (LinearMap.range (F : E →ₗ[ℝ] E))) : IsFiniteRank (cx F) := by
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).2 hF
  set W : Submodule ℂ (Cx E) := Submodule.span ℂ (ofReal '' (s : Set E))
  have hW : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image _)
  have hmem : ∀ x : E, F x ∈ LinearMap.range (F : E →ₗ[ℝ] E) → ofReal (F x) ∈ W := by
    intro x hx
    rw [← hs] at hx
    have h1 : ofReal (F x) ∈ Submodule.span ℝ (ofReal '' (s : Set E)) :=
      Submodule.image_span_subset_span ofReal _ ⟨F x, hx, rfl⟩
    exact Submodule.span_le_restrictScalars ℝ ℂ _ h1
  have hle : LinearMap.range ((cx F : Cx E →L[ℂ] Cx E) : Cx E →ₗ[ℂ] Cx E) ≤ W := by
    rintro _ ⟨z, rfl⟩
    have hz : (cx F z) = ofReal (F (re z)) + Complex.I • ofReal (F (im z)) := by
      ext <;> simp
    change cx F z ∈ W
    rw [hz]
    exact W.add_mem (hmem _ ⟨_, rfl⟩) (W.smul_mem _ (hmem _ ⟨_, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

end Cx

end UnforcedLeray.Loc.L06
