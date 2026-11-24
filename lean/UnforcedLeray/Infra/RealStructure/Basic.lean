import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Complex.Basic

/-!
# Conjugations (real structures) on complex normed spaces

A *conjugation* on a complex normed space `X` is a conjugate-linear isometric involution
`J : X → X`:
`J (x + y) = J x + J y`, `J (c • x) = conj c • J x`, `‖J x‖ = ‖x‖`, `J (J x) = x`.
Its fixed points form the real closed subspace of *real vectors*; every `x` is uniquely
`x = re x + i • im x` with `re x`, `im x` real.

For the localization of `paper/main.tex` (§ "A right inverse on the ancient interval",
lines 329–380) `X` is the complexification of `H¹_div`, `J` is pointwise complex conjugation
and `T = 𝓜` is the period map, a real operator. This file proves the algebraic part of
"Both projections preserve real fields" (manuscript line 361):

* `Conjugation.conjOp J : (X →L[ℂ] X) ≃ₗᵢ⋆[ℂ] (X →L[ℂ] X)`, `S ↦ J S J`, is a conjugate-linear
  isometric ring automorphism (`conjOp_mul`, `conjOp_one`, `conjOpRingEquiv`);
* `Conjugation.CommutesWith J T : ∀ x, J (T x) = T (J x)`, equivalently `J.conjOp T = T`;
* `conjOp_resolvent`: `J (z - T)⁻¹ J = (conj z - J T J)⁻¹` for every `z` (both sides are
  Mathlib's `resolvent`, i.e. `Ring.inverse`, so no resolvent-set hypothesis is needed);
* `resolvent_apply_conj`: for `T` commuting with `J`,
  `(z - T)⁻¹ (J x) = J ((conj z - T)⁻¹ x)`;
* `conj_mem_resolventSet_iff`, `conj_mem_spectrum_iff`, `image_conj_spectrum`: the resolvent
  set and the spectrum of such `T` are invariant under complex conjugation;
* `fixedSubmodule J : Submodule ℝ X`, closed (`isClosed_fixedSubmodule`), preserved by every
  operator commuting with `J` (`CommutesWith.apply_mem_fixedSubmodule`), with the real
  restriction `CommutesWith.restrictFixed`.

The circle-integral (Riesz projection) statements are in `RealStructure/Riesz.lean`, and the
concrete conjugation of complex `L^p` fields in `RealStructure/Lp.lean`.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate

namespace UnforcedLeray.Infra.RealStructure

/-- A *conjugation* (real structure) on a complex normed space `X`: a conjugate-linear isometric
equivalence `J : X ≃ₗᵢ⋆[ℂ] X` that is an involution, `J (J x) = x`. -/
structure Conjugation (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The underlying conjugate-linear isometric equivalence. -/
  toLinearIsometryEquiv : X ≃ₗᵢ⋆[ℂ] X
  /-- `J` is an involution. -/
  involutive' : ∀ x, toLinearIsometryEquiv (toLinearIsometryEquiv x) = x

namespace Conjugation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

instance : FunLike (Conjugation X) X X where
  coe J := J.toLinearIsometryEquiv
  coe_injective J J' h := by
    cases J; cases J'
    congr
    exact DFunLike.coe_injective h

instance : SemilinearMapClass (Conjugation X) (starRingEnd ℂ) X X where
  map_add J := J.toLinearIsometryEquiv.map_add
  map_smulₛₗ J := J.toLinearIsometryEquiv.map_smulₛₗ

variable (J : Conjugation X)

@[simp] theorem coe_toLinearIsometryEquiv : ⇑J.toLinearIsometryEquiv = ⇑J := rfl

@[ext] theorem ext {J J' : Conjugation X} (h : ∀ x, J x = J' x) : J = J' :=
  DFunLike.ext _ _ h

/-- `J (J x) = x`. -/
@[simp] theorem apply_apply (x : X) : J (J x) = x := J.involutive' x

theorem involutive : Function.Involutive J := J.apply_apply

/-- `J (c • x) = conj c • J x`. -/
theorem map_smul_conj (c : ℂ) (x : X) : J (c • x) = conj c • J x := map_smulₛₗ J c x

/-- `‖J x‖ = ‖x‖`. -/
@[simp] theorem norm_apply (x : X) : ‖J x‖ = ‖x‖ := J.toLinearIsometryEquiv.norm_map x

theorem continuous : Continuous J := J.toLinearIsometryEquiv.continuous

/-- `J` is real-linear: `J (r • x) = r • J x` for `r : ℝ`. -/
theorem map_real_smul (r : ℝ) (x : X) : J (r • x) = r • J x := by
  rw [← Complex.coe_smul, J.map_smul_conj, Complex.conj_ofReal, Complex.coe_smul]

/-- `J (I • x) = -(I • J x)`. -/
theorem map_I_smul (x : X) : J (Complex.I • x) = -(Complex.I • J x) := by
  rw [J.map_smul_conj, Complex.conj_I, neg_smul]

/-- A constructor: a conjugate-linear map that is a norm contraction and an involution is a
conjugation (the involution forces the norm equality and bijectivity). -/
def mk' (L : X →ₛₗ[starRingEnd ℂ] X) (hinv : ∀ x, L (L x) = x) (hnorm : ∀ x, ‖L x‖ ≤ ‖x‖) :
    Conjugation X where
  toLinearIsometryEquiv :=
    { toFun := L
      invFun := L
      map_add' := L.map_add
      map_smul' := L.map_smulₛₗ
      left_inv := hinv
      right_inv := hinv
      norm_map' := fun x => le_antisymm (hnorm x) (by
        calc ‖x‖ = ‖L (L x)‖ := by rw [hinv]
          _ ≤ ‖L x‖ := hnorm _) }
  involutive' := hinv

@[simp] theorem mk'_apply (L : X →ₛₗ[starRingEnd ℂ] X) (hinv : ∀ x, L (L x) = x)
    (hnorm : ∀ x, ‖L x‖ ≤ ‖x‖) (x : X) : mk' L hinv hnorm x = L x := rfl

/-- The conjugation as a real-linear isometric equivalence. -/
def toRealLIE : X ≃ₗᵢ[ℝ] X where
  toFun := J
  invFun := J
  map_add' := map_add J
  map_smul' := J.map_real_smul
  left_inv := J.apply_apply
  right_inv := J.apply_apply
  norm_map' := J.norm_apply

@[simp] theorem toRealLIE_apply (x : X) : J.toRealLIE x = J x := rfl

/-! ### Real vectors -/

/-- The fixed points of `J`, the *real vectors*, as a real subspace. -/
def fixedSubmodule : Submodule ℝ X where
  carrier := {x | J x = x}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [J.map_real_smul, hx]

@[simp] theorem mem_fixedSubmodule {x : X} : x ∈ J.fixedSubmodule ↔ J x = x := Iff.rfl

/-- The real vectors form a closed subspace. -/
theorem isClosed_fixedSubmodule : IsClosed (J.fixedSubmodule : Set X) :=
  isClosed_eq J.continuous continuous_id

/-- The real part `re x = (x + J x) / 2`. -/
def re (x : X) : X := (2 : ℂ)⁻¹ • (x + J x)

/-- The imaginary part `im x = (x - J x) / (2 i)`. -/
def im (x : X) : X := (2 * Complex.I)⁻¹ • (x - J x)

theorem re_mem (x : X) : J.re x ∈ J.fixedSubmodule := by
  simp only [mem_fixedSubmodule, re, J.map_smul_conj, map_add, apply_apply, map_inv₀,
    map_ofNat]
  rw [add_comm]

theorem im_mem (x : X) : J.im x ∈ J.fixedSubmodule := by
  simp only [mem_fixedSubmodule, im, J.map_smul_conj, map_sub, apply_apply, map_inv₀,
    map_mul, map_ofNat, Complex.conj_I]
  rw [← neg_sub x (J x), smul_neg, ← neg_smul, mul_neg, inv_neg, neg_neg]

/-- Every vector is `re x + i • im x` with `re x`, `im x` real. -/
theorem re_add_I_smul_im (x : X) : J.re x + Complex.I • J.im x = x := by
  simp only [re, im, smul_smul]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hI : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
    field_simp
  rw [hI, ← smul_add]
  rw [show x + J x + (x - J x) = (2 : ℂ) • x by rw [two_smul]; abel, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

/-- Uniqueness of the decomposition `x = a + i b` into real vectors. -/
theorem eq_zero_of_add_I_smul_eq_zero {a b : X} (ha : a ∈ J.fixedSubmodule)
    (hb : b ∈ J.fixedSubmodule) (h : a + Complex.I • b = 0) : a = 0 ∧ b = 0 := by
  rw [mem_fixedSubmodule] at ha hb
  have h' : a - Complex.I • b = 0 := by
    have := congrArg J h
    rwa [map_add, J.map_I_smul, ha, hb, map_zero, ← sub_eq_add_neg] at this
  have ha0 : (2 : ℂ) • a = 0 := by
    rw [two_smul]
    calc a + a = (a + Complex.I • b) + (a - Complex.I • b) := by abel
      _ = 0 := by rw [h, h', add_zero]
  have hb0 : (2 * Complex.I) • b = 0 := by
    rw [mul_smul, two_smul]
    calc Complex.I • b + Complex.I • b = (a + Complex.I • b) - (a - Complex.I • b) := by abel
      _ = 0 := by rw [h, h', sub_zero]
  refine ⟨(smul_eq_zero.1 ha0).resolve_left two_ne_zero,
    (smul_eq_zero.1 hb0).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)⟩

/-! ### Conjugating operators: `S ↦ J S J` -/

/-- `J S J` as a complex-linear operator. -/
def conjOpFun (S : X →L[ℂ] X) : X →L[ℂ] X where
  toFun x := J (S (J x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [J.map_smul_conj, map_smul, RingHom.id_apply, Complex.conj_conj]
  cont := J.continuous.comp (S.continuous.comp J.continuous)

@[simp] theorem conjOpFun_apply (S : X →L[ℂ] X) (x : X) : J.conjOpFun S x = J (S (J x)) := rfl

theorem norm_conjOpFun_le (S : X →L[ℂ] X) : ‖J.conjOpFun S‖ ≤ ‖S‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [conjOpFun_apply, norm_apply]
    calc ‖S (J x)‖ ≤ ‖S‖ * ‖J x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [norm_apply]

/-- Conjugation of operators by `J`, `S ↦ J S J`, as a conjugate-linear isometric
equivalence of `X →L[ℂ] X`. It is also multiplicative (`conjOp_mul`, `conjOpRingEquiv`). -/
def conjOp : (X →L[ℂ] X) ≃ₗᵢ⋆[ℂ] (X →L[ℂ] X) where
  toFun := J.conjOpFun
  invFun := J.conjOpFun
  map_add' S T := by ext x; simp
  map_smul' c S := by ext x; simp [J.map_smul_conj]
  left_inv S := by ext x; simp
  right_inv S := by ext x; simp
  norm_map' S := le_antisymm (J.norm_conjOpFun_le S) (by
    calc ‖S‖ = ‖J.conjOpFun (J.conjOpFun S)‖ := by congr 1; ext x; simp
      _ ≤ ‖J.conjOpFun S‖ := J.norm_conjOpFun_le _)

@[simp] theorem conjOp_apply (S : X →L[ℂ] X) (x : X) : J.conjOp S x = J (S (J x)) := rfl

@[simp] theorem conjOp_conjOp (S : X →L[ℂ] X) : J.conjOp (J.conjOp S) = S := by
  ext x; simp

theorem conjOp_mul (S T : X →L[ℂ] X) : J.conjOp (S * T) = J.conjOp S * J.conjOp T := by
  ext x; simp

@[simp] theorem conjOp_one : J.conjOp 1 = 1 := by ext x; simp

theorem conjOp_smul (c : ℂ) (S : X →L[ℂ] X) : J.conjOp (c • S) = conj c • J.conjOp S :=
  map_smulₛₗ J.conjOp c S

theorem conjOp_algebraMap (z : ℂ) :
    J.conjOp (algebraMap ℂ (X →L[ℂ] X) z) = algebraMap ℂ (X →L[ℂ] X) (conj z) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, conjOp_smul, conjOp_one]

/-- `S ↦ J S J` as a ring automorphism of `X →L[ℂ] X`. -/
def conjOpRingEquiv : (X →L[ℂ] X) ≃+* (X →L[ℂ] X) where
  toFun := J.conjOp
  invFun := J.conjOp
  left_inv := J.conjOp_conjOp
  right_inv := J.conjOp_conjOp
  map_mul' := J.conjOp_mul
  map_add' := map_add J.conjOp

@[simp] theorem conjOpRingEquiv_apply (S : X →L[ℂ] X) : J.conjOpRingEquiv S = J.conjOp S := rfl

/-! ### Operators commuting with `J` -/

/-- `T` commutes with the conjugation `J` ("`T` is real"). -/
def CommutesWith (T : X →L[ℂ] X) : Prop := ∀ x, J (T x) = T (J x)

variable {J}

theorem commutesWith_iff_conjOp_eq (T : X →L[ℂ] X) : J.CommutesWith T ↔ J.conjOp T = T := by
  constructor
  · intro h
    ext x
    rw [conjOp_apply, h, apply_apply]
  · intro h x
    have := congrArg (fun S : X →L[ℂ] X => S (J x)) h
    simpa using this

theorem CommutesWith.conjOp_eq {T : X →L[ℂ] X} (hT : J.CommutesWith T) : J.conjOp T = T :=
  (J.commutesWith_iff_conjOp_eq T).1 hT

theorem commutesWith_one : J.CommutesWith 1 := fun _ => rfl

theorem CommutesWith.add {S T : X →L[ℂ] X} (hS : J.CommutesWith S) (hT : J.CommutesWith T) :
    J.CommutesWith (S + T) := fun x => by simp [hS x, hT x]

theorem CommutesWith.sub {S T : X →L[ℂ] X} (hS : J.CommutesWith S) (hT : J.CommutesWith T) :
    J.CommutesWith (S - T) := fun x => by simp [hS x, hT x]

theorem CommutesWith.mul {S T : X →L[ℂ] X} (hS : J.CommutesWith S) (hT : J.CommutesWith T) :
    J.CommutesWith (S * T) := fun x => by simp [hS _, hT x]

theorem CommutesWith.pow {T : X →L[ℂ] X} (hT : J.CommutesWith T) (n : ℕ) :
    J.CommutesWith (T ^ n) := by
  induction n with
  | zero => simpa using J.commutesWith_one
  | succ n ih => rw [pow_succ]; exact ih.mul hT

theorem CommutesWith.real_smul {T : X →L[ℂ] X} (hT : J.CommutesWith T) (r : ℝ) :
    J.CommutesWith ((r : ℂ) • T) := fun x => by
  simp [J.map_real_smul, hT x]

/-- A `J`-commuting operator maps real vectors to real vectors. -/
theorem CommutesWith.apply_mem_fixedSubmodule {T : X →L[ℂ] X} (hT : J.CommutesWith T) {x : X}
    (hx : x ∈ J.fixedSubmodule) : T x ∈ J.fixedSubmodule := by
  rw [mem_fixedSubmodule] at hx ⊢
  rw [hT, hx]

/-- The range of a `J`-commuting operator is `J`-invariant. -/
theorem CommutesWith.apply_mem_range {S : X →L[ℂ] X} (hS : J.CommutesWith S) {x : X}
    (hx : x ∈ LinearMap.range (S : X →ₗ[ℂ] X)) : J x ∈ LinearMap.range (S : X →ₗ[ℂ] X) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨J y, by simp [hS y]⟩

/-- The kernel of a `J`-commuting operator is `J`-invariant. -/
theorem CommutesWith.apply_mem_ker {S : X →L[ℂ] X} (hS : J.CommutesWith S) {x : X}
    (hx : x ∈ LinearMap.ker (S : X →ₗ[ℂ] X)) : J x ∈ LinearMap.ker (S : X →ₗ[ℂ] X) := by
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  rw [← hS, hx, map_zero]

/-- The restriction of a `J`-commuting operator to the real vectors, a real operator. -/
def CommutesWith.restrictFixed {T : X →L[ℂ] X} (hT : J.CommutesWith T) :
    J.fixedSubmodule →L[ℝ] J.fixedSubmodule :=
  ((T.restrictScalars ℝ).comp J.fixedSubmodule.subtypeL).codRestrict J.fixedSubmodule
    fun x => hT.apply_mem_fixedSubmodule x.2

@[simp] theorem CommutesWith.coe_restrictFixed_apply {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (x : J.fixedSubmodule) : (hT.restrictFixed x : X) = T x := rfl

/-! ### Resolvent and spectrum -/

variable (J)

/-- A ring automorphism commutes with `Ring.inverse`. -/
theorem _root_.UnforcedLeray.Infra.RealStructure.ringEquiv_map_ringInverse {A : Type*}
    [Ring A] (f : A ≃+* A) (a : A) : f (Ring.inverse a) = Ring.inverse (f a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hu : f (u : A) = ((Units.map (f : A →* A) u : Aˣ) : A) := rfl
    rw [Ring.inverse_unit, hu, Ring.inverse_unit, ← map_inv]
    rfl
  · have hfa : ¬IsUnit (f a) := by
      intro h
      apply ha
      have := h.map (f.symm : A →* A)
      simpa using this
    rw [Ring.inverse_non_unit a ha, Ring.inverse_non_unit _ hfa, map_zero]

/-- `J (z - S)⁻¹ J = (conj z - J S J)⁻¹`, for every `z` (Mathlib's `resolvent` is
`Ring.inverse`, which is zero off the resolvent set; both sides vanish together). -/
theorem conjOp_resolvent (S : X →L[ℂ] X) (z : ℂ) :
    J.conjOp (resolvent S z) = resolvent (J.conjOp S) (conj z) := by
  have h := ringEquiv_map_ringInverse J.conjOpRingEquiv (algebraMap ℂ (X →L[ℂ] X) z - S)
  simp only [conjOpRingEquiv_apply, map_sub, conjOp_algebraMap] at h
  exact h

variable {J}

/-- For `T` commuting with `J`: `J (z - T)⁻¹ J = (conj z - T)⁻¹`. -/
theorem CommutesWith.conjOp_resolvent {T : X →L[ℂ] X} (hT : J.CommutesWith T) (z : ℂ) :
    J.conjOp (resolvent T z) = resolvent T (conj z) := by
  rw [J.conjOp_resolvent, hT.conjOp_eq]

/-- **Resolvent and conjugation.** For `T` commuting with `J`,
`(z - T)⁻¹ J = J (conj z - T)⁻¹`, i.e. `(z - T)⁻¹ (J x) = J ((conj z - T)⁻¹ x)`. This holds
for every `z ∈ ℂ` (in particular on the resolvent set). -/
theorem CommutesWith.resolvent_apply_conj {T : X →L[ℂ] X} (hT : J.CommutesWith T) (z : ℂ)
    (x : X) : resolvent T z (J x) = J (resolvent T (conj z) x) := by
  have h := congrArg (fun S : X →L[ℂ] X => S (J x)) (hT.conjOp_resolvent (conj z))
  simp only [conjOp_apply, Complex.conj_conj, apply_apply] at h
  exact h.symm

/-- At real `z` the resolvent of a `J`-commuting operator commutes with `J`. -/
theorem CommutesWith.resolvent_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T) {z : ℂ}
    (hz : conj z = z) : J.CommutesWith (resolvent T z) := fun x => by
  rw [hT.resolvent_apply_conj, hz]

variable (J) in
/-- `J` conjugates the resolvent set: `conj z ∈ ρ(J S J) ↔ z ∈ ρ(S)`. -/
theorem conj_mem_resolventSet_conjOp_iff (S : X →L[ℂ] X) (z : ℂ) :
    conj z ∈ resolventSet ℂ (J.conjOp S) ↔ z ∈ resolventSet ℂ S := by
  rw [spectrum.mem_resolventSet_iff, spectrum.mem_resolventSet_iff]
  have h : J.conjOpRingEquiv (algebraMap ℂ (X →L[ℂ] X) z - S) =
      algebraMap ℂ (X →L[ℂ] X) (conj z) - J.conjOp S := by
    simp only [conjOpRingEquiv_apply, map_sub, conjOp_algebraMap]
  rw [← h]
  exact MulEquiv.isUnit_map (J.conjOpRingEquiv : (X →L[ℂ] X) ≃* (X →L[ℂ] X))

/-- **The resolvent set of a real operator is conjugation invariant.** -/
theorem CommutesWith.conj_mem_resolventSet_iff {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (z : ℂ) : conj z ∈ resolventSet ℂ T ↔ z ∈ resolventSet ℂ T := by
  have h := J.conj_mem_resolventSet_conjOp_iff T z
  rwa [hT.conjOp_eq] at h

/-- **The spectrum of a real operator is conjugation invariant.** -/
theorem CommutesWith.conj_mem_spectrum_iff {T : X →L[ℂ] X} (hT : J.CommutesWith T) (z : ℂ) :
    conj z ∈ spectrum ℂ T ↔ z ∈ spectrum ℂ T := by
  exact not_congr (hT.conj_mem_resolventSet_iff z)

/-- The spectrum of a real operator equals its complex conjugate. -/
theorem CommutesWith.image_conj_spectrum {T : X →L[ℂ] X} (hT : J.CommutesWith T) :
    (starRingEnd ℂ) '' spectrum ℂ T = spectrum ℂ T := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hT.conj_mem_spectrum_iff w).2 hw
  · intro hz
    exact ⟨conj z, (hT.conj_mem_spectrum_iff z).2 hz, Complex.conj_conj z⟩

end Conjugation

end UnforcedLeray.Infra.RealStructure
