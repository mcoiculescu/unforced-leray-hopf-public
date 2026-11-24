import UnforcedLeray.Infra.RealStructure.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Riesz projections of real operators preserve real vectors

Let `J` be a conjugation on a complex normed space `X` and `T : X →L[ℂ] X` an operator commuting
with `J`. This file proves manuscript line 361 of `paper/main.tex`, "Both projections preserve
real fields", for the Riesz integral over any circle centred on the real axis.

* `semilinearLIE_circleIntegral`: for a conjugate-linear isometric equivalence `L` of a complex
  normed space `E` and any `f : ℂ → E`,
  `L (∮_{C(c,R)} f) = -∮_{C(conj c,R)} L (f (conj z)) dz`
  (conjugation reverses the orientation; no integrability hypothesis is needed because `L` is
  an isometric equivalence);
* `rieszIntegral T c r = (2πi)⁻¹ ∮_{C(c,r)} (z - T)⁻¹ dz` (Mathlib's `resolvent`);
* `CommutesWith.conjOp_rieszIntegral`: `J P_{c,r} J = P_{conj c, r}`;
* `CommutesWith.rieszIntegral_commutesWith`, `…_zero_commutesWith`: for a real centre `c`
  (in particular `c = 0`) the Riesz integral `P_-` commutes with `J`, hence so does
  `P_+ = 1 - P_-` (`CommutesWith.one_sub_rieszIntegral_commutesWith`), and both map real vectors
  to real vectors (`rieszIntegral_mem_fixedSubmodule`, `one_sub_rieszIntegral_mem_fixedSubmodule`).

The same holds for any Dunford integral `(2πi)⁻¹ ∮ f(z) (z - T)⁻¹ dz` with `f` real on real
arguments, `conj (f (conj z)) = f z` (`CommutesWith.conjOp_dunfordIntegral`).

None of these statements needs the circle to avoid the spectrum: Mathlib's resolvent is
`Ring.inverse`, and the identities hold for the integral as defined. The projection property
of `rieszIntegral` (when the circle lies in the resolvent set) is not proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate

namespace UnforcedLeray.Infra.RealStructure

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A conjugate-linear isometric equivalence, viewed as a real-linear isometric equivalence. -/
def realLIEOfConj (L : E ≃ₗᵢ⋆[ℂ] E) : E ≃ₗᵢ[ℝ] E where
  toFun := L
  invFun := L.symm
  map_add' := map_add L
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
  left_inv := L.symm_apply_apply
  right_inv := L.apply_symm_apply
  norm_map' := L.norm_map

@[simp] theorem realLIEOfConj_apply (L : E ≃ₗᵢ⋆[ℂ] E) (x : E) : realLIEOfConj L x = L x := rfl

/-- A conjugate-linear isometric equivalence commutes with interval integrals (no integrability
hypothesis). -/
theorem semilinearLIE_intervalIntegral (L : E ≃ₗᵢ⋆[ℂ] E) (f : ℝ → E) (a b : ℝ)
    (μ : Measure ℝ) : L (∫ θ in a..b, f θ ∂μ) = ∫ θ in a..b, L (f θ) ∂μ := by
  have h := fun s : Set ℝ =>
    ((realLIEOfConj L).toContinuousLinearEquiv.integral_comp_comm (μ := μ.restrict s) f)
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, realLIEOfConj_apply] at h
  simp only [intervalIntegral, map_sub, h]

/-- **Conjugation of a circle integral.** For a conjugate-linear isometric equivalence `L` and
any `f : ℂ → E`, `L (∮_{|z-c|=R} f(z) dz) = -∮_{|z-conj c|=R} L (f (conj z)) dz`. -/
theorem semilinearLIE_circleIntegral (L : E ≃ₗᵢ⋆[ℂ] E) (f : ℂ → E) (c : ℂ) (R : ℝ) :
    L (∮ z in C(c, R), f z) = -∮ z in C(conj c, R), L (f (conj z)) := by
  simp only [circleIntegral]
  rw [semilinearLIE_intervalIntegral]
  set g : ℝ → E := fun θ =>
    deriv (circleMap (conj c) R) θ • L (f (conj (circleMap (conj c) R θ))) with hg_def
  have key : ∀ θ : ℝ, L (deriv (circleMap c R) θ • f (circleMap c R θ)) = -g (-θ) := by
    intro θ
    have h2 : circleMap c R θ = conj (circleMap (conj c) R (-θ)) := by
      rw [← conj_circleMap, Complex.conj_conj]
    simp only [hg_def]
    rw [map_smulₛₗ, deriv_circleMap, deriv_circleMap, ← h2, map_mul, conj_circleMap_zero,
      Complex.conj_I, mul_neg, neg_smul]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_zero]
  congr 1
  have hg : Function.Periodic g (2 * π) := by
    intro θ
    simp only [hg_def, deriv_circleMap, periodic_circleMap _ _ θ]
  have := hg.intervalIntegral_add_eq (-(2 * π)) 0
  simpa only [neg_add_cancel, zero_add] using this

end General

namespace Conjugation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `conj ((2πi)⁻¹) = -(2πi)⁻¹`. -/
theorem conj_two_pi_I_inv : conj ((2 * π * Complex.I)⁻¹ : ℂ) = -(2 * π * Complex.I)⁻¹ := by
  rw [map_inv₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, mul_neg,
    inv_neg]

variable (J : Conjugation X)

/-- `J (∮_{C(c,R)} F) J = -∮_{C(conj c,R)} J F(conj z) J dz` for operator-valued `F`. -/
theorem conjOp_circleIntegral (F : ℂ → X →L[ℂ] X) (c : ℂ) (R : ℝ) :
    J.conjOp (∮ z in C(c, R), F z) = -∮ z in C(conj c, R), J.conjOp (F (conj z)) :=
  semilinearLIE_circleIntegral J.conjOp F c R

variable {J}

/-- For `T` commuting with `J`: `J (∮_{C(c,R)} (z - T)⁻¹ dz) J = -∮_{C(conj c,R)} (z - T)⁻¹ dz`.
-/
theorem CommutesWith.conjOp_circleIntegral_resolvent {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (c : ℂ) (R : ℝ) :
    J.conjOp (∮ z in C(c, R), resolvent T z) = -∮ z in C(conj c, R), resolvent T z := by
  rw [J.conjOp_circleIntegral]
  simp only [hT.conjOp_resolvent, Complex.conj_conj]

/-- The Dunford integral `(2πi)⁻¹ ∮_{|z-c|=r} f(z) (z - T)⁻¹ dz` over the positively oriented
circle `C(c, r)`. -/
def dunfordIntegral (f : ℂ → ℂ) (T : X →L[ℂ] X) (c : ℂ) (r : ℝ) : X →L[ℂ] X :=
  (2 * π * Complex.I)⁻¹ • ∮ z in C(c, r), f z • resolvent T z

/-- The Riesz integral `(2πi)⁻¹ ∮_{|z-c|=r} (z - T)⁻¹ dz` over the positively oriented circle
`C(c, r)`. When the circle lies in the resolvent set this is the Riesz spectral projection
onto the part of the spectrum inside the circle (the projection `P_-` of the manuscript). -/
def rieszIntegral (T : X →L[ℂ] X) (c : ℂ) (r : ℝ) : X →L[ℂ] X :=
  (2 * π * Complex.I)⁻¹ • ∮ z in C(c, r), resolvent T z

/-- For `f` real on real arguments, `J D_{c,r}(f) J = D_{conj c, r}(f)`. -/
theorem CommutesWith.conjOp_dunfordIntegral {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    {f : ℂ → ℂ} (hf : ∀ z, conj (f (conj z)) = f z) (c : ℂ) (r : ℝ) :
    J.conjOp (dunfordIntegral f T c r) = dunfordIntegral f T (conj c) r := by
  rw [dunfordIntegral, dunfordIntegral, J.conjOp_smul, J.conjOp_circleIntegral]
  simp only [J.conjOp_smul, hT.conjOp_resolvent, Complex.conj_conj, hf]
  rw [conj_two_pi_I_inv, smul_neg, neg_smul, neg_neg]

/-- **Conjugation of the Riesz integral.** For `T` commuting with `J`,
`J P_{c,r} J = P_{conj c, r}`. -/
theorem CommutesWith.conjOp_rieszIntegral {T : X →L[ℂ] X} (hT : J.CommutesWith T) (c : ℂ)
    (r : ℝ) : J.conjOp (rieszIntegral T c r) = rieszIntegral T (conj c) r := by
  rw [rieszIntegral, rieszIntegral, J.conjOp_smul, hT.conjOp_circleIntegral_resolvent,
    conj_two_pi_I_inv, smul_neg, neg_smul, neg_neg]

/-- **Riesz projections of real operators are real.** For `T` commuting with `J` and a circle
with real centre `c`, the Riesz integral commutes with `J`. -/
theorem CommutesWith.rieszIntegral_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T) {c : ℂ}
    (hc : conj c = c) (r : ℝ) : J.CommutesWith (rieszIntegral T c r) := by
  rw [J.commutesWith_iff_conjOp_eq, hT.conjOp_rieszIntegral, hc]

/-- The Riesz integral over a circle centred at `0` commutes with `J`. -/
theorem CommutesWith.rieszIntegral_zero_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) : J.CommutesWith (rieszIntegral T 0 r) :=
  hT.rieszIntegral_commutesWith (map_zero _) r

/-- The complementary projection `P_+ = 1 - P_-` commutes with `J`. -/
theorem CommutesWith.one_sub_rieszIntegral_commutesWith {T : X →L[ℂ] X}
    (hT : J.CommutesWith T) {c : ℂ} (hc : conj c = c) (r : ℝ) :
    J.CommutesWith (1 - rieszIntegral T c r) :=
  J.commutesWith_one.sub (hT.rieszIntegral_commutesWith hc r)

/-- **Both projections preserve real fields** (manuscript line 361): the Riesz integral over a
circle centred at `0` maps real vectors to real vectors. -/
theorem CommutesWith.rieszIntegral_mem_fixedSubmodule {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) {x : X} (hx : x ∈ J.fixedSubmodule) :
    rieszIntegral T 0 r x ∈ J.fixedSubmodule :=
  (hT.rieszIntegral_zero_commutesWith r).apply_mem_fixedSubmodule hx

/-- The complementary projection `1 - P_-` maps real vectors to real vectors. -/
theorem CommutesWith.one_sub_rieszIntegral_mem_fixedSubmodule {T : X →L[ℂ] X}
    (hT : J.CommutesWith T) (r : ℝ) {x : X} (hx : x ∈ J.fixedSubmodule) :
    (1 - rieszIntegral T 0 r) x ∈ J.fixedSubmodule :=
  (hT.one_sub_rieszIntegral_commutesWith (map_zero _) r).apply_mem_fixedSubmodule hx

end Conjugation

end UnforcedLeray.Infra.RealStructure
