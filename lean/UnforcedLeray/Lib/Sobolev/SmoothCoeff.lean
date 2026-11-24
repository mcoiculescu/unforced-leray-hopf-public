import UnforcedLeray.Lib.Sobolev.WeakDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Weak-derivative calculus on the whole space (helpers for INF11 target S6)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S6, change of variables). The chain rule for
`W.compDiffeo` is proved by induction on the order; each step multiplies by smooth
coefficients and sums finitely many terms. This file records those calculus rules for
`HasWeakDeriv (wholeSpace n)` between locally integrable functions:

* `HasWeakDeriv.of_locallyIntegrable`: on the whole space only the identity has to be checked;
* `HasWeakDeriv.of_append`: `∂_{ws} (∂_{vs} f) = ∂_{vs ++ ws} f` read backwards;
* `HasWeakDeriv.sum`: finite sums;
* `HasWeakDeriv.smul_left`: the Leibniz rule with a smooth coefficient,
  `∂_v (a u) = (∂_v a) u + a ∂_v u` (manuscript use: tex 1228–1237, B0062; tex 1569–1580,
  B0102).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

theorem neg_one_pow_mul_pow_add (a b : ℕ) :
    (-1 : ℝ) ^ a * (-1 : ℝ) ^ (a + b) = (-1 : ℝ) ^ b := by
  rw [← pow_add, ← add_assoc, ← two_mul, pow_add, pow_mul]
  norm_num

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {n : ℕ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {D : TestDomain E n}

/-- Peeling a word off the front: if `g = ∂_{vs} f` and `h = ∂_{vs ++ ws} f` weakly, then
`h = ∂_{ws} g` weakly. -/
theorem HasWeakDeriv.of_append {vs ws : List E} {f g h : E → F}
    (h₁ : HasWeakDeriv D vs f g) (h₂ : HasWeakDeriv D (vs ++ ws) f h) :
    HasWeakDeriv D ws g h := by
  refine ⟨fun φ hφ => h₁.int_right _ (D.adm_iterDirDeriv hφ ws), h₂.int_right,
    fun φ hφ => ?_⟩
  have e1 := h₁.identity _ (D.adm_iterDirDeriv hφ ws)
  have e2 := h₂.identity φ hφ
  rw [iterDirDeriv_append, e1, List.length_append] at e2
  calc ∫ x, iterDirDeriv ws φ x • g x ∂D.μ
      = ((-1 : ℝ) ^ vs.length * (-1 : ℝ) ^ vs.length) •
          ∫ x, iterDirDeriv ws φ x • g x ∂D.μ := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
    _ = (-1 : ℝ) ^ vs.length • ((-1 : ℝ) ^ (vs.length + ws.length) •
          ∫ x, φ x • h x ∂D.μ) := by rw [mul_smul, e2]
    _ = (-1 : ℝ) ^ ws.length • ∫ x, φ x • h x ∂D.μ := by
        rw [smul_smul, neg_one_pow_mul_pow_add]

/-- Finite sums of weak derivatives. -/
theorem HasWeakDeriv.sum {ι : Type*} (s : Finset ι) {vs : List E} {f g : ι → E → F}
    (h : ∀ i ∈ s, HasWeakDeriv D vs (f i) (g i)) :
    HasWeakDeriv D vs (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasWeakDeriv.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end General

section Whole

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_smul_of_adm {φ : Eucl n → ℝ} (hφ : (wholeSpace n).Adm φ) {u : Eucl n → F}
    (hu : LocallyIntegrable u volume) : Integrable (fun x => φ x • u x) volume :=
  hu.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2

/-- On the whole space, weak derivatives between locally integrable functions need only the
identity. -/
theorem HasWeakDeriv.of_locallyIntegrable {vs : List (Eucl n)} {f g : Eucl n → F}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : ∀ φ : Eucl n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, iterDirDeriv vs φ x • f x = (-1 : ℝ) ^ vs.length • ∫ x, φ x • g x) :
    HasWeakDeriv (wholeSpace n) vs f g :=
  ⟨fun φ hφ => integrable_smul_of_adm ((wholeSpace n).adm_iterDirDeriv hφ vs) hf,
    fun φ hφ => integrable_smul_of_adm hφ hg, fun φ hφ => h φ hφ.1 hφ.2⟩

/-- **Leibniz rule with a smooth coefficient**: `∂_v (a u) = (∂_v a) u + a ∂_v u`. -/
theorem HasWeakDeriv.smul_left {a : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a) {v : Eucl n}
    {u u' : Eucl n → F} (hu : LocallyIntegrable u volume) (hu' : LocallyIntegrable u' volume)
    (h : HasWeakDeriv (wholeSpace n) [v] u u') :
    HasWeakDeriv (wholeSpace n) [v] (fun x => a x • u x)
      (fun x => fderiv ℝ a x v • u x + a x • u' x) := by
  have hda : Continuous fun x => fderiv ℝ a x v := (contDiff_dirDeriv ha v).continuous
  refine HasWeakDeriv.of_locallyIntegrable (hu.continuous_smul ha.continuous)
    ((hu.continuous_smul hda).add (hu'.continuous_smul ha.continuous)) fun φ hφ hφc => ?_
  have hψ : (wholeSpace n).Adm (fun x => φ x * a x) := ⟨hφ.mul ha, hφc.mul_right⟩
  have e : ∫ x, fderiv ℝ (fun y => φ y * a y) x v • u x =
      -∫ x, (φ x * a x) • u' x := by
    have := h.identity _ hψ
    simpa only [iterDirDeriv_singleton, wholeSpace_μ, List.length_singleton, pow_one,
      neg_smul, one_smul] using this
  simp only [iterDirDeriv_singleton, List.length_singleton, pow_one, neg_smul, one_smul]
  have hd : ∀ x, fderiv ℝ (fun y => φ y * a y) x v =
      fderiv ℝ φ x v * a x + φ x * fderiv ℝ a x v := by
    intro x
    have h1 : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ a x := (ha.differentiable (by simp)) x
    have : fderiv ℝ (fun y => φ y * a y) x = φ x • fderiv ℝ a x + a x • fderiv ℝ φ x :=
      fderiv_mul h1 h2
    rw [this]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hφ' : (wholeSpace n).Adm φ := ⟨hφ, hφc⟩
  have i1 : Integrable (fun x => fderiv ℝ (fun y => φ y * a y) x v • u x) volume :=
    integrable_smul_of_adm ((wholeSpace n).deriv_mem hψ v) hu
  have i2 : Integrable (fun x => (φ x * fderiv ℝ a x v) • u x) volume :=
    integrable_smul_of_adm (φ := fun x => φ x * fderiv ℝ a x v)
      ⟨hφ.mul (contDiff_dirDeriv ha v), hφc.mul_right⟩ hu
  have i3 : Integrable (fun x => φ x • (fderiv ℝ a x v • u x)) volume := by
    refine i2.congr (Eventually.of_forall fun x => ?_)
    simp only [smul_smul]
  have i4 : Integrable (fun x => φ x • (a x • u' x)) volume := by
    refine (integrable_smul_of_adm hψ hu').congr (Eventually.of_forall fun x => ?_)
    simp only [smul_smul]
  calc ∫ x, fderiv ℝ φ x v • (a x • u x)
      = ∫ x, (fderiv ℝ (fun y => φ y * a y) x v • u x - (φ x * fderiv ℝ a x v) • u x) := by
        congr 1 with x
        rw [hd, smul_smul, add_smul, add_sub_cancel_right]
    _ = -(∫ x, (φ x * a x) • u' x) - ∫ x, (φ x * fderiv ℝ a x v) • u x := by
        rw [integral_sub i1 i2, e]
    _ = -∫ x, φ x • (fderiv ℝ a x v • u x + a x • u' x) := by
        have e3 : ∫ x, φ x • (fderiv ℝ a x v • u x + a x • u' x) =
            (∫ x, (φ x * fderiv ℝ a x v) • u x) + ∫ x, (φ x * a x) • u' x := by
          rw [← integral_add i2 (integrable_smul_of_adm hψ hu' :
            Integrable (fun x => (φ x * a x) • u' x) volume)]
          congr 1 with x
          rw [smul_add, smul_smul, smul_smul]
        rw [e3]
        abel

end Whole

end UnforcedLeray.Sob
