import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Tactic

/-!
# Quantitative Neumann bounds (INF19, targets T19.1 and T19.2)


§5 Level 0.  Uses: `paper/main.tex` (2.40c) lines 5577-5586 (unit B0540), (2.40n) lines
5665-5676 (B0683), (t00601) lines 10290-10302 (B0948), (B4) lines 4383-4411 (B0256),
(t00424) lines 14018-14029 (B0900).

Mathlib has `Units.oneSub`, `Units.ofNearby` and the first-order statement
`NormedRing.inverse_add_norm_diff_first_order`, but no explicit bound
`‖b⁻¹ - a⁻¹‖ ≤ ‖a⁻¹‖² ‖b - a‖ / (1 - q)`.  This file supplies it.

Main results (`R` a normed ring with summable geometric series, e.g. a complete one, and
`‖1‖ ≤ 1`, which holds in every algebra of operators):
* `norm_inverse_one_sub_le : ‖(1 - t)⁻¹ʳ‖ ≤ (1 - ‖t‖)⁻¹` for `‖t‖ < 1`;
* `isUnit_of_perturb`, `norm_inverse_le_of_perturb`, `norm_inverse_sub_inverse_le`;
* `neumann_half` : the `Q δ ≤ 1/2` form used in (2.40n) and (t00601);
* `ContinuousLinearMap.isInvertible_of_perturb` (T19.2): the same for maps `E →L F`
  between different Banach spaces, measured against a continuous linear equivalence.

`⁻¹ʳ` is `Ring.inverse` (junk value `0` on non-units); every statement below that mentions an
inverse also proves the relevant element is a unit, so no junk value is ever used.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Ring

namespace UnforcedLeray.Algebra

section Ring

variable {R : Type*} [Ring R]

/-- A two-sided inverse is the ring inverse. -/
theorem inverse_eq_of_mul_eq_one {x y : R} (h1 : x * y = 1) (h2 : y * x = 1) : x⁻¹ʳ = y := by
  have hx : x = ((⟨x, y, h1, h2⟩ : Rˣ) : R) := rfl
  rw [hx, Ring.inverse_unit]
  rfl

theorem isUnit_of_mul_eq_one_of_mul_eq_one {x y : R} (h1 : x * y = 1) (h2 : y * x = 1) :
    IsUnit x :=
  ⟨⟨x, y, h1, h2⟩, rfl⟩

end Ring

section NormedRing

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- T19.1: Neumann bound `‖(1 - t)⁻¹‖ ≤ (1 - ‖t‖)⁻¹` when `‖1‖ ≤ 1`. -/
theorem norm_inverse_one_sub_le (h1 : ‖(1 : R)‖ ≤ 1) {t : R} (ht : ‖t‖ < 1) :
    ‖(1 - t)⁻¹ʳ‖ ≤ (1 - ‖t‖)⁻¹ := by
  rw [← geom_series_eq_inverse t ht]
  have := tsum_geometric_le_of_norm_lt_one t ht
  linarith

theorem isUnit_one_sub {t : R} (ht : ‖t‖ < 1) : IsUnit (1 - t) :=
  (Units.oneSub t ht).isUnit

/-- Factorization `b = a (1 - a⁻¹ (a - b))`. -/
theorem eq_mul_one_sub {a b : R} (ha : IsUnit a) : b = a * (1 - a⁻¹ʳ * (a - b)) := by
  rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel a ha, one_mul, sub_sub_cancel]

theorem norm_inverse_mul_sub_le {a b : R} : ‖a⁻¹ʳ * (a - b)‖ ≤ ‖a⁻¹ʳ‖ * ‖b - a‖ := by
  rw [← norm_neg (b - a), neg_sub]
  exact norm_mul_le _ _

/-- T19.1: a perturbation `b` of a unit `a` with `‖a⁻¹‖ ‖b - a‖ < 1` is a unit. -/
theorem isUnit_of_perturb {a b : R} (ha : IsUnit a) (h : ‖a⁻¹ʳ‖ * ‖b - a‖ < 1) : IsUnit b := by
  rw [eq_mul_one_sub (b := b) ha]
  exact ha.mul (isUnit_one_sub (norm_inverse_mul_sub_le.trans_lt h))

/-- `b⁻¹ = (1 - a⁻¹ (a - b))⁻¹ a⁻¹`. -/
theorem inverse_eq_of_perturb {a b : R} (ha : IsUnit a) (h : ‖a⁻¹ʳ‖ * ‖b - a‖ < 1) :
    b⁻¹ʳ = (1 - a⁻¹ʳ * (a - b))⁻¹ʳ * a⁻¹ʳ := by
  have ht := isUnit_one_sub (norm_inverse_mul_sub_le.trans_lt h)
  set t := 1 - a⁻¹ʳ * (a - b) with htdef
  have hb : b = a * t := eq_mul_one_sub ha
  apply inverse_eq_of_mul_eq_one
  · calc b * (t⁻¹ʳ * a⁻¹ʳ) = a * (t * t⁻¹ʳ) * a⁻¹ʳ := by rw [hb]; noncomm_ring
      _ = 1 := by rw [Ring.mul_inverse_cancel t ht, mul_one, Ring.mul_inverse_cancel a ha]
  · calc t⁻¹ʳ * a⁻¹ʳ * b = t⁻¹ʳ * (a⁻¹ʳ * a) * t := by rw [hb]; noncomm_ring
      _ = 1 := by rw [Ring.inverse_mul_cancel a ha, mul_one, Ring.inverse_mul_cancel t ht]

/-- T19.1: `‖b⁻¹‖ ≤ ‖a⁻¹‖ / (1 - q)` when `‖a⁻¹‖ ‖b - a‖ ≤ q < 1`. -/
theorem norm_inverse_le_of_perturb (h1 : ‖(1 : R)‖ ≤ 1) {a b : R} (ha : IsUnit a) {q : ℝ}
    (hq : ‖a⁻¹ʳ‖ * ‖b - a‖ ≤ q) (hq1 : q < 1) : ‖b⁻¹ʳ‖ ≤ ‖a⁻¹ʳ‖ / (1 - q) := by
  have hlt : ‖a⁻¹ʳ‖ * ‖b - a‖ < 1 := hq.trans_lt hq1
  have ht : ‖a⁻¹ʳ * (a - b)‖ ≤ q := norm_inverse_mul_sub_le.trans hq
  have ht1 : ‖a⁻¹ʳ * (a - b)‖ < 1 := ht.trans_lt hq1
  rw [inverse_eq_of_perturb ha hlt]
  have hN := norm_inverse_one_sub_le h1 ht1
  have hpos : 0 < 1 - q := by linarith
  have hpos' : 0 < 1 - ‖a⁻¹ʳ * (a - b)‖ := by linarith
  calc ‖(1 - a⁻¹ʳ * (a - b))⁻¹ʳ * a⁻¹ʳ‖
      ≤ ‖(1 - a⁻¹ʳ * (a - b))⁻¹ʳ‖ * ‖a⁻¹ʳ‖ := norm_mul_le _ _
    _ ≤ (1 - q)⁻¹ * ‖a⁻¹ʳ‖ := by
        gcongr
        exact hN.trans (inv_anti₀ hpos (by linarith))
    _ = ‖a⁻¹ʳ‖ / (1 - q) := by rw [div_eq_inv_mul]

/-- The resolvent identity `b⁻¹ - a⁻¹ = b⁻¹ (a - b) a⁻¹` for units. -/
theorem inverse_sub_inverse {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    b⁻¹ʳ - a⁻¹ʳ = b⁻¹ʳ * (a - b) * a⁻¹ʳ := by
  rw [mul_sub, sub_mul, mul_assoc (b⁻¹ʳ) a, Ring.mul_inverse_cancel a ha, mul_one,
    Ring.inverse_mul_cancel b hb, one_mul]

/-- T19.1: `‖b⁻¹ - a⁻¹‖ ≤ ‖a⁻¹‖² ‖b - a‖ / (1 - q)` when `‖a⁻¹‖ ‖b - a‖ ≤ q < 1`. -/
theorem norm_inverse_sub_inverse_le (h1 : ‖(1 : R)‖ ≤ 1) {a b : R} (ha : IsUnit a) {q : ℝ}
    (hq : ‖a⁻¹ʳ‖ * ‖b - a‖ ≤ q) (hq1 : q < 1) :
    ‖b⁻¹ʳ - a⁻¹ʳ‖ ≤ ‖a⁻¹ʳ‖ ^ 2 * ‖b - a‖ / (1 - q) := by
  have hb : IsUnit b := isUnit_of_perturb ha (hq.trans_lt hq1)
  have hbinv := norm_inverse_le_of_perturb h1 ha hq hq1
  have hpos : 0 < 1 - q := by linarith
  rw [inverse_sub_inverse ha hb]
  calc ‖b⁻¹ʳ * (a - b) * a⁻¹ʳ‖ ≤ ‖b⁻¹ʳ‖ * ‖a - b‖ * ‖a⁻¹ʳ‖ := norm_mul₃_le
    _ ≤ (‖a⁻¹ʳ‖ / (1 - q)) * ‖b - a‖ * ‖a⁻¹ʳ‖ := by
        rw [norm_sub_rev]; gcongr
    _ = ‖a⁻¹ʳ‖ ^ 2 * ‖b - a‖ / (1 - q) := by ring

/-- T19.1, the `Q δ ≤ 1/2` form: (2.40n) (tex 5665-5676, B0683) and (t00601)
(tex 10290-10302, B0948).  If `‖a⁻¹‖ ≤ Q`, `‖b - a‖ ≤ δ` and `Q δ ≤ 1/2`, then `b` is a unit,
`‖b⁻¹‖ ≤ 2Q` and `‖b⁻¹ - a⁻¹‖ ≤ 2 Q² δ`. -/
theorem neumann_half (h1 : ‖(1 : R)‖ ≤ 1) {a b : R} (ha : IsUnit a) {Q δ : ℝ}
    (hQ : ‖a⁻¹ʳ‖ ≤ Q) (hδ : ‖b - a‖ ≤ δ) (h : Q * δ ≤ 1 / 2) :
    IsUnit b ∧ ‖b⁻¹ʳ‖ ≤ 2 * Q ∧ ‖b⁻¹ʳ - a⁻¹ʳ‖ ≤ 2 * Q ^ 2 * δ := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hQ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hq : ‖a⁻¹ʳ‖ * ‖b - a‖ ≤ 1 / 2 :=
    (mul_le_mul hQ hδ (norm_nonneg _) hQ0).trans h
  have hq1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨isUnit_of_perturb ha (hq.trans_lt hq1), ?_, ?_⟩
  · have := norm_inverse_le_of_perturb h1 ha hq hq1
    calc ‖b⁻¹ʳ‖ ≤ ‖a⁻¹ʳ‖ / (1 - 1 / 2) := this
      _ ≤ Q / (1 - 1 / 2) := by gcongr
      _ = 2 * Q := by ring
  · have := norm_inverse_sub_inverse_le h1 ha hq hq1
    calc ‖b⁻¹ʳ - a⁻¹ʳ‖ ≤ ‖a⁻¹ʳ‖ ^ 2 * ‖b - a‖ / (1 - 1 / 2) := this
      _ ≤ Q ^ 2 * δ / (1 - 1 / 2) := by gcongr
      _ = 2 * Q ^ 2 * δ := by ring

end NormedRing

/-! ### T19.2: maps between different Banach spaces -/

section CLM

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- T19.2: perturbation of a continuous linear equivalence `e : E ≃L F` (`E` complete).  If
`‖e⁻¹‖ ‖T - e‖ ≤ q < 1` then `T` is invertible, `‖T⁻¹‖ ≤ ‖e⁻¹‖ / (1 - q)` and
`‖T⁻¹ - e⁻¹‖ ≤ ‖e⁻¹‖² ‖T - e‖ / (1 - q)`.  Uses: B0256, B0258 (tex 4383-4475),
B0540 (tex 5577-5586), B0262 (tex 4535-4555). -/
theorem _root_.ContinuousLinearMap.isInvertible_of_perturb (e : E ≃L[𝕜] F) (T : E →L[𝕜] F)
    {q : ℝ} (hq : ‖(e.symm : F →L[𝕜] E)‖ * ‖T - (e : E →L[𝕜] F)‖ ≤ q) (hq1 : q < 1) :
    T.IsInvertible ∧ ‖T.inverse‖ ≤ ‖(e.symm : F →L[𝕜] E)‖ / (1 - q) ∧
    ‖T.inverse - (e.symm : F →L[𝕜] E)‖ ≤
      ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖T - (e : E →L[𝕜] F)‖ / (1 - q) := by
  set es : F →L[𝕜] E := (e.symm : F →L[𝕜] E) with hes
  set ee : E →L[𝕜] F := (e : E →L[𝕜] F) with hee
  have hese : es ∘L ee = ContinuousLinearMap.id 𝕜 E := by
    ext x; simp [hes, hee]
  have hees : ee ∘L es = ContinuousLinearMap.id 𝕜 F := by
    ext x; simp [hes, hee]
  -- t := -(es ∘ (T - ee)), so that es ∘ T = 1 - t
  set t : E →L[𝕜] E := -(es ∘L (T - ee)) with ht
  have hS : es ∘L T = 1 - t := by
    rw [ht, sub_neg_eq_add, ContinuousLinearMap.comp_sub, hese]
    ext x; simp
  have htn : ‖t‖ ≤ q := by
    rw [ht, norm_neg]; exact (ContinuousLinearMap.opNorm_comp_le _ _).trans hq
  have ht1 : ‖t‖ < 1 := htn.trans_lt hq1
  set w : E →L[𝕜] E := (1 - t)⁻¹ʳ with hw
  have hwu : IsUnit (1 - t) := isUnit_one_sub (R := E →L[𝕜] E) ht1
  have hw1 : (1 - t) * w = 1 := Ring.mul_inverse_cancel _ hwu
  have hw2 : w * (1 - t) = 1 := Ring.inverse_mul_cancel _ hwu
  set g : F →L[𝕜] E := w ∘L es with hg
  have hT : T = ee ∘L (es ∘L T) := by
    rw [← ContinuousLinearMap.comp_assoc, hees, ContinuousLinearMap.id_comp]
  have hTg : T ∘L g = ContinuousLinearMap.id 𝕜 F := by
    rw [hT, hS, hg, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (1 - t) w es,
      ← ContinuousLinearMap.mul_def, hw1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    exact hees
  have hgT : g ∘L T = ContinuousLinearMap.id 𝕜 E := by
    rw [hg, ContinuousLinearMap.comp_assoc, hS]
    exact hw2
  have hinv : T.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hTg hgT
  have hTinv : T.inverse = g := ContinuousLinearMap.inverse_eq hTg hgT
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hpos : 0 < 1 - q := by linarith
  have hwn : ‖w‖ ≤ (1 - q)⁻¹ :=
    (norm_inverse_one_sub_le h1 ht1).trans (inv_anti₀ hpos (by linarith))
  have hgn : ‖g‖ ≤ ‖es‖ / (1 - q) := by
    calc ‖g‖ ≤ ‖w‖ * ‖es‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 - q)⁻¹ * ‖es‖ := by gcongr
      _ = ‖es‖ / (1 - q) := by rw [div_eq_inv_mul]
  refine ⟨hinv, hTinv ▸ hgn, ?_⟩
  -- g - es = g ∘ (ee - T) ∘ es
  have hdiff : g - es = g ∘L (ee - T) ∘L es := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hees,
      ← ContinuousLinearMap.comp_assoc g T, hgT]
    ext x; simp
  rw [hTinv, hdiff]
  calc ‖g ∘L (ee - T) ∘L es‖ ≤ ‖g‖ * (‖ee - T‖ * ‖es‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (‖es‖ / (1 - q)) * (‖T - ee‖ * ‖es‖) := by
        rw [norm_sub_rev ee T]; gcongr
    _ = ‖es‖ ^ 2 * ‖T - ee‖ / (1 - q) := by ring

/-- T19.2 in the form used for chains: the reference map `a` is only assumed invertible. -/
theorem _root_.ContinuousLinearMap.IsInvertible.perturb {a : E →L[𝕜] F} (ha : a.IsInvertible)
    (T : E →L[𝕜] F) {q : ℝ} (hq : ‖a.inverse‖ * ‖T - a‖ ≤ q) (hq1 : q < 1) :
    T.IsInvertible ∧ ‖T.inverse‖ ≤ ‖a.inverse‖ / (1 - q) ∧
    ‖T.inverse - a.inverse‖ ≤ ‖a.inverse‖ ^ 2 * ‖T - a‖ / (1 - q) := by
  obtain ⟨e, rfl⟩ := ha
  rw [ContinuousLinearMap.inverse_equiv] at hq ⊢
  exact ContinuousLinearMap.isInvertible_of_perturb e T hq hq1

/-- `inverse_near_one` (T19.6 core, B0234, B0402): an operator within `δ ≤ 1/2` of the identity
on a Banach space is invertible with `‖M⁻¹‖ ≤ 2` and `‖M⁻¹ - 1‖ ≤ 2δ`. -/
theorem inverse_near_one {M : E →L[𝕜] E} {δ : ℝ} (h : ‖M - 1‖ ≤ δ) (hδ : δ ≤ 1 / 2) :
    M.IsInvertible ∧ ‖M.inverse‖ ≤ 2 ∧ ‖M.inverse - 1‖ ≤ 2 * δ := by
  have hid : ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans h
  have h' : ‖M - ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E)‖ ≤ δ := h
  have hq : ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖ *
      ‖M - ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E)‖ ≤ δ :=
    (mul_le_mul hid h' (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  obtain ⟨hinv, hn, hd⟩ :=
    ContinuousLinearMap.isInvertible_of_perturb (ContinuousLinearEquiv.refl 𝕜 E) M hq
      (by linarith)
  have hpos : 0 < 1 - δ := by linarith
  have hhalf : (1 - δ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  refine ⟨hinv, ?_, ?_⟩
  · calc ‖M.inverse‖ ≤ ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖ / (1 - δ) := hn
      _ ≤ 1 / (1 - δ) := by gcongr
      _ ≤ 2 := by rw [one_div]; exact hhalf
  · have hd' : ‖M.inverse - 1‖ ≤
        ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖ ^ 2 * ‖M - 1‖ / (1 - δ) := hd
    calc ‖M.inverse - 1‖ ≤ ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖ ^ 2 *
          ‖M - 1‖ / (1 - δ) := hd'
      _ ≤ 1 ^ 2 * δ / (1 - δ) := by gcongr
      _ = δ * (1 - δ)⁻¹ := by ring
      _ ≤ δ * 2 := by gcongr
      _ = 2 * δ := by ring

end CLM

end UnforcedLeray.Algebra
