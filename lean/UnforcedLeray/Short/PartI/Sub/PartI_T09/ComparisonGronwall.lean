import UnforcedLeray.Short.PartI.Sub.PartI_T09
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.DenselyOrdered

/-!
# `PartI:T09` leaf 1: time-ordered Gronwall (`ComparisonGronwall`, source lines 346-349)

Proof by a explicit supersolution. With `a = 1 + νs`, `T = (b/2) c²`, `t = T⁻¹` and
`P(a) = t a⁻³ + 3t² a⁻² + 6t³ a⁻¹ + 6t⁴`, the function `Q = 2C ν⁻² e^{-T/a} P(a)` satisfies
`Q' ≥ (C/a²) Q + (C/(ν a⁵)) e^{-bc²/a}`. The function `G = (E - Q) e^{-C s/(1+νs)}` is
antitone, `G(0) ≤ 0`, so `E ≤ Q`, and `Q ≤ K ν⁻² a⁻⁴ e^{-(b/2)c²/a}` with `b' = b/2`,
`K = R = 2C M(b/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- Polynomial prefactor `P(a) = t a⁻³ + 3t² a⁻² + 6t³ a⁻¹ + 6t⁴` of the supersolution. -/
def cgPoly (t a : ℝ) : ℝ :=
  t * (a⁻¹) ^ 3 + 3 * t ^ 2 * (a⁻¹) ^ 2 + 6 * t ^ 3 * a⁻¹ + 6 * t ^ 4

/-- `M(β) = 1/β + 3(1/β)² + 6(1/β)³ + 6(1/β)⁴`. -/
def cgM (β : ℝ) : ℝ := 1 / β + 3 * (1 / β) ^ 2 + 6 * (1 / β) ^ 3 + 6 * (1 / β) ^ 4

lemma cgM_pos {β : ℝ} (hβ : 0 < β) : 0 < cgM β := by
  have h : 0 < 1 / β := one_div_pos.2 hβ
  unfold cgM
  linarith [pow_pos h 2, pow_pos h 3, pow_pos h 4]

lemma cg_bounds {β c a : ℝ} (hβ : 0 < β) (hc : 0 < c) (ha : 0 < a) (hac : a ≤ c ^ 2) :
    0 ≤ cgPoly (β * c ^ 2)⁻¹ a ∧
      a ^ 3 * cgPoly (β * c ^ 2)⁻¹ a ≤ cgM β / c ^ 2 ∧
      a ^ 4 * cgPoly (β * c ^ 2)⁻¹ a ≤ cgM β := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hT : 0 < β * c ^ 2 := mul_pos hβ hc2
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, (β * c ^ 2)⁻¹ = t := ⟨_, rfl⟩
  rw [ht_def]
  have ht : 0 < t := by rw [← ht_def]; exact inv_pos.2 hT
  have ha0 : a ≠ 0 := ha.ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hv0 : 0 ≤ t * a := (mul_pos ht ha).le
  have hv1 : t * a ≤ 1 / β := by
    rw [← ht_def, inv_mul_le_iff₀ hT]
    have h1 : 1 / β * (β * c ^ 2) = c ^ 2 := by field_simp
    linarith
  have hpow : ∀ k : ℕ, (t * a) ^ k ≤ (1 / β) ^ k := fun k => pow_le_pow_left₀ hv0 hv1 k
  have e4 : a ^ 4 * cgPoly t a = t * a + 3 * (t * a) ^ 2 + 6 * (t * a) ^ 3 + 6 * (t * a) ^ 4 := by
    unfold cgPoly
    field_simp
  have e3 : a ^ 3 * cgPoly t a = t * (1 + 3 * (t * a) + 6 * (t * a) ^ 2 + 6 * (t * a) ^ 3) := by
    unfold cgPoly
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold cgPoly
    have hai : 0 ≤ a⁻¹ := inv_nonneg.2 ha.le
    have h1 : 0 ≤ t * a⁻¹ ^ 3 := mul_nonneg ht.le (pow_nonneg hai 3)
    have h2 : 0 ≤ 3 * t ^ 2 * a⁻¹ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg t)) (pow_nonneg hai 2)
    have h3 : 0 ≤ 6 * t ^ 3 * a⁻¹ := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.le 3)) hai
    have h4 : 0 ≤ 6 * t ^ 4 := mul_nonneg (by norm_num) (pow_nonneg ht.le 4)
    linarith
  · calc a ^ 3 * cgPoly t a = t * (1 + 3 * (t * a) + 6 * (t * a) ^ 2 + 6 * (t * a) ^ 3) := e3
      _ ≤ t * (1 + 3 * (1 / β) + 6 * (1 / β) ^ 2 + 6 * (1 / β) ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith [hv1, hpow 2, hpow 3]) ht.le
      _ = cgM β / c ^ 2 := by
          rw [← ht_def]
          unfold cgM
          field_simp
  · calc a ^ 4 * cgPoly t a = t * a + 3 * (t * a) ^ 2 + 6 * (t * a) ^ 3 + 6 * (t * a) ^ 4 := e4
      _ ≤ cgM β := by
          unfold cgM
          linarith [hv1, hpow 2, hpow 3, hpow 4]

lemma cg_hasDerivAt (T a : ℝ) (hT : T ≠ 0) (ha : a ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.exp (-(T * x⁻¹)) * cgPoly T⁻¹ x)
      (a⁻¹ ^ 5 * Real.exp (-(T * a⁻¹))) a := by
  have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(a ^ 2)⁻¹) a := hasDerivAt_inv ha
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-(T * x⁻¹)))
      (Real.exp (-(T * a⁻¹)) * -(T * -(a ^ 2)⁻¹)) a :=
    ((h1.const_mul T).neg).exp
  have hP : HasDerivAt (fun x : ℝ => cgPoly T⁻¹ x)
      (-(3 * T⁻¹ * a⁻¹ ^ 4) - 6 * T⁻¹ ^ 2 * a⁻¹ ^ 3 - 6 * T⁻¹ ^ 3 * a⁻¹ ^ 2) a := by
    have h3 := (h1.pow 3).const_mul T⁻¹
    have h2 := (h1.pow 2).const_mul (3 * T⁻¹ ^ 2)
    have h1' := h1.const_mul (6 * T⁻¹ ^ 3)
    have hsum := (((h3.add h2).add h1').add_const (6 * T⁻¹ ^ 4))
    refine hsum.congr_deriv ?_
    norm_num <;> field_simp <;> ring
  have hprod := hE.mul hP
  refine hprod.congr_deriv ?_
  unfold cgPoly
  field_simp
  ring

lemma cg_key (C ν w ε X P : ℝ) (hC : 0 < C) (hν : 0 < ν) (hw : 0 < w) (hX : 0 < X)
    (hε : 0 ≤ ε) (hεX : ε ≤ X) (hP : 0 ≤ P) (hwP : 2 * C * ν⁻¹ * (w ^ 3 * P) ≤ 1) :
    C * ν⁻¹ * w⁻¹ ^ 5 * ε + C / w ^ 2 * (2 * C * ν⁻¹ ^ 2 * (X * P)) ≤
      2 * C * ν⁻¹ * (w⁻¹ ^ 5 * X) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hK0 : 0 < C * ν⁻¹ * w⁻¹ ^ 5 * X :=
    mul_pos (mul_pos (mul_pos hC (inv_pos.2 hν)) (pow_pos (inv_pos.2 hw) 5)) hX
  have h1 : C * ν⁻¹ * w⁻¹ ^ 5 * ε ≤ C * ν⁻¹ * w⁻¹ ^ 5 * X :=
    mul_le_mul_of_nonneg_left hεX
      (le_of_lt (mul_pos (mul_pos hC (inv_pos.2 hν)) (pow_pos (inv_pos.2 hw) 5)))
  have h2 : C / w ^ 2 * (2 * C * ν⁻¹ ^ 2 * (X * P)) =
      (C * ν⁻¹ * w⁻¹ ^ 5 * X) * (2 * C * ν⁻¹ * (w ^ 3 * P)) := by
    field_simp
  have h3 : (C * ν⁻¹ * w⁻¹ ^ 5 * X) * (2 * C * ν⁻¹ * (w ^ 3 * P)) ≤
      (C * ν⁻¹ * w⁻¹ ^ 5 * X) * 1 :=
    mul_le_mul_of_nonneg_left hwP hK0.le
  have h4 : 2 * C * ν⁻¹ * (w⁻¹ ^ 5 * X) = 2 * (C * ν⁻¹ * w⁻¹ ^ 5 * X) := by ring
  rw [h2, h4]
  linarith [h1, h3]

theorem comparisonGronwall_proof : ComparisonGronwall := by
  intro C b hC hb
  have hβ : 0 < b / 2 := by linarith
  have hM : 0 < cgM (b / 2) := cgM_pos hβ
  have hK : 0 < 2 * C * cgM (b / 2) := mul_pos (mul_pos two_pos hC) hM
  refine ⟨2 * C * cgM (b / 2), b / 2, 2 * C * cgM (b / 2), hK, hβ, hK, ?_⟩
  intro ν c S hν hc1 hRc hS0 hSc E hE hE0 hODE
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := pow_pos hc0 2
  have hT : b / 2 * c ^ 2 ≠ 0 := (mul_pos hβ hc2).ne'
  have hν0 : ν ≠ 0 := hν.ne'
  have hwd : ∀ s : ℝ, HasDerivAt (fun y : ℝ => width ν y) ν s := fun s => by
    unfold width
    simpa using ((hasDerivAt_id' s).const_mul ν).const_add 1
  have hwpos : ∀ s : ℝ, 0 ≤ s → 0 < width ν s := fun s hs => Train.width_pos hν.le hs
  have hwle : ∀ s : ℝ, s ≤ S → width ν s ≤ c ^ 2 := fun s hs => by
    have h1 : width ν s ≤ width ν S := by
      unfold width
      have := mul_le_mul_of_nonneg_left hs hν.le
      linarith
    exact h1.trans hSc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, ∀ s, Q s = 2 * C * ν⁻¹ ^ 2 *
      (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) * cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)) :=
    ⟨fun s => 2 * C * ν⁻¹ ^ 2 *
      (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) * cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)),
      fun s => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ s, A s = C * s / width ν s :=
    ⟨fun s => C * s / width ν s, fun s => rfl⟩
  obtain ⟨Qd, hQd_def⟩ : ∃ Qd : ℝ → ℝ, ∀ s, Qd s =
      2 * C * ν⁻¹ * ((width ν s)⁻¹ ^ 5 * Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹))) :=
    ⟨fun s => 2 * C * ν⁻¹ * ((width ν s)⁻¹ ^ 5 * Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹))),
      fun s => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ s, G s = (E s - Q s) * Real.exp (-(A s)) :=
    ⟨fun s => (E s - Q s) * Real.exp (-(A s)), fun s => rfl⟩
  have hQfun : Q = fun s => 2 * C * ν⁻¹ ^ 2 *
      (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) * cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)) :=
    funext hQ
  have hAfun : A = fun s => C * s / width ν s := funext hA
  have hGfun : G = fun s => (E s - Q s) * Real.exp (-(A s)) := funext hG
  have hνν : ν⁻¹ ^ 2 * ν = ν⁻¹ := by
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hν0, mul_one]
  have hQderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt Q (Qd s) s := by
    intro s hs
    have hw0 : width ν s ≠ 0 := (hwpos s hs).ne'
    have hcomp := (cg_hasDerivAt (b / 2 * c ^ 2) (width ν s) hT hw0).comp s (hwd s)
    have h2 := hcomp.const_mul (2 * C * ν⁻¹ ^ 2)
    rw [hQfun, hQd_def]
    refine h2.congr_deriv ?_
    linear_combination (2 * C * ((width ν s)⁻¹ ^ 5 *
      Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)))) * hνν
  have hAderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt A (C / (width ν s) ^ 2) s := by
    intro s hs
    have hw0 : width ν s ≠ 0 := (hwpos s hs).ne'
    have hcs : HasDerivAt (fun y : ℝ => C * y) C s := by
      simpa using (hasDerivAt_id' s).const_mul C
    have h := hcs.div (hwd s) hw0
    rw [hAfun]
    refine h.congr_deriv ?_
    simp only [width]
    ring
  have hExpA : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun x => Real.exp (-(A x)))
      (Real.exp (-(A s)) * -(C / (width ν s) ^ 2)) s := fun s hs => (hAderiv s hs).neg.exp
  have hGcont : ContinuousOn G (Icc 0 S) := by
    intro s hs
    have hQc : ContinuousAt Q s := (hQderiv s hs.1).continuousAt
    have hAc : ContinuousAt A s := (hAderiv s hs.1).continuousAt
    have hEc : ContinuousWithinAt E (Icc 0 S) s := hE s hs
    rw [hGfun]
    exact (hEc.sub hQc.continuousWithinAt).mul
      (Real.continuous_exp.continuousAt.comp hAc.neg).continuousWithinAt
  choose! D hD hineq using hODE
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, ∀ s, F' s = (D s - Qd s) * Real.exp (-(A s)) +
      (E s - Q s) * (Real.exp (-(A s)) * -(C / width ν s ^ 2)) :=
    ⟨fun s => (D s - Qd s) * Real.exp (-(A s)) +
      (E s - Q s) * (Real.exp (-(A s)) * -(C / width ν s ^ 2)), fun s => rfl⟩
  have hAnti : AntitoneOn G (Icc 0 S) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := F') (convex_Icc 0 S) hGcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      have hs0 : 0 ≤ s := hs.1.le
      have hGd : HasDerivAt G (F' s) s := by
        rw [hGfun, hF']
        exact ((hD s hs).sub (hQderiv s hs0)).mul (hExpA s hs0)
      exact hGd.hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := hs.1
      have hsS : s < S := hs.2
      have hwpos' : 0 < width ν s := hwpos s hs0.le
      have hw0 : width ν s ≠ 0 := hwpos'.ne'
      have hwc : width ν s ≤ c ^ 2 := hwle s hsS.le
      have hD1 : D s ≤ C / (width ν s) ^ 2 * E s +
          C * ν⁻¹ * (width ν s)⁻¹ ^ 5 * Real.exp (-(b * c ^ 2 / width ν s)) := by
        have h := hineq s hs
        have hm := mul_le_mul_of_nonneg_left h hν.le
        have e1 : ν * (ν⁻¹ * D s) = D s := by
          rw [← mul_assoc, mul_inv_cancel₀ hν0, one_mul]
        have e2 : ν * (C / (ν * width ν s ^ 2) * E s +
            C / (ν ^ 2 * width ν s ^ 5) * Real.exp (-(b * c ^ 2 / width ν s))) =
            C / (width ν s) ^ 2 * E s +
              C * ν⁻¹ * (width ν s)⁻¹ ^ 5 * Real.exp (-(b * c ^ 2 / width ν s)) := by
          field_simp <;> ring
        linarith
      have hX : 0 < Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) := Real.exp_pos _
      have hεX : Real.exp (-(b * c ^ 2 / width ν s)) ≤
          Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) := by
        apply Real.exp_le_exp.2
        have hx : 0 ≤ b * c ^ 2 / width ν s :=
          div_nonneg (mul_nonneg hb.le (sq_nonneg c)) hwpos'.le
        have hy : b / 2 * c ^ 2 * (width ν s)⁻¹ = b * c ^ 2 / width ν s / 2 := by ring
        linarith
      have hP := cg_bounds (β := b / 2) hβ hc0 hwpos' hwc
      have hwP : 2 * C * ν⁻¹ * (width ν s ^ 3 * cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)) ≤ 1 := by
        have h1 : 2 * C * ν⁻¹ * (width ν s ^ 3 * cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)) ≤
            2 * C * ν⁻¹ * (cgM (b / 2) / c ^ 2) :=
          mul_le_mul_of_nonneg_left hP.2.1
            (mul_nonneg (mul_nonneg two_pos.le hC.le) (inv_nonneg.2 hν.le))
        have h2 : 2 * C * ν⁻¹ * (cgM (b / 2) / c ^ 2) = 2 * C * cgM (b / 2) / (ν * c ^ 2) := by
          field_simp <;> ring
        have h3 : 2 * C * cgM (b / 2) / (ν * c ^ 2) ≤ 1 :=
          (div_le_one (mul_pos hν hc2)).2 hRc
        linarith
      have hkey := cg_key C ν (width ν s) (Real.exp (-(b * c ^ 2 / width ν s)))
        (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)))
        (cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s)) hC hν hwpos' hX (Real.exp_pos _).le hεX
        hP.1 hwP
      have hk : D s - Qd s ≤ C / width ν s ^ 2 * (E s - Q s) := by
        rw [hQ s, hQd_def s]
        have e3 : C / width ν s ^ 2 * (E s - 2 * C * ν⁻¹ ^ 2 *
            (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) *
              cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s))) =
            C / width ν s ^ 2 * E s - C / width ν s ^ 2 * (2 * C * ν⁻¹ ^ 2 *
              (Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) *
                cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s))) := by ring
        rw [e3]
        linarith [hD1, hkey]
      rw [hF']
      have hE' : 0 ≤ Real.exp (-(A s)) := (Real.exp_pos _).le
      have e4 : (D s - Qd s) * Real.exp (-(A s)) +
          (E s - Q s) * (Real.exp (-(A s)) * -(C / width ν s ^ 2)) =
          Real.exp (-(A s)) * ((D s - Qd s) - C / width ν s ^ 2 * (E s - Q s)) := by ring
      rw [e4]
      exact mul_nonpos_of_nonneg_of_nonpos hE' (by linarith)
  have hG0 : G 0 ≤ 0 := by
    have hA0 : A 0 = 0 := by rw [hA]; simp
    have hQ0 : 0 ≤ Q 0 := by
      rw [hQ 0]
      have hwc0 : width ν 0 ≤ c ^ 2 := hwle 0 hS0
      have hP0 := (cg_bounds (β := b / 2) hβ hc0 (hwpos 0 le_rfl) hwc0).1
      exact mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hC.le) (sq_nonneg _))
        (mul_nonneg (Real.exp_pos _).le hP0)
    rw [hG, hE0, hA0, neg_zero, Real.exp_zero, mul_one, zero_sub]
    linarith
  intro s hs
  have hGs : G s ≤ 0 := (hAnti ⟨le_rfl, hS0⟩ hs hs.1).trans hG0
  rw [hG] at hGs
  have hEQ : E s ≤ Q s := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < (E s - Q s) * Real.exp (-(A s)) := mul_pos (by linarith) (Real.exp_pos _)
    linarith
  have hfinal : Q s ≤ 2 * C * cgM (b / 2) / (ν ^ 2 * width ν s ^ 4) *
      Real.exp (-(b / 2 * c ^ 2 / width ν s)) := by
    have hw : 0 < width ν s := hwpos s hs.1
    have hwc : width ν s ≤ c ^ 2 := hwle s hs.2
    have hP := cg_bounds (β := b / 2) hβ hc0 hw hwc
    have hP4 : cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s) ≤ cgM (b / 2) / width ν s ^ 4 := by
      rw [le_div_iff₀ (pow_pos hw 4)]
      linarith [hP.2.2, mul_comm (width ν s ^ 4) (cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s))]
    have hXeq : Real.exp (-(b / 2 * c ^ 2 * (width ν s)⁻¹)) =
        Real.exp (-(b / 2 * c ^ 2 / width ν s)) := by
      congr 1
    rw [hQ s, hXeq]
    calc 2 * C * ν⁻¹ ^ 2 * (Real.exp (-(b / 2 * c ^ 2 / width ν s)) *
          cgPoly (b / 2 * c ^ 2)⁻¹ (width ν s))
        ≤ 2 * C * ν⁻¹ ^ 2 * (Real.exp (-(b / 2 * c ^ 2 / width ν s)) *
          (cgM (b / 2) / width ν s ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP4 (Real.exp_pos _).le)
            (mul_nonneg (mul_nonneg two_pos.le hC.le) (sq_nonneg _))
      _ = 2 * C * cgM (b / 2) / (ν ^ 2 * width ν s ^ 4) *
          Real.exp (-(b / 2 * c ^ 2 / width ν s)) := by
          field_simp <;> ring
  exact hEQ.trans hfinal

end UnforcedLeray.Short.PartI
