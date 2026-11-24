import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_1

/-!
# `PartIII-b:C/rep/8/2/6/1/2`: the pointwise bookkeeping of term 1 (`Term1Pointwise`)

Source `the November 2 reference manuscript` 5470-5472, 5460-5465, 5438-5448.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Real-to-extended bookkeeping: a real bound times the common factor `N`. -/
theorem t1_mul_le {x y a b : ℝ} {N : ℝ≥0∞} (ha : 0 ≤ a)
    (h : ENNReal.ofReal |x| ≤ ENNReal.ofReal a * N) (hy : |y| ≤ b) :
    ENNReal.ofReal |x * y| ≤ ENNReal.ofReal (a * b) * N := by
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg x), ENNReal.ofReal_mul ha]
  calc ENNReal.ofReal |x| * ENNReal.ofReal |y|
      ≤ (ENNReal.ofReal a * N) * ENNReal.ofReal b :=
        mul_le_mul' h (ENNReal.ofReal_le_ofReal hy)
    _ = ENNReal.ofReal a * ENNReal.ofReal b * N := by ring

/-- Merid vectors are controlled componentwise. -/
theorem t1_merid_enorm_le (E : Merid) : ‖E‖ₑ ≤ ‖E 0‖ₑ + ‖E 1‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  simp only [Real.norm_eq_abs]
  nlinarith [mul_nonneg (abs_nonneg (E 0)) (abs_nonneg (E 1)), sq_abs (E 0), sq_abs (E 1)]

/-- Square root and the rpow exponent `3/2`. -/
theorem t1_sqrt_inv_mul_rpow {s : ℝ} (hs : 0 < s) :
    (Real.sqrt s)⁻¹ * s ^ (3 / 2 : ℝ) = s := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one,
    ← Real.sqrt_eq_rpow, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

theorem t1_s52 {s : ℝ} (hs : 0 < s) : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]

/-- Algebra of one chart component: with `U_j = r v_j + eU_j`, `Y_j = s B_j + eY_j`, `s = r r`. -/
theorem t1_identity {r s : ℝ} (hr : 0 < r) (hs : s = r * r) {n : ℕ}
    (v B eU eY : Fin n → ℝ) :
    (r)⁻¹ * (2 * ∑ j, (r * v j + eU j) * (s * B j + eY j)) - 2 * s * ∑ j, B j * v j =
      2 * ∑ j, (v j * eY j + r * eU j * B j + r⁻¹ * eU j * eY j) := by
  subst hs
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : ∀ j, r⁻¹ * (2 * ((r * v j + eU j) * (r * r * B j + eY j))) =
      2 * (r * r * (v j * B j)) + 2 * (v j * eY j + r * eU j * B j + r⁻¹ * eU j * eY j) := by
    intro j
    field_simp
    ring
  have hL : r⁻¹ * (2 * ∑ j, (r * v j + eU j) * (r * r * B j + eY j)) =
      ∑ j, (2 * (r * r * (v j * B j)) + 2 * (v j * eY j + r * eU j * B j + r⁻¹ * eU j * eY j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hvb : ∑ j, v j * B j = ∑ j, B j * v j := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hL, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hvb]
  ring


theorem t1_pow_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {a b : ℕ} (h : a ≤ b) :
    ν⁻¹ ^ a ≤ ν⁻¹ ^ b :=
  pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) h

theorem t1_pow_nonneg {ν : ℝ} (hν : 0 < ν) (k : ℕ) : 0 ≤ ν⁻¹ ^ k :=
  pow_nonneg (inv_nonneg.2 hν.le) k

/-- The common real bound `Q` of the pieces of one component (constants made nonnegative). -/
def t1Q (CMa CBa CRa w4 ν ε s : ℝ) (k : ℕ) : ℝ :=
  (CMa + CBa * CRa + CRa * CMa) * (ν⁻¹ ^ k * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4)

theorem t1_RA {ν ε s η w3 w4 CMa CBa CRa : ℝ} {kR kM kB : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 ≤ ε) (hs : 0 < s) (hCM : 0 ≤ CMa) (hCB : 0 ≤ CBa) (hCR : 0 ≤ CRa)
    (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4) (hηw : |η| * w3 ≤ w4) :
    CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * w3 ≤
      t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB) := by
  have hp : ν⁻¹ ^ kM ≤ ν⁻¹ ^ (kR + kM + kB) := t1_pow_le hν hν1 (by omega)
  have hX : 0 ≤ ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
  have hY : 0 ≤ ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by
    have := t1_pow_nonneg hν (kR + kM + kB)
    positivity
  have s1 : CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * w3 ≤
      CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by
    calc CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * w3
        = CMa * ν⁻¹ ^ kM * (ε ^ 4 * s ^ (5 / 2 : ℝ)) * (|η| * w3) := by ring
      _ ≤ CMa * ν⁻¹ ^ (kR + kM + kB) * (ε ^ 4 * s ^ (5 / 2 : ℝ)) * w4 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCM) hX)
            hηw (by positivity) (by positivity)
      _ = CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by ring
  unfold t1Q
  have e : CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 ≤
      (CMa + CBa * CRa + CRa * CMa) *
        (ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4) := by
    nlinarith [mul_nonneg (mul_nonneg hCB hCR) hY, mul_nonneg (mul_nonneg hCR hCM) hY]
  linarith


theorem t1_RB {ν ε s w3 w4 CBa CRa : ℝ} {kR kM kB : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 ≤ ε) (hs : 0 < s) (hCB : 0 ≤ CBa) (hCR : 0 ≤ CRa) (hw3 : 0 ≤ w3) (hw34 : w3 ≤ w4)
    (hw4 : 0 ≤ w4) (CMa : ℝ) (hCM : 0 ≤ CMa) :
    CBa * ν⁻¹ ^ kB * ε ^ 3 * s ^ (3 / 2 : ℝ) * (CRa * ν⁻¹ ^ kR * ε * s * w3) ≤
      t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB) := by
  have hpk : ν⁻¹ ^ kB * ν⁻¹ ^ kR ≤ ν⁻¹ ^ (kR + kM + kB) := by
    rw [← pow_add]; exact t1_pow_le hν hν1 (by omega)
  have hY : 0 ≤ ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4 := by
    have := t1_pow_nonneg hν (kR + kM + kB)
    have : 0 ≤ s ^ (3 / 2 : ℝ) := by positivity
    positivity
  have hC : 0 ≤ CBa * CRa := mul_nonneg hCB hCR
  have s1 : CBa * ν⁻¹ ^ kB * ε ^ 3 * s ^ (3 / 2 : ℝ) * (CRa * ν⁻¹ ^ kR * ε * s * w3) ≤
      CBa * CRa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4 := by
    calc CBa * ν⁻¹ ^ kB * ε ^ 3 * s ^ (3 / 2 : ℝ) * (CRa * ν⁻¹ ^ kR * ε * s * w3)
        = (CBa * CRa * (ν⁻¹ ^ kB * ν⁻¹ ^ kR)) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w3 := by ring
      _ ≤ (CBa * CRa * ν⁻¹ ^ (kR + kM + kB)) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4 := by
          apply mul_le_mul _ (hw34) hw3 (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpk hC
      _ = CBa * CRa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4 := by ring
  unfold t1Q
  rw [t1_s52 hs]
  have e : CBa * CRa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4 ≤
      (CMa + CBa * CRa + CRa * CMa) *
        (ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * (s ^ (3 / 2 : ℝ) * s) * w4) := by
    nlinarith [mul_nonneg hCM hY, mul_nonneg (mul_nonneg hCR hCM) hY]
  linarith

theorem t1_RC {ν ε s η w3 w4 CMa CRa CBa : ℝ} {kR kM kB : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : 0 < s) (hCM : 0 ≤ CMa) (hCB : 0 ≤ CBa) (hCR : 0 ≤ CRa)
    (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4) (hηw : |η| * w3 ≤ w4) :
    CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * (CRa * ν⁻¹ ^ kR * ε * w3) ≤
      t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB) := by
  have ha1 : ν⁻¹ ^ kR * ν⁻¹ ^ kM ≤ ν⁻¹ ^ (kR + kM + kB) := by
    rw [← pow_add]; exact t1_pow_le hν hν1 (by omega)
  have ha2 : ε * ε ^ 4 ≤ ε ^ 4 := mul_le_of_le_one_left (pow_nonneg hε 4) hε1
  have hY : 0 ≤ ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by
    have := t1_pow_nonneg hν (kR + kM + kB)
    positivity
  have hC : 0 ≤ CRa * CMa := mul_nonneg hCR hCM
  have s1 : CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * (CRa * ν⁻¹ ^ kR * ε * w3) ≤
      CRa * CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by
    calc CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η| * (CRa * ν⁻¹ ^ kR * ε * w3)
        = (CRa * CMa * (ν⁻¹ ^ kR * ν⁻¹ ^ kM)) * (ε * ε ^ 4) * s ^ (5 / 2 : ℝ) * (|η| * w3) := by
          ring
      _ ≤ (CRa * CMa * ν⁻¹ ^ (kR + kM + kB)) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by
          apply mul_le_mul _ hηw (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left ha1 hC) ha2 (by positivity) (by positivity)
      _ = CRa * CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 := by ring
  unfold t1Q
  have e : CRa * CMa * ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4 ≤
      (CMa + CBa * CRa + CRa * CMa) *
        (ν⁻¹ ^ (kR + kM + kB) * ε ^ 4 * s ^ (5 / 2 : ℝ) * w4) := by
    nlinarith [mul_nonneg hCM hY, mul_nonneg (mul_nonneg hCB hCR) hY]
  linarith


/-- One chart component of the substitution error, with the `N`-factor carried once. -/
theorem t1_comp {N : ℝ≥0∞} {r s ε ν η CMa CBa CRa w3 w4 : ℝ} {kR kM kB : ℕ}
    (hr : 0 < r) (hs : s = r * r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hCM : 0 ≤ CMa) (hCB : 0 ≤ CBa) (hCR : 0 ≤ CRa)
    (hw3 : 0 ≤ w3) (hw34 : w3 ≤ w4) (hw4 : 0 ≤ w4) (hηw : |η| * w3 ≤ w4)
    (v B eU eY : Fin 3 → ℝ)
    (hv : ∀ j, |v j| ≤ w3)
    (hU : ∀ j, |eU j| ≤ CRa * ν⁻¹ ^ kR * ε * r * w3)
    (hY : ∀ j, ENNReal.ofReal |eY j| ≤
      ENNReal.ofReal (CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) * N)
    (hB : ∀ j, ENNReal.ofReal |B j| ≤
      ENNReal.ofReal (CBa * ν⁻¹ ^ kB * ε ^ 3 * s ^ (3 / 2 : ℝ)) * N) :
    ENNReal.ofReal |(r)⁻¹ * (2 * ∑ j, (r * v j + eU j) * (s * B j + eY j)) -
        2 * s * ∑ j, B j * v j| ≤
      ENNReal.ofReal (18 * t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N := by
  have hs0 : 0 < s := by rw [hs]; exact mul_pos hr hr
  rw [t1_identity hr hs v B eU eY]
  have pA : ∀ j, ENNReal.ofReal |v j * eY j| ≤
      ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N := by
    intro j
    have h1 := t1_mul_le (x := eY j) (y := v j)
      (a := CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) (b := w3)
      (by positivity) (hY j) (hv j)
    rw [mul_comm (v j) (eY j)]
    refine h1.trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (t1_RA hν hν1 hε hs0 hCM hCB hCR hw3 hw4 hηw)) le_rfl
  have pB : ∀ j, ENNReal.ofReal |r * eU j * B j| ≤
      ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N := by
    intro j
    have hyB : |r * eU j| ≤ CRa * ν⁻¹ ^ kR * ε * s * w3 := by
      rw [abs_mul, abs_of_pos hr, hs]
      calc r * |eU j| ≤ r * (CRa * ν⁻¹ ^ kR * ε * r * w3) :=
            mul_le_mul_of_nonneg_left (hU j) hr.le
        _ = CRa * ν⁻¹ ^ kR * ε * (r * r) * w3 := by ring
    have h1 := t1_mul_le (x := B j) (y := r * eU j)
      (a := CBa * ν⁻¹ ^ kB * ε ^ 3 * s ^ (3 / 2 : ℝ)) (b := CRa * ν⁻¹ ^ kR * ε * s * w3)
      (by positivity) (hB j) hyB
    rw [show r * eU j * B j = B j * (r * eU j) by ring]
    refine h1.trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (t1_RB hν hν1 hε hs0 hCB hCR hw3 hw34 hw4 CMa hCM)) le_rfl
  have pC : ∀ j, ENNReal.ofReal |r⁻¹ * eU j * eY j| ≤
      ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N := by
    intro j
    have hyC : |r⁻¹ * eU j| ≤ CRa * ν⁻¹ ^ kR * ε * w3 := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hr)]
      calc r⁻¹ * |eU j| ≤ r⁻¹ * (CRa * ν⁻¹ ^ kR * ε * r * w3) :=
            mul_le_mul_of_nonneg_left (hU j) (inv_nonneg.2 hr.le)
        _ = CRa * ν⁻¹ ^ kR * ε * w3 := by field_simp
    have h1 := t1_mul_le (x := eY j) (y := r⁻¹ * eU j)
      (a := CMa * ν⁻¹ ^ kM * ε ^ 4 * s ^ (5 / 2 : ℝ) * |η|) (b := CRa * ν⁻¹ ^ kR * ε * w3)
      (by positivity) (hY j) hyC
    rw [show r⁻¹ * eU j * eY j = eY j * (r⁻¹ * eU j) by ring]
    refine h1.trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (t1_RC hν hν1 hε hε1 hs0 hCM hCB hCR hw3 hw4 hηw)) le_rfl
  have hG : ∀ j, ENNReal.ofReal (|v j * eY j| + |r * eU j * B j| + |r⁻¹ * eU j * eY j|) ≤
      3 * (ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N) := by
    intro j
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ENNReal.ofReal |v j * eY j| + ENNReal.ofReal |r * eU j * B j| +
          ENNReal.ofReal |r⁻¹ * eU j * eY j|
        ≤ ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N +
          ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N +
          ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N :=
          add_le_add (add_le_add (pA j) (pB j)) (pC j)
      _ = 3 * (ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N) := by ring
  have hreal : |2 * ∑ j, (v j * eY j + r * eU j * B j + r⁻¹ * eU j * eY j)| ≤
      2 * ∑ j, (|v j * eY j| + |r * eU j * B j| + |r⁻¹ * eU j * eY j|) := by
    rw [abs_mul, abs_two]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  calc ENNReal.ofReal |2 * ∑ j, (v j * eY j + r * eU j * B j + r⁻¹ * eU j * eY j)|
      ≤ ENNReal.ofReal (2 * ∑ j, (|v j * eY j| + |r * eU j * B j| + |r⁻¹ * eU j * eY j|)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 2 * ∑ j : Fin 3,
          ENNReal.ofReal (|v j * eY j| + |r * eU j * B j| + |r⁻¹ * eU j * eY j|) := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    _ ≤ ENNReal.ofReal 2 * ∑ j : Fin 3, 3 * (ENNReal.ofReal (t1Q CMa CBa CRa w4 ν ε s
          (kR + kM + kB)) * N) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => hG j)
    _ = ENNReal.ofReal (18 * t1Q CMa CBa CRa w4 ν ε s (kR + kM + kB)) * N := by
        rw [Fin.sum_univ_three, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
        simp only [ENNReal.ofReal_ofNat]
        ring


theorem t1_w34 (L : ReturnLevel) (p : Chart) : trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun j _ => by positivity)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg p.2.2]) (by norm_num)

theorem t1_ηw (L : ReturnLevel) (p : Chart) :
    |p.2.2| * trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  have hS : 0 ≤ ∑ j ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg fun j _ => by positivity
  have h3 : 0 ≤ (1 + |p.2.2|) ^ 3 := by positivity
  have e : (1 + |p.2.2|) ^ 4 = (1 + |p.2.2|) ^ 3 + |p.2.2| * (1 + |p.2.2|) ^ 3 := by ring
  have hx : |p.2.2| * (1 + |p.2.2|) ^ 3 ≤ (1 + |p.2.2|) ^ 4 := by linarith
  calc |p.2.2| * ((1 + |p.2.2|) ^ 3 * ∑ j ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖))
      = (|p.2.2| * (1 + |p.2.2|) ^ 3) * ∑ j ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) := by ring
    _ ≤ (1 + |p.2.2|) ^ 4 * ∑ j ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
        mul_le_mul_of_nonneg_right hx hS
    _ = (1 + |p.2.2|) ^ 4 * ∑ j ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) := rfl

/-- The component of the term-1 ring expression at chart coefficient index `a` (Cartesian). -/
def t1Expr (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (T : LStr Pl K L)
    (p : Chart) (a : Fin 3) : ℝ :=
  (Real.sqrt p.1)⁻¹ * (2 * ∑ j : Fin 3,
      rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j *
        physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j
          (NearInst.chartY L.ε⁻¹ p) a) -
    2 * p.1 * ∑ j : Fin 3,
      Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j * emb (trainV L p.1 p.2) j

theorem t1_Expr_bound {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    {CR CM CB : ℝ} {kR kM kB : ℕ} (T : LStr Pl K L) (p : Chart)
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hp0 : 0 < p.1) (hp1 : p.1 ≤ 1 / L.ν)
    (hR : RingChartRulesAt Pl L CR kR) (hM : MeanJetAt Pl K L μ CM kM)
    (hB : BjetYoungBoundAt Pl K L μ CB kB) (a : Fin 3) :
    ENNReal.ofReal |t1Expr Pl K L μ T p a| ≤
      ENNReal.ofReal (18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1
        (kR + kM + kB)) * oldN1 Pl K L T := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hs : p.1 = Real.sqrt p.1 * Real.sqrt p.1 := (Real.mul_self_sqrt hp0.le).symm
  have hr : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hw3 : 0 ≤ trainWeight 3 L p := trainWeight_nonneg 3 L p
  have hw4 : 0 ≤ trainWeight 4 L p := trainWeight_nonneg 4 L p
  obtain ⟨hU, -, -, -⟩ := hR p hp0 hp1
  obtain ⟨-, hYj, -⟩ := hM T p hp0 hp1
  have hBy := hB T p.1 hp0 hp1
  have hv : ∀ j, |emb (trainV L p.1 p.2) j| ≤ trainWeight 3 L p := by
    intro j
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans ((norm_emb_le _).trans (trainV_le_weight 3 L hp0))
  have hUj : ∀ j, |rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j -
      Real.sqrt p.1 * emb (trainV L p.1 p.2) j| ≤
      |CR| * L.ν⁻¹ ^ kR * L.ε * Real.sqrt p.1 * trainWeight 3 L p := by
    intro j
    have h1 := PiLp.norm_apply_le (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)
      (NearInst.chartY L.ε⁻¹ p) - Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2))) j
    have h2 : |rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j -
        Real.sqrt p.1 * emb (trainV L p.1 p.2) j| ≤
        ‖rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) -
          Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2))‖ := by
      rw [← Real.norm_eq_abs]
      simpa [vecSp] using h1
    refine h2.trans (hU.trans ?_)
    gcongr
    exact le_abs_self _
  have hYj' : ∀ j, ENNReal.ofReal |physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
      (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) a - p.1 *
        Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j| ≤
      ENNReal.ofReal (|CM| * L.ν⁻¹ ^ kM * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2|) * oldN1 Pl K L T := by
    intro j
    have h2 : ENNReal.ofReal |physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
        (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) a - p.1 *
          Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j| ≤
        ‖physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
          (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) -
            p.1 • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 i j)‖ₑ := by
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      have h1 := PiLp.norm_apply_le (physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
          (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) -
            p.1 • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 i j)) a
      simpa [vecSp, Real.norm_eq_abs] using h1
    have h3 := hYj j
    refine h2.trans (h3.trans ?_)
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    gcongr
    exact le_abs_self _
  have hB'' : ∀ j, ENNReal.ofReal |Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j| ≤
      ENNReal.ofReal (|CB| * L.ν⁻¹ ^ kB * L.ε ^ 3 * p.1 ^ (3 / 2 : ℝ)) * oldN1 Pl K L T := by
    intro j
    refine (ENNReal.ofReal_le_ofReal (abs_le_frob _ a j)).trans (hBy.trans ?_)
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    gcongr
    exact le_abs_self _
  have key := t1_comp (N := oldN1 Pl K L T) (r := Real.sqrt p.1) (s := p.1) (ε := L.ε)
    (ν := L.ν) (η := p.2.2) (CMa := |CM|) (CBa := |CB|) (CRa := |CR|)
    (w3 := trainWeight 3 L p) (w4 := trainWeight 4 L p) (kR := kR) (kM := kM) (kB := kB)
    hr hs hε.le hε1 hν hν1 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hw3 (t1_w34 L p) hw4
    (t1_ηw L p) (emb (trainV L p.1 p.2))
    (fun j => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j)
    (fun j => rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j -
      Real.sqrt p.1 * emb (trainV L p.1 p.2) j)
    (fun j => physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
      (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) a - p.1 *
        Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j)
    hv hUj hYj' hB''
  have e1 : ∀ j, Real.sqrt p.1 * emb (trainV L p.1 p.2) j +
      (rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j -
        Real.sqrt p.1 * emb (trainV L p.1 p.2) j) =
      rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) j := fun j => by ring
  have e2 : ∀ j, p.1 * Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j +
      (physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
          (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) a - p.1 *
        Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 a j) =
      physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
          (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) a := fun j => by ring
  simp only [e1, e2] at key
  unfold t1Expr
  exact key

theorem t1_fderiv_comp (f : Space → Space) (y u : Space) (a : Fin 3) :
    fderiv ℝ f y u a = ∑ j : Fin 3, u j * physPd f j y a := by
  rw [fderiv_eq_sum_physPd]
  simp [Fin.sum_univ_three, physPd]

theorem t1_diff_zero {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (T : LStr Pl K L) (p : Chart) (hp0 : 0 < p.1) :
    (wardC1 Pl K L μ T p - ringT1 Pl K L μ T p) 0 = t1Expr Pl K L μ T p 0 := by
  have hk := t1_sqrt_inv_mul_rpow hp0
  unfold wardC1 coefOf ringT1 merOf t1Expr
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, mv,
    t1_fderiv_comp]
  linear_combination (-2 * ∑ j : Fin 3, Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 0 j *
    emb (trainV L p.1 p.2) j) * hk

theorem t1_diff_one {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (T : LStr Pl K L) (p : Chart) (hp0 : 0 < p.1) :
    (wardC1 Pl K L μ T p - ringT1 Pl K L μ T p) 1 = t1Expr Pl K L μ T p 2 := by
  have hk := t1_sqrt_inv_mul_rpow hp0
  unfold wardC1 coefOf ringT1 merOf t1Expr
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, mv,
    t1_fderiv_comp]
  linear_combination (-2 * ∑ j : Fin 3, Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 2 j *
    emb (trainV L p.1 p.2) j) * hk


/-- **Lemma 2** (source 5470-5472, 5460-5465, 5438-5448): the pointwise bookkeeping of term 1. -/
theorem term1Pointwise : Term1Pointwise := by
  unfold Term1Pointwise
  intro CR CM CW CB kR kM kW kB
  refine ⟨36 * (|CM| + |CB| * |CR| + |CR| * |CM|), kR + kM + kB, ?_⟩
  intro Pl K L μ hν1 hε1 hR hM _hW hB
  unfold RingTerm1At
  intro T p hp0 hp1
  unfold ringBound
  have hw4 : 0 ≤ trainWeight 4 L p := trainWeight_nonneg 4 L p
  have hν := L.ν_pos
  have hε := L.ε_pos
  have h0 := t1_Expr_bound (Pl := Pl) (K := K) (L := L) (μ := μ) (CR := CR) (CM := CM)
    (CB := CB) (kR := kR) (kM := kM) (kB := kB) T p hν1 hε1 hp0 hp1 hR hM hB 0
  have h2 := t1_Expr_bound (Pl := Pl) (K := K) (L := L) (μ := μ) (CR := CR) (CM := CM)
    (CB := CB) (kR := kR) (kM := kM) (kB := kB) T p hν1 hε1 hp0 hp1 hR hM hB 2
  have hT : 0 ≤ 18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1 (kR + kM + kB) := by
    unfold t1Q
    have hA : 0 ≤ |CM| + |CB| * |CR| + |CR| * |CM| := by positivity
    have hB' : 0 ≤ L.ν⁻¹ ^ (kR + kM + kB) * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p := by
      have := pow_nonneg (inv_nonneg.2 hν.le) (kR + kM + kB)
      have : 0 ≤ p.1 ^ (5 / 2 : ℝ) := Real.rpow_nonneg hp0.le _
      positivity
    positivity
  have hsum : ENNReal.ofReal (18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1
        (kR + kM + kB)) +
      ENNReal.ofReal (18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1
        (kR + kM + kB)) =
      ENNReal.ofReal (36 * (|CM| + |CB| * |CR| + |CR| * |CM|) * L.ν⁻¹ ^ (kR + kM + kB) *
        L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) := by
    rw [← ENNReal.ofReal_add hT hT]
    congr 1
    unfold t1Q
    ring
  refine (t1_merid_enorm_le _).trans ?_
  rw [t1_diff_zero T p hp0, t1_diff_one T p hp0, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    Real.norm_eq_abs, Real.norm_eq_abs]
  calc ENNReal.ofReal |t1Expr Pl K L μ T p 0| + ENNReal.ofReal |t1Expr Pl K L μ T p 2|
      ≤ ENNReal.ofReal (18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1
          (kR + kM + kB)) * oldN1 Pl K L T +
        ENNReal.ofReal (18 * t1Q |CM| |CB| |CR| (trainWeight 4 L p) L.ν L.ε p.1
          (kR + kM + kB)) * oldN1 Pl K L T := add_le_add h0 h2
    _ = ENNReal.ofReal (36 * (|CM| + |CB| * |CR| + |CR| * |CM|) * L.ν⁻¹ ^ (kR + kM + kB) *
        L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) * oldN1 Pl K L T := by
        rw [← add_mul, hsum]

end UnforcedLeray.Short.PartIIIb.Concrete
