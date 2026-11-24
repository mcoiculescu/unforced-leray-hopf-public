import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Homog
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# `TransJet` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/4`)

Source `the November 2 reference manuscript`,
lines 1208-1210: `η = R z/r`. Here `Axi.trans R y = R * y 2 / ϱ y = (R * y 2) * (ϱ y)⁻¹`.

* `(ϱ)⁻¹` has jets `≤ C_j ϱ^(-1-j)` (`homogJets`, `d = -1`, order `0` by hand).
* `y ↦ R * y 2` is linear: its order-`0` norm is `R |y 2|`, order-`1` norm is `R ‖proj 2‖`, and
  its orders `≥ 2` vanish (the derivative is the constant CLM).
* Leibniz on the open set `axisᶜ` (`norm_iteratedFDerivWithin_mul_le`) gives the bound with the
  factor `(1 + |y 2|/ϱ)`: the order-`0` term carries `|y 2|`, the order-`1` term carries `ϱ^(-m)`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Scalar estimate for the order-`0` Leibniz term. -/
theorem transJet_key0 {R A X P q K : ℝ} (hP : 0 < P) (hX : 0 ≤ X) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hRA : R * A ≤ K) :
    R * q * (A * (X * P⁻¹)) ≤ K * (X * (1 + q / P)) := by
  have e : R * q * (A * (X * P⁻¹)) = (R * A) * X * (q / P) := by
    rw [div_eq_mul_inv]
    ring
  have hqP : 0 ≤ q / P := div_nonneg hq hP.le
  rw [e]
  calc (R * A) * X * (q / P) ≤ K * X * (q / P) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRA hX) hqP
    _ ≤ K * X * (1 + q / P) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK hX)
    _ = K * (X * (1 + q / P)) := by ring

/-- Scalar estimate for the order-`1` Leibniz term. -/
theorem transJet_key1 {B X q P K : ℝ} (hX : 0 ≤ X) (hq : 0 ≤ q) (hP : 0 < P) (hK : 0 ≤ K)
    (hB : B ≤ K) : B * X ≤ K * (X * (1 + q / P)) := by
  have hqP : 0 ≤ q / P := div_nonneg hq hP.le
  calc B * X ≤ K * X := mul_le_mul_of_nonneg_right hB hX
    _ ≤ K * (X * (1 + q / P)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hX (by linarith)) hK

theorem transJet : TransJet := by
  intro R hR m
  -- (1) jets of the inverse radius
  have hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ j (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ ≤
        C * Axi.ϱ y ^ (-1 - (j : ℝ)) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hjpos
    · refine ⟨1, zero_le_one, fun y hy => ?_⟩
      subst hj
      simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, one_mul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (Axi.ϱ_nonneg y), Real.rpow_neg_one]
      exact le_rfl
    · have hf : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) Axi.axisᶜ :=
        Axi.contDiffOn_ϱ.inv (fun y hy => Axi.ϱ_ne_zero hy)
      have hinv : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ,
          (Axi.ϱ (y + t • Axi.e3))⁻¹ = (Axi.ϱ y)⁻¹ := by
        intro y hy t
        have hϱ : Axi.ϱ (y + t • Axi.e3) = Axi.ϱ y := by
          unfold Axi.ϱ
          simp [Axi.e3_apply]
        rw [hϱ]
      have hsc : ∀ lam : ℝ, 0 < lam → ∀ z : UnforcedLeray.Space, z ∉ Axi.axis →
          (Axi.ϱ (lam • z))⁻¹ = lam ^ (-1 : ℝ) • (Axi.ϱ z)⁻¹ + 0 := by
        intro lam hlam z hz
        rw [Axi.ϱ_smul, abs_of_pos hlam, Real.rpow_neg_one, smul_eq_mul, add_zero, mul_inv]
      obtain ⟨C, hC0, hCb⟩ :=
        homogJets ℝ (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) (-1) (fun _ => 0) hf hinv hsc
          j hjpos
      exact ⟨C, hC0, hCb⟩
  choose Cb hCb0 hCb using hb
  obtain ⟨Kc, hKc0, hCbK⟩ : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ j : ℕ, j ≤ m → Cb j ≤ Kc :=
    ⟨∑ j ∈ Finset.range (m + 1), Cb j, Finset.sum_nonneg (fun j _ => hCb0 j),
      fun j hj => Finset.single_le_sum (f := Cb) (fun k _ => hCb0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))⟩
  -- (2) the linear factor `y ↦ R * y 2`
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ,
      M = ‖(EuclideanSpace.proj (2 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact norm_nonneg _
  obtain ⟨Lc, hLc⟩ : ∃ L : UnforcedLeray.Space →L[ℝ] ℝ,
      L = R • (EuclideanSpace.proj (2 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ) := ⟨_, rfl⟩
  have ha : (fun y : UnforcedLeray.Space => R * y 2) = ⇑Lc := by
    funext y
    rw [hLc]
    simp
  have hfd : fderiv ℝ (fun y : UnforcedLeray.Space => R * y 2) = fun _ => Lc := by
    rw [ha]
    funext y
    exact Lc.fderiv
  have hA0 : ∀ y : UnforcedLeray.Space,
      ‖iteratedFDeriv ℝ 0 (fun y : UnforcedLeray.Space => R * y 2) y‖ = R * |y 2| := by
    intro y
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hR]
  have hA1 : ∀ y : UnforcedLeray.Space,
      ‖iteratedFDeriv ℝ 1 (fun y : UnforcedLeray.Space => R * y 2) y‖ = R * M := by
    intro y
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0)
      (f := fun y : UnforcedLeray.Space => R * y 2) (x := y)
    rw [hfd] at h1
    simp only [zero_add, norm_iteratedFDeriv_zero] at h1
    rw [← h1, hLc, hMdef, norm_smul, Real.norm_of_nonneg hR.le]
  have hvan : ∀ (k : ℕ) (y : UnforcedLeray.Space),
      ‖iteratedFDeriv ℝ (k + 2) (fun y : UnforcedLeray.Space => R * y 2) y‖ = 0 := by
    intro k y
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := k + 1)
      (f := fun y : UnforcedLeray.Space => R * y 2) (x := y)
    rw [hfd, iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)] at h1
    simp only [Pi.zero_apply, norm_zero] at h1
    exact h1.symm
  have htr : Axi.trans R = fun y : UnforcedLeray.Space => R * y 2 * (Axi.ϱ y)⁻¹ := by
    funext y
    unfold Axi.trans
    rw [div_eq_mul_inv]
  -- (3) Leibniz on the open set `axisᶜ`
  have hLeib : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ m (fun y : UnforcedLeray.Space => R * y 2 * (Axi.ϱ y)⁻¹) y‖ ≤
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : UnforcedLeray.Space => R * y 2) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ := by
    intro y hy
    have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
    have hyU : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hy
    have hA : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => R * y 2) Axi.axisᶜ :=
      (show ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => R * y 2) by fun_prop).contDiffOn
    have hB : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) Axi.axisᶜ :=
      Axi.contDiffOn_ϱ.inv (fun y hy => Axi.ϱ_ne_zero hy)
    have h := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hA hB hU.uniqueDiffOn hyU (hjLe m)
    have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun y : UnforcedLeray.Space => R * y 2) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹)
            Axi.axisᶜ y‖
        = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : UnforcedLeray.Space => R * y 2) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hU hyU, iteratedFDerivWithin_of_isOpen (m - i) hU hyU]
    rw [hsum, iteratedFDerivWithin_of_isOpen m hU hyU] at h
    exact h
  -- (4) constants
  have hK0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hR.le (by linarith)) hKc0)
  have hRKc : R * Kc ≤ ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) := by
    have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have h2 : R * Kc ≤ R * (M + 1) * Kc := by
      have e : R * (M + 1) * Kc = R * Kc * (M + 1) := by ring
      rw [e]
      exact le_mul_of_one_le_right (mul_nonneg hR.le hKc0) (by linarith)
    have h3 : R * (M + 1) * Kc ≤ ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) :=
      le_mul_of_one_le_left (mul_nonneg (mul_nonneg hR.le (by linarith)) hKc0) h1
    linarith
  have hB1 : ∀ k : ℕ, k ≤ m → (m.choose 1 : ℝ) * (R * M) * Cb k ≤
      ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) := by
    intro k hk
    have hc : ((m.choose 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      rw [Nat.choose_one_right]
      exact_mod_cast Nat.le_succ m
    have hRM : R * M ≤ R * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hR.le
    have hRMn : 0 ≤ R * M := mul_nonneg hR.le hM0
    have hstep : (m.choose 1 : ℝ) * (R * M) * Cb k ≤
        ((m + 1 : ℕ) : ℝ) * (R * (M + 1)) * Kc :=
      mul_le_mul (mul_le_mul hc hRM hRMn (Nat.cast_nonneg _)) (hCbK k hk) (hCb0 k)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hR.le (by linarith)))
    calc (m.choose 1 : ℝ) * (R * M) * Cb k ≤ ((m + 1 : ℕ) : ℝ) * (R * (M + 1)) * Kc := hstep
      _ = ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) := by ring
  -- (5) each Leibniz term
  have hterm : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : UnforcedLeray.Space => R * y 2) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ ≤
        ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    intro y hy i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    have hP : 0 < Axi.ϱ y := Axi.ϱ_pos hy
    have hX : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hP.le _
    have hq : 0 ≤ |y 2| := abs_nonneg _
    have hT1 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by
      have := div_nonneg hq hP.le
      linarith
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · interval_cases i
      · -- order zero of the linear factor
        have hbm := hCb m y hy
        have hpow : Axi.ϱ y ^ (-1 - (m : ℝ)) = Axi.ϱ y ^ (-(m : ℝ)) * (Axi.ϱ y)⁻¹ := by
          rw [show (-1 - (m : ℝ)) = -(m : ℝ) + (-1) by ring, Real.rpow_add hP,
            Real.rpow_neg_one]
        rw [hpow] at hbm
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, hA0]
        have h1 : R * |y 2| * ‖iteratedFDeriv ℝ m (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ ≤
            R * |y 2| * (Cb m * (Axi.ϱ y ^ (-(m : ℝ)) * (Axi.ϱ y)⁻¹)) :=
          mul_le_mul_of_nonneg_left hbm (mul_nonneg hR.le hq)
        have h2' := transJet_key0 (R := R) (A := Cb m) (X := Axi.ϱ y ^ (-(m : ℝ)))
          (P := Axi.ϱ y) (q := |y 2|) (K := ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc)) hP hX hq hK0
          (le_trans (mul_le_mul_of_nonneg_left (hCbK m le_rfl) hR.le) hRKc)
        exact le_trans h1 h2'
      · -- order one of the linear factor
        have hm1 : 1 ≤ m := by omega
        have hbm := hCb (m - 1) y hy
        have hc2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm1, Nat.cast_one]
        rw [hc2, show (-1 - ((m : ℝ) - 1)) = -(m : ℝ) by ring] at hbm
        rw [hA1]
        have h1' : (m.choose 1 : ℝ) * (R * M) * ‖iteratedFDeriv ℝ (m - 1)
            (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ ≤
            (m.choose 1 : ℝ) * (R * M) * (Cb (m - 1) * Axi.ϱ y ^ (-(m : ℝ))) :=
          mul_le_mul_of_nonneg_left hbm
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hR.le hM0))
        have h2' := transJet_key1 (B := (m.choose 1 : ℝ) * (R * M) * Cb (m - 1))
          (X := Axi.ϱ y ^ (-(m : ℝ))) (q := |y 2|) (P := Axi.ϱ y)
          (K := ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc)) hX hq hP hK0
          (hB1 (m - 1) (Nat.sub_le m 1))
        have e : (m.choose 1 : ℝ) * (R * M) * (Cb (m - 1) * Axi.ϱ y ^ (-(m : ℝ))) =
            (m.choose 1 : ℝ) * (R * M) * Cb (m - 1) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        rw [e] at h1'
        exact le_trans h1' h2'
    · -- order at least two: the linear factor has vanishing derivative
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [hvan k y, mul_zero, zero_mul]
      exact mul_nonneg hK0 (mul_nonneg hX hT1)
  -- (6) assemble
  refine ⟨((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc)), ?_, fun y hy => ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _) hK0
  · rw [htr]
    have hS : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : UnforcedLeray.Space => R * y 2) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y : UnforcedLeray.Space => (Axi.ϱ y)⁻¹) y‖ ≤
        ∑ _i ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℝ) * (R * (M + 1) * Kc) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
      Finset.sum_le_sum (fun i hi => hterm y hy i hi)
    refine le_trans (hLeib y hy) (le_trans hS (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
