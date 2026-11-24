import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Hp.Common
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart

/-!
# `PartIII-b:C/inst/11/3/1`: Gaussian cell bound for `h^p` with constant matrix (source 4973, 5063-5079)

Term bound `‖T_j(x)‖ ≤ 2 Kmat(C) (1+|x_j|²)² e^{-|x_j|²/(4a)}` (explicit `∇V_j`, `gp_fderiv_Vj_norm`),
then the generic lattice argument `l3_lattice_sq` and cell integral `l3_cell_bound`;
measurability from the continuity of each term and `l3_measurable_ztsum`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l3_norm_sq_le_sq2 (y : ℝ × ℝ) : ‖y‖ ^ 2 ≤ sq2 y := by
  unfold sq2
  have h1 : ‖y.1‖ ^ 2 = y.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖y.2‖ ^ 2 = y.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have : ‖y‖ = ‖y.1‖ ∨ ‖y‖ = ‖y.2‖ := by
    show max ‖y.1‖ ‖y.2‖ = ‖y.1‖ ∨ max ‖y.1‖ ‖y.2‖ = ‖y.2‖
    rcases le_total ‖y.1‖ ‖y.2‖ with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  rcases this with h | h
  · rw [h, h1]; nlinarith [sq_nonneg y.2]
  · rw [h, h2]; nlinarith [sq_nonneg y.1]

theorem l3_hp_term_bound (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (C : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    ‖merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C (xj ν j x))‖ ≤
      2 * Kmat C * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
  have ha0 : 0 < ageA ν s := by linarith
  set y := xj ν j x with hy
  set E := Real.exp (-(sq2 y) / (4 * ageA ν s)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hK := Kmat_nonneg C
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hq := l3_norm_sq_le_sq2 y
  have hi1 : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hi0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hdiv : ‖y‖ ^ 2 / ageA ν s ≤ ‖y‖ ^ 2 := div_le_self (sq_nonneg _) ha1
  have hv : ‖merApply C y‖ ≤ Kmat C * ‖y‖ := gp_merApply_norm_le C y
  have n1 : ‖merApply C (Vj ν s j x)‖ ≤ Kmat C * (E * ‖y‖) := by
    refine (gp_merApply_norm_le C _).trans ?_
    rw [gp_Vj_norm_eq]
    show Kmat C * ((ageA ν s ^ 2)⁻¹ * E * ‖y‖) ≤ _
    refine mul_le_mul_of_nonneg_left ?_ hK
    nlinarith [mul_nonneg hE0 hr0, mul_nonneg (sub_nonneg.2 hi1) (mul_nonneg hE0 hr0)]
  have n2 : ‖fderiv ℝ (Vj ν s j) x (merApply C y)‖ ≤ E * (1 + ‖y‖ ^ 2) * (Kmat C * ‖y‖) := by
    refine (gp_fderiv_Vj_norm ν s ha0 j x (merApply C y)).trans ?_
    have h1 : (ageA ν s ^ 2)⁻¹ * E * (1 + ‖y‖ ^ 2 / ageA ν s) ≤ E * (1 + ‖y‖ ^ 2) := by
      have : 1 + ‖y‖ ^ 2 / ageA ν s ≤ 1 + ‖y‖ ^ 2 := by linarith
      calc (ageA ν s ^ 2)⁻¹ * E * (1 + ‖y‖ ^ 2 / ageA ν s)
          ≤ 1 * E * (1 + ‖y‖ ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hi1 hE0) this (by positivity) (by positivity)
        _ = _ := by ring
    calc _ ≤ (E * (1 + ‖y‖ ^ 2)) * ‖merApply C y‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hsum : ‖merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C y)‖ ≤
      Kmat C * (E * ‖y‖) + E * (1 + ‖y‖ ^ 2) * (Kmat C * ‖y‖) :=
    (norm_sub_le _ _).trans (add_le_add n1 n2)
  refine hsum.trans ?_
  have hr1 : ‖y‖ ≤ 1 + sq2 y := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hp1 : 1 ≤ 1 + sq2 y := by unfold sq2; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have hA : ‖y‖ ≤ (1 + sq2 y) ^ 2 := by nlinarith
  have hB : (1 + ‖y‖ ^ 2) * ‖y‖ ≤ (1 + sq2 y) ^ 2 := by
    have : 1 + ‖y‖ ^ 2 ≤ 1 + sq2 y := by linarith
    calc (1 + ‖y‖ ^ 2) * ‖y‖ ≤ (1 + sq2 y) * (1 + sq2 y) :=
          mul_le_mul this hr1 hr0 (by linarith)
      _ = _ := by ring
  have : Kmat C * (E * ‖y‖) + E * (1 + ‖y‖ ^ 2) * (Kmat C * ‖y‖)
      = Kmat C * E * (‖y‖ + (1 + ‖y‖ ^ 2) * ‖y‖) := by ring
  rw [this]
  have h2 : Kmat C * E * (‖y‖ + (1 + ‖y‖ ^ 2) * ‖y‖) ≤ Kmat C * E * (2 * (1 + sq2 y) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc _ ≤ _ := h2
    _ = _ := by ring

theorem l3_hp_term_measurable (ν s : ℝ) (C : Mat3) (j : ℤ) :
    Measurable (fun x : ℝ × ℝ =>
      merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C (xj ν j x))) := by
  have e : (fun x : ℝ × ℝ =>
      merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C (xj ν j x))) =
      fun x : ℝ × ℝ => merApply C (Vj ν s j x) -
        (((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) •
          Jrot (merApply C (xj ν j x))
        + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
            (-(2 * (xj ν j x).1 * (merApply C (xj ν j x)).1
              + 2 * (xj ν j x).2 * (merApply C (xj ν j x)).2) / (4 * ageA ν s)))) •
          Jrot (xj ν j x)) := by
    funext x
    rw [gp_fderiv_Vj]
  rw [e]
  apply Continuous.measurable
  unfold merApply Vj xj Jrot sq2
  fun_prop

theorem hAcPieceHp : HAcPieceHp := by
  obtain ⟨C1, hC1⟩ := fAcLatticeWeight
  obtain ⟨K2, hK2, hcell⟩ := l3_cell_bound
  refine ⟨8 * Real.sqrt (max C1 0 * K2), by positivity, ?_⟩
  intro ν s hν hν1 hs hsT C
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hsT
    linarith [mul_comm ν s]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have hKm : Kmat C ≤ 4 * frob C := by
    unfold Kmat
    have := fAc_abs_le_frob C 0 0
    have := fAc_abs_le_frob C 0 2
    have := fAc_abs_le_frob C 2 0
    have := fAc_abs_le_frob C 2 2
    linarith
  have hf0 : 0 ≤ frob C := Real.sqrt_nonneg _
  have hmeas : Measurable (hpAC ν s C) := by
    unfold hpAC
    exact l3_measurable_ztsum _ (fun j => l3_hp_term_measurable ν s C j)
  refine ⟨hmeas, ?_⟩
  have hM : 0 ≤ 8 * frob C := by positivity
  have hpt : ∀ x : ℝ × ℝ, ‖hpAC ν s C x‖ ^ 2 ≤
      (max C1 0 * (8 * frob C) ^ 2) * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by
    intro x
    have := l3_lattice_sq C1 hC1 ν s x hν hν1 hs hsT
      (fun j => merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C (xj ν j x)))
      (8 * frob C) hM (fun j => by
        refine (l3_hp_term_bound ν s ha1 C j x).trans ?_
        have hE := (Real.exp_pos (-(sq2 (xj ν j x)) / (4 * ageA ν s))).le
        have hP : 0 ≤ (1 + sq2 (xj ν j x)) ^ 2 := sq_nonneg _
        have : 2 * Kmat C ≤ 8 * frob C := by linarith
        calc 2 * Kmat C * (1 + sq2 (xj ν j x)) ^ 2 *
              Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            ≤ 8 * frob C * (1 + sq2 (xj ν j x)) ^ 2 *
              Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by gcongr)
    exact this
  have h := hcell ν s hν hν1 hs hsT (fun x => ‖hpAC ν s C x‖)
    (max C1 0 * (8 * frob C) ^ 2) (by positivity) (fun x => by simpa using hpt x)
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have : Real.sqrt (max C1 0 * K2) ^ 2 = max C1 0 * K2 :=
    Real.sq_sqrt (mul_nonneg (le_max_right _ _) hK2)
  have e2 : (8 * Real.sqrt (max C1 0 * K2)) ^ 2 = 64 * (max C1 0 * K2) := by
    rw [mul_pow, this]; ring
  rw [e2]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
