import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Hp

/-!
# `PartIII-b:C/inst/11/3/2`: Gaussian cell bound for `ψ^p` with constant matrix (source 4974-4975, 5063-5079)

The `j`-th term is `psiPhi ν s C (x_j)` (translate of one profile, as in `psipATerm_eq_phi`);
`psiPhi_abs_le` and the generic lattice argument of `Hp/Common.lean` give the cell bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l3_psi_term_eq (ν s : ℝ) (C : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x)) =
      psiPhi ν s C (xj ν j x) := by
  unfold psiPhi
  rw [gp_fderiv_psij]
  unfold psij
  ring

theorem l3_psi_term_bound (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (C : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    ‖merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x))‖ ≤
      8 * Kmat C * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
  rw [l3_psi_term_eq, Real.norm_eq_abs]
  refine (psiPhi_abs_le ν s ha1 C (xj ν j x)).trans ?_
  set y := xj ν j x
  have hE := (Real.exp_pos (-(sq2 y) / (4 * ageA ν s))).le
  have hK := Kmat_nonneg C
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hq := l3_norm_sq_le_sq2 y
  have hp1 : 1 ≤ 1 + sq2 y := by unfold sq2; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have hr1 : ‖y‖ ≤ 1 + sq2 y := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have h3 : (1 + ‖y‖) ^ 3 ≤ 4 * (1 + sq2 y) ^ 2 := by
    have h2 : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + sq2 y) := by nlinarith [sq_nonneg (‖y‖ - 1)]
    have h1 : 1 + ‖y‖ ≤ 2 * (1 + sq2 y) := by linarith
    calc (1 + ‖y‖) ^ 3 = (1 + ‖y‖) ^ 2 * (1 + ‖y‖) := by ring
      _ ≤ (2 * (1 + sq2 y)) * (2 * (1 + sq2 y)) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hE) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK)
  calc 2 * Kmat C * ((1 + ‖y‖) ^ 3 * Real.exp (-(sq2 y) / (4 * ageA ν s)))
      ≤ 2 * Kmat C * (4 * (1 + sq2 y) ^ 2 * Real.exp (-(sq2 y) / (4 * ageA ν s))) := by
        simpa [mul_assoc] using this
    _ = _ := by ring

theorem l3_psi_term_measurable (ν s : ℝ) (C : Mat3) (j : ℤ) :
    Measurable (fun x : ℝ × ℝ =>
      merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x))) := by
  have e : (fun x : ℝ × ℝ =>
      merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x))) =
      fun x : ℝ × ℝ => psiPhi ν s C (xj ν j x) := by
    funext x; exact l3_psi_term_eq ν s C j x
  rw [e]
  apply Continuous.measurable
  unfold psiPhi merApply xj sq2
  fun_prop

theorem hAcPiecePsi : HAcPiecePsi := by
  obtain ⟨C1, hC1⟩ := fAcLatticeWeight
  obtain ⟨K2, hK2, hcell⟩ := l3_cell_bound
  refine ⟨32 * Real.sqrt (max C1 0 * K2), by positivity, ?_⟩
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
  have hmeas : Measurable (psipAC ν s C) := by
    unfold psipAC
    exact l3_measurable_ztsum _ (fun j => l3_psi_term_measurable ν s C j)
  refine ⟨hmeas, ?_⟩
  have hM : 0 ≤ 32 * frob C := by positivity
  have hpt : ∀ x : ℝ × ℝ, ‖psipAC ν s C x‖ ^ 2 ≤
      (max C1 0 * (32 * frob C) ^ 2) * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by
    intro x
    have := l3_lattice_sq C1 hC1 ν s x hν hν1 hs hsT
      (fun j => merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x)))
      (32 * frob C) hM (fun j => by
        refine (l3_psi_term_bound ν s ha1 C j x).trans ?_
        have hE := (Real.exp_pos (-(sq2 (xj ν j x)) / (4 * ageA ν s))).le
        have hP : 0 ≤ (1 + sq2 (xj ν j x)) ^ 2 := sq_nonneg _
        have : 8 * Kmat C ≤ 32 * frob C := by linarith
        calc 8 * Kmat C * (1 + sq2 (xj ν j x)) ^ 2 *
              Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            ≤ 32 * frob C * (1 + sq2 (xj ν j x)) ^ 2 *
              Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by gcongr)
    exact this
  have h := hcell ν s hν hν1 hs hsT (fun x => ‖psipAC ν s C x‖)
    (max C1 0 * (32 * frob C) ^ 2) (by positivity) (fun x => by simpa using hpt x)
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have : Real.sqrt (max C1 0 * K2) ^ 2 = max C1 0 * K2 :=
    Real.sq_sqrt (mul_nonneg (le_max_right _ _) hK2)
  have e2 : (32 * Real.sqrt (max C1 0 * K2)) ^ 2 = 1024 * (max C1 0 * K2) := by
    rw [mul_pow, this]; ring
  rw [e2]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
