import UnforcedLeray.Lib.Cylinder.WeightDerivs

/-!
# The centred seam weight `ρc`: derivative bounds, dilation, cell integral (INF13, CY02)


§5 CY02, last line: "the same three bounds for `ρc` on the centred cell (the B0343 constant is
computed from them)".  Blueprint units B0242 (`paper/main.tex` lines 4171-4184: the centred
weight `(1+q²+η²)^m` on the centred cell) and B0271 (lines 4569-4578: comparable weights with
`c`-independent derivative ratios).

* `norm_iteratedFDeriv_ρc_le`: `‖Dⁿ ρc‖ ≤ 4 ρc`;
* `norm_iteratedFDeriv_rpow_ρc_le`: for every order `n` and real exponent `s`,
  `‖Dⁿ(ρc^s)‖ ≤ C ρc^s` (same proof as `B0656.norm_iteratedFDeriv_rho_rpow_le`, copied from

  of `rhoConst n`); `ρc` does not depend on the period, so neither does `C`;
* `ρc_dilate`: `ρc(√a z) = 1 + a (ρc z - 1)` (the analogue of `ρw_dilate`);
* `setIntegral_rpow_neg_ρc_le`: `∫_{cell c} ρc^{-m} ≤ ∫_{ℝ²} ρc^{-m}` for `m > 1`, uniformly in
  the period.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ContDiff Nat

namespace UnforcedLeray.Cyl

/-- Every derivative of `ρc` is bounded by `4 ρc`. -/
theorem norm_iteratedFDeriv_ρc_le (n : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ n ρc z‖ ≤ 4 * ρc z := by
  have hρ := one_le_ρc z
  rcases n with _ | n
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (ρc_pos z)]
    linarith
  have hsplit : ρc = ((fun _ : Plane => (1 : ℝ)) + fun w : Plane => w.1 ^ 2) +
      fun w : Plane => w.2 ^ 2 := by
    funext w
    rfl
  have h1 : ContDiff ℝ ∞ (fun _ : Plane => (1 : ℝ)) := contDiff_const
  have hQ : ContDiff ℝ ∞ (fun w : Plane => w.1 ^ 2) := by fun_prop
  have hS : ContDiff ℝ ∞ (fun w : Plane => w.2 ^ 2) := by fun_prop
  have hle : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have h1Q : ContDiff ℝ ∞ ((fun _ : Plane => (1 : ℝ)) + fun w : Plane => w.1 ^ 2) := h1.add hQ
  have hD : iteratedFDeriv ℝ (n + 1) ρc z =
      iteratedFDeriv ℝ (n + 1) (fun w : Plane => w.1 ^ 2) z +
        iteratedFDeriv ℝ (n + 1) (fun w : Plane => w.2 ^ 2) z := by
    rw [hsplit, iteratedFDeriv_add_apply (h1Q.contDiffAt.of_le hle) (hS.contDiffAt.of_le hle),
      iteratedFDeriv_add_apply (h1.contDiffAt.of_le hle) (hQ.contDiffAt.of_le hle),
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n), Pi.zero_apply, zero_add]
  rw [hD]
  refine (norm_add_le _ _).trans ?_
  have ha := (B0656.norm_iteratedFDeriv_comp_fst_le (f := fun x : ℝ => x ^ 2) (by fun_prop)
    (n + 1) z).trans (B0656.abs_iteratedDeriv_sq_le (n + 1) z.1)
  have hb := (B0656.norm_iteratedFDeriv_comp_snd_le (f := fun x : ℝ => x ^ 2) (by fun_prop)
    (n + 1) z).trans (B0656.abs_iteratedDeriv_sq_le (n + 1) z.2)
  have : ρc z = 1 + z.1 ^ 2 + z.2 ^ 2 := rfl
  nlinarith

/-- **Derivative bounds for powers of the centred weight** (CY02 for `ρc`; B0242, B0271): for
every order `n` and real exponent `s` there is `C` with `‖Dⁿ(ρc^s)(z)‖ ≤ C ρc(z)^s` for all `z`.
Adapted from `B0656.norm_iteratedFDeriv_rho_rpow_le`
-/
theorem norm_iteratedFDeriv_rpow_ρc_le (n : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Plane,
      ‖iteratedFDeriv ℝ n (fun w => ρc w ^ s) z‖ ≤ C * ρc z ^ s := by
  set Cs : ℝ := ∑ i ∈ Finset.range (n + 1),
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ s) (Ioi 0) 1‖ with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨n ! * Cs * (4 : ℝ) ^ n, by positivity, ?_⟩
  intro z
  set c := ρc z with hc_def
  have hc : 0 < c := ρc_pos z
  set f : Plane → ℝ := fun w => c⁻¹ * ρc w with hf_def
  have hfz : f z = 1 := by
    simp only [f]
    exact inv_mul_cancel₀ hc.ne'
  have hfun : (fun w => ρc w ^ s) = fun w => c ^ s • ((fun t : ℝ => t ^ s) ∘ f) w := by
    funext w
    simp only [Function.comp, f, smul_eq_mul]
    rw [Real.mul_rpow (inv_nonneg.2 hc.le) (ρc_pos w).le, Real.inv_rpow hc.le, ← mul_assoc,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  have hf_smooth : ContDiff ℝ ∞ f := contDiff_const.mul contDiff_ρc
  have hg : ContDiffOn ℝ n (fun t : ℝ => t ^ s) (Ioi 0) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hcomp : ‖iteratedFDeriv ℝ n ((fun t : ℝ => t ^ s) ∘ f) z‖ ≤
      n ! * Cs * (4 : ℝ) ^ n := by
    apply norm_iteratedFDeriv_comp_le' (t := Ioi 0) (N := n)
    · rintro _ ⟨w, rfl⟩
      simp only [f, mem_Ioi]
      exact mul_pos (inv_pos.2 hc) (ρc_pos w)
    · exact isOpen_Ioi.uniqueDiffOn
    · exact hg
    · exact contDiff_infty.1 hf_smooth n
    · exact le_rfl
    · intro i hi
      rw [hfz, hCs]
      exact Finset.single_le_sum (f := fun i =>
        ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t ^ s) (Ioi 0) 1‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · intro i hi1 _
      have hfeq : f = fun w => c⁻¹ • ρc w := rfl
      rw [hfeq, iteratedFDeriv_const_smul_apply'
        (contDiff_ρc.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
      have hb := norm_iteratedFDeriv_ρc_le i z
      calc c⁻¹ * ‖iteratedFDeriv ℝ i ρc z‖ ≤ c⁻¹ * (4 * c) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hc.le)
        _ = 4 := by field_simp
        _ ≤ (4 : ℝ) ^ i := by
            calc (4 : ℝ) = 4 ^ 1 := (pow_one _).symm
              _ ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hi1
  have hsmooth_at : ContDiffAt ℝ n ((fun t : ℝ => t ^ s) ∘ f) z := by
    apply ContDiffAt.comp
    · rw [hfz]
      exact Real.contDiffAt_rpow_const_of_ne one_ne_zero
    · exact (contDiff_infty.1 hf_smooth n).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply' hsmooth_at, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hc s)]
  calc c ^ s * ‖iteratedFDeriv ℝ n ((fun t : ℝ => t ^ s) ∘ f) z‖
      ≤ c ^ s * (n ! * Cs * (4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hc s).le
    _ = n ! * Cs * (4 : ℝ) ^ n * c ^ s := mul_comm _ _

/-- Dilation of the centred weight: `ρc(√a z) = 1 + a (ρc z - 1)` for `a ≥ 0`. -/
theorem ρc_dilate {a : ℝ} (ha : 0 ≤ a) (z : Plane) :
    ρc (Real.sqrt a • z) = 1 + a * (ρc z - 1) := by
  simp only [ρc, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, Real.sq_sqrt ha]
  ring

/-- The cell integral of `ρc^{-m}`, `m > 1`, is bounded uniformly in the period (CY02 for
`ρc`). -/
theorem setIntegral_rpow_neg_ρc_le {m : ℝ} (hm : 1 < m) :
    ∃ C, ∀ c : ℝ, ∫ z in cell c, ρc z ^ (-m) ≤ C :=
  ⟨∫ z, ρc z ^ (-m), fun _ => setIntegral_le_integral (integrable_rpow_neg_ρc hm)
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (ρc_pos z).le _)⟩

end UnforcedLeray.Cyl
