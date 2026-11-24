import UnforcedLeray.Short.PartIIIa.FlatCausal

/-!
# Gain facts for `CoreImpliesWeighted`

Helper lemmas (SP 3541-3552, proof of `CoreImpliesWeighted`): calculus of
`g(s) = gainG γ ν s = exp(γ s/(1+νs))` and the scaling of the norms `vnorm2`, `tnorm2` under
`gainConj γ ν = g⁻¹ •`, used to rewrite the conjugated energies `E_u = g⁻² E`, `N_u = g⁻² N`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem gainG_pos (γ ν s : ℝ) : 0 < gainG γ ν s := Real.exp_pos _

theorem hasDerivAt_gainG (γ ν : ℝ) {s : ℝ} (hs : 1 + ν * s ≠ 0) :
    HasDerivAt (gainG γ ν) (gainG γ ν s * (γ / (1 + ν * s) ^ 2)) s := by
  have hc : HasDerivAt (fun t : ℝ => γ * t) γ s := by
    simpa using (hasDerivAt_id s).const_mul γ
  have hd : HasDerivAt (fun t : ℝ => 1 + ν * t) ν s := by
    simpa using ((hasDerivAt_id s).const_mul ν).const_add 1
  have h1 : HasDerivAt (fun t : ℝ => γ * t / (1 + ν * t)) (γ / (1 + ν * s) ^ 2) s := by
    refine HasDerivAt.congr_deriv (hc.div hd hs) ?_
    congr 1
    ring
  have h2 := h1.exp
  unfold gainG
  exact h2

theorem vnorm2_smul_real (a : ℝ) (z : Fin 2 → ℂ) :
    vnorm2 (a • z) = |a| * vnorm2 z := by
  unfold vnorm2
  have h : ∑ i : Fin 2, ‖(a • z) i‖ ^ 2 = a ^ 2 * ∑ i : Fin 2, ‖z i‖ ^ 2 := by
    simp [Fin.sum_univ_two, mul_pow]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem tnorm2_smul_real (a : ℝ) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (a • T) = |a| * tnorm2 T := by
  unfold tnorm2
  have h : ∑ i : Fin 2, ∑ j : Fin 2, ‖(a • T) i j‖ ^ 2 = a ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    simp [Fin.sum_univ_two, mul_pow]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- `vnorm2 (gainConj γ ν b (s,x))² = g(s)⁻² vnorm2 (b (s,x))²`. -/
theorem vnorm2_gainConj_sq (γ ν : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    vnorm2 (gainConj γ ν b p) ^ 2 = ((gainG γ ν p.1)⁻¹) ^ 2 * vnorm2 (b p) ^ 2 := by
  unfold gainConj
  rw [vnorm2_smul_real, mul_pow, sq_abs]

/-- `tnorm2 (gainConj γ ν T (s,x))² = g(s)⁻² tnorm2 (T (s,x))²`. -/
theorem tnorm2_gainConj_sq (γ ν : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν T p) ^ 2 = ((gainG γ ν p.1)⁻¹) ^ 2 * tnorm2 (T p) ^ 2 := by
  unfold gainConj
  rw [tnorm2_smul_real, mul_pow, sq_abs]

/-- The pointwise Cauchy-Schwarz bound behind `-Re⟨F̃, G̃⟩ ≤ |F̃||G̃|`:
`|∑ᵢⱼ (Re Fᵢⱼ Re Gᵢⱼ + Im Fᵢⱼ Im Gᵢⱼ)| ≤ tnorm2 F * tnorm2 G`. -/
theorem abs_sum_re_le_tnorm2_mul (F G : Fin 2 → Fin 2 → ℂ) :
    |∑ i : Fin 2, ∑ j : Fin 2, ((F i j).re * (G i j).re + (F i j).im * (G i j).im)|
      ≤ tnorm2 F * tnorm2 G := by
  unfold tnorm2
  set f : Fin 2 × Fin 2 × Fin 2 → ℝ := fun k =>
    if k.2.2 = 0 then (F k.1 k.2.1).re else (F k.1 k.2.1).im with hf
  set g : Fin 2 × Fin 2 × Fin 2 → ℝ := fun k =>
    if k.2.2 = 0 then (G k.1 k.2.1).re else (G k.1 k.2.1).im with hg
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2, ((F i j).re * (G i j).re + (F i j).im * (G i j).im)
      = ∑ k : Fin 2 × Fin 2 × Fin 2, f k * g k := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, hf, hg] <;> ring
  have hF : ∑ i : Fin 2, ∑ j : Fin 2, ‖F i j‖ ^ 2
      = ∑ k : Fin 2 × Fin 2 × Fin 2, f k ^ 2 := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, hf, Complex.sq_norm, Complex.normSq_apply] <;>
      ring
  have hG : ∑ i : Fin 2, ∑ j : Fin 2, ‖G i j‖ ^ 2
      = ∑ k : Fin 2 × Fin 2 × Fin 2, g k ^ 2 := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, hg, Complex.sq_norm, Complex.normSq_apply] <;>
      ring
  have hA : (0 : ℝ) ≤ ∑ k : Fin 2 × Fin 2 × Fin 2, f k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hsum, hF, hG, ← Real.sqrt_mul hA]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq _ f g

end UnforcedLeray.Short.IIIa
