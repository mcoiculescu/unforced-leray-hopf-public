import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3_3

/-!
# Proof of `SCCylDeriv` (source 4178-4186)

`cylR y = √(y₀² + y₁²)` is smooth off the axis and homogeneous of degree one in `(y₀,y₁)`,
independent of `y₂`. The bound `‖D^i cylR y‖ ≤ K r^{1-i}` (`r = cylR y`) follows from the
boundedness of `D^i cylR` on the compact set `{cylR = 1, y₂ = 0}`, after shifting in `y₂`
(`iteratedFDeriv_comp_add_right`) and rescaling by `r⁻¹` (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ScCylDerivAux

theorem cylR_smul_pos {ε : ℝ} (hε : 0 < ε) (y : Vec3) : cylR (ε • y) = ε * cylR y := by
  unfold cylR
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (ε * y 0) ^ 2 + (ε * y 1) ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

theorem contDiffAt_cylR_of_pos {p : Vec3} (hp : 0 < cylR p) : ContDiffAt ℝ 7 cylR p := by
  have hq : ContDiffAt ℝ 7 (fun z : Vec3 => z 0 ^ 2 + z 1 ^ 2) p := by
    fun_prop
  have hne : (fun z : Vec3 => z 0 ^ 2 + z 1 ^ 2) p ≠ 0 := by
    intro h
    have h' : cylR p = 0 := by
      unfold cylR
      simp only at h
      rw [h, Real.sqrt_zero]
    exact hp.ne' h'
  exact hq.sqrt hne

theorem isOpen_cylPos : IsOpen {z : Vec3 | 0 < cylR z} :=
  isOpen_lt continuous_const continuous_cylR

theorem isCompact_circle0 : IsCompact {p : Vec3 | cylR p = 1 ∧ p 2 = 0} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq continuous_cylR continuous_const).inter
      (isClosed_eq (continuous_apply 2) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : Vec3)) (r := 1)).subset ?_
    rintro p ⟨h1, h2⟩
    rw [mem_closedBall_zero_iff]
    have hsq : p 0 ^ 2 + p 1 ^ 2 = 1 := by
      unfold cylR at h1
      exact Real.sqrt_eq_one.1 h1
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 ?_
    intro j
    fin_cases j
    · show ‖p 0‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (p 1)])
    · show ‖p 1‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (p 0)])
    · show ‖p 2‖ ≤ 1
      rw [h2]
      simp

/-- Bound for `D^i cylR` on the unit circle `{cylR = 1}`, reduced to `{cylR = 1, y₂ = 0}`. -/
theorem exists_bound_circle (i : ℕ) (hi : i ≤ 7) :
    ∃ C : ℝ, ∀ u : Vec3, cylR u = 1 → ‖iteratedFDeriv ℝ i cylR u‖ ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ i cylR) {p : Vec3 | cylR p = 1 ∧ p 2 = 0} := by
    intro p hp
    obtain ⟨h1, _⟩ := hp
    have hpos : 0 < cylR p := by rw [h1]; exact one_pos
    exact ((contDiffAt_cylR_of_pos hpos).continuousAt_iteratedFDeriv
      (by exact_mod_cast hi)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_circle0).exists_bound_of_continuousOn hcont
  refine ⟨C, fun u hu => ?_⟩
  set a : Vec3 := ![0, 0, u 2] with ha
  set p : Vec3 := ![u 0, u 1, 0] with hp
  have hfa : (fun z : Vec3 => cylR (z + a)) = cylR := by
    funext z
    unfold cylR
    simp [ha]
  have hpa : p + a = u := by
    funext j
    fin_cases j <;> simp [ha, hp]
  have hGu : iteratedFDeriv ℝ i cylR u = iteratedFDeriv ℝ i cylR p := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := cylR) i a p
    rw [hfa, hpa] at h
    exact h.symm
  have hpS : cylR p = 1 ∧ p 2 = 0 := by
    refine ⟨?_, ?_⟩
    · unfold cylR at hu ⊢
      simpa [hp] using hu
    · simp [hp]
  rw [hGu]
  exact hC p hpS

/-- Homogeneity bound on `{cylR > 0}`: `‖D^i cylR y‖ ≤ C r^{1-i}`, `r = cylR y`. -/
theorem norm_le_scaled (i : ℕ) (hi : i ≤ 7) {C : ℝ}
    (hC : ∀ u : Vec3, cylR u = 1 → ‖iteratedFDeriv ℝ i cylR u‖ ≤ C) (y : Vec3) (hy : 0 < cylR y) :
    ‖iteratedFDeriv ℝ i cylR y‖ ≤ C * cylR y ^ ((1 : ℝ) - i) := by
  have hU := isOpen_cylPos
  have hCD : ContDiffOn ℝ 7 cylR {z : Vec3 | 0 < cylR z} :=
    fun z hz => (contDiffAt_cylR_of_pos hz).contDiffWithinAt
  have hi' : (i : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hi
  let g : Vec3 →L[ℝ] Vec3 := (cylR y)⁻¹ • ContinuousLinearMap.id ℝ Vec3
  have hgx : ∀ x, g x = (cylR y)⁻¹ • x := fun x => by simp [g]
  have hpre : IsOpen (g ⁻¹' {z : Vec3 | 0 < cylR z}) := hU.preimage g.continuous
  have hmem : g y ∈ {z : Vec3 | 0 < cylR z} := by
    show 0 < cylR (g y)
    rw [hgx, cylR_smul_pos (inv_pos.2 hy)]
    positivity
  have hyPre : y ∈ g ⁻¹' {z : Vec3 | 0 < cylR z} := hmem
  have hfun : (cylR ∘ g) = fun x => (cylR y)⁻¹ • cylR x := by
    funext x
    simp only [Function.comp, hgx]
    rw [cylR_smul_pos (inv_pos.2 hy), smul_eq_mul]
  have hLHS : iteratedFDeriv ℝ i (fun x => (cylR y)⁻¹ • cylR x) y
      = (cylR y)⁻¹ • iteratedFDeriv ℝ i cylR y :=
    iteratedFDeriv_const_smul_apply' ((contDiffAt_cylR_of_pos hy).of_le (by exact_mod_cast hi))
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right g hCD hU.uniqueDiffOn
    hpre.uniqueDiffOn hmem (i := i) hi'
  rw [iteratedFDerivWithin_of_isOpen i hpre hyPre,
    iteratedFDerivWithin_of_isOpen i hU hmem] at key
  have E : (cylR y)⁻¹ • iteratedFDeriv ℝ i cylR y
      = (iteratedFDeriv ℝ i cylR (g y)).compContinuousLinearMap (fun _ => g) := by
    rw [← hLHS, ← key, hfun]
  have hgn : ‖g‖ ≤ (cylR y)⁻¹ := by
    calc ‖g‖ = ‖(cylR y)⁻¹‖ * ‖ContinuousLinearMap.id ℝ Vec3‖ := norm_smul _ _
      _ ≤ (cylR y)⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.2 hy.le)]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hy.le)
      _ = (cylR y)⁻¹ := mul_one _
  have hprod : ∏ _j : Fin i, ‖g‖ ≤ ((cylR y)⁻¹) ^ i := by
    calc ∏ _j : Fin i, ‖g‖ ≤ ∏ _j : Fin i, (cylR y)⁻¹ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hgn)
      _ = ((cylR y)⁻¹) ^ i := by simp
  have h2 : ‖(cylR y)⁻¹ • iteratedFDeriv ℝ i cylR y‖
      ≤ ‖iteratedFDeriv ℝ i cylR (g y)‖ * ((cylR y)⁻¹) ^ i := by
    rw [E]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  have hu1 : cylR (g y) = 1 := by
    rw [hgx, cylR_smul_pos (inv_pos.2 hy)]
    exact inv_mul_cancel₀ hy.ne'
  have hGC : ‖iteratedFDeriv ℝ i cylR (g y)‖ ≤ C := hC (g y) hu1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hy.le)] at h2
  have h3 : (cylR y)⁻¹ * ‖iteratedFDeriv ℝ i cylR y‖ ≤ C * ((cylR y)⁻¹) ^ i :=
    h2.trans (mul_le_mul_of_nonneg_right hGC (pow_nonneg (inv_nonneg.2 hy.le) i))
  rw [Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast]
  calc ‖iteratedFDeriv ℝ i cylR y‖
      = cylR y * ((cylR y)⁻¹ * ‖iteratedFDeriv ℝ i cylR y‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]
    _ ≤ cylR y * (C * ((cylR y)⁻¹) ^ i) := mul_le_mul_of_nonneg_left h3 hy.le
    _ = C * (cylR y / cylR y ^ i) := by rw [inv_pow]; ring

end ScCylDerivAux

theorem scCylDeriv : SCCylDeriv := by
  intro i hi
  obtain ⟨C, hC⟩ := ScCylDerivAux.exists_bound_circle i hi
  exact ⟨C, fun y hy => ScCylDerivAux.norm_le_scaled i hi hC y hy⟩

end UnforcedLeray.Short.PartIIIb.Concrete
