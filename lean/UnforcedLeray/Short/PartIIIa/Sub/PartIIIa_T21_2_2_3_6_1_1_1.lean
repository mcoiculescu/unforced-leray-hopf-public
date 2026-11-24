import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1

/-!
# `PartIII-a:T21/2/2/3/6/1/1/1`: scaling reduction of the `d > 0` kernel leaves to `d = 1`

Source: `the November 2 reference manuscript` lines 2875-2896, 3052-3057.
The periodic kernel is homogeneous of degree `-1`: `K_d(z) = d⁻¹ K_1(z/d)`
(`(2πi)⁻¹ (π/d) cot(πz/d)`).  Hence for `ψ` a test on `C_d`, with `ψ_d(y) = ψ(d y)` a test on `C_1`,
`K_dψ(x) = d · K_1ψ_d(x/d)`, and `meanShear d Γ x = d · meanShear 1 (Γ/d²) (x/d)`.
This reduces the `d > 0` leaves to the `d = 1` instance of the `d ≥ 1` leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem cell_preimage_inv {d : ℝ} (hd : 0 < d) :
    (fun x : ℝ × ℝ => d⁻¹ • x) ⁻¹' B0579.cell 1 = B0579.cell d := by
  ext x
  simp only [B0579.cell, mem_preimage, mem_prod, mem_Ico, mem_univ, and_true, Prod.smul_fst,
    smul_eq_mul]
  have h : d⁻¹ * x.1 = x.1 / d := by ring
  rw [h, le_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem measurableSet_cell1 (c : ℝ) : MeasurableSet (B0579.cell c) := by
  unfold B0579.cell
  exact measurableSet_Ico.prod MeasurableSet.univ

theorem map_restrict_cell {d : ℝ} (hd : 0 < d) :
    (volume.restrict (B0579.cell d)).map (fun x : ℝ × ℝ => d⁻¹ • x) =
      ENNReal.ofReal (d ^ 2) • volume.restrict (B0579.cell 1) := by
  have hm : Measurable (fun x : ℝ × ℝ => d⁻¹ • x) := measurable_const_smul _
  rw [← cell_preimage_inv hd, ← Measure.restrict_map hm (measurableSet_cell1 1),
    Measure.map_addHaar_smul volume (inv_ne_zero hd.ne')]
  rw [Measure.restrict_smul]
  congr 2
  simp only [Module.finrank_prod, Module.finrank_self]
  rw [show (1 + 1 : ℕ) = 2 from rfl, inv_pow, inv_inv, abs_of_pos (by positivity)]

theorem integral_cell_scale {d : ℝ} (hd : 0 < d) (g : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell d, g x = d ^ 2 * ∫ y in B0579.cell 1, g (d • y) := by
  have hE := (MeasurableEquiv.smul₀ (d⁻¹ : ℝ) (inv_ne_zero hd.ne') :
    ℝ × ℝ ≃ᵐ ℝ × ℝ).measurableEmbedding
  have h2 : ∫ y, g (d • y) ∂((volume.restrict (B0579.cell d)).map (fun x : ℝ × ℝ => d⁻¹ • x)) =
      ∫ x in B0579.cell d, g x := by
    have := hE.integral_map (μ := volume.restrict (B0579.cell d)) (fun y : ℝ × ℝ => g (d • y))
    refine this.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    show g (d • (d⁻¹ • x)) = g x
    simp [smul_smul, hd.ne']
  rw [← h2, map_restrict_cell hd, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-! ## Scaling of the kernel, tests, kernel velocity and mean shear -/

theorem kerD_scale {d : ℝ} (hd : 0 < d) (z : ℝ × ℝ) (j : Fin 2) :
    kerD d z j = d⁻¹ * kerD 1 (d⁻¹ • z) j := by
  have hC : UnforcedLeray.Cyl.bsC d z =
      ((d⁻¹ : ℝ) : ℂ) * UnforcedLeray.Cyl.bsC 1 (d⁻¹ • z) := by
    unfold UnforcedLeray.Cyl.bsC UnforcedLeray.Kernels.cylinderBS
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have e : ((((d⁻¹ • z).1 : ℝ) : ℂ) + (((d⁻¹ • z).2 : ℝ) : ℂ) * Complex.I) =
        (d : ℂ)⁻¹ * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      ring
    rw [e]
    have e2 : (Real.pi : ℂ) * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / d =
        (Real.pi : ℂ) * ((d : ℂ)⁻¹ * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)) / ((1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2]
    push_cast
    ring
  unfold kerD UnforcedLeray.Cyl.bsKernel
  rw [hC]
  fin_cases j <;> simp [Complex.mul_re, Complex.mul_im]

theorem isCylTest_scale {d : ℝ} (hd : 0 < d) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) :
    B0579.IsCylTest 1 (fun y => ψ (d • y)) where
  smooth := hψ.smooth.comp (contDiff_const_smul d)
  periodic x := by
    have e : d • ((x.1 + 1, x.2) : ℝ × ℝ) = ((d • x).1 + d, (d • x).2) := by
      ext <;> simp [mul_add]
    show ψ (d • ((x.1 + 1, x.2) : ℝ × ℝ)) = ψ (d • x)
    rw [e]
    exact hψ.periodic (d • x)
  band := by
    obtain ⟨R, hR⟩ := hψ.band
    refine ⟨R / d, fun x hx => hR _ ?_⟩
    simp only [Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_pos hd]
    rw [div_lt_iff₀ hd] at hx
    linarith

theorem pd_scale {d : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) (j : Fin 2) (y : ℝ × ℝ) :
    B0579.pd j (fun y => ψ (d • y)) y = d * B0579.pd j ψ (d • y) := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => d • y) (d • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul d
  have h2 := (hψ.differentiable (d • y)).hasFDerivAt.comp y h1
  unfold B0579.pd
  have h3 : (fun y => ψ (d • y)) = ψ ∘ HSMul.hSMul d := rfl
  rw [h3, h2.fderiv]
  simp

theorem kerVel_scale {d : ℝ} (hd : 0 < d) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    kerVel d ψ x j = d * kerVel 1 (fun y => ψ (d • y)) (d⁻¹ • x) j := by
  unfold kerVel
  rw [integral_cell_scale hd (fun y => ψ y * kerD d (x - y) j)]
  have hpt : ∀ y : ℝ × ℝ, ψ (d • y) * kerD d (x - d • y) j =
      d⁻¹ * (ψ (d • y) * kerD 1 (d⁻¹ • x - y) j) := by
    intro y
    rw [kerD_scale hd]
    have : d⁻¹ • (x - d • y) = d⁻¹ • x - y := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
    rw [this]
    ring
  simp only [hpt]
  rw [integral_const_mul]
  field_simp

theorem meanShear_scale {d : ℝ} (hd : 0 < d) (Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    meanShear d Γ x j = d * meanShear 1 (Γ / d ^ 2) (d⁻¹ • x) j := by
  unfold meanShear
  have hs : Real.sign (d⁻¹ • x).2 = Real.sign x.2 := by
    simp only [Prod.smul_snd, smul_eq_mul]
    rcases lt_trichotomy x.2 0 with h | h | h
    · rw [Real.sign_of_neg h, Real.sign_of_neg]
      exact mul_neg_of_pos_of_neg (inv_pos.2 hd) h
    · simp [h]
    · rw [Real.sign_of_pos h, Real.sign_of_pos]
      exact mul_pos (inv_pos.2 hd) h
  split_ifs
  · rw [hs]
    field_simp
  · simp

/-- **`d > 0` far field from the `d = 1` instance of the `d ≥ 1` far field** (scaling). -/
theorem kerVelFarField0_of (h : KerVelFarField) : KerVelFarField0 := by
  intro d hd ψ hψ j
  have h1 := h 1 le_rfl (fun y => ψ (d • y)) (isCylTest_scale hd hψ) j
  set Γ' : ℝ := ∫ y in B0579.cell 1, ψ (d • y) with hΓ'
  have hΓ : (∫ y in B0579.cell d, ψ y) = d ^ 2 * Γ' := integral_cell_scale hd ψ
  set G : ℝ × ℝ → ℝ := fun x => kerVel 1 (fun y => ψ (d • y)) x j - meanShear 1 Γ' x j with hG
  have h2 : MemLp G 2 ((volume.restrict (B0579.cell d)).map (fun x : ℝ × ℝ => d⁻¹ • x)) := by
    rw [map_restrict_cell hd]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  have h3 : MemLp (fun x => d * G (d⁻¹ • x)) 2 (volume.restrict (B0579.cell d)) :=
    (h2.comp_of_map (measurable_const_smul _).aemeasurable).const_mul d
  have e : (fun x => kerVel d ψ x j - meanShear d (∫ y in B0579.cell d, ψ y) x j) =
      fun x => d * G (d⁻¹ • x) := by
    funext x
    rw [kerVel_scale hd, meanShear_scale hd, hΓ, mul_div_cancel_left₀ _ (by positivity)]
    simp only [hG]
    ring
  rw [e]
  exact h3

end UnforcedLeray.Short.IIIa.AdjE1
