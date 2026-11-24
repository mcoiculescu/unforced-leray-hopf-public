import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.HDeriv

/-!
# `PDYKerBound` helpers (3): bounds of the outward primitive at the normalized radius

Source `the November 2 reference manuscript` 4178-4186, 5592.

At `ϱ y = 1`, `y ↦ Ψ(y) = sKer ν μ h (ϱ y) y₃ z M` is `C²` and its derivatives of order `≤ 2` are
`≤ C λ^{2μ+3}|M| (1 + (y₃ - λ z₃)²)^{-1}` (`primY_main` after the vertical translation
`y ↦ y - y₃ e₃`, which moves the receiver into a compact set).  The combination
`(∂_h - ½ x·∇_x) xKer` integrated along the outward ray obeys the same bound
(`∫_{u>0} (κ+u)((κ+u)² + b²)^{-2} = 1/(2(κ² + b²))`, `primJ2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ykb_primInt_shift (A : Space → ℝ) (w q d : Space) (hd : d 0 = 0) :
    primInt A w q = primInt A (w + d) (q + d) := by
  unfold primInt primF
  congr 1
  funext u
  have e1 : (q + d) 0 = q 0 := by simp [hd]
  have e2 : q + d + (u • primE0 - (w + d)) = q + (u • primE0 - w) := by abel
  rw [e1, e2]

/-- The vertical shift `(0, 0, c)`. -/
def ykVert (c : ℝ) : Space := !₂[0, 0, c]

theorem ykVert_apply0 (c : ℝ) : ykVert c 0 = 0 := by simp [ykVert]

theorem ykb_ringMap_sub (y : Space) (c : ℝ) : ringMap (y - ykVert c) = ringMap y - ykVert c := by
  have hϱ : ϱ (y - ykVert c) = ϱ y := by simp [ϱ, ykVert]
  unfold ringMap
  rw [hϱ]
  ext i
  fin_cases i <;> simp [ykVert]

theorem ykb_sKer_eq (ν μ h : ℝ) (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (y' : Space) :
    sKer ν μ h (ϱ y') (y' 2) z M =
      -primInt (xKerA ν μ h M) (pdLam h • z - ykVert c) (ringMap (y' - ykVert c)) := by
  rw [sKer_eq_primInt]
  change -primInt (xKerA ν μ h M) (pdLam h • z) (ringMap y') = _
  rw [ykb_ringMap_sub,
    ykb_primInt_shift (xKerA ν μ h M) (pdLam h • z) (ringMap y') (-ykVert c)
      (by simp [ykVert]), sub_eq_add_neg, sub_eq_add_neg]

theorem ykb_kb_le (b : ℝ) : 1 / (2 * (ykKap ^ 2 + b ^ 2)) ≤ (ykKap ^ 2)⁻¹ * (1 + b ^ 2)⁻¹ := by
  have hk := ykKap_pos
  have hk1 := ykKap_le_one
  rw [← mul_inv, one_div]
  refine inv_anti₀ (by positivity) ?_
  have hk2 : ykKap ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg b]

/-- **Bounds of the outward primitive** at `ϱ y = 1`. -/
theorem ykb_psi_bounds {C : ℝ} (hC : YKB C) : ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ (ν μ : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ),
      0 < h → ∀ y z : Space, ϱ y = 1 → ϱ z ≤ ykR0 →
        ContDiffAt ℝ 2 (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y ∧
        ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y‖ ≤
          CF * (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) *
            (1 + (y 2 - pdLam h * z 2) ^ 2)⁻¹ := by
  have hκ := ykKap_pos
  have hr1 : 0 < ykR0 + ykKap / 2 := by linarith [ykR0_nonneg]
  obtain ⟨D, hD1, hD⟩ := primY_main hr1 2
  refine ⟨2 * primCp ykR0 (ykKap / 2) * D ^ 2 * (ykKap ^ 2)⁻¹, ?_, ?_⟩
  · have := primCp_nonneg ykR0_nonneg (half_pos hκ)
    positivity
  intro ν μ hν hμ0 hμ1 M h hh y z hy hz
  set c := y 2 with hc
  set A := xKerA ν μ h M with hA
  set w := pdLam h • z - ykVert c with hw
  set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  obtain ⟨hAc, b0, b1, b2⟩ := xKerA_props C hC.1 hC.2 ν μ h hν hμ0 hμ1 hh M
  have hw0 : w 0 ≤ ykR0 := by
    rw [hw]
    have := ykb_z0_le hz (pdLam_pos h) (ykb_pdLam_le_one hh.le)
    simpa [ykVert] using this
  set yh := y - ykVert c with hyh
  have hyh_ϱ : ϱ yh = 1 := by rw [hyh, ← hy]; simp [ϱ, ykVert]
  have hyh2 : yh 2 = 0 := by simp [hyh, ykVert, hc]
  have hyh_norm : ‖yh‖ < 2 := by
    have e : ‖yh‖ = ϱ yh := by
      rw [EuclideanSpace.norm_eq]
      unfold ϱ
      congr 1
      simp [Fin.sum_univ_three, hyh2]
    rw [e, hyh_ϱ]; norm_num
  have hr : ykR0 + ykKap / 2 < ϱ yh := by
    rw [hyh_ϱ]; unfold ykKap; linarith [ykR0_lt_one]
  obtain ⟨hcd, hbd⟩ := hD hAc w hK0 ykR0_nonneg (half_pos hκ) rfl hw0 b0 b1 b2 yh hr hyh_norm
  set G : Space → ℝ := fun y'' => primInt A w (ringMap y'') with hG
  have hfun : (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) =
      -(fun y' => G (y' - ykVert c)) := by
    funext y'
    rw [ykb_sKer_eq ν μ h z M c y']
    rfl
  rw [hfun]
  refine ⟨?_, fun n hn => ?_⟩
  · have hsub : ContDiffAt ℝ 2 (fun y' : Space => y' - ykVert c) y :=
      contDiffAt_id.sub contDiffAt_const
    exact (ContDiffAt.comp y (f := fun y' : Space => y' - ykVert c) hcd hsub).neg
  · rw [iteratedFDeriv_neg_apply, norm_neg, iteratedFDeriv_comp_sub]
    refine (hbd n hn).trans ?_
    have e1 : ϱ yh - ykR0 = ykKap := by rw [hyh_ϱ]; rfl
    have e2 : (yh 2 - w 2) ^ 2 = (y 2 - pdLam h * z 2) ^ 2 := by
      rw [hyh2, hw]; simp [ykVert, hc]
    rw [e1, e2]
    have hfac : (n.factorial : ℝ) ≤ 2 := by
      have : n.factorial ≤ (2 : ℕ).factorial := Nat.factorial_le hn
      exact_mod_cast this
    have hDn : D ^ n ≤ D ^ 2 := pow_le_pow_right₀ hD1 hn
    have hCp := primCp_nonneg ykR0_nonneg (half_pos hκ)
    have hb := ykb_kb_le (y 2 - pdLam h * z 2)
    have hb0 : 0 ≤ 1 / (2 * (ykKap ^ 2 + (y 2 - pdLam h * z 2) ^ 2)) := by positivity
    have hDn0 : 0 ≤ D ^ n := by positivity
    calc (n.factorial : ℝ) * (primCp ykR0 (ykKap / 2) * K *
          (1 / (2 * (ykKap ^ 2 + (y 2 - pdLam h * z 2) ^ 2)))) * D ^ n
        ≤ 2 * (primCp ykR0 (ykKap / 2) * K *
          ((ykKap ^ 2)⁻¹ * (1 + (y 2 - pdLam h * z 2) ^ 2)⁻¹)) * D ^ 2 := by
          refine mul_le_mul (mul_le_mul hfac ?_ (by positivity) (by norm_num)) hDn hDn0
            (by positivity)
          exact mul_le_mul_of_nonneg_left hb (mul_nonneg hCp hK0)
      _ = _ := by ring

/-- `‖DJ (1, -x/2)‖ ≤ C λ^p |M| (3/2 + κ^{-2}) |x|^{-4}` for `|x| ≥ κ`, `ν ≤ 1`. -/
theorem ykb_DJ_half {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    {x : Space} (hx : ykKap ≤ ‖x‖) :
    ‖fderiv ℝ (ykJ ν μ M) (h, x) (1, -(1 / 2 : ℝ) • x)‖ ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M * ((3 / 2 + (ykKap ^ 2)⁻¹) * (‖x‖ ^ 4)⁻¹) := by
  have hκ := ykKap_pos
  have hX : 0 < ‖x‖ := lt_of_lt_of_le hκ hx
  have hxne : x ≠ 0 := norm_pos_iff.1 hX
  refine (ykb_DJ_bound hC ν μ hν hμ0 hμ1 M hh hxne _).trans ?_
  have hK0 : 0 ≤ C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M :=
    mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  refine mul_le_mul_of_nonneg_left ?_ hK0
  obtain ⟨-, -, p6⟩ := ykb_pow_inv hκ hx le_rfl
  have e5 : (‖x‖ ^ 5)⁻¹ * ‖-(1 / 2 : ℝ) • x‖ = (1 / 2) * (‖x‖ ^ 4)⁻¹ := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    field_simp
  rw [e5]
  have h4 : 0 ≤ (‖x‖ ^ 4)⁻¹ := by positivity
  have hk2 : 0 ≤ (ykKap ^ 2)⁻¹ * (‖x‖ ^ 4)⁻¹ := by positivity
  have a1 : ν * (‖x‖ ^ 6)⁻¹ ≤ (ykKap ^ 2)⁻¹ * (‖x‖ ^ 4)⁻¹ := by
    calc ν * (‖x‖ ^ 6)⁻¹ ≤ 1 * ((ykKap ^ 2)⁻¹ * (‖x‖ ^ 4)⁻¹) :=
          mul_le_mul hν1 p6 (by positivity) zero_le_one
      _ = _ := one_mul _
  nlinarith

/-- **The combination integral** `∫_{u>0} (1+u) [(∂_h - ½x·∇) xKer]_z (x_u) du` at `q₀ = 1`. -/
theorem ykb_comb_bound {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (z q : Space) (hz : ϱ z ≤ ykR0) (hq0 : q 0 = 1) :
    ‖∫ u in Ioi (0 : ℝ), (q 0 + u) * (fderiv ℝ (ykJ ν μ M) (h, q + (u • primE0 - pdLam h • z))
        (1, -(1 / 2 : ℝ) • (q + (u • primE0 - pdLam h • z)))) 2‖ ≤
      C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M *
        ((3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹) * (1 + (q 2 - pdLam h * z 2) ^ 2)⁻¹ := by
  have hκ := ykKap_pos
  set b := q 2 - pdLam h * z 2 with hbdef
  set K := C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  set c' := K * ((3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹) with hc'
  have hc'0 : 0 ≤ c' := by positivity
  obtain ⟨hJi, hJv⟩ := primJ2 hκ b
  have hg : Integrable (fun u : ℝ => c' * ((ykKap + u) * (((ykKap + u) ^ 2 + b ^ 2) ^ 2)⁻¹))
      (volume.restrict (Ioi 0)) := hJi.const_mul c'
  have hpt : ∀ u : ℝ, 0 < u → ‖(q 0 + u) * (fderiv ℝ (ykJ ν μ M) (h, q + (u • primE0 - pdLam h • z))
        (1, -(1 / 2 : ℝ) • (q + (u • primE0 - pdLam h • z)))) 2‖ ≤
      c' * ((ykKap + u) * (((ykKap + u) ^ 2 + b ^ 2) ^ 2)⁻¹) := by
    intro u hu
    set x := q + (u • primE0 - pdLam h • z) with hx
    have hl0 := pdLam_pos h
    have hl1 := ykb_pdLam_le_one hh.le
    have hw0 := ykb_z0_le hz hl0 hl1
    obtain ⟨hsq, hlow⟩ := ykb_xlow (w := pdLam h • z) hq0 hw0 hu.le
    have hxk : ykKap ≤ ‖x‖ := le_trans (le_add_of_nonneg_right hu.le) hlow
    have hD := ykb_DJ_half hC ν μ hν hν1 hμ0 hμ1 M hh hxk
    have e2 : (pdLam h • z) 2 = pdLam h * z 2 := by simp
    rw [e2] at hsq
    have hS : 0 < (ykKap + u) ^ 2 + b ^ 2 := by
      have : 0 < ykKap + u := by linarith
      positivity
    have h4 : (‖x‖ ^ 4)⁻¹ ≤ (((ykKap + u) ^ 2 + b ^ 2) ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ hS.le hsq 2
    have h1u : 1 + u ≤ ykKap⁻¹ * (ykKap + u) := by
      rw [le_inv_mul_iff₀ hκ]; nlinarith [ykKap_le_one]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hq0, abs_of_pos (by linarith)]
    have h2 := (ykb_abs2_le (fderiv ℝ (ykJ ν μ M) (h, x) (1, -(1 / 2 : ℝ) • x))).trans hD
    have hA0 : 0 ≤ 3 / 2 + (ykKap ^ 2)⁻¹ := by positivity
    calc (1 + u) * |(fderiv ℝ (ykJ ν μ M) (h, x) (1, -(1 / 2 : ℝ) • x)) 2|
        ≤ (ykKap⁻¹ * (ykKap + u)) * (K * ((3 / 2 + (ykKap ^ 2)⁻¹) *
            (((ykKap + u) ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
          refine mul_le_mul h1u (h2.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hA0) hK0
      _ = c' * ((ykKap + u) * (((ykKap + u) ^ 2 + b ^ 2) ^ 2)⁻¹) := by rw [hc']; ring
  refine (norm_integral_le_of_norm_le hg
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => hpt u hu))).trans ?_
  rw [integral_const_mul, hJv]
  have hb := ykb_kb_le b
  calc c' * (1 / (2 * (ykKap ^ 2 + b ^ 2))) ≤ c' * ((ykKap ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hb hc'0
    _ = _ := by rw [hc']; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
