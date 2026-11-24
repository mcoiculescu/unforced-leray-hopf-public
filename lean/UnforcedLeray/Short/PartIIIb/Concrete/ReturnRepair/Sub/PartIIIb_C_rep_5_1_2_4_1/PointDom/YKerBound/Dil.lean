import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Psi

/-!
# `PDYKerBound` helpers (4): the dilation derivative of the outward primitive

Source `the November 2 reference manuscript` 4178-4186 (`Ψ_{AZ} = AΨ_Z + Ψ_Z`,
`A = -½ y·∇`).

At `ϱ y = 1`, `y·∇Ψ(y) = d/dt Ψ((1+t) y)|_{t=0}` and `Ψ((1+t)y) = -(1+t)² ∫_{v>0} (1+v)
xKer((1+t)(q + v e₀) - λz)_z dv` (`q = (1,0,y₃)`, substitution `u = (1+t) v`), so
`y·∇Ψ = -(2 ∫ (1+v) xKer_z + ∫ (1+v) (D xKer · (q + v e₀))_z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ykb_ϱ_smul {c : ℝ} (hc : 0 ≤ c) (y : Space) : ϱ (c • y) = c * ϱ y := by
  unfold ϱ
  have e : (c • y) 0 ^ 2 + (c • y) 1 ^ 2 = c ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
    simp only [PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The substitution `u = s v` in the outward primitive. -/
theorem ykb_primInt_smul (A : Space → ℝ) (w q : Space) {s : ℝ} (hs : 0 < s) :
    primInt A w (s • q) =
      s ^ 2 * ∫ v in Ioi (0 : ℝ), (q 0 + v) * A (s • (q + v • primE0) - w) := by
  unfold primInt primF
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => ((s • q) 0 + u) * A (s • q + (u • primE0 - w))) 0 hs
  rw [mul_zero] at h
  have h2 : ∫ u in Ioi (0 : ℝ), ((s • q) 0 + u) * A (s • q + (u • primE0 - w)) =
      s * ∫ x in Ioi (0 : ℝ), ((s • q) 0 + s * x) * A (s • q + ((s * x) • primE0 - w)) := by
    rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [h2]
  have h3 : ∀ x : ℝ, ((s • q) 0 + s * x) * A (s • q + ((s * x) • primE0 - w)) =
      s * ((q 0 + x) * A (s • (q + x • primE0) - w)) := by
    intro x
    have e1 : (s • q) 0 = s * q 0 := by simp
    have e2 : s • q + ((s * x) • primE0 - w) = s • (q + x • primE0) - w := by
      rw [smul_add, mul_smul]; abel
    rw [e1, e2]; ring
  simp_rw [h3]
  rw [integral_const_mul]
  ring

/-- **Part 2 dilation derivative** (normalized radius `1`). -/
theorem ykb_partD {C : ℝ} (hC : YKB C) (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ)
    (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h) (y z : Space)
    (hy : ϱ y = 1) (hz : ϱ z ≤ ykR0)
    (hdiff : DifferentiableAt ℝ (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y) :
    Integrable (fun v => ((!₂[1, 0, y 2] : Space) 0 + v) *
        (fderiv ℝ (fun x' => xKer ν μ h x' M)
          ((!₂[1, 0, y 2] : Space) + (v • primE0 - pdLam h • z))
          ((!₂[1, 0, y 2] : Space) + v • primE0)) 2) (volume.restrict (Ioi 0)) ∧
    fderiv ℝ (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y y =
      -(2 * primInt (xKerA ν μ h M) (pdLam h • z) !₂[1, 0, y 2] +
        ∫ v in Ioi (0 : ℝ), ((!₂[1, 0, y 2] : Space) 0 + v) *
          (fderiv ℝ (fun x' => xKer ν μ h x' M)
            ((!₂[1, 0, y 2] : Space) + (v • primE0 - pdLam h • z))
            ((!₂[1, 0, y 2] : Space) + v • primE0)) 2) := by
  set q : Space := !₂[1, 0, y 2] with hqdef
  have hq0 : q 0 = 1 := by simp [hqdef]
  set w : Space := pdLam h • z with hw
  have hκ := ykKap_pos
  have hκ1 := ykKap_le_one
  have hw0 : w 0 ≤ ykR0 := ykb_z0_le hz (pdLam_pos h) (ykb_pdLam_le_one hh.le)
  obtain ⟨hcd, -, hbd⟩ := hC.2 ν μ h hν hμ0 hμ1 hh M
  set X : Space → Space := fun x' => xKer ν μ h x' M with hX
  set A := xKerA ν μ h M with hA
  have hM0 := kb_tensor_nonneg M
  have hCM : 0 ≤ C * IIIa.tensorNorm M := mul_nonneg hC.1 hM0
  have hp1 := ykb_pdLam_rpow_le_one μ h hμ0 hh.le
  have hp0 := ykb_rpow_nonneg μ h
  -- the integrands
  set F : ℝ → ℝ → ℝ := fun t v => (q 0 + v) * A ((1 + t) • (q + v • primE0) - w) with hF
  set F' : ℝ → ℝ → ℝ := fun t v =>
    (q 0 + v) * (fderiv ℝ X ((1 + t) • (q + v • primE0) - w) (q + v • primE0)) 2 with hF'
  -- lower bound of the first coordinate
  have hlow : ∀ t : ℝ, |t| < ykKap / 2 → ∀ v : ℝ, 0 < v →
      ykKap / 2 * (1 + v) ≤ ‖(1 + t) • (q + v • primE0) - w‖ := by
    intro t ht v hv
    have hc0 : ((1 + t) • (q + v • primE0) - w) 0 = (1 + t) * (1 + v) - w 0 := by
      simp [hq0, primE0_apply0]; ring
    have hn : |((1 + t) • (q + v • primE0) - w) 0| ≤ ‖(1 + t) • (q + v • primE0) - w‖ := by
      have := PiLp.norm_apply_le ((1 + t) • (q + v • primE0) - w) 0
      rwa [Real.norm_eq_abs] at this
    rw [hc0] at hn
    have ht' := (abs_lt.1 ht).1
    have hR := ykR0_lt_one
    have hk : ykKap = 1 - ykR0 := rfl
    have : ykKap / 2 * (1 + v) ≤ (1 + t) * (1 + v) - w 0 := by nlinarith
    exact this.trans ((le_abs_self _).trans hn)
  -- the derivative of the integrand
  have hFd : ∀ t v : ℝ, HasDerivAt (fun t' => F t' v) (F' t v) t := by
    intro t v
    have hXd : HasFDerivAt X (fderiv ℝ X ((1 + t) • (q + v • primE0) - w))
        ((1 + t) • (q + v • primE0) - w) :=
      ((hcd.differentiable (by norm_num)) _).hasFDerivAt
    have hpath : HasDerivAt (fun t' : ℝ => (1 + t') • (q + v • primE0) - w) (q + v • primE0) t := by
      have := (((hasDerivAt_id' t).const_add 1).smul_const (q + v • primE0)).sub_const w
      simpa using this
    have := ykb_comp2 (hXd.comp_hasDerivAt t hpath)
    exact this.const_mul (q 0 + v)
  -- domination on `|t| < κ/2`
  set B : ℝ := C * IIIa.tensorNorm M * (‖q‖ + 1) * (ykKap / 2)⁻¹ ^ 5 with hB
  have hB0 : 0 ≤ B := by positivity
  have hBi : Integrable (fun v : ℝ => B * ((1 + v) * (((1 + v) ^ 2 + 0 ^ 2) ^ 2)⁻¹))
      (volume.restrict (Ioi 0)) := (primJ2 one_pos 0).1.const_mul B
  have hdom : ∀ t : ℝ, |t| < ykKap / 2 → ∀ v : ℝ, 0 < v →
      ‖F' t v‖ ≤ B * ((1 + v) * (((1 + v) ^ 2 + 0 ^ 2) ^ 2)⁻¹) := by
    intro t ht v hv
    have hL := hlow t ht v hv
    set x := (1 + t) • (q + v • primE0) - w with hxdef
    have hs : 0 < ykKap / 2 * (1 + v) := by positivity
    have hxne : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hL; linarith
    have hb1 := (hbd x hxne).2.1
    have hpv : ‖q + v • primE0‖ ≤ ‖q‖ + v := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hv]
      have : ‖(primE0 : Space)‖ = 1 := by simp [primE0]
      rw [this, mul_one]
    have h5 : (‖x‖ ^ 5)⁻¹ ≤ ((ykKap / 2 * (1 + v)) ^ 5)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hs.le hL 5)
    have hDx : ‖fderiv ℝ X x‖ ≤ C * IIIa.tensorNorm M * ((ykKap / 2 * (1 + v)) ^ 5)⁻¹ := by
      refine hb1.trans ?_
      have e : C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M =
          pdLam h ^ (2 * μ + 3) * (C * IIIa.tensorNorm M * (‖x‖ ^ 5)⁻¹) := by ring
      rw [e]
      have h6 : 0 ≤ C * IIIa.tensorNorm M * (‖x‖ ^ 5)⁻¹ := by positivity
      calc pdLam h ^ (2 * μ + 3) * (C * IIIa.tensorNorm M * (‖x‖ ^ 5)⁻¹)
          ≤ 1 * (C * IIIa.tensorNorm M * (‖x‖ ^ 5)⁻¹) := mul_le_mul_of_nonneg_right hp1 h6
        _ ≤ C * IIIa.tensorNorm M * ((ykKap / 2 * (1 + v)) ^ 5)⁻¹ := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h5 hCM
    have hval : ‖F' t v‖ ≤ (1 + v) * ((C * IIIa.tensorNorm M *
        ((ykKap / 2 * (1 + v)) ^ 5)⁻¹) * (‖q‖ + v)) := by
      simp only [hF']
      rw [norm_mul, Real.norm_eq_abs, hq0, abs_of_pos (by linarith)]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      refine (ykb_abs2_le _).trans ?_
      refine ((fderiv ℝ X x).le_opNorm _).trans ?_
      exact mul_le_mul hDx hpv (norm_nonneg _) (by positivity)
    refine hval.trans ?_
    have hv1 : 0 < 1 + v := by linarith
    have hκne : ykKap ≠ 0 := hκ.ne'
    have hvne : 1 + v ≠ 0 := hv1.ne'
    have hE : 0 ≤ C * IIIa.tensorNorm M * (ykKap / 2)⁻¹ ^ 5 := by positivity
    have eL : (1 + v) * ((C * IIIa.tensorNorm M * ((ykKap / 2 * (1 + v)) ^ 5)⁻¹) * (‖q‖ + v)) =
        (C * IIIa.tensorNorm M * (ykKap / 2)⁻¹ ^ 5) * ((‖q‖ + v) / (1 + v) ^ 4) := by
      field_simp
    have eR : B * ((1 + v) * (((1 + v) ^ 2 + 0 ^ 2) ^ 2)⁻¹) =
        (C * IIIa.tensorNorm M * (ykKap / 2)⁻¹ ^ 5) * ((‖q‖ + 1) / (1 + v) ^ 3) := by
      rw [hB]; field_simp; ring
    rw [eL, eR]
    refine mul_le_mul_of_nonneg_left ?_ hE
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hqv : ‖q‖ + v ≤ (‖q‖ + 1) * (1 + v) := by nlinarith [norm_nonneg q]
    have := mul_le_mul_of_nonneg_right hqv (pow_nonneg hv1.le 3)
    calc (‖q‖ + v) * (1 + v) ^ 3 ≤ (‖q‖ + 1) * (1 + v) * (1 + v) ^ 3 := this
      _ = (‖q‖ + 1) * (1 + v) ^ 4 := by ring
  -- continuity / measurability
  have hAc : Continuous A := (xKerA_props C hC.1 hC.2 ν μ h hν hμ0 hμ1 hh M).1.continuous
  have hFc : ∀ t : ℝ, Continuous (F t) := by
    intro t
    simp only [hF]
    exact (continuous_const.add continuous_id).mul (hAc.comp (by fun_prop))
  have hF'c : Continuous (F' 0) := by
    simp only [hF']
    refine (continuous_const.add continuous_id).mul (ykb_cont2 ?_)
    exact ((hcd.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply (by fun_prop)
  have hx0 : ∀ v : ℝ, (1 + (0 : ℝ)) • (q + v • primE0) - w = q + (v • primE0 - w) := by
    intro v; rw [add_zero, one_smul]; abel
  have hFint : Integrable (F 0) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' ((ykb_int1 hκ hκ1).const_mul (C * IIIa.tensorNorm M))
      (hFc 0).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    obtain ⟨-, hxl⟩ := ykb_xlow hq0 hw0 hv0.le
    have hxne : q + (v • primE0 - w) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hxl; linarith
    have hb0 := (xKerA_props C hC.1 hC.2 ν μ h hν hμ0 hμ1 hh M).2.1 _ hxne
    obtain ⟨p4, -, -⟩ := ykb_pow_inv hκ (le_add_of_nonneg_right hv0.le) hxl
    simp only [hF]
    rw [hx0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hq0, abs_of_pos (by linarith)]
    have hle : C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M ≤ C * IIIa.tensorNorm M := by
      have := mul_le_mul_of_nonneg_left hp1 hCM
      nlinarith
    have h5 : |A (q + (v • primE0 - w))| ≤ C * IIIa.tensorNorm M * ((ykKap + v) ^ 4)⁻¹ :=
      hb0.trans (mul_le_mul hle p4 (by positivity) hCM)
    calc (1 + v) * |A (q + (v • primE0 - w))|
        ≤ (1 + v) * (C * IIIa.tensorNorm M * ((ykKap + v) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = C * IIIa.tensorNorm M * ((1 + v) * ((ykKap + v) ^ 4)⁻¹) := by ring
  have hball : Metric.ball (0 : ℝ) (ykKap / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := 0)
    (bound := fun v => B * ((1 + v) * (((1 + v) ^ 2 + 0 ^ 2) ^ 2)⁻¹)) hball
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hFint
    hF'c.aestronglyMeasurable ?_ hBi ?_
  rotate_left
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv t ht => ?_)
    have ht' : |t| < ykKap / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht
    exact hdom t ht' v hv
  · exact Eventually.of_forall fun v t _ => hFd t v
  obtain ⟨hint', hderI⟩ := key
  set I : ℝ → ℝ := fun t => ∫ v in Ioi (0 : ℝ), F t v with hI
  -- the composite along the dilation
  have hsq : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) 2 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).pow 2
    exact this.congr_deriv (by norm_num)
  have hG : HasDerivAt (fun t => -((1 + t) ^ 2 * I t))
      (-(2 * I 0 + ∫ v in Ioi (0 : ℝ), F' 0 v)) 0 := by
    have := (hsq.mul hderI).neg
    refine this.congr_deriv ?_
    simp
  have heq : (fun t : ℝ => sKer ν μ h (ϱ ((1 + t) • y)) (((1 + t) • y) 2) z M) =ᶠ[𝓝 0]
      fun t => -((1 + t) ^ 2 * I t) := by
    have hmem : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [hmem] with t ht
    have ht1 : 0 < 1 + t := by have : (-1 : ℝ) < t := ht; linarith
    rw [sKer_eq_primInt, ykb_ϱ_smul ht1.le, hy, mul_one]
    have e : (!₂[1 + t, 0, ((1 + t) • y) 2] : Space) = (1 + t) • q := by
      ext i; fin_cases i <;> simp [hqdef]
    rw [e, ykb_primInt_smul A w q ht1]
  have hchain : HasDerivAt (fun t : ℝ => sKer ν μ h (ϱ ((1 + t) • y)) (((1 + t) • y) 2) z M)
      (fderiv ℝ (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y y) 0 := by
    have hpath : HasDerivAt (fun t : ℝ => (1 + t) • y) y 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).smul_const y
      simpa using this
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have huniq := hchain.unique (hG.congr_of_eventuallyEq heq)
  have hI0 : I 0 = primInt A w q := by
    simp only [hI, hF]
    unfold primInt primF
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [hx0]
  have hF'0 : (fun v => F' 0 v) = fun v => (q 0 + v) *
      (fderiv ℝ X (q + (v • primE0 - w)) (q + v • primE0)) 2 := by
    funext v; simp only [hF']; rw [hx0]
  refine ⟨?_, ?_⟩
  · rw [← hF'0]; exact hint'
  · rw [huniq, hI0, hF'0]

end UnforcedLeray.Short.PartIIIb.Concrete

end
