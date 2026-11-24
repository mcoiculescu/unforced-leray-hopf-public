import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Cut

/-!
# `PDYKerBound` helpers (6): the `χ_y X₀` part at the normalized radius

Source `the November 2 reference manuscript` 4198-4205, 3700-3713.

`X₁(h, y) = c(ϱ y) xKer(h, y - λ(h) z)`.  The transport `∂_h - ½ y·∇` recombines into
`(∂_h - ½ x·∇_x) xKer` at `x = y - λz` (`DJ (1, -x/2)`), plus `-½ (y·∇c) xKer`; the Laplacian is
`(c'' + c'/r) xKer + 2c' ∂_r xKer + c Δ xKer`; each piece is `≤ C λ^{2μ+3}|x|^{-4}|M|` since
`|x| ≥ 1 - √(5/6)` and `ν ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ykb_fderiv_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    {y : Space} (hf : ContDiffAt ℝ 2 f y) (v w : Space) :
    fderiv ℝ (fun y' => fderiv ℝ f y' v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y := by
    have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem ykb_physLap_norm {f : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y) :
    ‖physLap f y‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by
  have hcv : ∀ j : Fin 3, ‖(coordinateVector j : Space)‖ = 1 := by
    intro j; simp [coordinateVector]
  have hhess : ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := f) (x := y)
    rw [norm_iteratedFDeriv_one] at h1
    exact h1
  unfold physLap
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ j : Fin 3, ‖physPd2 f j j y‖ ≤ ‖iteratedFDeriv ℝ 2 f y‖ := by
    intro j
    unfold physPd2 physPd
    rw [ykb_fderiv_dir hf]
    calc ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector j)‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j)‖ * ‖(coordinateVector j : Space)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖(coordinateVector j : Space)‖ *
            ‖(coordinateVector j : Space)‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ 2 f y‖ := by rw [hcv, hhess]; ring
  calc ∑ j : Fin 3, ‖physPd2 f j j y‖ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 2 f y‖ :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by simp

theorem ykb_ϱ_le_norm (v : Space) : ϱ v ≤ ‖v‖ := by
  unfold ϱ
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three]
  positivity

/-- The radial gap at the normalized radius: `κ ≤ |y - λz|`. -/
theorem ykb_xnorm {y z : Space} (hy : ϱ y = 1) (hz : ϱ z ≤ ykR0) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l ≤ 1) : ykKap ≤ ‖y - l • z‖ := by
  have hs0 := ϱ_nonneg z
  have hzs : ϱ z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    unfold ϱ; rw [Real.sq_sqrt (by positivity)]
  have hys : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold ϱ; rw [Real.sq_sqrt (by positivity)]
  rw [hy] at hys
  have hcs : (y 0 * z 0 + y 1 * z 1) ^ 2 ≤ ϱ z ^ 2 := by
    nlinarith [sq_nonneg (y 0 * z 1 - y 1 * z 0)]
  have hdot : y 0 * z 0 + y 1 * z 1 ≤ ϱ z := le_of_abs_le (abs_le_of_sq_le_sq hcs hs0)
  have hR := ykR0_lt_one
  have hls : l * ϱ z ≤ ykR0 := by nlinarith
  have hsq : ykKap ^ 2 ≤ (y - l • z) 0 ^ 2 + (y - l • z) 1 ^ 2 := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hk : ykKap = 1 - ykR0 := rfl
    have h1 : ykKap ≤ 1 - l * ϱ z := by linarith
    have h0 : 0 ≤ ykKap := ykKap_pos.le
    have h2 : ykKap ^ 2 ≤ (1 - l * ϱ z) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have e : (y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2 =
        (y 0 ^ 2 + y 1 ^ 2) - 2 * (l * (y 0 * z 0 + y 1 * z 1)) + l ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
      ring
    rw [e, ← hys, ← hzs]
    have h3 := mul_le_mul_of_nonneg_left hdot hl0.le
    have e2 : (1 - l * ϱ z) ^ 2 = 1 - 2 * (l * ϱ z) + l ^ 2 * ϱ z ^ 2 := by ring
    rw [e2] at h2
    linarith
  have hϱ : ykKap ≤ ϱ (y - l • z) := by
    unfold ϱ
    exact Real.le_sqrt_of_sq_le hsq
  exact hϱ.trans (ykb_ϱ_le_norm _)

theorem ykb_norm4 {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a - b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a - b - c) d
  have h2 := norm_sub_le (a - b) c
  have h3 := norm_sub_le a b
  linarith

theorem ykb_norm3 {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

/-- The `χ_y X₀` part of the kernel. -/
def ykX1 (ν μ R : ℝ) (χ : ℝ → ℝ) (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (h' : ℝ)
    (y' : Space) : Space :=
  tcC0 ν R χ (ϱ y') • xKer ν μ h' (y' - pdLam h' • z) M

theorem ykb_offAxis_cd {y : Space} (hy : 0 < ϱ y) : ContDiffAt ℝ 2 ϱ y :=
  contDiffOn_ϱ_pos.contDiffAt (RingMapOff.isOpen_offAxis.mem_nhds hy)

/-- **Part 1** at the normalized radius. -/
theorem ykb_part1 {C : ℝ} (hC : YKB C) (ν μ R : ℝ) (χ : ℝ → ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (y z : Space) (hy : ϱ y = 1) (hz : ϱ z ≤ ykR0) {A : ℝ} (hA0 : 0 ≤ A)
    (hc2 : ContDiffAt ℝ 2 (tcC0 ν R χ) 1) (hc0 : |tcC0 ν R χ 1| ≤ 1)
    (hc1 : |deriv (tcC0 ν R χ) 1| ≤ A)
    (hcc : |deriv (deriv (tcC0 ν R χ)) 1 + deriv (tcC0 ν R χ) 1 / 1| ≤ A) :
    DifferentiableAt ℝ (fun t => ykX1 ν μ R χ z M t y) h ∧
    ContDiffAt ℝ 2 (ykX1 ν μ R χ z M h) y ∧
    ‖physDmu ν (μ + 1) (ykX1 ν μ R χ z M) h y‖ ≤
      (3 + 4 * (ykKap ^ 2)⁻¹ + 2 * A + 2 * A * ykKap⁻¹) *
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (‖y - pdLam h • z‖ ^ 4)⁻¹ := by
  have hyp : 0 < ϱ y := by rw [hy]; norm_num
  have hκ := ykKap_pos
  set c := tcC0 ν R χ with hcdef
  set l := pdLam h with hl
  set x := y - l • z with hx
  set L := fderiv ℝ (ykJ ν μ M) (h, x) with hL
  set K := C * l ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  set T := (‖x‖ ^ 4)⁻¹ with hT
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  have hxk : ykKap ≤ ‖x‖ := ykb_xnorm hy hz (pdLam_pos h) (ykb_pdLam_le_one hh.le)
  have hX0 : 0 < ‖x‖ := lt_of_lt_of_le hκ hxk
  have hxne : x ≠ 0 := norm_pos_iff.1 hX0
  have hT0 : 0 ≤ T := by positivity
  have hc2' : ContDiffAt ℝ 2 c (ϱ y) := by rw [hy]; exact hc2
  have hcy : ContDiffAt ℝ 2 (fun y' => c (ϱ y')) y := hc2'.comp y (ykb_offAxis_cd hyp)
  obtain ⟨hxkc, -, hbd⟩ := hC.2 ν μ h hν hμ0 hμ1 hh M
  obtain ⟨b0, b1, b2, -, -⟩ := hbd x hxne
  set V : Space → Space := fun y' => xKer ν μ h (y' - l • z) M with hV
  have hVc : ContDiffAt ℝ 2 V y :=
    hxkc.contDiffAt.comp y (contDiffAt_id.sub contDiffAt_const)
  have hX1 : ykX1 ν μ R χ z M h = fun y' => c (ϱ y') • V y' := rfl
  -- time derivative
  have hB := (ykb_partB ν μ hν M hh y z).const_smul (c (ϱ y))
  have hderiv : deriv (fun t => ykX1 ν μ R χ z M t y) h = c (ϱ y) • L (1, (l / 2) • z) := hB.deriv
  -- space derivative along `y`
  have hφd : DifferentiableAt ℝ (fun y' => c (ϱ y')) y := hcy.differentiableAt (by norm_num)
  have hVd : HasFDerivAt V (fderiv ℝ (fun x' => xKer ν μ h x' M) x) y := by
    have h1 : HasFDerivAt (fun x' => xKer ν μ h x' M) (fderiv ℝ (fun x' => xKer ν μ h x' M) x) x :=
      ((hxkc.differentiable (by norm_num)) x).hasFDerivAt
    have h2 : HasFDerivAt (fun y' : Space => y' - l • z) (ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).sub_const (l • z)
    have := h1.comp y h2
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hfd : fderiv ℝ (ykX1 ν μ R χ z M h) y y =
      c (ϱ y) • L (0, y) + (ϱ y * deriv c (ϱ y)) • V y := by
    have hP : HasFDerivAt (fun y' => c (ϱ y') • V y') _ y := hφd.hasFDerivAt.smul hVd
    rw [hX1, hP.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [tcle_dy_comp hyp (hc2'.differentiableAt (by norm_num)),
      ykJ_fderiv_eq ν μ hν M hh x y]
  -- Laplacian
  have hlap : physLap (ykX1 ν μ R χ z M h) y =
      (deriv (deriv c) (ϱ y) + deriv c (ϱ y) / ϱ y) • V y +
        (2 : ℝ) • (deriv c (ϱ y) • fderiv ℝ V y (radialUnit y)) + c (ϱ y) • physLap V y := by
    rw [hX1, tcle_lap_smul hcy hVc, tcle_lapS_comp hyp hc2',
      tcle_grad_sum c hyp (hc2'.differentiableAt (by norm_num)) (fderiv ℝ V y)]
  -- the recombination of the transport
  have hcomb : L (1, (l / 2) • z) - (1 / 2 : ℝ) • L (0, y) = L (1, -(1 / 2 : ℝ) • x) := by
    rw [← map_smul, ← map_sub]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · show (l / 2) • z - (1 / 2 : ℝ) • y = -(1 / 2 : ℝ) • x
      rw [hx]; module
  have heq : physDmu ν (μ + 1) (ykX1 ν μ R χ z M) h y =
      c (ϱ y) • L (1, -(1 / 2 : ℝ) • x) - (1 / 2 : ℝ) • ((ϱ y * deriv c (ϱ y)) • V y) -
        ν • ((deriv (deriv c) (ϱ y) + deriv c (ϱ y) / ϱ y) • V y +
          (2 : ℝ) • (deriv c (ϱ y) • fderiv ℝ V y (radialUnit y)) + c (ϱ y) • physLap V y) +
        (μ + 1 - 1 / 2) • (c (ϱ y) • V y) := by
    unfold physDmu
    rw [hderiv, hfd, hlap, ← hcomb]
    have : ykX1 ν μ R χ z M h y = c (ϱ y) • V y := rfl
    rw [this]
    module
  -- bounds
  rw [hy] at heq
  have hVy : ‖V y‖ ≤ K * T := by
    have : V y = xKer ν μ h x M := rfl
    rw [this]; refine b0.trans (le_of_eq ?_); rw [hK, hT]; ring
  obtain ⟨-, p5, p6⟩ := ykb_pow_inv hκ hxk le_rfl
  have hDV : ‖fderiv ℝ V y (radialUnit y)‖ ≤ K * (ykKap⁻¹ * T) := by
    rw [hVd.fderiv]
    refine ((fderiv ℝ (fun x' => xKer ν μ h x' M) x).le_opNorm _).trans ?_
    have hr := tc_radialUnit_norm hyp
    calc ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ * ‖radialUnit y‖
        ≤ ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ * 1 :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ ≤ K * (ykKap⁻¹ * T) := by
          rw [mul_one]; refine b1.trans ?_
          have e : C * l ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M = K * (‖x‖ ^ 5)⁻¹ := by
            rw [hK]; ring
          rw [e]; exact mul_le_mul_of_nonneg_left p5 hK0
  have hLV : ‖physLap V y‖ ≤ 3 * (K * ((ykKap ^ 2)⁻¹ * T)) := by
    refine (ykb_physLap_norm hVc).trans ?_
    have e : iteratedFDeriv ℝ 2 V y = iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x :=
      iteratedFDeriv_comp_sub (f := fun x' => xKer ν μ h x' M) 2 (l • z) y
    rw [e]
    refine mul_le_mul_of_nonneg_left (b2.trans ?_) (by norm_num)
    have e2 : C * l ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M = K * (‖x‖ ^ 6)⁻¹ := by
      rw [hK]; ring
    rw [e2]; exact mul_le_mul_of_nonneg_left p6 hK0
  have hDJ := ykb_DJ_half hC ν μ hν hν1 hμ0 hμ1 M hh hxk
  have hμa : |μ + 1 - 1 / 2| ≤ 3 / 2 := by rw [abs_le]; constructor <;> linarith
  refine ⟨hB.differentiableAt, by rw [hX1]; exact hcy.smul hVc, ?_⟩
  rw [heq]
  refine (ykb_norm4 _ _ _ _).trans ?_
  have hκi : 0 ≤ ykKap⁻¹ := inv_nonneg.2 hκ.le
  have hκ2 : 0 ≤ (ykKap ^ 2)⁻¹ := by positivity
  have n1 : ‖tcC0 ν R χ 1 • L (1, -(1 / 2 : ℝ) • x)‖ ≤ K * ((3 / 2 + (ykKap ^ 2)⁻¹) * T) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |tcC0 ν R χ 1| * ‖L (1, -(1 / 2 : ℝ) • x)‖ ≤ 1 * (K * ((3 / 2 + (ykKap ^ 2)⁻¹) * T)) :=
          mul_le_mul hc0 hDJ (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have n2 : ‖(1 / 2 : ℝ) • ((1 * deriv (tcC0 ν R χ) 1) • V y)‖ ≤ (1 / 2) * (A * (K * T)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hc1 hVy (norm_nonneg _) hA0) (by norm_num)
  have n3 : ‖ν • ((deriv (deriv (tcC0 ν R χ)) 1 + deriv (tcC0 ν R χ) 1 / 1) • V y +
      (2 : ℝ) • (deriv (tcC0 ν R χ) 1 • fderiv ℝ V y (radialUnit y)) +
        tcC0 ν R χ 1 • physLap V y)‖ ≤
      1 * (A * (K * T) + 2 * (A * (K * (ykKap⁻¹ * T))) + 1 * (3 * (K * ((ykKap ^ 2)⁻¹ * T)))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hν]
    refine mul_le_mul hν1 ((ykb_norm3 _ _ _).trans ?_) (norm_nonneg _) zero_le_one
    rw [norm_smul, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have a1 := mul_le_mul hcc hVy (norm_nonneg _) hA0
    have a2 := mul_le_mul hc1 hDV (norm_nonneg _) hA0
    have a3 := mul_le_mul hc0 hLV (norm_nonneg _) zero_le_one
    linarith
  have n4 : ‖(μ + 1 - 1 / 2) • (tcC0 ν R χ 1 • V y)‖ ≤ 3 / 2 * (1 * (K * T)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul hμa (mul_le_mul hc0 hVy (norm_nonneg _) zero_le_one)
      (by positivity) (by norm_num)
  have hKT : 0 ≤ K * T := mul_nonneg hK0 hT0
  have e5 : (3 + 4 * (ykKap ^ 2)⁻¹ + 2 * A + 2 * A * ykKap⁻¹) * K * T =
      K * ((3 / 2 + (ykKap ^ 2)⁻¹) * T) + (1 / 2) * (A * (K * T)) +
        1 * (A * (K * T) + 2 * (A * (K * (ykKap⁻¹ * T))) + 1 * (3 * (K * ((ykKap ^ 2)⁻¹ * T)))) +
        3 / 2 * (1 * (K * T)) + (1 / 2) * (A * (K * T)) := by ring
  have hAKT : 0 ≤ (1 / 2) * (A * (K * T)) := by positivity
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
