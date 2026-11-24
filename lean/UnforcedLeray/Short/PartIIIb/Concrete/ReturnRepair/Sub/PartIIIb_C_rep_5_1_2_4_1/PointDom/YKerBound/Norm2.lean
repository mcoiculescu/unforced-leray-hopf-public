import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Norm1

/-!
# `PDYKerBound` helpers (7): the stream part at the normalized radius

Source `the November 2 reference manuscript` 4178-4186, 5592.

`X₂(h, y) = F(ϱ y) Ψ(h, y) e_z`.  The transport is `F (∂_h - ½ y·∇)Ψ - ½ (y·∇F) Ψ`, and
`(∂_h - ½ y·∇)Ψ = Ψ[(∂_h - ½ x·∇_x) xKer] - Ψ` (`ykb_partC`, `ykb_partD`; the `λz`-transport of
`∂_h` and the dilation recombine); the Laplacian is bounded through the derivative bounds of `Ψ`.
Every term is `≤ C λ^{2μ+3} (1 + (y₃ - λz₃)²)^{-1} |M|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The stream part of the kernel. -/
def ykX2 (ν μ R : ℝ) (χ : ℝ → ℝ) (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (h' : ℝ)
    (y' : Space) : Space :=
  (tcF0 ν R χ (ϱ y') * sKer ν μ h' (ϱ y') (y' 2) z M) • coordinateVector 2

theorem ykb_e2_norm : ‖(coordinateVector 2 : Space)‖ = 1 := by simp [coordinateVector]

/-- **Part 2** at the normalized radius. -/
theorem ykb_part2 {C : ℝ} (hC : YKB C) (ν μ R : ℝ) (χ : ℝ → ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (y z : Space) (hy : ϱ y = 1) (hz : ϱ z ≤ ykR0) {A CF : ℝ} (hA0 : 0 ≤ A) (hCF0 : 0 ≤ CF)
    (hP2 : ContDiffAt ℝ 2 (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y)
    (hPb : ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun y' => sKer ν μ h (ϱ y') (y' 2) z M) y‖ ≤
        CF * (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (1 + (y 2 - pdLam h * z 2) ^ 2)⁻¹)
    (hf2 : ContDiffAt ℝ 2 (tcF0 ν R χ) 1) (hf0 : |tcF0 ν R χ 1| ≤ A)
    (hf1 : |deriv (tcF0 ν R χ) 1| ≤ A)
    (hff : |deriv (deriv (tcF0 ν R χ)) 1 + deriv (tcF0 ν R χ) 1 / 1| ≤ A) :
    DifferentiableAt ℝ (fun t => ykX2 ν μ R χ z M t y) h ∧
    ContDiffAt ℝ 2 (ykX2 ν μ R χ z M h) y ∧
    ‖physDmu ν (μ + 1) (ykX2 ν μ R χ z M) h y‖ ≤
      (A * (9 * CF + (3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹)) *
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (1 + (y 2 - pdLam h * z 2) ^ 2)⁻¹ := by
  have hyp : 0 < ϱ y := by rw [hy]; norm_num
  have hκ := ykKap_pos
  set f := tcF0 ν R χ with hfdef
  set l := pdLam h with hl
  set P : Space → ℝ := fun y' => sKer ν μ h (ϱ y') (y' 2) z M with hPdef
  set e2 : Space := coordinateVector 2 with he2
  set K := C * l ^ (2 * μ + 3) * IIIa.tensorNorm M with hK
  set T := (1 + (y 2 - l * z 2) ^ 2)⁻¹ with hT
  set q : Space := !₂[1, 0, y 2] with hqdef
  have hq0 : q 0 = 1 := by simp [hqdef]
  have hq2 : q 2 = y 2 := by simp [hqdef]
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC.1 (ykb_rpow_nonneg μ h)) (kb_tensor_nonneg M)
  have hT0 : 0 ≤ T := by positivity
  have hKT : 0 ≤ K * T := mul_nonneg hK0 hT0
  have hf2' : ContDiffAt ℝ 2 f (ϱ y) := by rw [hy]; exact hf2
  have hφ : ContDiffAt ℝ 2 (fun y' => f (ϱ y')) y := hf2'.comp y (ykb_offAxis_cd hyp)
  have hφd : DifferentiableAt ℝ (fun y' => f (ϱ y')) y := hφ.differentiableAt (by norm_num)
  have hPd : DifferentiableAt ℝ P y := hP2.differentiableAt (by norm_num)
  set V : Space → Space := fun y' => P y' • e2 with hV
  have hVc : ContDiffAt ℝ 2 V y := hP2.smul contDiffAt_const
  have hX2 : ykX2 ν μ R χ z M h = fun y' => f (ϱ y') • V y' := by
    funext y'; simp only [ykX2, hV, hPdef, mul_smul]; rfl
  -- bounds on `P`
  have hP0 : |P y| ≤ CF * K * T := by
    have := hPb 0 (by norm_num); rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hP1 : ‖fderiv ℝ P y‖ ≤ CF * K * T := by
    have := hPb 1 (by norm_num); rwa [norm_iteratedFDeriv_one] at this
  have hPy : P y = -primInt (xKerA ν μ h M) (l • z) q := by
    simp only [hPdef]; rw [sKer_eq_primInt, hy]
  -- time derivative
  obtain ⟨hFhi, hFhd⟩ := ykb_partC hC ν μ hν hμ0 hμ1 M hh z hz (y 2)
  have htime : (fun t => ykX2 ν μ R χ z M t y) = fun t => (f 1 * sKer ν μ t 1 (y 2) z M) • e2 := by
    funext t; simp only [ykX2, hy]; rfl
  set Ph := -∫ u in Ioi (0 : ℝ), ykFh ν μ M z q h u with hPh
  have hdt : HasDerivAt (fun t => ykX2 ν μ R χ z M t y) ((f 1 * Ph) • e2) h := by
    rw [htime]; exact (hFhd.const_mul (f 1)).smul_const e2
  -- space derivative along `y`
  obtain ⟨hGi, hPyeq⟩ := ykb_partD hC ν μ hν hμ0 hμ1 M hh y z hy hz hPd
  have hM' : HasFDerivAt (fun y' => f (ϱ y') * P y') _ y := hφd.hasFDerivAt.mul hPd.hasFDerivAt
  have hS : HasFDerivAt (fun y' => (f (ϱ y') * P y') • e2) _ y := hM'.smul_const e2
  have hfd : fderiv ℝ (ykX2 ν μ R χ z M h) y y =
      (f (ϱ y) * fderiv ℝ P y y + P y * (ϱ y * deriv f (ϱ y))) • e2 := by
    have e : ykX2 ν μ R χ z M h = fun y' => (f (ϱ y') * P y') • e2 := rfl
    rw [e, hS.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [tcle_dy_comp hyp (hf2'.differentiableAt (by norm_num))]
  -- Laplacian
  have hlap : physLap (ykX2 ν μ R χ z M h) y =
      (deriv (deriv f) (ϱ y) + deriv f (ϱ y) / ϱ y) • V y +
        (2 : ℝ) • (deriv f (ϱ y) • fderiv ℝ V y (radialUnit y)) + f (ϱ y) • physLap V y := by
    rw [hX2, tcle_lap_smul hφ hVc, tcle_lapS_comp hyp hf2',
      tcle_grad_sum f hyp (hf2'.differentiableAt (by norm_num)) (fderiv ℝ V y)]
  have hVy : ‖V y‖ ≤ CF * K * T := by
    simp only [hV]; rw [norm_smul, ykb_e2_norm, mul_one, Real.norm_eq_abs]; exact hP0
  have hVd : HasFDerivAt V ((fderiv ℝ P y).smulRight e2) y := hPd.hasFDerivAt.smul_const e2
  have hDV : ‖fderiv ℝ V y (radialUnit y)‖ ≤ CF * K * T := by
    rw [hVd.fderiv]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, ykb_e2_norm, mul_one]
    calc ‖fderiv ℝ P y‖ * ‖radialUnit y‖ ≤ ‖fderiv ℝ P y‖ * 1 :=
          mul_le_mul_of_nonneg_left (tc_radialUnit_norm hyp) (norm_nonneg _)
      _ ≤ CF * K * T := by rw [mul_one]; exact hP1
  have hLV : ‖physLap V y‖ ≤ 3 * (CF * K * T) := by
    refine (ykb_physLap_norm hVc).trans ?_
    have hVL : V = (ContinuousLinearMap.toSpanSingleton ℝ e2) ∘ P := by
      funext y'; simp [hV, ContinuousLinearMap.toSpanSingleton_apply]
    rw [hVL]
    have := (ContinuousLinearMap.toSpanSingleton ℝ e2).norm_iteratedFDeriv_comp_left hP2
      (n := 2) le_rfl
    rw [ContinuousLinearMap.norm_toSpanSingleton, ykb_e2_norm, one_mul] at this
    exact mul_le_mul_of_nonneg_left (this.trans (hPb 2 le_rfl)) (by norm_num)
  -- the recombination `Ph - ½ Py`
  set G : ℝ → ℝ := fun v => (q 0 + v) * (fderiv ℝ (fun x' => xKer ν μ h x' M)
    (q + (v • primE0 - l • z)) (q + v • primE0)) 2 with hG
  set W : ℝ → ℝ := fun u => (q 0 + u) * (fderiv ℝ (ykJ ν μ M) (h, q + (u • primE0 - l • z))
    (1, -(1 / 2 : ℝ) • (q + (u • primE0 - l • z)))) 2 with hW
  have hpt : ∀ u : ℝ, ykFh ν μ M z q h u - (1 / 2) * G u = W u := by
    intro u
    simp only [ykFh, hG, hW]
    rw [ykJ_fderiv_eq ν μ hν M hh]
    set L := fderiv ℝ (ykJ ν μ M) (h, q + (u • primE0 - l • z))
    have hc : L (1, (l / 2) • z) - (1 / 2 : ℝ) • L (0, q + u • primE0) =
        L (1, -(1 / 2 : ℝ) • (q + (u • primE0 - l • z))) := by
      rw [← map_smul, ← map_sub]
      congr 1
      refine Prod.ext ?_ ?_
      · simp
      · show (l / 2) • z - (1 / 2 : ℝ) • (q + u • primE0) = -(1 / 2 : ℝ) • (q + (u • primE0 - l • z))
        module
    rw [← hc]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hQ : Ph - (1 / 2) * fderiv ℝ P y y =
      primInt (xKerA ν μ h M) (l • z) q - ∫ u in Ioi (0 : ℝ), W u := by
    have hPy' : fderiv ℝ P y y = -(2 * primInt (xKerA ν μ h M) (l • z) q + ∫ v in Ioi (0 : ℝ), G v) :=
      hPyeq
    rw [hPy', hPh]
    have hI : ∫ u in Ioi (0 : ℝ), W u =
        (∫ u in Ioi (0 : ℝ), ykFh ν μ M z q h u) - (1 / 2) * ∫ v in Ioi (0 : ℝ), G v := by
      rw [← integral_const_mul, ← integral_sub hFhi (hGi.const_mul (1 / 2))]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      exact (hpt u).symm
    rw [hI]
    ring
  have hcb := ykb_comb_bound hC ν μ hν hν1 hμ0 hμ1 M hh z q hz hq0
  rw [hq2] at hcb
  set Cc := (3 / 2 + (ykKap ^ 2)⁻¹) * ykKap⁻¹ * (ykKap ^ 2)⁻¹ with hCc
  have hWb : |∫ u in Ioi (0 : ℝ), W u| ≤ Cc * (K * T) := by
    have := hcb
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [hCc, hK, hT]; ring
  have hQb : |Ph - (1 / 2) * fderiv ℝ P y y| ≤ CF * K * T + Cc * (K * T) := by
    rw [hQ]
    have h1 : |primInt (xKerA ν μ h M) (l • z) q| ≤ CF * K * T := by
      have := hP0; rw [hPy, abs_neg] at this; exact this
    exact (abs_sub _ _).trans (add_le_add h1 hWb)
  -- the expansion of `physDmu`
  have heq : physDmu ν (μ + 1) (ykX2 ν μ R χ z M) h y =
      (f 1 * (Ph - (1 / 2) * fderiv ℝ P y y) - (1 / 2) * (P y * (1 * deriv f 1)) +
        (μ + 1 - 1 / 2) * (f 1 * P y)) • e2 -
      ν • ((deriv (deriv f) 1 + deriv f 1 / 1) • V y +
        (2 : ℝ) • (deriv f 1 • fderiv ℝ V y (radialUnit y)) + f 1 • physLap V y) := by
    unfold physDmu
    have : ykX2 ν μ R χ z M h y = (f (ϱ y) * P y) • e2 := rfl
    rw [hdt.deriv, hfd, hlap, this, hy]
    module
  refine ⟨hdt.differentiableAt, by rw [hX2]; exact hφ.smul hVc, ?_⟩
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  have hμa : |μ + 1 - 1 / 2| ≤ 3 / 2 := by rw [abs_le]; constructor <;> linarith
  have n1 : ‖(f 1 * (Ph - (1 / 2) * fderiv ℝ P y y) - (1 / 2) * (P y * (1 * deriv f 1)) +
      (μ + 1 - 1 / 2) * (f 1 * P y)) • e2‖ ≤
      A * (CF * K * T + Cc * (K * T)) + (1 / 2) * (CF * K * T * A) +
        3 / 2 * (A * (CF * K * T)) := by
    rw [norm_smul _ e2, ykb_e2_norm, mul_one, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_sub _ _) le_rfl).trans ?_
    have t1 : |f 1 * (Ph - (1 / 2) * fderiv ℝ P y y)| ≤ A * (CF * K * T + Cc * (K * T)) := by
      rw [abs_mul]; exact mul_le_mul hf0 hQb (abs_nonneg _) hA0
    have t2 : |(1 / 2) * (P y * (1 * deriv f 1))| ≤ (1 / 2) * (CF * K * T * A) := by
      rw [one_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hP0 hf1 (abs_nonneg _) (by positivity))
        (by norm_num)
    have t3 : |(μ + 1 - 1 / 2) * (f 1 * P y)| ≤ 3 / 2 * (A * (CF * K * T)) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul hμa (mul_le_mul hf0 hP0 (abs_nonneg _) hA0) (by positivity) (by norm_num)
    linarith
  have n2 : ‖ν • ((deriv (deriv f) 1 + deriv f 1 / 1) • V y +
      (2 : ℝ) • (deriv f 1 • fderiv ℝ V y (radialUnit y)) + f 1 • physLap V y)‖ ≤
      1 * (A * (CF * K * T) + 2 * (A * (CF * K * T)) + A * (3 * (CF * K * T))) := by
    have t1 : ‖(deriv (deriv f) 1 + deriv f 1 / 1) • V y‖ ≤ A * (CF * K * T) := by
      rw [norm_smul (deriv (deriv f) 1 + deriv f 1 / 1) (V y), Real.norm_eq_abs]
      exact mul_le_mul hff hVy (norm_nonneg _) hA0
    have t2 : ‖(2 : ℝ) • (deriv f 1 • fderiv ℝ V y (radialUnit y))‖ ≤ 2 * (A * (CF * K * T)) := by
      rw [norm_smul (2 : ℝ), norm_smul (deriv f 1), Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hf1 hDV (norm_nonneg _) hA0) (by norm_num)
    have t3 : ‖f 1 • physLap V y‖ ≤ A * (3 * (CF * K * T)) := by
      rw [norm_smul (f 1) (physLap V y), Real.norm_eq_abs]
      exact mul_le_mul hf0 hLV (norm_nonneg _) hA0
    rw [norm_smul ν, Real.norm_eq_abs, abs_of_pos hν]
    refine mul_le_mul hν1 ((ykb_norm3 _ _ _).trans ?_) (norm_nonneg _) zero_le_one
    linarith
  have e5 : A * (9 * CF + Cc) * K * T =
      A * (CF * K * T + Cc * (K * T)) + (1 / 2) * (CF * K * T * A) +
        3 / 2 * (A * (CF * K * T)) +
        1 * (A * (CF * K * T) + 2 * (A * (CF * K * T)) + A * (3 * (CF * K * T))) := by ring
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
