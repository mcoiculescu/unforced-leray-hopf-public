import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleRHS

/-!
# Part III-a, task `PartIII-a:T21/c5/3/2` decomposition (`Sub/PartIII-a_T21_c5_3_2.lean`, SP 2866-2889, 2905-2918, 2990-2997)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2889,
2905-2918, and 2990-2997 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Proved infrastructure in this file (zero `sorry`)

1. **Unconditional moving pullback of `physLamDualEuler` (`cylinderBS_scale`, `kerD_scale`,
   `pdCx_physAdj_scale`, `movPullback_ladTransport_eq`, `movPullback_kerAdj_eq`,
   `movPullback_physLamDualEuler_eq`, `movLamDualEulerSub_eq_movEulerAdj_sub`)**:
   * Proves the exact scaling law `kerD c (√a z₁, √a z₂) k = (√a)⁻¹ * kerD (c / √a) z k` for the
     cylinder Biot-Savart kernel directly from `Kernels.cylinderBS` and `Cyl.bsKernel`.
   * Proves the chain rule `pdCx k (physAdj a Φ) (√a y₁, √a y₂) = (a / √a) * pdCx k Φ y` for every
     complex field `Φ : ℝ × ℝ → ℂ` without any differentiability assumption (both sides vanish
     when `Φ` is not differentiable at `y`).
   * Combines these with `E0.rescaleRHS_cellScaleC` and `E0.rescaleRHS_pd` to prove unconditionally
     that pulling back `physLamDualEuler κ tr r i` by `a(r)² * movingPhi ν` yields the moving
     linearised Euler adjoint operator `movEulerAdj d(r) (movingTrainV tr r) (movingTrainE tr r)`
     acting on `perLam κ d(r) i`.
2. **Unconditional quantitative `O(d⁻²)` Gram-inverse error (`perGram_sub_id_bound`,
   `gram_inv_sub_id_le`, `perGram_inv_sub_id_bound`, `perGram_inv_offDiag_bound`)**:
   Combines `perGramUnfold κ` and `perGramTail κ` (`Clock/FrameFacts.lean`) with the identity
   `G⁻¹ - I = G⁻¹ (I - G)` and `gram_inv_bound` to prove unconditionally that
   `‖(perGram κ d)⁻¹ i j - δ_{i,j}‖ ≤ C_inv / d²` for all sufficiently large `d`.
3. **Gram-normalisation reduction and conditional assemblies (`movLamDualEulerSub_split_of_linear`,
   `movLam0DualEulerSubBound_of_leaves`, `movLamDualEulerSubBound_of`,
   `movLamDualEulerSubBound_of_leaves`)**:
   Reduces `MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`) to two independent leaves:
   * `MovEulerAdjLinear κ` (`PartIII-a:T21/c5/3/2/1`): linearity of `movEulerAdj d(r)` across the
     2-term finite linear combination `perLam κ d(r) i = ∑ j, (perGram κ d(r))⁻¹ i j * perLam0 κ d(r) j`;
   * `MovLam0DualEulerSubNormBound κ` (`PartIII-a:T21/c5/3/2/2`): the `X_{-m, d(r)}` bound
     `O(1 / clockTheta ν r)` on the unnormalised seed residual `movLam0DualEulerSub κ lam tr r j`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplCouplingEuler

open ComplCouplingHeat

/-! ## 1. Moving-variable linearised Euler adjoint and unconditional pullback of `physLamDualEuler` -/

/-- Moving-variable linearised Euler adjoint operator on the cell of period `d`:
`V · ∇Φ - K_d^T (Φ ∇E)` (SP 2862-2865, 2905-2918). -/
def movEulerAdj (d : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (E : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ)
    (y : ℝ × ℝ) : ℂ :=
  E0.transCx V Φ y - kerAdj d (fun k w => Φ w * (B0579.pd k E w : ℂ)) y

/-- Scaling of the complex cylinder Biot-Savart kernel `Kernels.cylinderBS`:
`K_c(s z) = s⁻¹ K_{c / s}(z)` for `s ≠ 0`. -/
theorem cylinderBS_scale (c s : ℝ) (hs : s ≠ 0) (z : ℂ) :
    Kernels.cylinderBS c ((s : ℂ) * z) =
      ((s⁻¹ : ℝ) : ℂ) * Kernels.cylinderBS (c / s) z := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold Kernels.cylinderBS
  have harg : Real.pi * ((s : ℂ) * z) / (c : ℂ) = Real.pi * z / ((c / s : ℝ) : ℂ) := by
    push_cast
    rw [div_div_eq_mul_div]
    ring
  have hpre : (Real.pi : ℂ) / (c : ℂ) =
      ((s⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c / s : ℝ) : ℂ)) := by
    push_cast
    field_simp [hsC]
  rw [harg, hpre]
  ring

/-- Scaling of the real periodic Biot-Savart kernel `kerD`:
`kerD c (√a z₁, √a z₂) k = (√a)⁻¹ * kerD (cellLen c a) z k` for `a > 0`. -/
theorem kerD_scale (c a : ℝ) (ha : 0 < a) (z : ℝ × ℝ) (k : Fin 2) :
    kerD c (Real.sqrt a * z.1, Real.sqrt a * z.2) k =
      (Real.sqrt a)⁻¹ * kerD (cellLen c a) z k := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hbsC : UnforcedLeray.Cyl.bsC c (Real.sqrt a * z.1, Real.sqrt a * z.2) =
      (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * UnforcedLeray.Cyl.bsC (cellLen c a) z := by
    unfold UnforcedLeray.Cyl.bsC cellLen
    have hmul : ((Real.sqrt a * z.1 : ℝ) : ℂ) + ((Real.sqrt a * z.2 : ℝ) : ℂ) * Complex.I =
        (Real.sqrt a : ℂ) * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hmul, cylinderBS_scale c (Real.sqrt a) hs]
  unfold kerD UnforcedLeray.Cyl.bsKernel
  rw [hbsC, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, sub_zero, add_zero]
  fin_cases k <;> simp

/-- Chain rule for `pdCx k (physAdj a Φ)` at `(√a y₁, √a y₂)` for every `Φ : ℝ × ℝ → ℂ`
(no differentiability hypothesis needed: both sides vanish when `Φ` is not differentiable at `y`). -/
theorem pdCx_physAdj_scale (a : ℝ) (ha : 0 < a) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (physAdj a Φ) (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      ((a / Real.sqrt a : ℝ) : ℂ) * pdCx k Φ y := by
  set s : ℝ := (Real.sqrt a)⁻¹
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs : 0 < s := inv_pos.2 hsa
  have hsa_ne : Real.sqrt a ≠ 0 := hsa.ne'
  have hs_ne : s ≠ 0 := hs.ne'
  have ha_ne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpt : ∀ z : ℝ × ℝ, s • z = (z.1 / Real.sqrt a, z.2 / Real.sqrt a) := fun z => by
    ext <;> simp [s, div_eq_inv_mul]
  have hfun : physAdj a Φ = fun z : ℝ × ℝ => (a : ℂ) * Φ (s • z) := by
    funext z
    unfold physAdj
    rw [hpt z]
  set x : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have hxy : s • x = y := by
    ext <;> simp [s, x, inv_mul_cancel_left₀ hsa_ne]
  by_cases hΦ : DifferentiableAt ℝ Φ y
  · have hΦx : DifferentiableAt ℝ Φ (s • x) := hxy.symm ▸ hΦ
    have hg : HasFDerivAt (fun z : ℝ × ℝ => s • z) (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      (hasFDerivAt_id x).const_smul s
    have hc : HasFDerivAt (fun z : ℝ × ℝ => (a : ℂ) * Φ (s • z))
        ((a : ℂ) • ((fderiv ℝ Φ (s • x)).comp (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
      (hΦx.hasFDerivAt.comp x hg).const_mul (a : ℂ)
    unfold pdCx
    rw [hfun, hc.fderiv, hxy]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, Complex.real_smul, smul_eq_mul, s]
    push_cast
    ring
  · have hnd : ¬ DifferentiableAt ℝ (physAdj a Φ) x := by
      intro hd
      apply hΦ
      have hd2 : DifferentiableAt ℝ (physAdj a Φ) ((Real.sqrt a) • y) := by
        have hsy : (Real.sqrt a) • y = x := by ext <;> simp [x]
        rwa [hsy]
      have hΦeq : Φ = fun p : ℝ × ℝ =>
          (a : ℂ)⁻¹ * physAdj a Φ ((Real.sqrt a) • p) := by
        funext p
        unfold physAdj
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          mul_div_cancel_left₀ _ hsa_ne, Prod.mk.eta]
        rw [← mul_assoc, inv_mul_cancel₀ ha_ne, one_mul]
      rw [hΦeq]
      exact (hd2.comp y (differentiableAt_id.const_smul (Real.sqrt a))).const_mul (a : ℂ)⁻¹
    unfold pdCx
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hΦ]
    simp

/-- Unconditional moving pullback of `ladTransport tr r (physAdj (clockA ν r) Φ)`. -/
theorem movPullback_ladTransport_eq {ν c : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (Φ : ℝ → ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => ladTransport tr r' (physAdj (clockA ν r') (Φ r'))) r y =
      E0.transCx (movingTrainV tr r) (Φ r) y := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  have hsa_ne : Real.sqrt (clockA ν r) ≠ 0 := hsa.ne'
  have ha_ne : clockA ν r ≠ 0 := ha.ne'
  unfold movingPhi ladTransport E0.transCx movingTrainV
  dsimp only
  rw [pdCx_physAdj_scale (clockA ν r) ha (Φ r) 0 y,
    pdCx_physAdj_scale (clockA ν r) ha (Φ r) 1 y]
  have h32 : clockA ν r ^ (3 / 2 : ℝ) = clockA ν r * Real.sqrt (clockA ν r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' ha.le (by norm_num)]
    congr 1
    norm_num
  have h2 : clockA ν r ^ (2 : ℝ) = clockA ν r ^ 2 := Real.rpow_two (clockA ν r)
  have hdiv_sqrt : clockA ν r / Real.sqrt (clockA ν r) = Real.sqrt (clockA ν r) := by
    rw [div_eq_iff hsa_ne, Real.mul_self_sqrt ha.le]
  rw [h32, h2, hdiv_sqrt]
  push_cast
  have hsaC : (Real.sqrt (clockA ν r) : ℂ) ≠ 0 := by exact_mod_cast hsa_ne
  have haC : (clockA ν r : ℂ) ≠ 0 := by exact_mod_cast ha_ne
  field_simp [hsaC, haC]

/-- Unconditional moving pullback of `kerAdj c (fun k w => physAdj a Φ w * pd k E w)`. -/
theorem movPullback_kerAdj_eq {ν c : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (Φ : ℝ → ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' x' =>
        kerAdj c (fun k z => physAdj (clockA ν r') (Φ r') z *
          (B0579.pd k (UnforcedLeray.B0238.Ec tr r') z : ℂ)) x') r y =
      kerAdj (cellLen c (clockA ν r))
        (fun k w => Φ r w * (B0579.pd k (movingTrainE tr r) w : ℂ)) y := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  have hsa_ne : Real.sqrt (clockA ν r) ≠ 0 := hsa.ne'
  have ha_ne : clockA ν r ≠ 0 := ha.ne'
  have ha2_ne : (clockA ν r) ^ 2 ≠ 0 := pow_ne_zero 2 ha_ne
  have haC_ne : (clockA ν r : ℂ) ≠ 0 := by exact_mod_cast ha_ne
  have hsaC_ne : (Real.sqrt (clockA ν r) : ℂ) ≠ 0 := by exact_mod_cast hsa_ne
  have hsq_sqrtC : (Real.sqrt (clockA ν r) : ℂ) ^ 2 = (clockA ν r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  unfold movingPhi kerAdj
  dsimp only
  have hCoV := E0.rescaleRHS_cellScaleC c (clockA ν r) ha (fun z =>
    ∑ j : Fin 2, physAdj (clockA ν r) (Φ r) z *
      (B0579.pd j (UnforcedLeray.B0238.Ec tr r) z : ℂ) *
      ((kerD c (z - (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) j : ℝ) : ℂ))
  have hIntEq : (∫ w in B0579.cell (cellLen c (clockA ν r)),
      ∑ j : Fin 2, physAdj (clockA ν r) (Φ r)
          (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2) *
        (B0579.pd j (UnforcedLeray.B0238.Ec tr r)
          (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2) : ℂ) *
        ((kerD c ((Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2) -
          (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) j : ℝ) : ℂ)) =
      ((((clockA ν r) ^ 2)⁻¹ : ℝ) : ℂ) * ∫ w in B0579.cell (cellLen c (clockA ν r)),
        ∑ j : Fin 2, Φ r w * (B0579.pd j (movingTrainE tr r) w : ℂ) *
          ((kerD (cellLen c (clockA ν r)) (w - y) j : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    have hphys : physAdj (clockA ν r) (Φ r)
        (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2) =
        (clockA ν r : ℂ) * Φ r w := by
      unfold physAdj
      simp [mul_div_cancel_left₀ _ hsa_ne]
    have hsub : (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2) -
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
        (Real.sqrt (clockA ν r) * (w - y).1, Real.sqrt (clockA ν r) * (w - y).2) := by
      ext <;> dsimp <;> ring
    have hpd : ∀ j : Fin 2, B0579.pd j (movingTrainE tr r) w =
        (clockA ν r) ^ 2 * (Real.sqrt (clockA ν r) *
          B0579.pd j (UnforcedLeray.B0238.Ec tr r)
            (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2)) :=
      fun j => E0.rescaleRHS_pd (UnforcedLeray.B0238.Ec tr r) (Real.sqrt (clockA ν r))
        ((clockA ν r) ^ 2) hsa ha2_ne j w
    simp only [Fin.sum_univ_two, hphys, hsub, kerD_scale c (clockA ν r) ha (w - y), hpd 0, hpd 1]
    push_cast
    rw [← hsq_sqrtC]
    field_simp [hsaC_ne]
  have hCoV' : (∫ z in B0579.cell c,
      ∑ j : Fin 2, physAdj (clockA ν r) (Φ r) z *
        (B0579.pd j (UnforcedLeray.B0238.Ec tr r) z : ℂ) *
        ((kerD c (z - (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) j : ℝ) : ℂ)) =
      (clockA ν r : ℂ) * ((((clockA ν r) ^ 2)⁻¹ : ℝ) : ℂ) *
        ∫ w in B0579.cell (cellLen c (clockA ν r)),
          ∑ j : Fin 2, Φ r w * (B0579.pd j (movingTrainE tr r) w : ℂ) *
            ((kerD (cellLen c (clockA ν r)) (w - y) j : ℝ) : ℂ) := by
    rw [mul_assoc, ← hIntEq, hCoV, ← mul_assoc]
    have hinv : (clockA ν r : ℂ) * (((clockA ν r)⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast
      exact mul_inv_cancel₀ haC_ne
    rw [hinv, one_mul]
  rw [hCoV']
  have h2 : (clockA ν r) ^ (2 : ℝ) = (clockA ν r) ^ 2 := Real.rpow_two (clockA ν r)
  rw [h2]
  push_cast
  field_simp [haC_ne]

/-- Unconditional moving pullback of `physLamDualEuler`:
`a(r)² * movingPhi ν (physLamDualEuler κ tr · i) r = movEulerAdj d(r) (movingTrainV tr r) (movingTrainE tr r) (perLam κ d(r) i)`. -/
theorem movPullback_physLamDualEuler_eq (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2) (y : ℝ × ℝ) :
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y =
      movEulerAdj (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
        (movingTrainV tr r) (movingTrainE tr r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) y := by
  have hsplit : (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y =
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => ladTransport tr r' (physFrameLam κ ν r' i)) r y -
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' x' =>
          kerAdj (ν ^ (-2 : ℝ)) (fun k z => physFrameLam κ ν r' i z *
            (B0579.pd k (UnforcedLeray.B0238.Ec tr r') z : ℂ)) x') r y := by
    unfold movingPhi physLamDualEuler
    dsimp only
    ring
  rw [hsplit]
  unfold physFrameLam movEulerAdj
  rw [movPullback_ladTransport_eq tr hν hr
      (fun r' => perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i) y,
    movPullback_kerAdj_eq tr hν hr
      (fun r' => perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i) y]

/-- Unconditional moving-variable representation of `movLamDualEulerSub`:
`movLamDualEulerSub κ lam tr r i = movEulerAdj d(r) V E_mov (perLam κ d(r) i) - λ_i * perLam κ d(r) i`. -/
theorem movLamDualEulerSub_eq_movEulerAdj_sub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2) (y : ℝ × ℝ) :
    movLamDualEulerSub κ lam tr r i y =
      movEulerAdj (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
        (movingTrainV tr r) (movingTrainE tr r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) y -
      seedModeEigen lam i * perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y := by
  unfold movLamDualEulerSub
  rw [movPullback_physLamDualEuler_eq κ tr hν hr i y]

/-! ## 2. Quantitative `O(d⁻²)` Gram-inverse error -/

/-- Quantitative `O(d⁻²)` bound on `perGram κ d - I` from `perGramUnfold` and `perGramTail`. -/
theorem perGram_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧ ∀ d : ℝ, D_G ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ C_G / d ^ 2 := by
  obtain ⟨C, D₀, hC⟩ := perGramTail κ
  refine ⟨|C|, max D₀ 1, abs_nonneg C, le_max_right _ _, fun d hd i j => ?_⟩
  have hd0 : D₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  obtain ⟨hs, he⟩ := perGramUnfold κ d hdpos i j
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  have h0 : gramTerm κ d i j 0 = if i = j then 1 else 0 := by
    simp only [gramTerm, Int.cast_zero, zero_mul, add_zero]
    exact κ.biorth i j
  have hrest : perGram κ d i j - (if i = j then 1 else 0) =
      ∑' k : ℤ, (if k = 0 then (0 : ℂ) else gramTerm κ d i j k) := by
    rw [he, hsplit, h0]
    simp only [add_sub_cancel_left]
  rw [hrest]
  refine (hC d hd0 i j).trans ?_
  exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)

/-- For any `2 × 2` complex matrix `G` within `δ ≤ 1 / 4` of the identity,
`‖G⁻¹ i j - δ_{i,j}‖ ≤ 6 * δ` (from `G⁻¹ - I = G⁻¹ (I - G)` and `gram_inv_bound`). -/
theorem gram_inv_sub_id_le (G : Matrix (Fin 2) (Fin 2) ℂ) {δ : ℝ}
    (hδ : δ ≤ 1 / 4) (hG : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ δ) :
    ∀ i j : Fin 2, ‖G⁻¹ i j - (if i = j then 1 else 0)‖ ≤ 6 * δ := by
  have hG4 : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4 :=
    fun i j => (hG i j).trans hδ
  obtain ⟨hdet, hinv3⟩ := gram_inv_bound G hG4
  have hmul : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hdiff : G⁻¹ - 1 = G⁻¹ * (1 - G) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hmul]
  intro i j
  have hentry : G⁻¹ i j - (if i = j then 1 else 0) =
      G⁻¹ i 0 * ((if (0 : Fin 2) = j then 1 else 0) - G 0 j) +
      G⁻¹ i 1 * ((if (1 : Fin 2) = j then 1 else 0) - G 1 j) := by
    have h1 : G⁻¹ i j - (if i = j then 1 else 0) = (G⁻¹ - 1) i j := by
      simp [Matrix.sub_apply, Matrix.one_apply]
    rw [h1, hdiff, Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.sub_apply, Matrix.one_apply]
  rw [hentry]
  have hb0 : ‖(if (0 : Fin 2) = j then (1 : ℂ) else 0) - G 0 j‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hG 0 j
  have hb1 : ‖(if (1 : Fin 2) = j then (1 : ℂ) else 0) - G 1 j‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hG 1 j
  calc ‖G⁻¹ i 0 * ((if (0 : Fin 2) = j then 1 else 0) - G 0 j) +
          G⁻¹ i 1 * ((if (1 : Fin 2) = j then 1 else 0) - G 1 j)‖
      ≤ ‖G⁻¹ i 0 * ((if (0 : Fin 2) = j then 1 else 0) - G 0 j)‖ +
          ‖G⁻¹ i 1 * ((if (1 : Fin 2) = j then 1 else 0) - G 1 j)‖ := norm_add_le _ _
    _ = ‖G⁻¹ i 0‖ * ‖(if (0 : Fin 2) = j then (1 : ℂ) else 0) - G 0 j‖ +
          ‖G⁻¹ i 1‖ * ‖(if (1 : Fin 2) = j then (1 : ℂ) else 0) - G 1 j‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ 3 * δ + 3 * δ := by
        gcongr
        · exact hinv3 i 0
        · exact hinv3 i 1
    _ = 6 * δ := by ring

/-- Quantitative `O(d⁻²)` bound on `(perGram κ d)⁻¹ - I` for all sufficiently large `d`. -/
theorem perGram_inv_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_inv D_inv : ℝ, 0 ≤ C_inv ∧ 1 ≤ D_inv ∧ ∀ d : ℝ, D_inv ≤ d → ∀ i j : Fin 2,
      ‖(perGram κ d)⁻¹ i j - (if i = j then 1 else 0)‖ ≤ C_inv / d ^ 2 := by
  obtain ⟨C_G, D_G, hC_G0, hD_G1, hG⟩ := perGram_sub_id_bound κ
  set D_inv : ℝ := max D_G (2 * Real.sqrt C_G + 1)
  have hD_inv1 : 1 ≤ D_inv := le_trans hD_G1 (le_max_left _ _)
  refine ⟨6 * C_G, D_inv, by positivity, hD_inv1, fun d hd i j => ?_⟩
  have hdG : D_G ≤ d := le_trans (le_max_left _ _) hd
  have hd_sqrt : 2 * Real.sqrt C_G + 1 ≤ d := le_trans (le_max_right _ _) hd
  have hd1 : 1 ≤ d := le_trans hD_inv1 hd
  have hδ4 : C_G / d ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : 2 * Real.sqrt C_G ≤ d := by linarith
    have hsq : (2 * Real.sqrt C_G) ^ 2 ≤ d ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, Real.sq_sqrt hC_G0] at hsq
    linarith
  have hle := gram_inv_sub_id_le (perGram κ d) hδ4 (hG d hdG) i j
  calc ‖(perGram κ d)⁻¹ i j - (if i = j then 1 else 0)‖
      ≤ 6 * (C_G / d ^ 2) := hle
    _ = (6 * C_G) / d ^ 2 := by ring

/-- In particular, for off-diagonal indices `i ≠ j`, `‖(perGram κ d)⁻¹ i j‖ ≤ C_inv / d ^ 2`. -/
theorem perGram_inv_offDiag_bound (κ : PlanarFrameKernels) :
    ∃ C_inv D_inv : ℝ, 0 ≤ C_inv ∧ 1 ≤ D_inv ∧ ∀ d : ℝ, D_inv ≤ d → ∀ i j : Fin 2,
      i ≠ j → ‖(perGram κ d)⁻¹ i j‖ ≤ C_inv / d ^ 2 := by
  obtain ⟨C_inv, D_inv, hC0, hD1, hbound⟩ := perGram_inv_sub_id_bound κ
  refine ⟨C_inv, D_inv, hC0, hD1, fun d hd i j hij => ?_⟩
  have h := hbound d hd i j
  simp only [hij, ↓reduceIte, sub_zero] at h
  exact h

/-! ## 3. Unnormalised moving Euler residual and Gram-normalisation reduction -/

/-- Unnormalised moving Euler residual on `perLam0 κ d(r) j`:
`movEulerAdj d(r) V E_mov (perLam0 κ d(r) j) - λ_j * perLam0 κ d(r) j` (SP 2896, 2905-2918). -/
def movLam0DualEulerSub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movEulerAdj (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (movingTrainV tr r) (movingTrainE tr r)
    (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y -
    seedModeEigen lam j * perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- When `movEulerAdj` distributes linearly over `perLam κ d i = ∑_j (G⁻¹)_{i,j} perLam0 κ d j`,
`movLamDualEulerSub` splits into the Gram-normalised sum of `movLam0DualEulerSub` plus the
off-diagonal eigenvalue mismatch `(G⁻¹)_{i,j} (λ_j - λ_i) perLam0 κ d j`. -/
theorem movLamDualEulerSub_split_of_linear (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2) (y : ℝ × ℝ)
    (hlin :
      let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
      movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) y =
        ∑ j : Fin 2, (perGram κ d)⁻¹ i j *
          movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d j) y) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movLamDualEulerSub κ lam tr r i y =
      ∑ j : Fin 2,
        ((perGram κ d)⁻¹ i j * movLam0DualEulerSub κ lam tr r j y +
          ((perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)) *
            perLam0 κ d j y) := by
  intro d
  rw [movLamDualEulerSub_eq_movEulerAdj_sub κ lam tr hν hr i y, hlin]
  unfold perLam movLam0DualEulerSub
  simp only [Fin.sum_univ_two]
  ring

/-! ## 4. Analytical leaves for `MovLamDualEulerSubBound` (`PartIII-a:T21/c5/3/2`) -/

/-- **Leaf 1 (`PartIII-a:T21/c5/3/2/1`, `MovEulerAdjLinear`, SP 2891-2897, 2905-2918)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), `0 < ν`, a BUC train `tr`, and `0 ≤ r` with
`1 ≤ d(r)`, the moving-variable linearised Euler adjoint `movEulerAdj d(r) (movingTrainV tr r) (movingTrainE tr r)`
distributes linearly over the 2-term finite linear combination
`perLam κ d(r) i = ∑ j : Fin 2, (perGram κ d(r))⁻¹ i j * perLam0 κ d(r) j`
(via differentiability of `perLam0 κ d(r) j` for `E0.transCx` and local `L¹` integrability of the
cylinder Biot-Savart integrand on `B0579.cell d(r)` for `kerAdj`).
Composed by `PartIII-a:T21/c5/3/2` via `movLamDualEulerSubBound_of_leaves`. -/
def MovEulerAdjLinear (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ {ν : ℝ}, 0 < ν →
  ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
  ∀ {r : ℝ}, 0 ≤ r →
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    1 ≤ d →
    ∀ (i : Fin 2) (y : ℝ × ℝ),
      movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) y =
        ∑ j : Fin 2, (perGram κ d)⁻¹ i j *
          movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d j) y

/-- **Leaf 2 (`PartIII-a:T21/c5/3/2/2`, `MovLam0DualEulerSubNormBound`, SP 2866-2889, 2905-2918, 2990-2997)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`) and `m > 8`, there exist the planar seed
eigenvalue `lam : ℂ` and constants `C_0 ≥ 0`, `b_0 ≥ 1` such that for `b ≥ b_0`, small `ν > 0`,
and any BUC train `tr`, at every age `r ≥ 0` with `b ≤ clockTheta ν r`, the unnormalised moving
Euler residual `movLam0DualEulerSub κ lam tr r j` (combining the planar seed duality
`L_0^* λ_j = λ_j λ_j`, the paired-image cylinder Biot-Savart tail `O(d(r)⁻²) = O(ν³ / θ(r))`, and
the rescaled BUC train comparison) belongs to `X_{-m, d(r)}` with norm at most
`C_0 / clockTheta ν r`.
Composed by `PartIII-a:T21/c5/3/2` via `movLamDualEulerSubBound_of_leaves`. -/
def MovLam0DualEulerSubNormBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ lam : ℂ, ∃ C_0 b_0 : ℝ, 0 ≤ C_0 ∧ 1 ≤ b_0 ∧
    ∀ b : ℝ, b_0 ≤ b →
      ∃ ν_0 : ℝ, 0 < ν_0 ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_0 →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          ∀ j : Fin 2,
            MemLp (movLam0DualEulerSub κ lam tr r j) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (movLam0DualEulerSub κ lam tr r j) ≤
              ENNReal.ofReal (C_0 * (1 / clockTheta ν r))

/-- Combined unnormalised seed-row package `MovLam0DualEulerSubBound κ` (SP 2866-2889, 2905-2918, 2990-2997). -/
def MovLam0DualEulerSubBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ lam : ℂ, ∃ C_0 b_0 : ℝ, 0 ≤ C_0 ∧ 1 ≤ b_0 ∧
    ∀ b : ℝ, b_0 ≤ b →
      ∃ ν_0 : ℝ, 0 < ν_0 ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_0 →
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
          let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
          (∀ (i : Fin 2) (y : ℝ × ℝ),
            movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam κ d i) y =
              ∑ j : Fin 2, (perGram κ d)⁻¹ i j *
                movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d j) y) ∧
          ∀ j : Fin 2,
            MemLp (movLam0DualEulerSub κ lam tr r j) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (movLam0DualEulerSub κ lam tr r j) ≤
              ENNReal.ofReal (C_0 * (1 / clockTheta ν r))

/-- Combines `MovEulerAdjLinear κ` (`PartIII-a:T21/c5/3/2/1`) and `MovLam0DualEulerSubNormBound κ`
(`PartIII-a:T21/c5/3/2/2`) into `MovLam0DualEulerSubBound κ`. -/
theorem movLam0DualEulerSubBound_of_leaves (κ : PlanarFrameKernels)
    (hLin : MovEulerAdjLinear κ)
    (hNorm : MovLam0DualEulerSubNormBound κ) :
    MovLam0DualEulerSubBound κ := by
  intro hκ m hm
  obtain ⟨lam, C_0, b_0, hC_0, hb_0, hN⟩ := hNorm hκ m hm
  refine ⟨lam, C_0, b_0, hC_0, hb_0, fun b hb => ?_⟩
  obtain ⟨ν_0, hν_0, hν0⟩ := hN b hb
  refine ⟨min ν_0 1, lt_min hν_0 zero_lt_one, fun ν hν tr hBUC r hr hθ => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν0' : ν ≤ ν_0 := le_trans hν.2 (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hθ1 : 1 ≤ clockTheta ν r := le_trans (le_trans hb_0 hb) hθ
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    ComplCouplingSub.one_le_cellLen_of_theta hν_pos hν1 hr hθ1
  exact ⟨hLin hκ hν_pos tr hBUC hr hd1, hν0 ν ⟨hν_pos, hν0'⟩ tr hBUC r hr hθ⟩

/-- Conditional proof of `MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`) from
`MovLam0DualEulerSubBound κ`, using the proved `O(d⁻²) = O(ν³ / θ(r))` off-diagonal Gram-inverse
bound (`perGram_inv_offDiag_bound`) and `inv_cellLen_sq_eq_nu_cube_div_theta`. -/
theorem movLamDualEulerSubBound_of (κ : PlanarFrameKernels)
    (hLam0 : MovLam0DualEulerSubBound κ) :
    MovLamDualEulerSubBound κ := by
  intro hκ m hm
  have hm1 : 1 < m := by linarith
  obtain ⟨lam, C_0, b_0, hC_0, hb_0, h0⟩ := hLam0 hκ m hm
  obtain ⟨K₀, hK₀, hPerLam0⟩ := memLp_and_xNorm_perLam0_neg κ hm1
  obtain ⟨D_1, hD_1, hGramInv3⟩ := perGram_inv_entry_bound κ
  obtain ⟨C_inv, D_inv, hC_inv0, hD_inv1, hOffDiag⟩ := perGram_inv_offDiag_bound κ
  set D : ℝ := max D_1 D_inv
  have hD1 : 1 ≤ D := le_trans hD_1 (le_max_left _ _)
  have hD0 : 0 ≤ D := by linarith
  set L_diff : ℝ := 2 * ‖lam‖
  have hL_diff0 : 0 ≤ L_diff := by positivity
  have heigen_diff : ∀ i j : Fin 2, ‖seedModeEigen lam j - seedModeEigen lam i‖ ≤ L_diff := by
    intro i j
    calc ‖seedModeEigen lam j - seedModeEigen lam i‖
        ≤ ‖seedModeEigen lam j‖ + ‖seedModeEigen lam i‖ := norm_sub_le _ _
      _ ≤ ‖lam‖ + ‖lam‖ := by
          gcongr <;> {
            unfold seedModeEigen
            split_ifs <;> simp
          }
      _ = L_diff := by unfold L_diff; ring
  set C_e : ℝ := 2 * (3 * C_0 + C_inv * L_diff * K₀)
  have hC_e0 : 0 ≤ C_e := by positivity
  refine ⟨lam, C_e, b_0, hC_e0, hb_0, fun b hb => ?_⟩
  obtain ⟨ν_0, hν_0, hν0_bound⟩ := h0 b hb
  set ν_e : ℝ := min ν_0 (min 1 (1 / (D + 1) ^ 2))
  have hν_e_pos : 0 < ν_e := by
    refine lt_min hν_0 (lt_min zero_lt_one (by positivity))
  refine ⟨ν_e, hν_e_pos, fun ν hν tr hBUC r hr hθ i => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_le_0 : ν ≤ ν_0 := le_trans hν.2 (min_le_left _ _)
  have hν_le_1 : ν ≤ 1 := le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hν_le_D : ν ≤ 1 / (D + 1) ^ 2 :=
    le_trans hν.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hb1 : 1 ≤ b := le_trans hb_0 hb
  have hdD : D ≤ d := cellLen_ge hD0 hν_pos hν_le_D hb1 hr hθ
  have hd1 : 1 ≤ d := le_trans hD1 hdD
  have hd_D1 : D_1 ≤ d := le_trans (le_max_left _ _) hdD
  have hd_Dinv : D_inv ≤ d := le_trans (le_max_right _ _) hdD
  have hθ1 : 1 ≤ clockTheta ν r := le_trans hb1 hθ
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ1
  have hinv_d_le : 1 / d ^ 2 ≤ 1 / clockTheta ν r := by
    rw [ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta hν_pos hr]
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν_pos.le hν_le_1
    exact div_le_div_of_nonneg_right hν3 hθ_pos.le
  obtain ⟨hlin, h0_row⟩ := hν0_bound ν ⟨hν_pos, hν_le_0⟩ tr hBUC r hr hθ
  have hterm : ∀ j : Fin 2,
      let T := fun y => (perGram κ d)⁻¹ i j * movLam0DualEulerSub κ lam tr r j y +
        ((perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)) * perLam0 κ d j y
      MemLp T 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) T ≤
        ENNReal.ofReal ((3 * C_0 + C_inv * L_diff * K₀) * (1 / clockTheta ν r)) := by
    intro j
    obtain ⟨h0m, h0x⟩ := h0_row j
    obtain ⟨hL0m, hL0x⟩ := hPerLam0 d hd1 j
    have hAm : MemLp (fun y => (perGram κ d)⁻¹ i j * movLam0DualEulerSub κ lam tr r j y) 2
        (B0579.cellMeasure d (-m)) := h0m.const_mul _
    have hAx : xNorm d (-m) (fun y => (perGram κ d)⁻¹ i j * movLam0DualEulerSub κ lam tr r j y) ≤
        ENNReal.ofReal (3 * C_0 * (1 / clockTheta ν r)) := by
      refine (xNorm_const_mul_le (by positivity) h0x).trans (ENNReal.ofReal_le_ofReal ?_)
      have hG_le : ‖(perGram κ d)⁻¹ i j‖ ≤ 3 := hGramInv3 d hd_D1 i j
      calc ‖(perGram κ d)⁻¹ i j‖ * (C_0 * (1 / clockTheta ν r))
          ≤ 3 * (C_0 * (1 / clockTheta ν r)) := by gcongr
        _ = 3 * C_0 * (1 / clockTheta ν r) := by ring
    have hBm : MemLp
        (fun y => ((perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)) *
          perLam0 κ d j y) 2 (B0579.cellMeasure d (-m)) := hL0m.const_mul _
    have hcoeff : ‖(perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)‖ ≤
        C_inv * L_diff * (1 / clockTheta ν r) := by
      by_cases hij : i = j
      · subst hij
        simp only [sub_self, mul_zero, norm_zero]
        positivity
      · rw [norm_mul]
        have hG_off : ‖(perGram κ d)⁻¹ i j‖ ≤ C_inv * (1 / clockTheta ν r) := by
          calc ‖(perGram κ d)⁻¹ i j‖ ≤ C_inv / d ^ 2 := hOffDiag d hd_Dinv i j hij
            _ = C_inv * (1 / d ^ 2) := by ring
            _ ≤ C_inv * (1 / clockTheta ν r) := by gcongr
        have heig : ‖seedModeEigen lam j - seedModeEigen lam i‖ ≤ L_diff := heigen_diff i j
        calc ‖(perGram κ d)⁻¹ i j‖ * ‖seedModeEigen lam j - seedModeEigen lam i‖
            ≤ (C_inv * (1 / clockTheta ν r)) * L_diff := by gcongr
          _ = C_inv * L_diff * (1 / clockTheta ν r) := by ring
    have hBx : xNorm d (-m)
        (fun y => ((perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)) *
          perLam0 κ d j y) ≤
        ENNReal.ofReal (C_inv * L_diff * K₀ * (1 / clockTheta ν r)) := by
      refine (xNorm_const_mul_le hK₀ hL0x).trans (ENNReal.ofReal_le_ofReal ?_)
      calc ‖(perGram κ d)⁻¹ i j * (seedModeEigen lam j - seedModeEigen lam i)‖ * K₀
          ≤ (C_inv * L_diff * (1 / clockTheta ν r)) * K₀ := by gcongr
        _ = C_inv * L_diff * K₀ * (1 / clockTheta ν r) := by ring
    obtain ⟨hABm, hABx⟩ := memLp_and_xNorm_add_le
      (by positivity) (by positivity) hAm hBm hAx hBx
    refine ⟨hABm, hABx.trans ?_⟩
    rw [show 3 * C_0 * (1 / clockTheta ν r) + C_inv * L_diff * K₀ * (1 / clockTheta ν r) =
      (3 * C_0 + C_inv * L_diff * K₀) * (1 / clockTheta ν r) by ring]
  obtain ⟨hm0, hx0⟩ := hterm 0
  obtain ⟨hm1', hx1'⟩ := hterm 1
  have hsum_eq : movLamDualEulerSub κ lam tr r i = fun y =>
      ((perGram κ d)⁻¹ i 0 * movLam0DualEulerSub κ lam tr r 0 y +
        ((perGram κ d)⁻¹ i 0 * (seedModeEigen lam 0 - seedModeEigen lam i)) * perLam0 κ d 0 y) +
      ((perGram κ d)⁻¹ i 1 * movLam0DualEulerSub κ lam tr r 1 y +
        ((perGram κ d)⁻¹ i 1 * (seedModeEigen lam 1 - seedModeEigen lam i)) * perLam0 κ d 1 y) := by
    funext y
    rw [movLamDualEulerSub_split_of_linear κ lam tr hν_pos hr i y (hlin i y), Fin.sum_univ_two]
  rw [hsum_eq]
  obtain ⟨hm_tot, hx_tot⟩ := memLp_and_xNorm_add_le
    (by positivity) (by positivity) hm0 hm1' hx0 hx1'
  refine ⟨hm_tot, hx_tot.trans ?_⟩
  rw [show (3 * C_0 + C_inv * L_diff * K₀) * (1 / clockTheta ν r) +
      (3 * C_0 + C_inv * L_diff * K₀) * (1 / clockTheta ν r) =
      C_e * (1 / clockTheta ν r) by unfold C_e; ring]

/-- Primary two-leaf conditional assembly of `MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`)
from `MovEulerAdjLinear κ` (`PartIII-a:T21/c5/3/2/1`) and `MovLam0DualEulerSubNormBound κ`
(`PartIII-a:T21/c5/3/2/2`). -/
theorem movLamDualEulerSubBound_of_leaves (κ : PlanarFrameKernels)
    (hLin : MovEulerAdjLinear κ)
    (hNorm : MovLam0DualEulerSubNormBound κ) :
    MovLamDualEulerSubBound κ :=
  movLamDualEulerSubBound_of κ (movLam0DualEulerSubBound_of_leaves κ hLin hNorm)

end ComplCouplingEuler

end UnforcedLeray.Short.IIIa
