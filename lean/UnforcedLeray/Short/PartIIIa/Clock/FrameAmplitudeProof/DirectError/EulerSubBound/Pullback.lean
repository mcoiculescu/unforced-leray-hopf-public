import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum

/-!
# Part III-a, task `PartIII-a:T21/c5/2/2/1`: unnormalised moving Euler pullback (`MovLam0EulerPullback`, SP 2905-2918)

Source of record: `the November 2 reference manuscript` (SP), lines 2905-2918
(`eq:short-causal-ampl-moving`).

## Proved results in this file (zero `sorry`)

1. **Unconditional moving pullback of `physLam0DualEuler` (`movPullback_physLam0DualEuler_eq`,
   `movLam0DualEulerSub_eq_movEulerAdj_sub`)**:
   * Pulls `physLam0DualEuler κ tr r k` back to moving coordinates via
     `ComplCouplingEuler.movPullback_ladTransport_eq` and `ComplCouplingEuler.movPullback_kerAdj_eq`,
     showing unconditionally that for `0 < ν` and `0 ≤ r`,
     `(((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y =
       ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d k) y`.
   * Identifies `UnforcedLeray.Short.IIIa.movLam0DualEulerSub` (`Sub/PartIII-a_T21_c5_2_2.lean`)
     pointwise with `ComplCouplingEuler.movLam0DualEulerSub` (`Sub/PartIII-a_T21_c5_3_2.lean`).

2. **General near/far integrability and `L^∞` bound for `kerAdj` terms
   (`kerAdj_term_integrableOn_and_bound`, `kerAdj_linear_comb_two`)**:
   * For any `1 ≤ d` and any a.e. strongly measurable field `G : ℝ × ℝ → ℂ` on `B0579.cell d`
     satisfying `∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M`, combines periodic extension from
     `B0579.cell d` (`toIcoMod`), translation invariance (`Cyl.lintegral_cell_comp_sub_left`),
     `Lam0B.integrable_jb_neg_two`, and the near/far Biot-Savart split `kerNearFar` to prove both
     `IntegrableOn (fun w => G w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d)` and the uniform
     pointwise bound `‖∫ w in B0579.cell d, G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ ≤ C_K * M` for all
     `y : ℝ × ℝ` and `l : Fin 2`.
   * Deduces linearity of `kerAdj d` over two-term linear combinations (`kerAdj_linear_comb_two`).

3. **Unconditional `kerAdj` linearity on `perLam` (`pd_movingTrainE_eq_movingTrainGradE`,
   `kerAdj_perLam_eq`)**:
   * Combines `CutFTCDual.ladTrainBddAll_unconditional 2` and `Lam0B.perLam0_sup` with
     `kerAdj_term_integrableOn_and_bound` to prove unconditionally that for `d ≥ D_ep`,
     `kerAdj d (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y =
       ∑ k : Fin 2, (perGram κ d)⁻¹ i k *
         kerAdj d (fun l w => perLam0 κ d k w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y`.

4. **Linearity of `E0.transCx` and conditional assembly (`transCx_perLam_eq_of_diff`,
   `movLam0EulerPullback_of_diff`, `movLam0EulerPullback_of`)**:
   * Uses `CutFTCAux.pdCx_perLam_eq` to prove linearity of `E0.transCx V` on `perLam κ d i`
     whenever `perLam0 κ d 0` and `perLam0 κ d 1` are differentiable at `y`.
   * Combines the `E0.transCx` and `kerAdj` linearities with `movPullback_physLamDualEuler_eq` and
     `movPullback_physLam0DualEuler_eq` to derive `MovLam0EulerPullback κ` from
     `PerLam0Differentiable κ` (and in particular from sibling leaf `SeedLamGradPerSum κ`,
     `PartIII-a:T21/c5/1/1/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DirectEulerSub

open ComplCouplingSub ComplCouplingHeat ComplCouplingEuler CutFTCDual CutFTCAux EulerErrorSub

/-! ## 1. Unconditional moving pullback of `physLam0DualEuler` -/

/-- Unconditional moving pullback of `physLam0DualEuler`:
`a(r)² * movingPhi ν (physLam0DualEuler κ tr · k) r = movEulerAdj d(r) (movingTrainV tr r) (movingTrainE tr r) (perLam0 κ d(r) k)`. -/
theorem movPullback_physLam0DualEuler_eq (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (k : Fin 2) (y : ℝ × ℝ) :
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y =
      movEulerAdj (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
        (movingTrainV tr r) (movingTrainE tr r)
        (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) y := by
  have hsplit : (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y =
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => ladTransport tr r' (physFrameLam0Euler κ ν r' k)) r y -
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' x' =>
          kerAdj (ν ^ (-2 : ℝ)) (fun l z => physFrameLam0Euler κ ν r' k z *
            (B0579.pd l (UnforcedLeray.B0238.Ec tr r') z : ℂ)) x') r y := by
    unfold movingPhi physLam0DualEuler
    dsimp only
    ring
  rw [hsplit]
  unfold physFrameLam0Euler movEulerAdj
  rw [movPullback_ladTransport_eq tr hν hr
      (fun r' => perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) k) y,
    movPullback_kerAdj_eq tr hν hr
      (fun r' => perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) k) y]

/-- Unconditional moving-variable representation of `movLam0DualEulerSub`:
identifies `UnforcedLeray.Short.IIIa.movLam0DualEulerSub` with
`ComplCouplingEuler.movLam0DualEulerSub`. -/
theorem movLam0DualEulerSub_eq_movEulerAdj_sub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (k : Fin 2) (y : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.movLam0DualEulerSub κ lam tr r k y =
      ComplCouplingEuler.movLam0DualEulerSub κ lam tr r k y := by
  unfold UnforcedLeray.Short.IIIa.movLam0DualEulerSub ComplCouplingEuler.movLam0DualEulerSub
  rw [movPullback_physLam0DualEuler_eq κ tr hν hr k y]

/-! ## 2. General near/far integrability and `L^∞` bound for `kerAdj` terms -/

/-- Any field `G : ℝ × ℝ → ℂ` on `B0579.cell d` satisfying `B0579.jb w ^ 2 * ‖G w‖ ≤ M` has
cell `L¹` lintegral bounded by `M * ∫ z, B0579.jb z ^ (-(2 : ℝ))`. -/
theorem lintegral_cell_le_of_jb_sq {d M : ℝ} (hM : 0 ≤ M) {G : ℝ × ℝ → ℂ}
    (hG : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M) :
    (∫⁻ w in B0579.cell d, ‖G w‖ₑ) ≤
      ENNReal.ofReal (M * ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))) := by
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hint : Integrable (fun z : ℝ × ℝ => M * B0579.jb z ^ (-(2 : ℝ))) :=
    Lam0B.integrable_jb_neg_two.const_mul M
  have hnn : ∀ z : ℝ × ℝ, 0 ≤ M * B0579.jb z ^ (-(2 : ℝ)) :=
    fun z => mul_nonneg hM (Real.rpow_nonneg (B0579.jb_pos z).le _)
  calc ∫⁻ w in B0579.cell d, ‖G w‖ₑ
      ≤ ∫⁻ w in B0579.cell d, ENNReal.ofReal (M * B0579.jb w ^ (-(2 : ℝ))) := by
        refine setLIntegral_mono' hmeas_cell (fun w hw => ?_)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have hjb_pos : 0 < B0579.jb w := B0579.jb_pos w
        rw [Real.rpow_neg hjb_pos.le, Real.rpow_two, ← div_eq_mul_inv,
          le_div_iff₀ (sq_pos_of_pos hjb_pos), mul_comm]
        exact hG w hw
    _ ≤ ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (M * B0579.jb w ^ (-(2 : ℝ))) :=
        setLIntegral_le_lintegral (B0579.cell d) _
    _ = ENNReal.ofReal (∫ z : ℝ × ℝ, M * B0579.jb z ^ (-(2 : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
    _ = ENNReal.ofReal (M * ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))) := by
        rw [integral_const_mul]

/-- Universal near/far integrability and `L^∞` bound for each component of `kerAdj d`:
there exists `C_K ≥ 0` such that for any `d ≥ 1`, `M ≥ 0`, and any `G : ℝ × ℝ → ℂ` that is a.e.
strongly measurable on `B0579.cell d` and satisfies `∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M`,
for every `y : ℝ × ℝ` and `l : Fin 2`:
1. `IntegrableOn (fun w => G w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d)`, and
2. `‖∫ w in B0579.cell d, G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ ≤ C_K * M`. -/
theorem kerAdj_term_integrableOn_and_bound :
    ∃ C_K : ℝ, 0 ≤ C_K ∧
      ∀ {d M : ℝ}, 1 ≤ d → 0 ≤ M →
      ∀ {G : ℝ × ℝ → ℂ},
        AEStronglyMeasurable G (volume.restrict (B0579.cell d)) →
        (∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖G w‖ ≤ M) →
        ∀ (y : ℝ × ℝ) (l : Fin 2),
          IntegrableOn (fun w => G w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) ∧
          ‖∫ w in B0579.cell d, G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ ≤ C_K * M := by
  obtain ⟨C_NF, hCNF_pos, hNF⟩ := kerNearFar
  set I_jb : ℝ := ∫ z : ℝ × ℝ, B0579.jb z ^ (-(2 : ℝ))
  have hIjb_pos : 0 ≤ I_jb :=
    integral_nonneg (fun z => Real.rpow_nonneg (B0579.jb_pos z).le _)
  set C_K : ℝ := C_NF * (1 + I_jb)
  refine ⟨C_K, by positivity, fun {d M} hd hM {G} hGm hG_bd y l => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hK_meas, hK_per, hK_odd, hK_near, hK_far⟩ := hNF d hd
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hmeas_ball : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  set near : Set (ℝ × ℝ) := B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1
  set far : Set (ℝ × ℝ) := B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1
  have hmeas_near : MeasurableSet near := hmeas_cell.inter hmeas_ball
  have hmeas_far : MeasurableSet far := hmeas_cell.diff hmeas_ball
  -- Periodize `G` from `B0579.cell d` via `toIcoMod`
  set p : ℝ × ℝ → ℝ × ℝ := fun z => (toIcoMod hd0 (-(d / 2)) z.1, z.2)
  set Gp : ℝ × ℝ → ℂ := fun z => G (p z)
  have hp_mem : ∀ z : ℝ × ℝ, p z ∈ B0579.cell d := by
    intro z
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, p]
    have hm := toIcoMod_mem_Ico hd0 (-(d / 2)) z.1
    refine ⟨by linarith [hm.1, neg_div d 2], by linarith [hm.2, neg_div d 2]⟩
  have hp_id : ∀ w ∈ B0579.cell d, p w = w := by
    intro w hw
    have hw1 : -(d / 2) ≤ w.1 ∧ w.1 < -(d / 2) + d := by
      refine ⟨by linarith [hw.1.1, neg_div d 2], by linarith [hw.1.2, neg_div d 2]⟩
    ext
    · exact (toIcoMod_eq_self hd0).2 hw1
    · rfl
  have hGp_sup : ∀ z : ℝ × ℝ, ‖Gp z‖ ≤ M := by
    intro z
    have hz := hG_bd (p z) (hp_mem z)
    have hjb1 : 1 ≤ B0579.jb (p z) ^ 2 := one_le_pow₀ (Lam0B.jb_ge_one (p z))
    exact (le_mul_of_one_le_left (norm_nonneg _) hjb1).trans hz
  have hGp_int : (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) ≤ ENNReal.ofReal (M * I_jb) := by
    have heq : ∫⁻ w in B0579.cell d, ‖Gp w‖ₑ = ∫⁻ w in B0579.cell d, ‖G w‖ₑ := by
      refine setLIntegral_congr_fun hmeas_cell (fun w hw => ?_)
      dsimp [Gp]
      rw [hp_id w hw]
    rw [heq]
    exact lintegral_cell_le_of_jb_sq hM hG_bd
  -- Periodic translation `z = y - w` on `B0579.cell d`
  have hH_per : UnforcedLeray.Cyl.IsPeriodic d
      (fun z : ℝ × ℝ => ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
    intro z
    dsimp only [Gp, p]
    have hadd1 : (y - z).1 = (y - (z.1 + d, z.2)).1 + d := by dsimp; ring
    have hmod : toIcoMod hd0 (-(d / 2)) (y - (z.1 + d, z.2)).1 =
        toIcoMod hd0 (-(d / 2)) (y - z).1 := by
      rw [hadd1, toIcoMod_add_right]
    have hsub2 : (y - (z.1 + d, z.2)).2 = (y - z).2 := rfl
    rw [hmod, hsub2, hK_per z l]
  have hconv_eq :
      (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ₑ) =
      (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
    have hcongr : (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ₑ) =
        (∫⁻ w in B0579.cell d, ‖Gp (y - (y - w))‖ₑ * ‖kerD d (y - w) l‖ₑ) := by
      refine setLIntegral_congr_fun hmeas_cell (fun w hw => ?_)
      have hwy : w - y = -(y - w) := by abel
      have hker : ‖((kerD d (w - y) l : ℝ) : ℂ)‖ₑ = ‖kerD d (y - w) l‖ₑ := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, hwy, hK_odd (y - w) l, abs_neg,
          ← Real.enorm_eq_ofReal_abs]
      rw [enorm_mul, sub_sub_cancel, hker]
      dsimp [Gp]
      rw [hp_id w hw]
    rw [hcongr, hcell_eq]
    exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hH_per y
  -- Near part bound
  have hnear_le :
      (∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) ≤ ENNReal.ofReal (C_NF * M) := by
    calc ∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ
        ≤ ∫⁻ z in near, ENNReal.ofReal M * ‖kerD d z l‖ₑ := by
          refine setLIntegral_mono' hmeas_near (fun z _ => ?_)
          have hle : ‖Gp (y - z)‖ₑ ≤ ENNReal.ofReal M := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hGp_sup (y - z))
          gcongr
      _ = ENNReal.ofReal M * ∫⁻ z in near, ‖kerD d z l‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ∫⁻ z in near, ∑ j', ‖kerD d z j'‖ₑ := by
          gcongr with z
          exact Finset.single_le_sum (f := fun j' => ‖kerD d z j'‖ₑ)
            (fun _ _ => bot_le) (Finset.mem_univ l)
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal C_NF := by gcongr
      _ = ENNReal.ofReal (C_NF * M) := by rw [← ENNReal.ofReal_mul hM, mul_comm]
  -- Far part bound
  have hfar_le :
      (∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) ≤ ENNReal.ofReal (C_NF * (M * I_jb)) := by
    have hGp_per : UnforcedLeray.Cyl.IsPeriodic d (fun w : ℝ × ℝ => ‖Gp w‖ₑ) := by
      intro w
      dsimp only [Gp, p]
      rw [toIcoMod_add_right]
    have hshift : (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ) =
        (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) := by
      rw [hcell_eq]
      exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hGp_per y
    calc ∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ
        ≤ ∫⁻ z in far, ‖Gp (y - z)‖ₑ * ENNReal.ofReal C_NF := by
          refine setLIntegral_mono' hmeas_far (fun z hz => ?_)
          have hle : ‖kerD d z l‖ₑ ≤ ENNReal.ofReal C_NF := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hK_far z hz.1 hz.2 l)
          gcongr
      _ ≤ ∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ENNReal.ofReal C_NF :=
          lintegral_mono_set sdiff_subset
      _ = (∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ) * ENNReal.ofReal C_NF :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ w in B0579.cell d, ‖Gp w‖ₑ) * ENNReal.ofReal C_NF := by rw [hshift]
      _ ≤ ENNReal.ofReal (M * I_jb) * ENNReal.ofReal C_NF := by gcongr
      _ = ENNReal.ofReal (C_NF * (M * I_jb)) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  -- Total lintegral bound
  have htot_le :
      (∫⁻ w in B0579.cell d, ‖G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ₑ) ≤
        ENNReal.ofReal (C_K * M) := by
    calc ∫⁻ w in B0579.cell d, ‖G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ₑ
        = ∫⁻ z in B0579.cell d, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ := hconv_eq
      _ = (∫⁻ z in near, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) +
            (∫⁻ z in far, ‖Gp (y - z)‖ₑ * ‖kerD d z l‖ₑ) := by
          rw [← lintegral_inter_add_sdiff _ (B0579.cell d) hmeas_ball]
      _ ≤ ENNReal.ofReal (C_NF * M) + ENNReal.ofReal (C_NF * (M * I_jb)) :=
          add_le_add hnear_le hfar_le
      _ = ENNReal.ofReal (C_K * M) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [C_K]
          ring
  have hker_sm : AEStronglyMeasurable (fun w : ℝ × ℝ => ((kerD d (w - y) l : ℝ) : ℂ))
      (volume.restrict (B0579.cell d)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((hK_meas l).comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  have hint : IntegrableOn (fun w => G w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) :=
    ⟨hGm.mul hker_sm, lt_of_le_of_lt htot_le ENNReal.ofReal_lt_top⟩
  have hnorm_le : ‖∫ w in B0579.cell d, G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ ≤ C_K * M := by
    have h1 : ‖∫ w in B0579.cell d, G w * ((kerD d (w - y) l : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal (C_K * M) :=
      (enorm_integral_le_lintegral_enorm _).trans htot_le
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  exact ⟨hint, hnorm_le⟩

/-- Linearity of `kerAdj d` over a two-term linear combination `c0 * F0 + c1 * F1` whenever the
component integrands of `F0` and `F1` are integrable on `B0579.cell d`. -/
theorem kerAdj_linear_comb_two (d : ℝ) (c0 c1 : ℂ) (F0 F1 : Fin 2 → ℝ × ℝ → ℂ) (y : ℝ × ℝ)
    (h0 : ∀ l : Fin 2, IntegrableOn (fun w => F0 l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d))
    (h1 : ∀ l : Fin 2, IntegrableOn (fun w => F1 l w * ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d)) :
    kerAdj d (fun l w => c0 * F0 l w + c1 * F1 l w) y =
      c0 * kerAdj d F0 y + c1 * kerAdj d F1 y := by
  unfold kerAdj
  simp only [Fin.sum_univ_two]
  have h00 : IntegrableOn (fun w => c0 * (F0 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ))) (B0579.cell d) :=
    (h0 0).const_mul c0
  have h01 : IntegrableOn (fun w => c0 * (F0 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ))) (B0579.cell d) :=
    (h0 1).const_mul c0
  have h10 : IntegrableOn (fun w => c1 * (F1 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ))) (B0579.cell d) :=
    (h1 0).const_mul c1
  have h11 : IntegrableOn (fun w => c1 * (F1 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ))) (B0579.cell d) :=
    (h1 1).const_mul c1
  have hlhs : (fun w => (c0 * F0 0 w + c1 * F1 0 w) * ((kerD d (w - y) 0 : ℝ) : ℂ) +
        (c0 * F0 1 w + c1 * F1 1 w) * ((kerD d (w - y) 1 : ℝ) : ℂ)) =
      (fun w => (c0 * (F0 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) +
          c0 * (F0 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ))) +
        (c1 * (F1 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) +
          c1 * (F1 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ)))) := by
    funext w
    ring
  rw [hlhs,
    integral_add (f := fun w => c0 * (F0 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) +
      c0 * (F0 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ)))
      (g := fun w => c1 * (F1 0 w * ((kerD d (w - y) 0 : ℝ) : ℂ)) +
        c1 * (F1 1 w * ((kerD d (w - y) 1 : ℝ) : ℂ))) (h00.add h01) (h10.add h11),
    integral_add h00 h01, integral_add h10 h11,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add (h0 0) (h0 1), integral_add (h1 0) (h1 1)]
  ring

/-! ## 3. Unconditional `kerAdj` linearity on `perLam` -/

/-- Pointwise identity `B0579.pd l (movingTrainE tr r) w = movingTrainGradE tr r w l` for
`0 < ν` and `0 ≤ r`. -/
theorem pd_movingTrainE_eq_movingTrainGradE {ν c : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (l : Fin 2) (w : ℝ × ℝ) :
    B0579.pd l (movingTrainE tr r) w = movingTrainGradE tr r w l := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have ha2_ne : (clockA ν r) ^ 2 ≠ 0 := pow_ne_zero 2 ha0.ne'
  have hpd := E0.rescaleRHS_pd (UnforcedLeray.B0238.Ec tr r) (Real.sqrt (clockA ν r))
    ((clockA ν r) ^ 2) hsa ha2_ne l w
  have hpow : (clockA ν r) ^ 2 * Real.sqrt (clockA ν r) = (clockA ν r) ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (clockA ν r) 2, ← Real.rpow_add ha0]
    norm_num
  unfold movingTrainGradE movingTrainE
  rw [hpd, ← mul_assoc, hpow]

/-- Unconditional linearity of `kerAdj d` on `perLam κ d i = ∑ k, (perGram κ d)⁻¹ i k * perLam0 κ d k`
for `d = cellLen (ν ^ (-2 : ℝ)) (clockA ν r) ≥ D_ker`. -/
theorem kerAdj_perLam_eq (κ : PlanarFrameKernels) :
    ∃ D_ker : ℝ, 1 ≤ D_ker ∧
      ∀ ν : ℝ, ν ∈ Ioc 0 1 →
      ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
      ∀ r : ℝ, 0 ≤ r →
        let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
        D_ker ≤ d →
        ∀ (i : Fin 2) (y : ℝ × ℝ),
          kerAdj d (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y =
            ∑ k : Fin 2, (perGram κ d)⁻¹ i k *
              kerAdj d (fun l w => perLam0 κ d k w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y := by
  obtain ⟨ν_bdd, hν_bdd, hBddAll⟩ := ladTrainBddAll_unconditional 2
  obtain ⟨B_0, hB0_pos, hB0⟩ := Lam0B.perLam0_sup κ
  obtain ⟨C_K, _, hKerInt⟩ := kerAdj_term_integrableOn_and_bound
  set D_ker : ℝ := max 1 ((ν_bdd⁻¹) ^ 2)
  have hD_ker1 : 1 ≤ D_ker := le_max_left _ _
  refine ⟨D_ker, hD_ker1, fun ν hν tr hBUC r hr => ?_⟩
  intro d hd i y
  have hν_pos : 0 < ν := hν.1
  have hd1 : 1 ≤ d := le_trans hD_ker1 hd
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν_pos.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa1 : 1 ≤ Real.sqrt (clockA ν r) := Real.one_le_sqrt.2 ha1
  have hsa0 : 0 < Real.sqrt (clockA ν r) := lt_of_lt_of_le zero_lt_one hsa1
  -- Deduce `ν ≤ ν_bdd` from `(ν_bdd⁻¹) ^ 2 ≤ D_ker ≤ d ≤ (ν⁻¹) ^ 2`
  have hd_le_c : d ≤ (ν⁻¹) ^ 2 := by
    have hc_eq : ν ^ (-2 : ℝ) = (ν⁻¹) ^ 2 := by
      rw [Real.rpow_neg hν_pos.le, Real.rpow_two, inv_pow]
    unfold d cellLen
    rw [hc_eq]
    exact div_le_self (by positivity) hsa1
  have hν_le_bdd : ν ≤ ν_bdd := by
    have hsq : (ν_bdd⁻¹) ^ 2 ≤ (ν⁻¹) ^ 2 :=
      le_trans (le_trans (le_max_right _ _) hd) hd_le_c
    have hinv_le : ν_bdd⁻¹ ≤ ν⁻¹ := by
      nlinarith [sq_nonneg (ν⁻¹ - ν_bdd⁻¹), inv_pos.2 hν_bdd, inv_pos.2 hν_pos]
    exact (inv_le_inv₀ hν_bdd hν_pos).mp hinv_le
  obtain ⟨C_tr, hBdd⟩ := hBddAll ν ⟨hν_pos, hν_le_bdd⟩ tr hBUC r hr
  set M : ℝ := B_0 * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0)
  have hM_pos : 0 ≤ M := by positivity
  -- Each `F_k l w := perLam0 κ d k w * (B0579.pd l (movingTrainE tr r) w : ℂ)` satisfies the `jb ^ 2` bound
  have hFk_int : ∀ k l : Fin 2,
      IntegrableOn (fun w =>
        (perLam0 κ d k w * (B0579.pd l (movingTrainE tr r) w : ℂ)) *
          ((kerD d (w - y) l : ℝ) : ℂ)) (B0579.cell d) := by
    intro k l
    have hcont : Continuous (fun w => perLam0 κ d k w * (B0579.pd l (movingTrainE tr r) w : ℂ)) := by
      have h1 : Continuous (perLam0 κ d k) := Lam0B.perLam0_continuous κ hd0 k
      have h2 : Continuous (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) := by
        have heq : (fun w => (B0579.pd l (movingTrainE tr r) w : ℂ)) =
            (fun w => (movingTrainGradE tr r w l : ℂ)) :=
          funext fun w => congrArg Complex.ofReal
            (pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w)
        rw [heq]
        exact Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr l)
      exact h1.mul h2
    refine (hKerInt hd1 hM_pos hcont.aestronglyMeasurable (fun w hw => ?_) y l).1
    set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * w.1, Real.sqrt (clockA ν r) * w.2)
    have hz_cell : z ∈ B0579.cell (ν ^ (-2 : ℝ)) := by
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, z]
      have hw1 := hw.1.1
      have hw2 := hw.1.2
      have hmul : Real.sqrt (clockA ν r) * (d / 2) = ν ^ (-2 : ℝ) / 2 := by
        dsimp [d, cellLen]
        field_simp [hsa0.ne']
      refine ⟨?_, ?_⟩
      · have hle := mul_le_mul_of_nonneg_left hw1 hsa0.le
        linarith [hmul]
      · have hlt := mul_lt_mul_of_pos_left hw2 hsa0
        linarith [hmul]
    have hjb_le : B0579.jb w ≤ B0579.jb z := by
      unfold B0579.jb
      dsimp [z]
      have h1 : w.1 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.1) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha0.le]
        exact le_mul_of_one_le_left (sq_nonneg w.1) ha1
      have h2 : w.2 ^ 2 ≤ (Real.sqrt (clockA ν r) * w.2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha0.le]
        exact le_mul_of_one_le_left (sq_nonneg w.2) ha1
      linarith
    have hjb_sq : B0579.jb w ^ 2 ≤ B0579.jb z ^ ((2 + 2 : ℝ) / 2) := by
      have hexp : (2 + 2 : ℝ) / 2 = (2 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      exact pow_le_pow_left₀ (B0579.jb_pos w).le hjb_le 2
    have hEc_bd : B0579.jb z ^ ((2 + 2 : ℝ) / 2) *
        |B0579.pd l (UnforcedLeray.B0238.Ec tr r) z| ≤ max C_tr 0 :=
      ((hBdd r ⟨hr, le_rfl⟩ z hz_cell).2 l).trans (le_max_left _ _)
    have hgrad_bd : B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w| ≤
        (clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0 := by
      rw [pd_movingTrainE_eq_movingTrainGradE tr hν_pos hr l w]
      unfold movingTrainGradE
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _), ← mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha0.le _)
      exact (mul_le_mul_of_nonneg_right hjb_sq (abs_nonneg _)).trans hEc_bd
    have hlam_bd : ‖perLam0 κ d k w‖ ≤ B_0 := hB0 d hd1 k w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc B0579.jb w ^ 2 * (‖perLam0 κ d k w‖ * |B0579.pd l (movingTrainE tr r) w|)
        = ‖perLam0 κ d k w‖ * (B0579.jb w ^ 2 * |B0579.pd l (movingTrainE tr r) w|) := by ring
      _ ≤ B_0 * ((clockA ν r) ^ ((5 : ℝ) / 2) * max C_tr 0) :=
          mul_le_mul hlam_bd hgrad_bd (by positivity) hB0_pos
  -- Apply `kerAdj_linear_comb_two`
  have hfun : (fun l w => perLam κ d i w * (B0579.pd l (movingTrainE tr r) w : ℂ)) =
      (fun l w =>
        (perGram κ d)⁻¹ i 0 * (perLam0 κ d 0 w * (B0579.pd l (movingTrainE tr r) w : ℂ)) +
        (perGram κ d)⁻¹ i 1 * (perLam0 κ d 1 w * (B0579.pd l (movingTrainE tr r) w : ℂ))) := by
    funext l w
    unfold perLam
    simp only [Fin.sum_univ_two]
    ring
  rw [hfun, kerAdj_linear_comb_two d ((perGram κ d)⁻¹ i 0) ((perGram κ d)⁻¹ i 1)
    (fun l w => perLam0 κ d 0 w * (B0579.pd l (movingTrainE tr r) w : ℂ))
    (fun l w => perLam0 κ d 1 w * (B0579.pd l (movingTrainE tr r) w : ℂ)) y
    (hFk_int 0) (hFk_int 1), Fin.sum_univ_two]

/-! ## 4. Linearity of `E0.transCx` and conditional assembly of `MovLam0EulerPullback` -/

/-- Linearity of `E0.transCx V` on `perLam κ d i` whenever `perLam0 κ d 0` and `perLam0 κ d 1`
are differentiable at `y`. -/
theorem transCx_perLam_eq_of_diff (κ : PlanarFrameKernels) (d : ℝ)
    (V : ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) (y : ℝ × ℝ)
    (hd0 : DifferentiableAt ℝ (perLam0 κ d 0) y)
    (hd1 : DifferentiableAt ℝ (perLam0 κ d 1) y) :
    E0.transCx V (perLam κ d i) y =
      ∑ k : Fin 2, (perGram κ d)⁻¹ i k * E0.transCx V (perLam0 κ d k) y := by
  unfold E0.transCx
  rw [pdCx_perLam_eq κ d i 0 y hd0 hd1, pdCx_perLam_eq κ d i 1 y hd0 hd1]
  simp only [Fin.sum_univ_two]
  ring

/-- Differentiability of the unnormalised periodized rows `perLam0 κ d k` on `ℝ × ℝ` for `d ≥ 1`
(the differentiability conjunct of `SeedLamGradPerSum κ`, `PartIII-a:T21/c5/1/1/1`). -/
def PerLam0Differentiable (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ {d : ℝ}, 1 ≤ d → ∀ (k : Fin 2) (y : ℝ × ℝ), DifferentiableAt ℝ (perLam0 κ d k) y

/-- `SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) implies `PerLam0Differentiable κ`. -/
theorem perLam0Differentiable_of_seedLamGradPerSum (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) : PerLam0Differentiable κ := by
  intro hκ d hd k y
  obtain ⟨_, _, _, _, hder0⟩ := hGrad hκ
  exact (hder0 hd k 0 y).1

/-- Conditional proof of `MovLam0EulerPullback κ` (`PartIII-a:T21/c5/2/2/1`) from
`PerLam0Differentiable κ`, combining `movPullback_physLamDualEuler_eq`,
`movPullback_physLam0DualEuler_eq`, `transCx_perLam_eq_of_diff`, and `kerAdj_perLam_eq`. -/
theorem movLam0EulerPullback_of_diff (κ : PlanarFrameKernels)
    (hDiff : PerLam0Differentiable κ) :
    MovLam0EulerPullback κ := by
  intro hκ
  obtain ⟨D_ker, hD_ker1, hKerLin⟩ := kerAdj_perLam_eq κ
  refine ⟨D_ker, hD_ker1, fun ν hν tr hBUC r hr _hθ => ?_⟩
  intro d hd i y
  have hν_pos : 0 < ν := hν.1
  have hd1 : 1 ≤ d := le_trans hD_ker1 hd
  rw [movPullback_physLamDualEuler_eq κ tr hν_pos hr i y]
  have h0 := movPullback_physLam0DualEuler_eq κ tr hν_pos hr 0 y
  have h1 := movPullback_physLam0DualEuler_eq κ tr hν_pos hr 1 y
  simp only [Fin.sum_univ_two, h0, h1]
  unfold movEulerAdj
  rw [transCx_perLam_eq_of_diff κ d (movingTrainV tr r) i y
      (hDiff hκ hd1 0 y) (hDiff hκ hd1 1 y),
    hKerLin ν hν tr hBUC r hr hd i y]
  simp only [Fin.sum_univ_two]
  ring

/-- Conditional proof of `MovLam0EulerPullback κ` (`PartIII-a:T21/c5/2/2/1`) from sibling leaf
`SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`). -/
theorem movLam0EulerPullback_of (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) :
    MovLam0EulerPullback κ :=
  movLam0EulerPullback_of_diff κ (perLam0Differentiable_of_seedLamGradPerSum κ hGrad)

end DirectEulerSub

/-- **`MovLam0EulerPullback κ` (`PartIII-a:T21/c5/2/2/1`, SP 2905-2918), unconditional.**
Combines the moving pullback `DirectEulerSub.movLam0EulerPullback_of` with the unconditional
spatial gradient periodization `seedLamGradPerSum` (`PartIII-a:T21/c5/1/1/1`). -/
theorem movLam0EulerPullback (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLam0EulerPullback κ :=
  DirectEulerSub.movLam0EulerPullback_of κ (seedLamGradPerSum κ)

end UnforcedLeray.Short.IIIa
