import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.CellBridge

/-!
# `PartI:T17`: `L²` decay of the train velocity before and after overlap (`TrainL2Decay`)

Source of record: `the November 2 reference manuscript`, lines 314-317, 326-336,
and 425-428.

* **Pre-overlap (`0 ≤ s ≤ s_c`, `width ν s ≤ c²`):** decompose
  `tr.v s = (tr.v s - Vc ν c s) + Vc ν c s` in `cellL2 c`, bound the error by
  `trainComparison_proof` (`j = 0`) and the periodized heat vortex by `Train.Vc_bounds 0 0`
  transported from `B0151.cellMeasure c` to `Cyl.cellμ c` via `eLpNorm_cellMeasure_eq`, and absorb
  `ν⁻¹ a⁻² e^{-b c²/a} ≤ b⁻¹ a⁻¹` for `1 ≤ ν c²`.
* **Post-overlap (`s ≥ s_c`, `T = ν (s - s_c) / c² ≥ 0`):** rescale `tr.v s` to
  `U T = overlapField ν c tr.v T = scaleField c (tr.v s)` via `cellL2_jet_scaleField` (`j = 0`),
  bound `cellL2 1 (U T) ≤ eLpNorm b 2 volume + cellL2 1 (hfluct 1 (U T))` using `hOv : TrainOverlap`
  (`j = 0`), and use `s / s_c ≤ 2 (1 + T)` for `2 ≤ c²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1.Norm and `cellL2` bridges at order `j = 0` -/

theorem cellL2_jet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : Plane → E) : cellL2 c (jet 0 f) = cellL2 c f := by
  unfold cellL2 jet
  rw [← eLpNorm_norm (fun z => iteratedFDeriv ℝ 0 f z), ← eLpNorm_norm f]
  congr 1
  funext z
  exact norm_iteratedFDeriv_zero

private theorem norm_vec_le_add_coords (v : Vec) : ‖v‖ ≤ |v 0| + |v 1| := by
  have h0 : 0 ≤ |v 0| := abs_nonneg _
  have h1 : 0 ≤ |v 1| := abs_nonneg _
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_left (add_nonneg h0 h1)]
  simp only [Real.norm_eq_abs]
  nlinarith [mul_nonneg h0 h1]

private theorem norm_vec_eq_abs_fst_of_snd_zero {v : Vec} (hv1 : v 1 = 0) :
    ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hv1]
  simp [Real.sqrt_sq_eq_abs]

/-- Pre-overlap `cellL2 c` bound for `Vc ν c s`: `cellL2 c (Vc ν c s) ≤ ofReal (2 * CV * a⁻¹)`
for `1 ≤ a ≤ c²`, derived from `Train.Vc_bounds 0 0` and `eLpNorm_cellMeasure_eq`. -/
theorem preOverlap_Vc_cellL2_bound :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s → width ν s ≤ c ^ 2 →
        cellL2 c (Vc ν c s) ≤ ENNReal.ofReal (CV * (width ν s)⁻¹) := by
  obtain ⟨C, _, hC, _, hVc⟩ := Train.Vc_bounds 0 0
  refine ⟨2 * C + 1, by positivity, fun ν c s hc ha1 hac => ?_⟩
  have ha0 : 0 < width ν s := zero_lt_one.trans_le ha1
  have hV_sm : ContDiff ℝ ∞ (Vc ν c s) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha0
  have hcoord : ∀ k : Fin 2,
      eLpNorm (fun z : Plane => Vc ν c s z k) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal (C * (width ν s)⁻¹) := by
    intro k
    have hk_cont : Continuous (fun z : Plane => Vc ν c s z k) :=
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).continuous).comp hV_sm.continuous
    have hk_per : Cyl.IsPeriodic c (fun z : Plane => Vc ν c s z k) := by
      intro z
      exact congrArg (fun v : Vec => v k) (Train.Vc_periodic ν c s z)
    rw [← eLpNorm_cellMeasure_eq hc hk_cont.measurable hk_per 2]
    have h2 := ((hVc ν c s hc ha1 hac).2.1 k).2
    simpa using h2
  have hm0 : AEStronglyMeasurable (fun z : Plane => |Vc ν c s z 0|) (Cyl.cellμ c) :=
    (((EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ).continuous.comp hV_sm.continuous).abs).aestronglyMeasurable
  have hm1 : AEStronglyMeasurable (fun z : Plane => |Vc ν c s z 1|) (Cyl.cellμ c) :=
    (((EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ).continuous.comp hV_sm.continuous).abs).aestronglyMeasurable
  have hmono : cellL2 c (Vc ν c s) ≤
      eLpNorm (fun z : Plane => |Vc ν c s z 0| + |Vc ν c s z 1|) 2 (Cyl.cellμ c) := by
    apply eLpNorm_mono
    intro z
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_vec_le_add_coords (Vc ν c s z)
  have hadd : eLpNorm (fun z : Plane => |Vc ν c s z 0| + |Vc ν c s z 1|) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z : Plane => |Vc ν c s z 0|) 2 (Cyl.cellμ c) +
        eLpNorm (fun z : Plane => |Vc ν c s z 1|) 2 (Cyl.cellμ c) :=
    eLpNorm_add_le hm0 hm1 one_le_two
  have habs : ∀ k : Fin 2,
      eLpNorm (fun z : Plane => |Vc ν c s z k|) 2 (Cyl.cellμ c) =
        eLpNorm (fun z : Plane => Vc ν c s z k) 2 (Cyl.cellμ c) := by
    intro k
    have heq : (fun z : Plane => |Vc ν c s z k|) = fun z : Plane => ‖Vc ν c s z k‖ :=
      funext fun z => (Real.norm_eq_abs _).symm
    rw [heq, eLpNorm_norm]
  calc cellL2 c (Vc ν c s)
      ≤ eLpNorm (fun z : Plane => Vc ν c s z 0) 2 (Cyl.cellμ c) +
          eLpNorm (fun z : Plane => Vc ν c s z 1) 2 (Cyl.cellμ c) := by
        rw [← habs 0, ← habs 1]
        exact hmono.trans hadd
    _ ≤ ENNReal.ofReal (C * (width ν s)⁻¹) + ENNReal.ofReal (C * (width ν s)⁻¹) :=
        add_le_add (hcoord 0) (hcoord 1)
    _ = ENNReal.ofReal (2 * C * (width ν s)⁻¹) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((2 * C + 1) * (width ν s)⁻¹) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [inv_nonneg.2 ha0.le]

/-! ### 2. Elementary exponential and power inequalities -/

/-- For `x ≥ 0`, `x * exp(-x) ≤ 1`. -/
private theorem mul_exp_neg_le_one {x : ℝ} (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 := by
  have h1 : x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  calc x * Real.exp (-x)
      ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- For `1 ≤ ν * c²`, `0 < a`, and `0 < b`,
`ν⁻¹ * a ^ (-(2 + 0 / 2)) * exp(-(b * c² / a)) ≤ b⁻¹ * a⁻¹`. -/
private theorem preOverlap_err_factor_le {ν c a b : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hνc2 : 1 ≤ ν * c ^ 2) :
    ν⁻¹ * a ^ (-(2 + (0 : ℝ) / 2)) * Real.exp (-(b * c ^ 2 / a)) ≤ b⁻¹ * a⁻¹ := by
  have hν_inv_le : ν⁻¹ ≤ c ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hν]
    linarith
  have hrpow : a ^ (-(2 + (0 : ℝ) / 2)) = a⁻¹ * a⁻¹ := by
    have h2 : -(2 + (0 : ℝ) / 2) = (-2 : ℝ) := by norm_num
    rw [h2, Real.rpow_neg ha.le, Real.rpow_two, sq, mul_inv]
  have hx_nn : 0 ≤ b * c ^ 2 / a := by positivity
  have h_exp := mul_exp_neg_le_one hx_nn
  have h_ca : c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a)) ≤ b⁻¹ := by
    calc c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))
        = b⁻¹ * ((b * c ^ 2 / a) * Real.exp (-(b * c ^ 2 / a))) := by
          have hb_ne : b ≠ 0 := hb.ne'
          field_simp
      _ ≤ b⁻¹ * 1 := mul_le_mul_of_nonneg_left h_exp (inv_nonneg.2 hb.le)
      _ = b⁻¹ := mul_one _
  calc ν⁻¹ * a ^ (-(2 + (0 : ℝ) / 2)) * Real.exp (-(b * c ^ 2 / a))
      = ν⁻¹ * (a⁻¹ * a⁻¹) * Real.exp (-(b * c ^ 2 / a)) := by rw [hrpow]
    _ ≤ c ^ 2 * (a⁻¹ * a⁻¹) * Real.exp (-(b * c ^ 2 / a)) := by
        gcongr
    _ = (c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))) * a⁻¹ := by ring
    _ ≤ b⁻¹ * a⁻¹ := mul_le_mul_of_nonneg_right h_ca (inv_nonneg.2 ha.le)

/-- For `T ≥ 0` and `lam > 0`, `exp(-(lam * T)) ≤ (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))`. -/
private theorem exp_neg_le_rpow_neg_three_fourths {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    Real.exp (-(lam * T)) ≤ (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ)) := by
  have h1T_pos : 0 < 1 + T := by linarith
  have h1T_ge1 : 1 ≤ 1 + T := by linarith
  have hexp_le1 : Real.exp (-(lam * T)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have hT_exp : T * Real.exp (-(lam * T)) ≤ lam⁻¹ := by
    have hx := mul_exp_neg_le_one (mul_nonneg hlam.le hT)
    calc T * Real.exp (-(lam * T))
        = lam⁻¹ * ((lam * T) * Real.exp (-(lam * T))) := by
          have hlam_ne : lam ≠ 0 := hlam.ne'
          field_simp
      _ ≤ lam⁻¹ * 1 := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hlam.le)
      _ = lam⁻¹ := mul_one _
  have hprod : (1 + T) * Real.exp (-(lam * T)) ≤ 1 + lam⁻¹ := by
    calc (1 + T) * Real.exp (-(lam * T))
        = Real.exp (-(lam * T)) + T * Real.exp (-(lam * T)) := by ring
      _ ≤ 1 + lam⁻¹ := add_le_add hexp_le1 hT_exp
  have hinv_le : (1 + T)⁻¹ ≤ (1 + T) ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h1T_ge1 (by norm_num)
  calc Real.exp (-(lam * T))
      = ((1 + T) * Real.exp (-(lam * T))) * (1 + T)⁻¹ := by
        rw [mul_comm (1 + T), mul_assoc, mul_inv_cancel₀ h1T_pos.ne', mul_one]
    _ ≤ (1 + lam⁻¹) * (1 + T)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod (inv_nonneg.2 h1T_pos.le)
    _ ≤ (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv_le (by positivity)

/-! ### 3. Unit-cell `L²` norm of a vertical profile -/

/-- For a continuous profile `b : ℝ → ℝ` and a vector field `M : Plane → Vec` with
`M y 0 = b y.2` and `M y 1 = 0`, `cellL2 1 M = eLpNorm b 2 volume`. -/
private theorem cellL2_one_eq_eLpNorm_of_vert {M : Plane → Vec} {b : ℝ → ℝ}
    (hb : Continuous b) (hM0 : ∀ y : Plane, M y 0 = b y.2) (hM1 : ∀ y : Plane, M y 1 = 0) :
    cellL2 1 M = eLpNorm b 2 volume := by
  unfold cellL2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div]
  congr 1
  have hnorm : ∀ y : Plane, ‖M y‖ₑ = ‖b y.2‖ₑ := by
    intro y
    rw [← ofReal_norm, ← ofReal_norm, norm_vec_eq_abs_fst_of_snd_zero (hM1 y),
      hM0 y, Real.norm_eq_abs]
  simp_rw [hnorm]
  have hm : AEMeasurable (fun y : Plane => ‖b y.2‖ₑ ^ (2 : ℝ)) (Cyl.cellμ 1) :=
    ((hb.measurable.enorm.pow_const (2 : ℝ)).comp measurable_snd).aemeasurable
  rw [Cyl.cellμ, Cyl.lintegral_cell_eq hm]
  dsimp only
  rw [setLIntegral_const, Real.volume_Ico]
  have h1 : (1 / 2 : ℝ) - -1 / 2 = 1 := by ring
  rw [h1, ENNReal.ofReal_one, mul_one]

/-! ### 4. Main theorem: `trainL2Decay_proof` (`PartI:T17`) -/

/-- **`PartI:T17` (`trainL2Decay_proof`)** (source lines 314-317, 326-336, 425-428):
proves `TrainL2Decay` from `trainComparison_proof` (`PartI:T10`) and `hOv : TrainOverlap`. -/
theorem trainL2Decay_proof (hOv : TrainOverlap) : TrainL2Decay := by
  intro ρ hρ
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ 0
  obtain ⟨CV, hCV, hVc⟩ := preOverlap_Vc_cellL2_bound
  obtain ⟨C_ov, lam, ν_ov, hC_ov, hlam, hν_ov, hov⟩ := hOv ρ hρ 0
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  let C_pre : ℝ := Ce * be⁻¹ + CV
  let C_post : ℝ := 2 * C_ov * (2 + lam⁻¹)
  have hC_pre : 0 < C_pre := by positivity
  have hC_post : 0 < C_post := by positivity
  refine ⟨max C_pre C_post, min νe (min ν_ov νp), lt_max_of_lt_left hC_pre,
    lt_min hνe (lt_min hν_ov hνp), ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_ov_le : ν ≤ ν_ov := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_p.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_p
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc2_ge2 : 2 ≤ c ^ 2 := by
    calc (2 : ℝ) ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hνc2_ge1 : 1 ≤ ν * c ^ 2 := by linarith
  let s_c := B0146.overlapAge ν c
  have hs_c_pos : 0 < s_c := by
    unfold s_c B0146.overlapAge
    exact div_pos (by linarith) hν
  refine ⟨?_, ?_⟩
  · -- Part (i): Pre-overlap (`s ≤ s_c`)
    intro hs_le
    have hw_ge1 : 1 ≤ width ν s := by
      unfold width
      nlinarith
    have hw_le_c2 : width ν s ≤ c ^ 2 := by
      have hw_sc : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
      have hmono : width ν s ≤ width ν s_c := by
        unfold width
        nlinarith
      exact hmono.trans_eq hw_sc
    have ha0 : 0 < width ν s := zero_lt_one.trans_le hw_ge1
    obtain ⟨hL2_err, _⟩ := hcomp ν hν hν_e tr htr s hs hw_le_c2
    rw [cellL2_jet_zero] at hL2_err
    simp only [Nat.cast_zero] at hL2_err
    have hL2_Vc := hVc ν c s hc0 hw_ge1 hw_le_c2
    have hv_sm : ContDiff ℝ ∞ (tr.v s) := by
      have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
        (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
      exact contDiffOn_univ.1 h
    have hV_sm : ContDiff ℝ ∞ (Vc ν c s) :=
      UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 ha0
    let err : Plane → Vec := fun z => tr.v s z - Vc ν c s z
    have herr_meas : AEStronglyMeasurable err (Cyl.cellμ c) :=
      (hv_sm.continuous.sub hV_sm.continuous).aestronglyMeasurable
    have hV_meas : AEStronglyMeasurable (Vc ν c s) (Cyl.cellμ c) :=
      hV_sm.continuous.aestronglyMeasurable
    have hv_decomp : tr.v s = fun z => err z + Vc ν c s z := by
      funext z
      simp [err, sub_add_cancel]
    have htri : cellL2 c (tr.v s) ≤ cellL2 c err + cellL2 c (Vc ν c s) := by
      unfold cellL2
      rw [hv_decomp]
      exact eLpNorm_add_le herr_meas hV_meas one_le_two
    have herr_le : cellL2 c err ≤ ENNReal.ofReal (Ce * be⁻¹ * (width ν s)⁻¹) := by
      refine hL2_err.trans (ENNReal.ofReal_le_ofReal ?_)
      have hfac := preOverlap_err_factor_le hν hc0 ha0 hbe hνc2_ge1
      calc Ce * ν⁻¹ * width ν s ^ (-(2 + (0 : ℝ) / 2)) * Real.exp (-(be * c ^ 2 / width ν s))
          = Ce * (ν⁻¹ * width ν s ^ (-(2 + (0 : ℝ) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s))) := by ring
        _ ≤ Ce * (be⁻¹ * (width ν s)⁻¹) := mul_le_mul_of_nonneg_left hfac hCe.le
        _ = Ce * be⁻¹ * (width ν s)⁻¹ := by ring
    calc cellL2 c (tr.v s)
        ≤ ENNReal.ofReal (Ce * be⁻¹ * (width ν s)⁻¹) +
            ENNReal.ofReal (CV * (width ν s)⁻¹) :=
          htri.trans (add_le_add herr_le hL2_Vc)
      _ = ENNReal.ofReal (C_pre * (width ν s)⁻¹) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [C_pre]; ring
      _ ≤ ENNReal.ofReal (max C_pre C_post * (width ν s)⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 ha0.le)
  · -- Part (ii): Post-overlap (`s_c ≤ s`)
    intro hs_ge
    let T : ℝ := ν * (s - s_c) / c ^ 2
    have hT_nn : 0 ≤ T := by
      dsimp [T]
      have : 0 ≤ s - s_c := sub_nonneg.2 hs_ge
      positivity
    have hs_eq : s_c + c ^ 2 * T / ν = s := by
      dsimp [T]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    let U := overlapField ν c tr.v T
    have hU_scale : U = scaleField c (tr.v s) := by
      funext y
      dsimp [U, overlapField, scaleField]
      rw [show B0146.overlapAge ν c + c ^ 2 * T / ν = s from hs_eq]
    have hv_sm : ContDiff ℝ ∞ (tr.v s) := by
      have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
        (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
      exact contDiffOn_univ.1 h
    have hscale_L2 : cellL2 c (tr.v s) = ENNReal.ofReal (c ^ (-2 : ℝ)) * cellL2 1 U := by
      have h1 := cellL2_jet_scaleField hc0 0 hv_sm
      rw [cellL2_jet_zero, cellL2_jet_zero, pow_zero, mul_one, ← hU_scale] at h1
      rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      have hpow : c ^ (-2 : ℝ) * c ^ 2 = 1 := by
        rw [Real.rpow_neg hc0.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 hc0.ne')]
      rw [hpow, ENNReal.ofReal_one, one_mul]
    obtain ⟨hU1, hb_sm, hb_L2, _, hW_L2, _⟩ := hov ν hν hν_ov_le tr htr T hT_nn
    rw [iteratedDeriv_zero] at hb_L2
    rw [cellL2_jet_zero] at hW_L2
    let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
    let M : Plane → Vec := fun y => hmean 1 U y.2
    have hM0 : ∀ y : Plane, M y 0 = b y.2 := fun _ => rfl
    have hM1 : ∀ y : Plane, M y 1 = 0 := fun y => hU1 y.2
    have hM_L2 : cellL2 1 M = eLpNorm b 2 volume :=
      cellL2_one_eq_eLpNorm_of_vert hb_sm.continuous hM0 hM1
    have hM_cont : Continuous M := by
      have h1 : Continuous (fun y : Plane => fun i : Fin 2 => (M y) i) := by
        refine continuous_pi fun i => ?_
        fin_cases i
        · exact hb_sm.continuous.comp continuous_snd
        · simpa [hM1] using (continuous_const : Continuous fun _ : Plane => (0 : ℝ))
      exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp h1
    have hU_cont : Continuous U := by
      rw [hU_scale]
      exact (hv_sm.continuous.comp (continuous_id.const_smul c)).const_smul (c ^ 3)
    have hW_cont : Continuous (hfluct 1 U) := hU_cont.sub hM_cont
    have hU_decomp : U = fun y => M y + hfluct 1 U y := by
      funext y
      simp [M, hfluct]
    have hU_tri : cellL2 1 U ≤ eLpNorm b 2 volume + cellL2 1 (hfluct 1 U) := by
      rw [← hM_L2]
      unfold cellL2
      conv_lhs => rw [hU_decomp]
      exact eLpNorm_add_le hM_cont.aestronglyMeasurable hW_cont.aestronglyMeasurable one_le_two
    have hexp_eq : (-1 - (0 : ℝ) / 2 + 1 / 4 : ℝ) = -(3 / 4 : ℝ) := by norm_num
    simp only [Nat.cast_zero] at hb_L2
    rw [hexp_eq] at hb_L2
    have hW_rpow : cellL2 1 (hfluct 1 U) ≤
        ENNReal.ofReal (C_ov * (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) := by
      refine hW_L2.trans (ENNReal.ofReal_le_ofReal ?_)
      have h_exp := exp_neg_le_rpow_neg_three_fourths hlam hT_nn
      calc C_ov * Real.exp (-(lam * T))
          ≤ C_ov * ((1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left h_exp hC_ov.le
        _ = C_ov * (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ)) := by ring
    have h1T_pos : 0 < 1 + T := by linarith
    have hU_L2 : cellL2 1 U ≤
        ENNReal.ofReal (C_ov * (2 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) := by
      calc cellL2 1 U
          ≤ ENNReal.ofReal (C_ov * (1 + T) ^ (-(3 / 4 : ℝ))) +
              ENNReal.ofReal (C_ov * (1 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) :=
            hU_tri.trans (add_le_add hb_L2 hW_rpow)
        _ = ENNReal.ofReal (C_ov * (2 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    -- Relate `1 + T` and `s / s_c`: since `c² ≥ 2`, `s_c = (c² - 1)/ν ≥ c²/(2ν)`, so `s/s_c ≤ 2(1 + T)`.
    have hsc_ge : c ^ 2 / (2 * ν) ≤ s_c := by
      unfold s_c B0146.overlapAge
      rw [div_le_div_iff₀ (by positivity) hν]
      nlinarith
    have hs_div_le : s / s_c ≤ 2 * (1 + T) := by
      rw [div_le_iff₀ hs_c_pos]
      have h1 : c ^ 2 * T = ν * (s - s_c) := by
        dsimp [T]
        exact mul_div_cancel₀ _ (pow_ne_zero 2 hc0.ne')
      have h2 : c ^ 2 ≤ 2 * ν * s_c := by
        have := (div_le_iff₀ (by positivity : 0 < 2 * ν)).1 hsc_ge
        linarith
      have h3 : ν * (s - s_c) ≤ c ^ 2 * T := h1.symm.le
      have h4 : s - s_c ≤ 2 * T * s_c := by
        have hν_pos : 0 < ν := hν
        have hT_s : 2 * ν * s_c * T = ν * (2 * T * s_c) := by ring
        have hle : c ^ 2 * T ≤ 2 * ν * s_c * T := mul_le_mul_of_nonneg_right h2 hT_nn
        rw [h1, hT_s] at hle
        exact le_of_mul_le_mul_left hle hν_pos
      linarith
    have hs_div_pos : 0 < s / s_c := div_pos (hs_c_pos.trans_le hs_ge) hs_c_pos
    have hrpow_T : (1 + T) ^ (-(3 / 4 : ℝ)) ≤ 2 * (s / s_c) ^ (-(3 / 4 : ℝ)) := by
      have hhalf : (s / s_c) / 2 ≤ 1 + T := by linarith
      have h_rpow := Real.rpow_le_rpow_of_nonpos (half_pos hs_div_pos) hhalf
        (by norm_num : -(3 / 4 : ℝ) ≤ 0)
      have hdiv2 : (s / s_c) / 2 = (s / s_c) * 2⁻¹ := div_eq_mul_inv (s / s_c) 2
      rw [hdiv2, Real.mul_rpow hs_div_pos.le (by norm_num)] at h_rpow
      have h2_le : (2⁻¹ : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 2 := by
        have h2_eq : (2⁻¹ : ℝ) ^ (-(3 / 4 : ℝ)) = (2 : ℝ) ^ (3 / 4 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
        rw [h2_eq]
        calc (2 : ℝ) ^ (3 / 4 : ℝ)
            ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      calc (1 + T) ^ (-(3 / 4 : ℝ))
          ≤ (s / s_c) ^ (-(3 / 4 : ℝ)) * (2⁻¹ : ℝ) ^ (-(3 / 4 : ℝ)) := h_rpow
        _ ≤ (s / s_c) ^ (-(3 / 4 : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left h2_le (Real.rpow_nonneg hs_div_pos.le _)
        _ = 2 * (s / s_c) ^ (-(3 / 4 : ℝ)) := mul_comm _ _
    rw [hscale_L2]
    calc ENNReal.ofReal (c ^ (-2 : ℝ)) * cellL2 1 U
        ≤ ENNReal.ofReal (c ^ (-2 : ℝ)) *
            ENNReal.ofReal (C_ov * (2 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hU_L2 zero_le
      _ = ENNReal.ofReal (c ^ (-2 : ℝ) *
            (C_ov * (2 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc0.le _)]
      _ ≤ ENNReal.ofReal (max C_pre C_post * c ^ (-2 : ℝ) *
            (s / s_c) ^ (-(3 / 4 : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hC_le : C_post ≤ max C_pre C_post := le_max_right _ _
          have hc_nn : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
          have hC2_nn : 0 ≤ C_ov * (2 + lam⁻¹) := by positivity
          have hs_rpow_nn : 0 ≤ (s / s_c) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hs_div_pos.le _
          calc c ^ (-2 : ℝ) * (C_ov * (2 + lam⁻¹) * (1 + T) ^ (-(3 / 4 : ℝ)))
              ≤ c ^ (-2 : ℝ) * (C_ov * (2 + lam⁻¹) * (2 * (s / s_c) ^ (-(3 / 4 : ℝ)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hrpow_T hC2_nn) hc_nn
            _ = C_post * c ^ (-2 : ℝ) * (s / s_c) ^ (-(3 / 4 : ℝ)) := by
                dsimp [C_post]; ring
            _ ≤ max C_pre C_post * c ^ (-2 : ℝ) * (s / s_c) ^ (-(3 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hC_le hc_nn) hs_rpow_nn

end UnforcedLeray.Short.PartI
