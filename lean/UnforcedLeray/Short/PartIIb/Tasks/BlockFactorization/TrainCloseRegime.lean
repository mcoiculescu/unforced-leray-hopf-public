import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Units.B0169
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `PartII-b:F2/1` (`TrainCloseRegime.lean`): Early-train comparison in the `m`-weighted derivative budget

Source of record: `the November 2 reference manuscript` (SP), lines 2085–2090
(`short-bg:train-early`).

Proves `trainCloseRegime_proof : UnforcedLeray.Short.IIb.TrainCloseRegime`:
for every `m > 8`, `Sg > 0`, `dm > 0`, and `δ > 0`, there exists `ν₀ > 0` such that
`BgRegime p d dm dp` and `p.ν ≤ ν₀` imply `TrainCloseM m p.train Sg δ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartI

namespace TrainCloseRegimeProof

/-! ### 1. Unconditional Part I velocity/stream/pressure tails -/

private theorem overlapFD_uncond : OverlapFluctuationDecay :=
  overlap_fluctuation_decay overlap_highnorm_uniform

private theorem trainOverlap_uncond : TrainOverlap :=
  trainOverlap_proof overlapFD_uncond
    (overlap_mean_decay overlap_highnorm_uniform overlapFD_uncond overlap_mean_primitive)

private theorem trainStreamVelocityPressureTails_uncond : TrainStreamVelocityPressureTails :=
  train_stream_velocity_pressure_tails trainOverlap_uncond
    (train_vorticity_gaussian_tail trainOverlap_uncond)

/-! ### 2. Pointwise extraction from `wSupNorm` and cell weight bounds -/

private theorem sqrt_jap_mul_norm_le_of_wSupNorm_le {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) {f : UnforcedLeray.Cyl.Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm m f ≤ ENNReal.ofReal B) (z : UnforcedLeray.Cyl.Plane) :
    Real.sqrt (UnforcedLeray.Train.jap m z) * ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ ≤
      ENNReal.ofReal B :=
    (le_iSup (fun w : UnforcedLeray.Cyl.Plane =>
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m w)) * ‖f w‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hz

private theorem norm_le_of_wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E]
    {f : UnforcedLeray.Cyl.Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm 0 f ≤ ENNReal.ofReal B) (z : UnforcedLeray.Cyl.Plane) :
    ‖f z‖ ≤ B := by
  have h1 := sqrt_jap_mul_norm_le_of_wSupNorm_le 0 hB h z
  have hjap : Real.sqrt (UnforcedLeray.Train.jap 0 z) = 1 := by simp [UnforcedLeray.Train.jap]
  rwa [hjap, one_mul] at h1

private theorem sqrt_jap_four_mul (M : ℕ) (z : UnforcedLeray.Cyl.Plane) :
    Real.sqrt (UnforcedLeray.Train.jap (4 * M) z) = (1 + z.2 ^ 2) ^ (2 * M) := by
  have hsq : UnforcedLeray.Train.jap (4 * M) z = ((1 + z.2 ^ 2) ^ (2 * M)) ^ 2 := by
    unfold UnforcedLeray.Train.jap
    have : 4 * M = (2 * M) * 2 := by omega
    rw [this, pow_mul]
  rw [hsq, Real.sqrt_sq (by positivity)]

private theorem jb_le_of_mem_cell {c : ℝ} {x : B0579.Plane} (hx : x ∈ B0579.cell c) (hc : 0 < c) :
    B0579.jb x ≤ (1 + c ^ 2) * (1 + x.2 ^ 2) := by
  have h1 := hx.1
  have hq : x.1 ^ 2 ≤ c ^ 2 := by
    have h2 : -(c / 2) ≤ x.1 := h1.1
    have h3 : x.1 < c / 2 := h1.2
    exact sq_le_sq' (by linarith) (by linarith)
  have h4 : 0 ≤ c ^ 2 * x.2 ^ 2 := by positivity
  have e : (1 + c ^ 2) * (1 + x.2 ^ 2) = 1 + c ^ 2 + x.2 ^ 2 + c ^ 2 * x.2 ^ 2 := by ring
  unfold B0579.jb
  rw [e]
  linarith

private theorem trainDiff_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    (fun z => tr.v 0 z - UnforcedLeray.Train.Vc ν c 0 z) = fun _ => 0 := by
  funext z
  rw [tr.isTrain.initial, B0169.trainDatum_eq_datum, UnforcedLeray.Train.Vc_zero, sub_self]

private theorem contDiff_train {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := Set.univ) (fun z _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ z⟩)
  exact contDiffOn_univ.1 h

private theorem norm_diff_le {ν c s : ℝ} (tr : B0140.TrainSol ν c) (hs : 0 ≤ s) (hc : 0 < c)
    (ha : 0 < UnforcedLeray.Train.width ν s) (j : ℕ) (x : B0579.Plane) :
    ‖iteratedFDeriv ℝ j (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) x‖ ≤
      ‖iteratedFDeriv ℝ j (tr.v s) x‖ + ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x‖ := by
  have h1 : ContDiffAt ℝ j (tr.v s) x :=
    ((contDiff_train tr hs).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ j (UnforcedLeray.Train.Vc ν c s) x :=
    ((UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ j (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) x =
      iteratedFDeriv ℝ j (tr.v s) x - iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) x :=
    iteratedFDeriv_sub_apply h1 h2
  rw [e]
  exact norm_sub_le _ _

private theorem pow_mul_exp_neg_le_inv {b u : ℝ} (hb : 0 < b) (hu : 0 < u) (N : ℕ) :
    u ^ N * Real.exp (-(b * u)) ≤ (((N + 1).factorial : ℝ) / b ^ (N + 1)) * u⁻¹ := by
  have hexp := Real.pow_div_factorial_le_exp (x := b * u) (by positivity) (N + 1)
  have hf : (0 : ℝ) < ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hbN : 0 < b ^ (N + 1) := pow_pos hb _
  have h1 : b ^ (N + 1) * (u ^ N * u) ≤ ((N + 1).factorial : ℝ) * Real.exp (b * u) := by
    have h2 := ( div_le_iff₀ hf ).1 hexp
    calc b ^ (N + 1) * (u ^ N * u) = (b * u) ^ (N + 1) := by rw [mul_pow, ← pow_succ u N]
      _ ≤ Real.exp (b * u) * ((N + 1).factorial : ℝ) := h2
      _ = ((N + 1).factorial : ℝ) * Real.exp (b * u) := mul_comm _ _
  have h3 : u ^ N * Real.exp (-(b * u)) * (b ^ (N + 1) * u) ≤ ((N + 1).factorial : ℝ) := by
    calc u ^ N * Real.exp (-(b * u)) * (b ^ (N + 1) * u)
        = (b ^ (N + 1) * (u ^ N * u)) * Real.exp (-(b * u)) := by ring
      _ ≤ (((N + 1).factorial : ℝ) * Real.exp (b * u)) * Real.exp (-(b * u)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = ((N + 1).factorial : ℝ) * (Real.exp (b * u) * Real.exp (-(b * u))) := by ring
      _ = ((N + 1).factorial : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hbu : 0 < b ^ (N + 1) * u := mul_pos hbN hu
  have h4 := (le_div_iff₀ hbu).2 h3
  calc u ^ N * Real.exp (-(b * u))
      ≤ ((N + 1).factorial : ℝ) / (b ^ (N + 1) * u) := h4
    _ = (((N + 1).factorial : ℝ) / b ^ (N + 1)) * u⁻¹ := by
        rw [div_mul_eq_div_div, div_eq_mul_inv]

/-! ### 3. Single-order `M`-weighted bound on `[0, Sg / p.ν]` -/

private theorem trainClose_order_bound (M : ℕ) {Sg : ℝ} (hSg : 0 < Sg) {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ s : ℝ, 0 ≤ s → s ≤ Sg / p.ν → ∀ x ∈ B0579.cell p.c,
          ‖iteratedFDeriv ℝ j (fun z => p.train.v s z - UnforcedLeray.Train.Vc p.ν p.c s z) x‖ *
            B0579.jb x ^ M ≤ δ := by
  obtain ⟨C₀, bS, ν₁, hC₀, hbS, hν₁, hUnw⟩ :=
    PartI_T25.trainFixedBand_vel_zero_unweighted 2 (by norm_num) Sg hSg j
  obtain ⟨C₁, N₁, ν₂, hC₁, hν₂, hTails⟩ :=
    trainStreamVelocityPressureTails_uncond.2.2 2 (by norm_num) (4 * M) 0 j
  obtain ⟨C_V, hCV, hSpat⟩ := vc_spatial_jet_weighted_bound j (2 * M)
  set C_W : ℝ := C₁ * (1 + Sg) ^ N₁ * 3 ^ (2 * N₁) + (1 + Sg) ^ (2 * M + 1) * C_V + 1
  have hCW_pos : 0 < C_W := by dsimp [C_W]; positivity
  set K_const : ℝ := 2 ^ (2 * M) * C_W * (3 * C₀)
  have hK_pos : 0 < K_const := by dsimp [K_const]; positivity
  set N_tot : ℕ := 2 * M + 2 * N₁ + 1
  set F_fac : ℝ := ((N_tot + 1).factorial : ℝ) / bS ^ (N_tot + 1)
  have hF_pos : 0 < F_fac := by
    dsimp [F_fac]
    have : (0 : ℝ) < ((N_tot + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  set c₀ : ℝ := max (1 + Sg) (K_const * F_fac / δ ^ 2 + 1)
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le (by positivity) (le_max_left (1 + Sg) _)
  set ν₀ : ℝ := min (min 1 (Real.sqrt c₀)⁻¹) (min ν₁ ν₂)
  have hν₀_pos : 0 < ν₀ :=
    lt_min (lt_min one_pos (inv_pos.2 (Real.sqrt_pos.2 hc₀_pos))) (lt_min hν₁ hν₂)
  refine ⟨ν₀, hν₀_pos, ?_⟩
  intro p d dm dp hbg hν_le s hs0 hs_le x hx
  rcases hs0.eq_or_lt with rfl | hs_pos
  · rw [trainDiff_zero p.train, iteratedFDeriv_fun_zero]
    simp [hδ.le]
  · have hν_pos : 0 < p.ν := p.ν_pos
    have hν1 : p.ν ≤ 1 := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hν_c0 : p.ν ≤ (Real.sqrt c₀)⁻¹ :=
      hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hν_1 : p.ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hν_2 : p.ν ≤ ν₂ := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hc_ge_c0 : c₀ ≤ p.c := bgRegime_c_ge hbg hc₀_pos hν_c0
    have hc_ge_one : 1 ≤ p.c := bgRegime_c_ge_one hbg hν1
    have hc_pos : 0 < p.c := p.c_pos
    set u : ℝ := p.c ^ 2
    have hu_ge_c : p.c ≤ u := by
      dsimp [u]
      nlinarith
    have hu_ge_one : 1 ≤ u := hc_ge_one.trans hu_ge_c
    have hu_pos : 0 < u := by positivity
    have hSg_le_u : 1 + Sg ≤ u := (le_max_left _ _).trans (hc_ge_c0.trans hu_ge_c)
    have hKF_le_u : K_const * F_fac / δ ^ 2 ≤ u := by
      have h1 : K_const * F_fac / δ ^ 2 + 1 ≤ c₀ := le_max_right _ _
      linarith [hc_ge_c0.trans hu_ge_c]
    have hc_eq_tp : p.c = trainPeriod 2 p.ν := by
      rw [hbg.c_eq, vb_trainPeriod_two hν_pos]
    obtain ⟨tr', htr'_buc, htr'_v⟩ := vb_transport hc_eq_tp p.train hbg.train_buc
    have hX_le_3u : 1 + p.c + p.ν⁻¹ ≤ 3 * u := by
      have hinv1 : 1 ≤ p.ν⁻¹ := one_le_inv₀ hν_pos |>.2 hν1
      have hinv_le_c : p.ν⁻¹ ≤ p.c := by
        rw [hbg.c_eq, ← inv_pow]
        exact le_self_pow₀ hinv1 (by norm_num)
      linarith
    -- Unweighted exponential bound on E
    set E : ℝ :=
      ‖iteratedFDeriv ℝ j (fun z => p.train.v s z - UnforcedLeray.Train.Vc p.ν p.c s z) x‖
    have hE_nn : 0 ≤ E := norm_nonneg _
    have hE_unw : E ≤ (3 * C₀) * u * Real.exp (-(bS * u)) := by
      have hSup := (hUnw p.ν hν_pos hν_1 tr' htr'_buc s hs_pos hs_le).2
      have hB_nn : 0 ≤ polyP C₀ 1 p.ν (trainPeriod 2 p.ν) *
          Real.exp (-(bS * (trainPeriod 2 p.ν) ^ 2)) := by
        unfold polyP
        have : 0 ≤ trainPeriod 2 p.ν := by rw [← hc_eq_tp]; exact hc_pos.le
        positivity
      have hpt := norm_le_of_wSupNorm_zero_le hB_nn hSup x
      have hage : ageJet 0 j
          (fun r z => tr'.v r z - UnforcedLeray.Train.Vc p.ν (trainPeriod 2 p.ν) r z) s x =
          iteratedFDeriv ℝ j
            (fun z => p.train.v s z - UnforcedLeray.Train.Vc p.ν p.c s z) x := by
        simp [ageJet, UnforcedLeray.Train.jet, htr'_v, hc_eq_tp]
      rw [hage, ← hc_eq_tp] at hpt
      have hpoly_le : polyP C₀ 1 p.ν p.c ≤ (3 * C₀) * u := by
        unfold polyP
        rw [pow_one]
        nlinarith [hC₀.le]
      exact hpt.trans (mul_le_mul_of_nonneg_right hpoly_le (Real.exp_pos _).le)
    -- Weighted polynomial bound on (1 + x.2^2)^(2M) * E
    have hw1 : 1 ≤ UnforcedLeray.Train.width p.ν s := by
      unfold UnforcedLeray.Train.width
      linarith [mul_pos hν_pos hs_pos]
    have hw_pos : 0 < UnforcedLeray.Train.width p.ν s := lt_of_lt_of_le one_pos hw1
    have hw_le_Sg : UnforcedLeray.Train.width p.ν s ≤ 1 + Sg := by
      unfold UnforcedLeray.Train.width
      have hνs : p.ν * s ≤ Sg := by
        have := mul_le_mul_of_nonneg_left hs_le hν_pos.le
        rwa [mul_div_cancel₀ _ hν_pos.ne'] at this
      linarith
    have hw_le_u : UnforcedLeray.Train.width p.ν s ≤ u := hw_le_Sg.trans hSg_le_u
    have htr_w : (1 + x.2 ^ 2) ^ (2 * M) * ‖iteratedFDeriv ℝ j (p.train.v s) x‖ ≤
        C₁ * (1 + Sg) ^ N₁ * 3 ^ (2 * N₁) * u ^ (2 * N₁) := by
      have hSup2 := ((hTails p.ν hν_pos hν_2 tr' htr'_buc s hs_pos).2.2.1).2
      have hK_nn : 0 ≤ polyPS C₁ N₁ p.ν (trainPeriod 2 p.ν) s := by
        unfold polyPS
        have : 0 ≤ trainPeriod 2 p.ν := by rw [← hc_eq_tp]; exact hc_pos.le
        positivity
      have hpt2 := sqrt_jap_mul_norm_le_of_wSupNorm_le (4 * M) hK_nn hSup2 x
      have hage2 : ageJet 0 j tr'.v s x = iteratedFDeriv ℝ j (p.train.v s) x := by
        simp [ageJet, UnforcedLeray.Train.jet, htr'_v]
      rw [sqrt_jap_four_mul M x, hage2, ← hc_eq_tp] at hpt2
      have hps_le := PartI_T25.polyPS_le_polyP_of_le_div_nu N₁ hC₁.le hSg.le hν_pos hc_pos.le
        hs_pos.le hs_le
      have hpp_le : polyP (C₁ * (1 + Sg) ^ N₁) (2 * N₁) p.ν p.c ≤
          C₁ * (1 + Sg) ^ N₁ * 3 ^ (2 * N₁) * u ^ (2 * N₁) := by
        unfold polyP
        have hpow : (1 + p.c + p.ν⁻¹) ^ (2 * N₁) ≤ (3 * u) ^ (2 * N₁) :=
          pow_le_pow_left₀ (by positivity) hX_le_3u (2 * N₁)
        calc C₁ * (1 + Sg) ^ N₁ * (1 + p.c + p.ν⁻¹) ^ (2 * N₁)
            ≤ C₁ * (1 + Sg) ^ N₁ * (3 * u) ^ (2 * N₁) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = C₁ * (1 + Sg) ^ N₁ * 3 ^ (2 * N₁) * u ^ (2 * N₁) := by rw [mul_pow]; ring
      exact hpt2.trans (hps_le.trans hpp_le)
    have hVc_w : (1 + x.2 ^ 2) ^ (2 * M) *
        ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ ≤
        (1 + Sg) ^ (2 * M + 1) * C_V * u ^ (2 * N₁) := by
      have hS := hSpat p.ν p.c s hν_pos hc_pos hs_pos.le hw1 hw_le_u x
      have h1 : 1 / (1 + Sg) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      have h2 : x.2 ^ 2 / (1 + Sg) ≤ x.2 ^ 2 / UnforcedLeray.Train.width p.ν s :=
        div_le_div_of_nonneg_left (sq_nonneg x.2) (by positivity) hw_le_Sg
      have h3 : (1 + x.2 ^ 2) / (1 + Sg) ≤ 1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s := by
        rw [add_div]; linarith
      have h4 : 1 + x.2 ^ 2 ≤ (1 + Sg) * (1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s) := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at h3
      have hpow1 : (1 + x.2 ^ 2) ^ (2 * M) ≤ (1 + x.2 ^ 2) ^ (2 * M + 1) :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg x.2]) (Nat.le_succ _)
      have hpow2 : (1 + x.2 ^ 2) ^ (2 * M + 1) ≤
          (1 + Sg) ^ (2 * M + 1) *
            (1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s) ^ (2 * M + 1) := by
        calc (1 + x.2 ^ 2) ^ (2 * M + 1)
            ≤ ((1 + Sg) * (1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s)) ^ (2 * M + 1) :=
              pow_le_pow_left₀ (by positivity) h4 (2 * M + 1)
          _ = (1 + Sg) ^ (2 * M + 1) *
                (1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s) ^ (2 * M + 1) := mul_pow _ _ _
      have hjet_eq : ‖UnforcedLeray.Train.jet j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ =
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ := rfl
      rw [hjet_eq] at hS
      have hprod : (1 + x.2 ^ 2) ^ (2 * M) *
          ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ ≤
          (1 + Sg) ^ (2 * M + 1) * C_V := by
        calc (1 + x.2 ^ 2) ^ (2 * M) *
              ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖
            ≤ ((1 + Sg) ^ (2 * M + 1) *
                (1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s) ^ (2 * M + 1)) *
                ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ :=
              mul_le_mul_of_nonneg_right (hpow1.trans hpow2) (norm_nonneg _)
          _ = (1 + Sg) ^ (2 * M + 1) *
                ((1 + x.2 ^ 2 / UnforcedLeray.Train.width p.ν s) ^ (2 * M + 1) *
                  ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖) := by ring
          _ ≤ (1 + Sg) ^ (2 * M + 1) * C_V :=
              mul_le_mul_of_nonneg_left hS (by positivity)
      have hu_pow : 1 ≤ u ^ (2 * N₁) := one_le_pow₀ hu_ge_one
      calc (1 + x.2 ^ 2) ^ (2 * M) *
            ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖
          ≤ ((1 + Sg) ^ (2 * M + 1) * C_V) * 1 := by linarith
        _ ≤ ((1 + Sg) ^ (2 * M + 1) * C_V) * u ^ (2 * N₁) :=
            mul_le_mul_of_nonneg_left hu_pow (by positivity)
    have hE_w : (1 + x.2 ^ 2) ^ (2 * M) * E ≤ C_W * u ^ (2 * N₁) := by
      have hdiff := norm_diff_le p.train hs_pos.le hc_pos hw_pos j x
      calc (1 + x.2 ^ 2) ^ (2 * M) * E
          ≤ (1 + x.2 ^ 2) ^ (2 * M) *
              (‖iteratedFDeriv ℝ j (p.train.v s) x‖ +
                ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = (1 + x.2 ^ 2) ^ (2 * M) * ‖iteratedFDeriv ℝ j (p.train.v s) x‖ +
              (1 + x.2 ^ 2) ^ (2 * M) *
                ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc p.ν p.c s) x‖ := by ring
        _ ≤ C₁ * (1 + Sg) ^ N₁ * 3 ^ (2 * N₁) * u ^ (2 * N₁) +
              (1 + Sg) ^ (2 * M + 1) * C_V * u ^ (2 * N₁) := add_le_add htr_w hVc_w
        _ ≤ C_W * u ^ (2 * N₁) := by
            dsimp [C_W]
            nlinarith [one_le_pow₀ hu_ge_one (n := 2 * N₁)]
    -- Combine on the cell via jb_le_of_mem_cell
    have hjb_cell : B0579.jb x ≤ (2 * u) * (1 + x.2 ^ 2) := by
      have h1 := jb_le_of_mem_cell hx hc_pos
      have h2 : 1 + p.c ^ 2 ≤ 2 * u := by dsimp [u]; linarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    have hjb_nn : 0 ≤ B0579.jb x := (B0579.jb_pos x).le
    have hjb_pow : (B0579.jb x ^ M) ^ 2 ≤
        2 ^ (2 * M) * u ^ (2 * M) * (1 + x.2 ^ 2) ^ (2 * M) := by
      calc (B0579.jb x ^ M) ^ 2
          = B0579.jb x ^ (2 * M) := by rw [← pow_mul, mul_comm M 2]
        _ ≤ ((2 * u) * (1 + x.2 ^ 2)) ^ (2 * M) :=
            pow_le_pow_left₀ hjb_nn hjb_cell (2 * M)
        _ = 2 ^ (2 * M) * u ^ (2 * M) * (1 + x.2 ^ 2) ^ (2 * M) := by
            rw [mul_pow, mul_pow]
    have hsq_le : (E * B0579.jb x ^ M) ^ 2 ≤
        K_const * (u ^ N_tot * Real.exp (-(bS * u))) := by
      calc (E * B0579.jb x ^ M) ^ 2
          = ((B0579.jb x ^ M) ^ 2 * E) * E := by ring
        _ ≤ (2 ^ (2 * M) * u ^ (2 * M) * ((1 + x.2 ^ 2) ^ (2 * M) * E)) * E := by
            apply mul_le_mul_of_nonneg_right _ hE_nn
            calc (B0579.jb x ^ M) ^ 2 * E
                ≤ (2 ^ (2 * M) * u ^ (2 * M) * (1 + x.2 ^ 2) ^ (2 * M)) * E :=
                  mul_le_mul_of_nonneg_right hjb_pow hE_nn
              _ = 2 ^ (2 * M) * u ^ (2 * M) * ((1 + x.2 ^ 2) ^ (2 * M) * E) := by ring
        _ ≤ (2 ^ (2 * M) * u ^ (2 * M) * (C_W * u ^ (2 * N₁))) *
              ((3 * C₀) * u * Real.exp (-(bS * u))) := by
            apply mul_le_mul _ hE_unw hE_nn (by positivity)
            exact mul_le_mul_of_nonneg_left hE_w (by positivity)
        _ = K_const * (u ^ N_tot * Real.exp (-(bS * u))) := by
            dsimp [K_const, N_tot]
            rw [pow_add, pow_add, pow_one]
            ring
    have hexp_inv := pow_mul_exp_neg_le_inv hbS hu_pos N_tot
    have hK_inv : K_const * F_fac * u⁻¹ ≤ δ ^ 2 := by
      have h1 := (div_le_iff₀ (sq_pos_of_pos hδ)).1 hKF_le_u
      have h2 : K_const * F_fac * u⁻¹ ≤ u * δ ^ 2 * u⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hu_pos.le)
      rwa [mul_comm u (δ ^ 2), mul_inv_cancel_right₀ hu_pos.ne'] at h2
    have hsq_δ : (E * B0579.jb x ^ M) ^ 2 ≤ δ ^ 2 := by
      calc (E * B0579.jb x ^ M) ^ 2
          ≤ K_const * (u ^ N_tot * Real.exp (-(bS * u))) := hsq_le
        _ ≤ K_const * (F_fac * u⁻¹) := mul_le_mul_of_nonneg_left hexp_inv hK_pos.le
        _ = K_const * F_fac * u⁻¹ := (mul_assoc _ _ _).symm
        _ ≤ δ ^ 2 := hK_inv
    have hsqrt := Real.sqrt_le_sqrt hsq_δ
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hδ.le] at hsqrt

end TrainCloseRegimeProof

/-- **Main theorem (`PartII-b:F2/1`, `short-bg:train-early`, SP 2085–2090)**: in `BgRegime`, for
small `p.ν`, the train difference `p.train.v - V_c` satisfies `TrainCloseM m p.train Sg δ`. -/
theorem trainCloseRegime_proof : UnforcedLeray.Short.IIb.TrainCloseRegime := by
  intro m hm Sg hSg dm dp _hdm δ hδ
  set M : ℕ := ⌈m / 2 + 1⌉₊
  have key : ∀ n : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ s : ℝ, 0 ≤ s → s ≤ Sg / p.ν → ∀ x ∈ B0579.cell p.c, ∀ j ≤ n,
          ‖iteratedFDeriv ℝ j (fun z => p.train.v s z - UnforcedLeray.Train.Vc p.ν p.c s z) x‖ *
            B0579.jb x ^ M ≤ δ := by
    intro n
    induction n with
    | zero =>
      obtain ⟨ν₀, hν₀, H⟩ := TrainCloseRegimeProof.trainClose_order_bound M hSg hδ 0
      refine ⟨ν₀, hν₀, fun p d hbg hν s hs0 hs1 x hx j hj => ?_⟩
      obtain rfl : j = 0 := by omega
      exact H p d dm dp hbg hν s hs0 hs1 x hx
    | succ n ih =>
      obtain ⟨ν₁, hν₁, H1⟩ := ih
      obtain ⟨ν₂, hν₂, H2⟩ := TrainCloseRegimeProof.trainClose_order_bound M hSg hδ (n + 1)
      refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hbg hν s hs0 hs1 x hx j hj => ?_⟩
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · exact H1 p d hbg (hν.trans (min_le_left _ _)) s hs0 hs1 x hx j (by omega)
      · obtain rfl : j = n + 1 := by omega
        exact H2 p d dm dp hbg (hν.trans (min_le_right _ _)) s hs0 hs1 x hx
  obtain ⟨ν₀, hν₀, H⟩ := key 4
  refine ⟨ν₀, hν₀, fun p d hbg hν s hs0 hs1 x hx j hj => ?_⟩
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hm_le_M : m / 2 + 1 ≤ (M : ℝ) := Nat.le_ceil (m / 2 + 1)
  have hpow : B0579.jb x ^ (m / 2 + 1) ≤ B0579.jb x ^ M := by
    rw [← Real.rpow_natCast (B0579.jb x) M]
    exact Real.rpow_le_rpow_of_exponent_le hjb1 hm_le_M
  exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (H p d hbg hν s hs0 hs1 x hx j hj)

end UnforcedLeray.Short.IIb
