import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Sub.PartI_T13
import UnforcedLeray.Short.PartI.Sub.PartI_T13.SmoothL2
import UnforcedLeray.Short.PartI.Sub.PartI_T13.EnergyBalance
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.PressureStep
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapAgeDeriv.VelFluctHigherStep

/-!
# `Short/PartI/Tasks/TrainHeatFixed/TrainFluctAgeJetFixed.lean` — Task `PartI:HF/2`

Source of record: `the November 2 reference manuscript`, lines 439–446, 516–526
at fixed parameters (lines 429–435).

Proves `trainFluctAgeJetFixed : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed`:
1. Fixes a single viscosity threshold `ν₀ > 0` for `ρ > 1/2` from the base `L²` overlap fluctuation
   decay (`PartI_T13.overlapFluctuation_jetEnergy_zero_decay`), base-order `TrainOverlap` gradient
   decay (`supNormD_pointwise_bound_j` at `j = 1`), and all-order velocity jet boundedness
   (`trainJetsBoundedFixed`).
2. Combines all-order post-overlap `H^k` propagation (`overlap_sobolevSq_fixed_of_grad_rpow`) and
   `jetEnergy_hfluct_unit_le` with `PartI_T13.jetEnergy_succ_le_unit` and `jetSupBridge_proof` to
   obtain exponential decay of `supNormD j (hfluct 1 (overlapField ν c tr.v T))` for all `j : ℕ`
   at fixed `0 < ν ≤ ν₀`.
3. Combines pre-overlap boundedness on `(0, s_c]` with post-overlap rescaling on `[s_c, ∞)` to
   establish the base age order `ℓ = 0` exponential decay of `ageJet 0 j (fun r => hfluct c (tr.v r))`
   on all `s > 0`.
4. Uses the cylinder pressure kernel (`PartI_T20_1.oscLinear_explicit`, `\bar p = -\overline{v₂²}`,
   and qualitative pressure-gradient boundedness from `PressStepFixed.abs_derivWord_iteratedDeriv_p_le`)
   together with the horizontally oscillated momentum equation (`PartI_T22_2_1.norm_ageJet_succ_hfluct_v_comp_le`)
   to propagate exponential decay of `ageJet ℓ j (fun r => hfluct c (tr.v r))` and `ageJet ℓ j tr.p`
   to all age orders `ℓ : ℕ` by strong induction on `ℓ`.
5. Deduces `TrainFluctAgeJetFixed` for the stream fluctuation `ψ − \bar ψ` at all `(ℓ, j)` via
   `PartI_T22.wSupNorm_zero_ageJet_streamFluct_zero_le` (`j = 0`) and
   `PartI_T22.norm_ageJet_streamFluct_succ_le` (`j = k + 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet cellL2 wCellL2 jap)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm)

namespace TrainFluctAgeJetFixedAux

/-! ### 1. Fixed-parameter all-order `jetEnergy` and `supNormD` decay of `hfluct 1 (overlapField ...)` -/

theorem overlap_hfluct_jetEnergy_bounded_fixed {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))))
    (k : ℕ) :
    ∃ E_k : ℝ, 0 < E_k ∧
      ∀ T : ℝ, 0 ≤ T → jetEnergy 1 k (hfluct 1 (overlapField ν c tr.v T)) ≤ E_k := by
  obtain ⟨E_k, hE_k, hsob⟩ := overlap_sobolevSq_fixed_of_grad_rpow hν hc tr htr hC₁ hGrad k
  refine ⟨E_k, hE_k, fun T hT => ?_⟩
  let U := overlapField ν c tr.v T
  have hU : CellSmoothL2 1 U := overlapField_cellSmoothL2 hν hc tr htr hT
  exact (jetEnergy_hfluct_unit_le hU k).trans
    ((jetEnergy_le_cylSobolevSq le_rfl U).trans (hsob T hT))

theorem overlap_hfluct_jetEnergy_decay_fixed {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₀ lam₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hlam₀ : 0 < lam₀) (hC₁ : 0 ≤ C₁)
    (hJ0 : ∀ T : ℝ, 0 ≤ T →
      jetEnergy 1 0 (hfluct 1 (overlapField ν c tr.v T)) ≤ C₀ * Real.exp (-(lam₀ * T)))
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ)))) :
    ∀ j : ℕ, ∃ Cj lamj : ℝ, 0 < Cj ∧ 0 < lamj ∧
      ∀ T : ℝ, 0 ≤ T →
        jetEnergy 1 j (hfluct 1 (overlapField ν c tr.v T)) ≤ Cj * Real.exp (-(lamj * T))
  | 0 => ⟨C₀, lam₀, hC₀, hlam₀, hJ0⟩
  | j + 1 => by
    obtain ⟨Cj, lamj, hCj, hlamj, hIj⟩ :=
      overlap_hfluct_jetEnergy_decay_fixed hν hc tr htr hC₀ hlam₀ hC₁ hJ0 hGrad j
    obtain ⟨M, hM, hJM⟩ :=
      overlap_hfluct_jetEnergy_bounded_fixed hν hc tr htr hC₁ hGrad (j + 2)
    let C_next : ℝ := 2 * 2 ^ (j + 1) * 16 * Real.sqrt Cj * Real.sqrt M
    refine ⟨C_next, lamj / 2, by positivity, by positivity, fun T hT => ?_⟩
    let U := overlapField ν c tr.v T
    let W := hfluct 1 U
    have hWs : CellSmoothL2 1 W :=
      (cellSmoothL2_hfluct_unit (overlapField_cellSmoothL2 hν hc tr htr hT)).1
    have hJj := hIj T hT
    have hJj2 := hJM T hT
    have hsqrt_j : Real.sqrt (jetEnergy 1 j W) ≤ Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
      calc Real.sqrt (jetEnergy 1 j W)
          ≤ Real.sqrt (Cj * Real.exp (-(lamj * T))) := Real.sqrt_le_sqrt hJj
        _ = Real.sqrt Cj * Real.sqrt (Real.exp (-(lamj * T))) := Real.sqrt_mul hCj.le _
        _ = Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
            congr 1
            ring
    have hsqrt_j2 : Real.sqrt (jetEnergy 1 (j + 2) W) ≤ Real.sqrt M := Real.sqrt_le_sqrt hJj2
    calc jetEnergy 1 (j + 1) W
        ≤ 2 * 2 ^ (j + 1) * 16 * Real.sqrt (jetEnergy 1 j W) *
            Real.sqrt (jetEnergy 1 (j + 2) W) := PartI_T13.jetEnergy_succ_le_unit j hWs
      _ ≤ 2 * 2 ^ (j + 1) * 16 * (Real.sqrt Cj * Real.exp (-(lamj / 2 * T))) * Real.sqrt M := by
          gcongr
      _ = C_next * Real.exp (-(lamj / 2 * T)) := by
          dsimp [C_next]
          ring

theorem overlap_hfluct_supNormD_decay_fixed {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₀ lam₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hlam₀ : 0 < lam₀) (hC₁ : 0 ≤ C₁)
    (hJ0 : ∀ T : ℝ, 0 ≤ T →
      jetEnergy 1 0 (hfluct 1 (overlapField ν c tr.v T)) ≤ C₀ * Real.exp (-(lam₀ * T)))
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))))
    (j : ℕ) :
    ∃ C_Sup lam_Sup : ℝ, 0 < C_Sup ∧ 0 < lam_Sup ∧
      ∀ T : ℝ, 0 ≤ T →
        B0277.supNormD j (hfluct 1 (overlapField ν c tr.v T)) ≤
          ENNReal.ofReal (C_Sup * Real.exp (-(lam_Sup * T))) := by
  obtain ⟨Cj, lamj, hCj, hlamj, hEj⟩ :=
    overlap_hfluct_jetEnergy_decay_fixed hν hc tr htr hC₀ hlam₀ hC₁ hJ0 hGrad j
  obtain ⟨M₁, hM₁, hJM₁⟩ :=
    overlap_hfluct_jetEnergy_bounded_fixed hν hc tr htr hC₁ hGrad (j + 1)
  obtain ⟨M₂, _hM₂, hJM₂⟩ :=
    overlap_hfluct_jetEnergy_bounded_fixed hν hc tr htr hC₁ hGrad (j + 2)
  obtain ⟨CSup, hCSup, hBrSup⟩ := jetSupBridge_proof j
  let M : ℝ := max M₁ M₂
  have hM_pos : 0 < M := lt_max_of_lt_left hM₁
  let C_Sup : ℝ := 2 * (CSup + 1) * (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ)
  refine ⟨C_Sup, lamj / 4, by positivity, by positivity, fun T hT => ?_⟩
  let U := overlapField ν c tr.v T
  let W := hfluct 1 U
  have hWs : CellSmoothL2 1 W :=
    (cellSmoothL2_hfluct_unit (overlapField_cellSmoothL2 hν hc tr htr hT)).1
  have hJj := hEj T hT
  have hsqrt_j : Real.sqrt (jetEnergy 1 j W) ≤ Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
    calc Real.sqrt (jetEnergy 1 j W)
        ≤ Real.sqrt (Cj * Real.exp (-(lamj * T))) := Real.sqrt_le_sqrt hJj
      _ = Real.sqrt Cj * Real.sqrt (Real.exp (-(lamj * T))) := Real.sqrt_mul hCj.le _
      _ = Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
          congr 1
          ring
  have hSup := (hBrSup 1 le_rfl W hWs).2
  refine hSup.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsqrt_j1 : Real.sqrt (jetEnergy 1 (j + 1) W) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt ((hJM₁ T hT).trans (le_max_left _ _))
  have hsqrt_j2 : Real.sqrt (jetEnergy 1 (j + 2) W) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt ((hJM₂ T hT).trans (le_max_right _ _))
  have hrpow_bound : ∀ K : ℝ, 0 ≤ K → Real.sqrt K ≤ Real.sqrt M →
      (Real.sqrt (jetEnergy 1 j W) * Real.sqrt K) ^ (1 / 2 : ℝ) ≤
        (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) * Real.exp (-(lamj / 4 * T)) := by
    intro K _ hK
    have hprod : Real.sqrt (jetEnergy 1 j W) * Real.sqrt K ≤
        (Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T)) := by
      calc Real.sqrt (jetEnergy 1 j W) * Real.sqrt K
          ≤ (Real.sqrt Cj * Real.exp (-(lamj / 2 * T))) * Real.sqrt M :=
            mul_le_mul hsqrt_j hK (Real.sqrt_nonneg _) (by positivity)
        _ = (Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T)) := by ring
    calc (Real.sqrt (jetEnergy 1 j W) * Real.sqrt K) ^ (1 / 2 : ℝ)
        ≤ ((Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            hprod (by norm_num)
      _ = (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) *
            (Real.exp (-(lamj / 2 * T))) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (by positivity) (Real.exp_nonneg _)
      _ = (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) * Real.exp (-(lamj / 4 * T)) := by
          congr 1
          rw [← Real.exp_mul]
          congr 1
          ring
  have hb1 := hrpow_bound (jetEnergy 1 (j + 1) W) (jetEnergy_nonneg 1 (j + 1) W) hsqrt_j1
  have hb2 := hrpow_bound (jetEnergy 1 (j + 2) W) (jetEnergy_nonneg 1 (j + 2) W) hsqrt_j2
  unfold supRhs
  rw [Real.one_rpow, one_mul]
  calc CSup * ((Real.sqrt (jetEnergy 1 j W) * Real.sqrt (jetEnergy 1 (j + 2) W)) ^ (1 / 2 : ℝ) +
          (Real.sqrt (jetEnergy 1 j W) * Real.sqrt (jetEnergy 1 (j + 1) W)) ^ (1 / 2 : ℝ))
      ≤ (CSup + 1) * (2 * ((Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) *
          Real.exp (-(lamj / 4 * T)))) := by
        apply mul_le_mul (by linarith) (by linarith)
          (add_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))
          (by linarith)
    _ = C_Sup * Real.exp (-(lamj / 4 * T)) := by dsimp [C_Sup]; ring

/-! ### 2. Global `4 * M_v` bound for `ageJet ℓ j (hfluct c (tr.v ·))` and `ℓ = 0` decay on `s > 0` -/

theorem norm_ageJet_hfluct_v_le_four_mul {ν c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s)
    (hV_bd : ∀ w : Plane, ‖ageJet ℓ j tr.v s w‖ ≤ M) (z : Plane) :
    ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤ 4 * M := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_fl : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hvec := PartI_T22_2_1.norm_ageJet_vec_le_add_proj
    (V := fun r w => hfluct c (tr.v r) w) hsm_fl ℓ j hs z
  have hcomp : ∀ k : Fin 2,
      ‖ageJet ℓ j (fun r w => (hfluct c (tr.v r) w) k) s z‖ ≤ 2 * M := by
    intro k
    let V_k : ℝ → Plane → ℝ := fun r w => tr.v r w k
    let M_k : ℝ → Plane → ℝ := fun r w => hmean c (V_k r) w.2
    have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => V_k x.1 x.2) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
    have hsm_mk : PartI_T20.SmR (fun x : ℝ × Plane => M_k x.1 x.2) :=
      PartI_T22_2_1.contDiffOn_snd_lift (g := fun r η => hmean c (V_k r) η)
        (hmeanContDiff c hc V_k hsm_vk)
    have hslice : ageJet ℓ j (fun r w => (hfluct c (tr.v r) w) k) s z =
        ageJet ℓ j (fun r w => V_k r w - M_k r w) s z := by
      unfold ageJet
      congr 1
      funext w
      have hev : (fun r => (hfluct c (tr.v r) w) k) =ᶠ[𝓝 s]
          fun r => V_k r w - M_k r w := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
        change (tr.v r w - hmean c (tr.v r) w.2) k = _
        rw [PiLp.sub_apply, PartI_T22.hmean_apply_vec' c hvc w.2 k]
      exact hev.iteratedDeriv_eq ℓ
    rw [hslice, PartI_T22.ageJet_sub V_k M_k hsm_vk hsm_mk hs ℓ j z]
    have h1 : ∀ w : Plane, ‖ageJet ℓ j V_k s w‖ ≤ M := fun w =>
      (PartI_T20.norm_ageJet_vec_proj_le hsm_v k ℓ j hs w).trans (hV_bd w)
    have h2 : ‖ageJet ℓ j M_k s z‖ ≤ M :=
      PartI_T22_2_1.norm_ageJet_hmean_scalar_le hc hM hsm_vk ℓ j hs z (fun q _ => h1 (q, z.2))
    have htri := norm_sub_le (ageJet ℓ j V_k s z) (ageJet ℓ j M_k s z)
    linarith [h1 z]
  linarith [hcomp 0, hcomp 1]

/-- Fixed-parameter all-spatial-order exponential decay of `ageJet r j (fun t => hfluct c (tr.v t))`
on `s > 0` at age order `r`. -/
def VelFluctOrderDecayFixed {ν c : ℝ} (tr : B0140.TrainSol ν c) (r : ℕ) : Prop :=
  ∀ j : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
    ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖ageJet r j (fun t => hfluct c (tr.v t)) s z‖ ≤ C * Real.exp (-(κ * s))

theorem velFluctOrderDecayFixed_zero {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₀ lam₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hlam₀ : 0 < lam₀) (hC₁ : 0 ≤ C₁)
    (hJ0 : ∀ T : ℝ, 0 ≤ T →
      jetEnergy 1 0 (hfluct 1 (overlapField ν c tr.v T)) ≤ C₀ * Real.exp (-(lam₀ * T)))
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))))
    (hV0 : VelOrderBoundedFixed tr 0) :
    VelFluctOrderDecayFixed tr 0 := by
  intro j
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨C_Sup, lam_Sup, hCSup, hlamSup, hSup_ov⟩ :=
    overlap_hfluct_supNormD_decay_fixed hν hc tr htr hC₀ hlam₀ hC₁ hJ0 hGrad j
  obtain ⟨M₀, hM₀⟩ := hV0 j
  let M_v : ℝ := max M₀ 0
  have hMv_nn : 0 ≤ M_v := le_max_right _ _
  let s_c : ℝ := B0146.overlapAge ν c
  let κ : ℝ := lam_Sup * ν / c ^ 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let C_post : ℝ := C_Sup * Real.exp lam_Sup
  let C_pre : ℝ := (4 * M_v + 1) * Real.exp (κ * s_c)
  let C : ℝ := max C_post C_pre
  have hC : 0 < C := lt_max_of_lt_left (by dsimp [C_post]; positivity)
  refine ⟨C, κ, hC, hκ, fun s hs z => ?_⟩
  rcases le_total s s_c with hsc | hsc
  · have hpt : ‖ageJet 0 j (fun t => hfluct c (tr.v t)) s z‖ ≤ 4 * M_v :=
      norm_ageJet_hfluct_v_le_four_mul hc0 hMv_nn tr 0 j hs
        (fun w => (hM₀ s hs w).trans (le_max_left _ _)) z
    have hexp1 : 1 ≤ Real.exp (κ * s_c) * Real.exp (-(κ * s)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖ageJet 0 j (fun t => hfluct c (tr.v t)) s z‖
        ≤ (4 * M_v + 1) * 1 := by linarith
      _ ≤ (4 * M_v + 1) * (Real.exp (κ * s_c) * Real.exp (-(κ * s))) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C_pre * Real.exp (-(κ * s)) := by dsimp [C_pre]; ring
      _ ≤ C * Real.exp (-(κ * s)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  · set T : ℝ := ν * (s - s_c) / c ^ 2
    have hT : 0 ≤ T := div_nonneg (mul_nonneg hν.le (sub_nonneg.2 hsc)) (sq_nonneg c)
    have hs_eq : s_c + c ^ 2 * T / ν = s := by
      have hν0 : ν ≠ 0 := hν.ne'
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      dsimp [T]
      field_simp
      ring
    have hU_eq : overlapField ν c tr.v T = scaleField c (tr.v s) := by
      funext y
      simp [overlapField, scaleField, s_c, hs_eq]
    have hW_eq : hfluct 1 (overlapField ν c tr.v T) = scaleField c (hfluct c (tr.v s)) := by
      rw [hU_eq, PartI_T22.hfluct_scaleField hc0]
    have hsup_T := hSup_ov T hT
    rw [hW_eq] at hsup_T
    have hsup_s : B0277.supNormD j (hfluct c (tr.v s)) ≤
        ENNReal.ofReal (C_Sup * Real.exp (-(lam_Sup * T))) :=
      (PartI_T22.supNormD_le_supNormD_scaleField hc.le j (hfluct c (tr.v s))).trans hsup_T
    have hpt : ‖ageJet 0 j (fun t => hfluct c (tr.v t)) s z‖ ≤
        C_Sup * Real.exp (-(lam_Sup * T)) :=
      B0277.norm_le_of_supNormD_le (by positivity) hsup_s z
    have hsc_le : ν * s_c ≤ c ^ 2 := by
      dsimp [s_c, B0146.overlapAge]
      rw [mul_div_cancel₀ _ hν.ne']
      linarith
    have hsc_div : ν * s_c / c ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hc0)).2 hsc_le
    have hT_id : -(lam_Sup * T) = lam_Sup * (ν * s_c / c ^ 2) - κ * s := by
      dsimp [T, κ]
      ring
    have hexp_le : C_Sup * Real.exp (-(lam_Sup * T)) ≤ C_post * Real.exp (-(κ * s)) := by
      dsimp [C_post]
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCSup.le
      rw [hT_id]
      nlinarith [mul_le_mul_of_nonneg_left hsc_div hlamSup.le]
    exact hpt.trans (hexp_le.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)))

/-! ### 3. Uniform rectangle bounds and cylinder pressure decay at age order `ℓ` -/

theorem uniform_velFluct_spatial {ν c : ℝ} {tr : B0140.TrainSol ν c} {r : ℕ}
    (hr : VelFluctOrderDecayFixed tr r) :
    ∀ K : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K,
        ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ C * Real.exp (-(κ * s))
  | 0 => by
    obtain ⟨C, κ, hC, hκ, h0⟩ := hr 0
    refine ⟨C, κ, hC, hκ, fun s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 s hs z
  | K + 1 => by
    obtain ⟨C₁, κ₁, hC₁, hκ₁, hIH⟩ := uniform_velFluct_spatial hr K
    obtain ⟨C₂, κ₂, _hC₂, hκ₂, hK1⟩ := hr (K + 1)
    refine ⟨max C₁ C₂, min κ₁ κ₂, lt_max_of_lt_left hC₁, lt_min hκ₁ hκ₂,
      fun s hs z i hi => ?_⟩
    rcases Nat.of_le_succ hi with hiK | rfl
    · refine (hIH s hs z i hiK).trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le))
    · refine (hK1 s hs z).trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le))

theorem uniform_velFluct_rect {ν c : ℝ} {tr : B0140.TrainSol ν c} (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, VelFluctOrderDecayFixed tr r) →
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
        ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
          ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ C * Real.exp (-(κ * s))
  | 0, hIH => by
    obtain ⟨C, κ, hC, hκ, h0⟩ := uniform_velFluct_spatial (hIH 0 le_rfl) K
    refine ⟨C, κ, hC, hκ, fun s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 s hs z i hi
  | L + 1, hIH => by
    obtain ⟨C₁, κ₁, hC₁, hκ₁, h1⟩ :=
      uniform_velFluct_rect K L (fun r hr => hIH r (Nat.le_succ_of_le hr))
    obtain ⟨C₂, κ₂, _hC₂, hκ₂, h2⟩ := uniform_velFluct_spatial (hIH (L + 1) le_rfl) K
    refine ⟨max C₁ C₂, min κ₁ κ₂, lt_max_of_lt_left hC₁, lt_min hκ₁ hκ₂,
      fun s hs z r hr i hi => ?_⟩
    rcases Nat.of_le_succ hr with hrL | rfl
    · refine (h1 s hs z r hrL i hi).trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le))
    · refine (h2 s hs z i hi).trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le))

/-- Bilinear spacetime Leibniz bound for `poissonSource (tr.v r)` retaining a fluctuation factor
`M_F` on every term. -/
theorem norm_ageJet_poissonSource_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    ‖ageJet ℓ j (fun r w => poissonSource (tr.v r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M_F * M_V := by
  let V : ℝ → Plane → Vec := tr.v
  let VF : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
  have hV : Sm (fun x : ℝ × Plane => V x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => VF x.1 x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_vf0 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hsm_vf1 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  let P₁ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 0) w * Cyl.partialQ (fun y => V r y 0) w
  let P₂ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 0) w
  let P₃ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialEta (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 1) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => P₁ x.1 x.2) := hQ0.mul hQ0
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => P₂ x.1 x.2) := hQ1.mul hE0
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => P₃ x.1 x.2) := hE1.mul hE1
  have hfun : (fun r w => poissonSource (V r) w) =
      fun r w => (P₁ r w + (P₂ r w + P₂ r w)) + P₃ r w := by
    funext r w
    unfold poissonSource
    dsimp [P₁, P₂, P₃]
    ring
  have hadd1 := PartI_T20.ageJet_add (fun r w => P₁ r w + (P₂ r w + P₂ r w)) P₃
    (hsm₁.add (hsm₂.add hsm₂)) hsm₃ hs ℓ j z
  have hadd2 := PartI_T20.ageJet_add P₁ (fun r w => P₂ r w + P₂ r w)
    hsm₁ (hsm₂.add hsm₂) hs ℓ j z
  have hadd3 := PartI_T20.ageJet_add P₂ P₂ hsm₂ hsm₂ hs ℓ j z
  have hQ0_eq : (fun t w => Cyl.partialQ (fun y => V t y 0) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 0) w :=
    funext fun t => funext fun w => PartI_T22_2_1.partialQ_train_v_eq_fluct tr t 0 w
  have hQ1_eq : (fun t w => Cyl.partialQ (fun y => V t y 1) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 1) w :=
    funext fun t => funext fun w => PartI_T22_2_1.partialQ_train_v_eq_fluct tr t 1 w
  have hQ0_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ0_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 0) hsm_vf0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 0 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hQ1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ1_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 1) hsm_vf1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hE1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    calc ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖
        ≤ ‖ageJet r (i + 1) (fun t w => V t w 1) s z‖ :=
          PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z
      _ = ‖ageJet r (i + 1) (fun t w => VF t w 1) s z‖ := by
          rw [PartI_T22_2_1.ageJet_train_v_one_eq_fluct hν hc tr r (i + 1) hs z]
      _ ≤ ‖ageJet r (i + 1) VF s z‖ :=
          PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z
      _ ≤ M_F := hF_bd r hr (i + 1) (by omega)
  have hQ0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE1_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hb₁ := PartI_T20.norm_ageJet_mul_le hQ0 hQ0 ℓ j hs hMF hMV z hQ0_F_bd hQ0_V_bd
  have hb₂ := PartI_T20.norm_ageJet_mul_le hQ1 hE0 ℓ j hs hMF hMV z hQ1_F_bd hE0_V_bd
  have hb₃ := PartI_T20.norm_ageJet_mul_le hE1 hE1 ℓ j hs hMF hMV z hE1_F_bd hE1_V_bd
  rw [hfun, hadd1, hadd2, hadd3]
  have htri1 := norm_add_le
    (ageJet ℓ j P₁ s z + (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)) (ageJet ℓ j P₃ s z)
  have htri2 := norm_add_le (ageJet ℓ j P₁ s z) (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)
  have htri3 := norm_add_le (ageJet ℓ j P₂ s z) (ageJet ℓ j P₂ s z)
  linarith

/-- Horizontal-mean bound for word derivatives of the age-iterated pressure slice retaining a
fluctuation factor `M_F`. -/
theorem abs_hmean_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w'‖ ≤ M_F)
    (hV_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s w'‖ ≤ M_V) :
    |hmean c (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z.2| ≤
      (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_sq : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) := by
    have : (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) =
        fun x : ℝ × Plane => tr.v x.1 x.2 1 * tr.v x.1 x.2 1 :=
      funext fun _ => sq _
    rw [this]
    exact hsm_v1.mul hsm_v1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  let G_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.v r z' 1 ^ 2) s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hG_sm : ContDiff ℝ ∞ G_ℓ :=
    PartI_T20_1.contDiff_iteratedDeriv_slice (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ :=
    PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs
  have hG_per : Cyl.IsPeriodic c G_ℓ := by
    refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    exact congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z')
  have hmean_eq : ∀ η : ℝ, hmean c P_ℓ η = -hmean c G_ℓ η := by
    intro η
    rw [← PartI_T20_1.iteratedDeriv_hmean_eq hc hsm_p ℓ hs η,
      ← PartI_T20_1.iteratedDeriv_hmean_eq hc (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs η,
      ← iteratedDeriv_neg]
    have hev : (fun r => hmean c (tr.p r) η) =ᶠ[𝓝 s]
        fun r => -hmean c (fun z' : Plane => tr.v r z' 1 ^ 2) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using
        PartI_T20_1.train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr η
    exact hev.iteratedDeriv_eq ℓ
  have hword_eq := PartI_T20_1.hmean_derivWord_neg_eq hc hP_sm hG_sm hP_per hG_per hmean_eq w z.2
  rw [hword_eq, abs_neg]
  refine cylpHmeanAbsLe hc (fun w' => ?_) z.2
  have hsq_fn : (fun r (z' : Plane) => tr.v r z' 1 ^ 2) =
      fun r z' => tr.v r z' 1 * tr.v r z' 1 := by
    funext r z'; exact sq _
  calc |B0151.derivWord w G_ℓ w'|
      ≤ ‖ageJet ℓ k (fun r z' => tr.v r z' 1 ^ 2) s w'‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => tr.v r z' 1 ^ 2)
          hsm_sq ℓ k hw hs w'
    _ = ‖ageJet ℓ k (fun r z' => tr.v r z' 1 * tr.v r z' 1) s w'‖ := by rw [hsq_fn]
    _ ≤ (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
        refine PartI_T20.norm_ageJet_mul_le
          (A := fun r z' => tr.v r z' 1) (B := fun r z' => tr.v r z' 1)
          hsm_v1 hsm_v1 ℓ k hs hMF hMV w' (fun r hr i hi => ?_) (fun r hr i hi => ?_)
        · rw [PartI_T22_2_1.ageJet_train_v_one_eq_fluct hν hc tr r i hs w']
          exact (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r i hs w').trans (hF_bd w' r hr i hi)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs w').trans (hV_bd w' r hr i hi)

/-- Laplacian bound for word derivatives of the age-iterated pressure slice retaining a
fluctuation factor `M_F`. -/
theorem abs_lapS_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    |Train.lapS (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z| ≤
      4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_src : PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (tr.v x.1) x.2) :=
    PartI_T20_1.smR_poissonSource hsm_v
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hlap_P : Train.lapS P_ℓ =
      fun z' => -iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s := by
    funext z'
    have h1 := PartI_T20.iteratedDeriv_mul_lapS_eq hsm_p 1 ℓ hs z'
    simp only [one_mul] at h1
    rw [← h1, ← iteratedDeriv_neg]
    have hev : (fun r => Train.lapS (tr.p r) z') =ᶠ[𝓝 s]
        fun r => -poissonSource (tr.v r) z' := by
      filter_upwards [Ioi_mem_nhds hs] with r (hr : 0 < r)
      exact slicePoisson ν c (r + 1) tr.v tr.p hν hc1 (by linarith)
        (trainSol_isClassicalOn tr (r + 1)) r ⟨hr.le, by linarith⟩ z'
    exact hev.iteratedDeriv_eq ℓ
  rw [PartI_T20_1.derivWord_lapS_comm hP_sm w z, hlap_P, PartI_T20_1.derivWord_neg _ w z, abs_neg]
  calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s) z|
      ≤ ‖ageJet ℓ k (fun r z' => poissonSource (tr.v r) z') s z‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => poissonSource (tr.v r) z')
          hsm_src ℓ k hw hs z
    _ ≤ 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V :=
        norm_ageJet_poissonSource_fluct_le hν hc hMF hMV tr ℓ k hs z hF_bd hV_bd

/-- Oscillating-part bound for `B0151.derivWord w P_ℓ` from a qualitative bound `L_p` on
`ageJet ℓ (k + 1) tr.p s` and the bilinear Laplacian bound `K_src = 4 * 2^(ℓ + k) * M_F * M_V`. -/
theorem abs_osc_derivWord_p_fluct_le {ν c M_F M_V L_p : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hp_grad : ∀ z' : Plane, ‖ageJet ℓ (k + 1) tr.p s z'‖ ≤ L_p)
    (hF_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z'‖ ≤ M_F)
    (hV_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z'‖ ≤ M_V) :
    let Q_s : Plane → ℝ := B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)
    let K_src : ℝ := 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V
    |Q_s z - hmean c Q_s z.2| ≤
      (K_src * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  intro Q_s K_src
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hK_nn : 0 ≤ K_src := by dsimp [K_src]; positivity
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hQ_C2 : ContDiff ℝ 2 Q_s := (B0151.contDiff_derivWord hP_sm w).of_le (by simp)
  have hQ_per : Cyl.IsPeriodic c Q_s :=
    PartI_T20_1.isPeriodic_derivWord
      (PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs) w
  have hgrad : ∃ L : ℝ, ∀ y : Plane, |Cyl.partialQ Q_s y| ≤ L ∧ |Cyl.partialEta Q_s y| ≤ L := by
    refine ⟨L_p, fun y => ⟨?_, ?_⟩⟩
    · have hlen_t : (true :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (true :: w) P_ℓ y| ≤ L_p
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_t hs y).trans
        (hp_grad y)
    · have hlen_f : (false :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (false :: w) P_ℓ y| ≤ L_p
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_f hs y).trans
        (hp_grad y)
  have hlap : ∀ y : Plane, |Train.lapS Q_s y| ≤ K_src := fun y =>
    abs_lapS_derivWord_p_fluct_le hν hc1 hMF hMV tr ℓ k hw hs y (hF_bd y) (hV_bd y)
  exact PartI_T20_1.oscLinear_explicit hc hK_nn hQ_C2 hQ_per hgrad hlap z

/-- Qualitative global bound on `ageJet ℓ m tr.p s z` from `∀ r ≤ ℓ, VelOrderBoundedFixed tr r`. -/
theorem pressure_ageJet_bounded_of_vel {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ : ℕ) (hV : ∀ r ≤ ℓ, VelOrderBoundedFixed tr r) (m : ℕ) :
    ∃ L_p : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet ℓ m tr.p s z‖ ≤ L_p := by
  choose M_w hM_w using fun w : List Bool =>
    PressStepFixed.abs_derivWord_iteratedDeriv_p_le hν hc tr htr ℓ hV w
  refine ⟨∑ w ∈ wordsOfLength m, M_w w, fun s hs z => ?_⟩
  have hsm_p : PartI_T20.SmR (fun p : ℝ × Plane => tr.p p.1 p.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hslice_p : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun t => tr.p t x) s) :=
    PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  calc ‖ageJet ℓ m tr.p s z‖
      ≤ ∑ w ∈ wordsOfLength m,
          |B0151.derivWord w (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) z| :=
        (cylJetWord_proof (fun x => iteratedDeriv ℓ (fun t => tr.p t x) s) hslice_p m z).2
    _ ≤ ∑ w ∈ wordsOfLength m, M_w w :=
        Finset.sum_le_sum (fun w _ => hM_w w s hs z)

/-- Exponential decay of `ageJet ℓ k tr.p` on `s > 0` from `∀ r ≤ ℓ, VelFluctOrderDecayFixed tr r`
and `∀ r ≤ ℓ, VelOrderBoundedFixed tr r`. -/
theorem pressure_orderDecayFixed_of_velFluct {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ : ℕ) (hV : ∀ r ≤ ℓ, VelOrderBoundedFixed tr r)
    (hF : ∀ r ≤ ℓ, VelFluctOrderDecayFixed tr r) (k : ℕ) :
    ∃ C_p κ_p : ℝ, 0 < C_p ∧ 0 < κ_p ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane,
        ‖ageJet ℓ k tr.p s z‖ ≤ C_p * Real.exp (-(κ_p * s)) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨M_V0, hMV0, hV_rect⟩ := PartI_HF_1.uniform_vel_rect (k + 1) ℓ hV
  let M_V : ℝ := M_V0 + 1
  have hMV_pos : 0 < M_V := by dsimp [M_V]; linarith
  obtain ⟨C_F, κ_F, hCF, hκF, hF_rect⟩ := uniform_velFluct_rect (k + 1) ℓ hF
  obtain ⟨L_p, hLp⟩ := pressure_ageJet_bounded_of_vel hν hc tr htr ℓ hV (k + 1)
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_p : ℝ :=
    (2 : ℝ) ^ k * (2 : ℝ) ^ (ℓ + k) * C_F * M_V * (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hCp : 0 < C_p := by dsimp [C_p]; positivity
  refine ⟨C_p, κ_F, hCp, hκF, fun s hs z => ?_⟩
  let M_F : ℝ := C_F * Real.exp (-(κ_F * s))
  have hMF : 0 ≤ M_F := by dsimp [M_F]; positivity
  have hF_s : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w'‖ ≤ M_F :=
    fun w' r hr i hi => hF_rect s hs w' r hr i hi
  have hV_s : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s w'‖ ≤ M_V :=
    fun w' r hr i hi => (hV_rect s hs w' r hr i hi).trans (by dsimp [M_V]; linarith)
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  let B_word : ℝ :=
    (2 : ℝ) ^ (ℓ + k) * M_F * M_V * (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hword_bd : ∀ w ∈ wordsOfLength k, |B0151.derivWord w P_ℓ z| ≤ B_word := by
    intro w hw
    have hlen : w.length = k := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    have hmean_bd := abs_hmean_derivWord_p_fluct_le
      hν hc.le hMF hMV_pos.le tr htr ℓ k hlen hs z
      (fun w' r hr i hi => hF_s w' r hr i (by omega))
      (fun w' r hr i hi => hV_s w' r hr i (by omega))
    have hosc_bd := abs_osc_derivWord_p_fluct_le
      hν hc.le hMF hMV_pos.le tr ℓ k hlen hs z (hLp s hs) hF_s hV_s
    have htri : |B0151.derivWord w P_ℓ z| ≤
        |B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2| +
          |hmean c (B0151.derivWord w P_ℓ) z.2| := by
      have := abs_add_le (B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2)
        (hmean c (B0151.derivWord w P_ℓ) z.2)
      rwa [sub_add_cancel] at this
    calc |B0151.derivWord w P_ℓ z|
        ≤ (4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
            (2 : ℝ) ^ (ℓ + k) * M_F * M_V :=
          htri.trans (add_le_add hosc_bd hmean_bd)
      _ = B_word := by dsimp [B_word]; ring
  have hjet_word := (cylJetWord_proof P_ℓ hP_sm k z).2
  have hcard_nat : (wordsOfLength k).card ≤ 2 ^ k := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength k).card : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hcard_nat
  have hB_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  calc ‖ageJet ℓ k tr.p s z‖
      ≤ ∑ w ∈ wordsOfLength k, |B0151.derivWord w P_ℓ z| := hjet_word
    _ ≤ ∑ _w ∈ wordsOfLength k, B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
    _ = ((wordsOfLength k).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * B_word := mul_le_mul_of_nonneg_right hcard hB_nn
    _ = C_p * Real.exp (-(κ_F * s)) := by dsimp [B_word, M_F, C_p]; ring

/-! ### 4. Inductive step `ℓ → ℓ + 1` and strong induction for `VelFluctOrderDecayFixed` -/

theorem uniform_pressure_spatial {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (r : ℕ) (hV : ∀ m ≤ r, VelOrderBoundedFixed tr m)
    (hF : ∀ m ≤ r, VelFluctOrderDecayFixed tr m) :
    ∀ K : ℕ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K,
        ‖ageJet r i tr.p s z‖ ≤ C * Real.exp (-(κ * s))
  | 0 => by
    obtain ⟨C, κ, hC, hκ, h0⟩ := pressure_orderDecayFixed_of_velFluct hν hc tr htr r hV hF 0
    refine ⟨C, κ, hC, hκ, fun s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 s hs z
  | K + 1 => by
    obtain ⟨C₁, κ₁, hC₁, hκ₁, hIH⟩ := uniform_pressure_spatial hν hc tr htr r hV hF K
    obtain ⟨C₂, κ₂, _hC₂, hκ₂, hK1⟩ :=
      pressure_orderDecayFixed_of_velFluct hν hc tr htr r hV hF (K + 1)
    refine ⟨max C₁ C₂, min κ₁ κ₂, lt_max_of_lt_left hC₁, lt_min hκ₁ hκ₂,
      fun s hs z i hi => ?_⟩
    rcases Nat.of_le_succ hi with hiK | rfl
    · refine (hIH s hs z i hiK).trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le))
    · refine (hK1 s hs z).trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le))

theorem uniform_pressure_rect {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, VelOrderBoundedFixed tr r) →
      (∀ r ≤ L, VelFluctOrderDecayFixed tr r) →
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
        ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K,
          ‖ageJet r i tr.p s z‖ ≤ C * Real.exp (-(κ * s))
  | 0, hV, hF => by
    obtain ⟨C, κ, hC, hκ, h0⟩ := uniform_pressure_spatial hν hc tr htr 0 hV hF K
    refine ⟨C, κ, hC, hκ, fun s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 s hs z i hi
  | L + 1, hV, hF => by
    obtain ⟨C₁, κ₁, hC₁, hκ₁, h1⟩ := uniform_pressure_rect hν hc tr htr K L
      (fun r hr => hV r (Nat.le_succ_of_le hr))
      (fun r hr => hF r (Nat.le_succ_of_le hr))
    obtain ⟨C₂, κ₂, _hC₂, hκ₂, h2⟩ := uniform_pressure_spatial hν hc tr htr (L + 1) hV hF K
    refine ⟨max C₁ C₂, min κ₁ κ₂, lt_max_of_lt_left hC₁, lt_min hκ₁ hκ₂,
      fun s hs z r hr i hi => ?_⟩
    rcases Nat.of_le_succ hr with hrL | rfl
    · refine (h1 s hs z r hrL i hi).trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le))
    · refine (h2 s hs z i hi).trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_nonneg _)
        (le_of_lt (lt_max_of_lt_left hC₁)))
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le))

theorem velFluctOrderDecayFixed_succ {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ : ℕ) (hV : ∀ r ≤ ℓ, VelOrderBoundedFixed tr r)
    (hIH : ∀ r ≤ ℓ, VelFluctOrderDecayFixed tr r) :
    VelFluctOrderDecayFixed tr (ℓ + 1) := by
  intro j
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨M_V, hMV, hV_rect⟩ := PartI_HF_1.uniform_vel_rect (j + 1) ℓ hV
  obtain ⟨C_F, κ_F, hCF, hκF, hF_rect⟩ := uniform_velFluct_rect (j + 2) ℓ hIH
  obtain ⟨C_P, κ_P, _hCP, hκP, hP_rect⟩ := uniform_pressure_rect hν hc tr htr (j + 2) ℓ hV hIH
  let C_fl : ℝ := max C_F C_P
  let κ : ℝ := min κ_F κ_P
  have hCfl : 0 < C_fl := lt_max_of_lt_left hCF
  have hκ : 0 < κ := lt_min hκF hκP
  let C_out : ℝ := 12 * C_fl + 8 * (2 : ℝ) ^ (ℓ + j) * M_V * C_fl
  have hC_out : 0 < C_out := by dsimp [C_out]; positivity
  refine ⟨C_out, κ, hC_out, hκ, fun s hs z => ?_⟩
  let M_fl : ℝ := C_fl * Real.exp (-(κ * s))
  have hMfl : 0 ≤ M_fl := by dsimp [M_fl]; positivity
  have hFl_bd : ∀ w : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 2,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w‖ ≤ M_fl ∧
      ‖ageJet r i tr.p s w‖ ≤ M_fl := by
    intro w r hr i hi
    refine ⟨?_, ?_⟩
    · refine (hF_rect s hs w r hr i hi).trans
        (mul_le_mul (le_max_left _ _) ?_ (Real.exp_nonneg _) hCfl.le)
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le))
    · refine (hP_rect s hs w r hr i hi).trans
        (mul_le_mul (le_max_right _ _) ?_ (Real.exp_nonneg _) hCfl.le)
      exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le))
  have hsm_fl : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc0 tr
  have hvec := PartI_T22_2_1.norm_ageJet_vec_le_add_proj
    (V := fun r w => hfluct c (tr.v r) w) hsm_fl (ℓ + 1) j hs z
  have h0 := PartI_T22_2_1.norm_ageJet_succ_hfluct_v_comp_le hν hν1 hc0 hMV hMfl tr 0 ℓ j hs z
    (hV_rect s hs) hFl_bd
  have h1 := PartI_T22_2_1.norm_ageJet_succ_hfluct_v_comp_le hν hν1 hc0 hMV hMfl tr 1 ℓ j hs z
    (hV_rect s hs) hFl_bd
  have hpt : ‖ageJet (ℓ + 1) j (fun r => hfluct c (tr.v r)) s z‖ ≤
      12 * M_fl + 8 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := by linarith
  calc ‖ageJet (ℓ + 1) j (fun r => hfluct c (tr.v r)) s z‖
      ≤ 12 * M_fl + 8 * (2 : ℝ) ^ (ℓ + j) * M_V * M_fl := hpt
    _ = C_out * Real.exp (-(κ * s)) := by dsimp [M_fl, C_out]; ring

theorem velFluctOrderDecayFixed_all {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hV : ∀ ℓ : ℕ, VelOrderBoundedFixed tr ℓ)
    (h0 : VelFluctOrderDecayFixed tr 0) :
    ∀ ℓ : ℕ, VelFluctOrderDecayFixed tr ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ m =>
      exact velFluctOrderDecayFixed_succ hν hν1 hc tr htr m
        (fun r _ => hV r)
        (fun r hr => ih r (Nat.lt_succ_of_le hr))

/-! ### 5. Stream-fluctuation exponential decay at all `(ℓ, j)` from `VelFluctOrderDecayFixed` -/

theorem streamFluct_decay_of_velFluctOrderDecayFixed {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ)
    (hFl : VelFluctOrderDecayFixed tr ℓ) :
    ∃ C κ : ℝ, 0 < κ ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane,
        ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖ ≤
          C * Real.exp (-(κ * s)) := by
  cases j with
  | zero =>
    obtain ⟨C_v, κ, hCv, hκ, hv0⟩ := hFl 0
    refine ⟨c * C_v, κ, hκ, fun s hs z => ?_⟩
    let B : ℝ := C_v * Real.exp (-(κ * s))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hSupV : wSupNorm 0 (ageJet ℓ 0 (fun r => hfluct c (tr.v r)) s) ≤ ENNReal.ofReal B :=
      PartI_T22_2_1.wSupNorm_zero_le_of_norm_le (hv0 s hs)
    have hSupΨ := PartI_T22.wSupNorm_zero_ageJet_streamFluct_zero_le hν hc hB tr ℓ hs hSupV
    have hpt := PartI_T22_2_1.norm_le_of_wSupNorm_zero_le (mul_nonneg hc.le hB) hSupΨ z
    calc ‖ageJet ℓ 0 (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖
        ≤ c * B := hpt
      _ = (c * C_v) * Real.exp (-(κ * s)) := by dsimp [B]; ring
  | succ k =>
    obtain ⟨C_v, κ, _hCv, hκ, hvk⟩ := hFl k
    refine ⟨2 * C_v, κ, hκ, fun s hs z => ?_⟩
    calc ‖ageJet ℓ (k + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖
        ≤ 2 * ‖ageJet ℓ k (fun r => hfluct c (tr.v r)) s z‖ :=
          PartI_T22.norm_ageJet_streamFluct_succ_le hν hc tr ℓ k hs z
      _ ≤ 2 * (C_v * Real.exp (-(κ * s))) :=
          mul_le_mul_of_nonneg_left (hvk s hs z) (by norm_num)
      _ = (2 * C_v) * Real.exp (-(κ * s)) := by ring

end TrainFluctAgeJetFixedAux

/-- **Fixed-parameter all-order exponential decay of mixed age/spatial jets of `ψ − \bar ψ`
(`trainFluctAgeJetFixed`, Task `PartI:HF/2`)**:
source lines 439–446, 516–526, 429–435 of `the November 2 reference manuscript`. -/
theorem trainFluctAgeJetFixed : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed := by
  intro ρ hρ
  have hFD : OverlapFluctuationDecay := overlap_fluctuation_decay overlapHighNormUniform_proof
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD
      (overlap_mean_decay_of overlapHighNormUniform_proof hFD overlap_mean_primitive
        overlap_mean_duhamel_split)
  obtain ⟨C₀, lam₀, ν_fl0, hC₀, hlam₀, hν_fl0, hJ0⟩ :=
    PartI_T13.overlapFluctuation_jetEnergy_zero_decay
      overlapFluctuationSmoothL2_proof
      (overlapFluctuationEnergyBalance_proof overlapFluctuationSmoothL2_proof)
      overlapHighNormUniform_proof ρ hρ
  obtain ⟨Cj, ν_bd, hCj, hν_bd, hbd1⟩ := supNormD_pointwise_bound_j hOv ρ hρ 1 le_rfl
  obtain ⟨ν_HF1, hν_HF1, hHF1⟩ := trainJetsBoundedFixed ρ hρ
  let ν₀ : ℝ := min (min ν_fl0 ν_bd) (min ν_HF1 (1 / 2))
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_fl0 hν_bd) (lt_min hν_HF1 (by norm_num))
  refine ⟨ν₀, hν₀, fun ν hν hν_le tr htr ℓ j => ?_⟩
  have hν_fl0_le : ν ≤ ν_fl0 := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_bd_le : ν ≤ ν_bd := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_HF1_le : ν ≤ ν_HF1 := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := by linarith
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    change 1 < trainPeriod ρ ν
    unfold trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  let s_c := B0146.overlapAge ν c
  have hsc_pos : 0 < s_c := by
    dsimp [s_c]
    unfold B0146.overlapAge
    have hc2 : 1 < c ^ 2 := one_lt_pow₀ hc1 (by norm_num)
    exact div_pos (by linarith) hν
  have hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (Cj * (1 + t) ^ (-(3 / 2 : ℝ))) := by
    intro t ht
    let s : ℝ := s_c + c ^ 2 * t / ν
    have hs_ge : s_c ≤ s := by
      dsimp [s]
      have : 0 ≤ c ^ 2 * t / ν := by positivity
      linarith
    have hs_nn : 0 ≤ s := hsc_pos.le.trans hs_ge
    have ht_eq : ν * (s - s_c) / c ^ 2 = t := by
      dsimp [s]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    have hpost1 := (hbd1 ν hν hν_bd_le tr htr s hs_nn).2 hs_ge
    rw [ht_eq] at hpost1
    have hscale : overlapField ν c tr.v t = scaleField c (tr.v s) := rfl
    calc B0277.supNormD 1 (overlapField ν c tr.v t)
        = B0277.supNormD 1 (scaleField c (tr.v s)) := by rw [hscale]
      _ ≤ ENNReal.ofReal (c ^ 3 * c ^ 1) * B0277.supNormD 1 (tr.v s) :=
          supNormD_scaleField_le hc0.le 1 (tr.v s)
      _ ≤ ENNReal.ofReal (c ^ 3 * c ^ 1) *
            ENNReal.ofReal (Cj * (c ^ 4)⁻¹ * (1 + t) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = ENNReal.ofReal (Cj * (1 + t) ^ (-(3 / 2 : ℝ))) := by
          have h1t : 0 ≤ 1 + t := by linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hc4_ne : c ^ 4 ≠ 0 := pow_ne_zero 4 hc0.ne'
          field_simp
  have hV_all : ∀ r : ℕ, VelOrderBoundedFixed tr r :=
    fun r i => hHF1 ν hν hν_HF1_le tr htr r i
  have hFl0 : TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr 0 :=
    TrainFluctAgeJetFixedAux.velFluctOrderDecayFixed_zero hν hc1 tr htr hC₀ hlam₀ hCj.le
      (hJ0 ν hν hν_fl0_le tr htr) hGrad (hV_all 0)
  have hFl_all : ∀ r : ℕ, TrainFluctAgeJetFixedAux.VelFluctOrderDecayFixed tr r :=
    TrainFluctAgeJetFixedAux.velFluctOrderDecayFixed_all hν hν1 hc1 tr htr hV_all hFl0
  exact TrainFluctAgeJetFixedAux.streamFluct_decay_of_velFluctOrderDecayFixed
    hν hc0 tr ℓ j (hFl_all ℓ)

end UnforcedLeray.Short.PartI

end
