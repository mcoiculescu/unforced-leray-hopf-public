import Mathlib.Analysis.Calculus.ContDiff.Bounds
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed
import UnforcedLeray.Short.PartI.Sub.PartI_T15
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Sub.PartI_T25_3
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainStrainIntegralProof

/-!
# `Short/PartI/Sub/PartI_HF_1.lean` — Sub-module for Task `PartI:HF/1` (`TrainJetsBoundedFixed`)

Source of record: `the November 2 reference manuscript`, lines 427–435, 326–359,
318–322, 255–258.

Fixed-parameter all-order boundedness of mixed age/spatial jets of `tr.v` for `s > 0`
(`TrainJetsBoundedFixed`):
1. **Integrable-strain Grönwall lemma (`tame_gronwall_rpow`)**: if `E(t) ≥ 0` satisfies
   `d/dt E(t) ≤ A (1 + t)^{-3/2} E(t)` on `t ≥ 0` (`A ≥ 0`), integrating with the factor
   `exp(2 A (1 + t)^{-1/2})` yields `E(T) ≤ E(0) exp(2 A)` for all `T ≥ 0`.
2. **All-order post-overlap `H^k` propagation (`overlap_sobolevSq_fixed_of_grad_rpow`)**:
   combining `overlap_tame_energy_inequality k` (`PartI:T10`) with `tame_gronwall_rpow` shows that
   once `supNormD 1 (overlapField ν c tr.v t) ≤ ofReal (C₁ (1 + t)^{-3/2})` holds for all `t ≥ 0`,
   every higher unit-cylinder Sobolev norm `cylSobolevSq k (U T)` is bounded for all `T ≥ 0` by
   `cylSobolevSq k (U 0) * exp(4 C_k eC ν c C₁)`, with no `k`-dependent smallness condition on `ν`.
3. **All-order post-overlap `supNormD j` bound (`overlap_supNormD_fixed_of_grad_rpow`)**:
   combining `overlap_sobolevSq_fixed_of_grad_rpow` at `k = max (j + 2) 3` with
   `jetSupBridge_proof j` and `supRhs_one_le_sqrt` bounds `B0277.supNormD j (U T)` uniformly in
   `T ≥ 0` for every spatial order `j : ℕ`.
4. **Base age order `ℓ = 0` (`trainJetsBoundedFixed_zero_of_overlap`)**:
   fixes a single viscosity threshold `ν₀ > 0` from `TrainOverlap` at base order `j = 1`, combines
   `IsBUCTrain.deriv_bound` on `[0, s_c]` with `overlap_supNormD_fixed_of_grad_rpow` and
   `scaleField` rescaling on `[s_c, ∞)` to establish `VelOrderBoundedFixed tr 0` (`∀ j, ∃ M, ...`)
   at every fixed `0 < ν ≤ ν₀`.
5. **Unconditional advection age-step (`trainVelAgeStepAdvFixed_proof : TrainVelAgeStepAdvFixed`)**:
   proves the spacetime Leibniz product rule `PartI_HF_1.norm_ageJet_mul_le` on jointly smooth
   scalar families (`SmS`) and bounds `ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z`
   from `∀ r ≤ ℓ, VelOrderBoundedFixed tr r`.
6. **Higher age orders (`ℓ ≥ 1`) by induction on `ℓ`**:
   proves the momentum identity `ageJet_succ_vel_eq`, the pressure-gradient domination
   `norm_ageJet_gradS_tr_p_le`, and the triangle-plus-viscous step `norm_ageJet_succ_vel_le`, and
   reduces `TrainJetsBoundedFixed` via strong induction on `ℓ` (`trainJetsBoundedFixed_of`) to
   `OverlapMeanDuhamelSplit` (`PartI:T15/1`) and `TrainVelAgeStepPressFixed` (`PartI:HF/1/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec Vc pc Qc width jap jet cellL2 wCellL2)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Dx eT eQ eE Sm Dv hasDerivAt_slice
  vb_slice_contDiffAt vb_slice_smooth_at vb_ageJet_sub norm_jet_vec_le)

/-! ### 1. Integrable-strain Grönwall lemma on `[0, ∞)` -/

/-- **Integrable-strain Grönwall inequality on `[0, ∞)`**:
if `E(T) ≥ 0` and `d/dT E(T) ≤ A * (1 + T)^{-3/2} * E(T)` for all `T ≥ 0` with `A ≥ 0`, then
`E(T) ≤ E(0) * exp(2 * A)` for all `T ≥ 0`. -/
theorem tame_gronwall_rpow {E : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hEnn : ∀ T : ℝ, 0 ≤ T → 0 ≤ E T)
    (hderiv : ∀ T : ℝ, 0 ≤ T →
      ∃ D : ℝ, HasDerivAt E D T ∧ D ≤ A * (1 + T) ^ (-(3 / 2 : ℝ)) * E T) :
    ∀ T : ℝ, 0 ≤ T → E T ≤ E 0 * Real.exp (2 * A) := by
  let φ : ℝ → ℝ := fun t => 2 * A * (1 + t) ^ (-(1 / 2 : ℝ))
  let g : ℝ → ℝ := fun t => E t * Real.exp (φ t)
  have hg_step : ∀ t : ℝ, 0 ≤ t → ∃ G : ℝ, HasDerivAt g G t ∧ G ≤ 0 := by
    intro t ht0
    obtain ⟨D, hD, hDle⟩ := hderiv t ht0
    have h1t_pos : 0 < 1 + t := by linarith
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    have hrpow : HasDerivAt (fun s : ℝ => (1 + s) ^ (-(1 / 2 : ℝ)))
        (1 * (-(1 / 2 : ℝ)) * (1 + t) ^ (-(1 / 2 : ℝ) - 1)) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl h1t_pos.ne')
    have hφ : HasDerivAt φ
        (2 * A * (1 * (-(1 / 2 : ℝ)) * (1 + t) ^ (-(1 / 2 : ℝ) - 1))) t :=
      hrpow.const_mul (2 * A)
    have hexp : HasDerivAt (fun s => Real.exp (φ s))
        (Real.exp (φ t) * (2 * A * (1 * (-(1 / 2 : ℝ)) * (1 + t) ^ (-(1 / 2 : ℝ) - 1)))) t :=
      HasDerivAt.exp hφ
    refine ⟨D * Real.exp (φ t) +
        E t * (Real.exp (φ t) * (2 * A * (1 * (-(1 / 2 : ℝ)) * (1 + t) ^ (-(1 / 2 : ℝ) - 1)))),
      hD.mul hexp, ?_⟩
    have hexp_sub : (-(1 / 2 : ℝ) - 1) = -(3 / 2 : ℝ) := by ring
    rw [hexp_sub]
    have hsimp : 2 * A * (1 * (-(1 / 2 : ℝ)) * (1 + t) ^ (-(3 / 2 : ℝ))) =
        -(A * (1 + t) ^ (-(3 / 2 : ℝ))) := by ring
    rw [hsimp]
    have hexp_pos : 0 < Real.exp (φ t) := Real.exp_pos _
    nlinarith
  have hanti : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      obtain ⟨G, hG, _⟩ := hg_step t ht
      exact hG.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨G, hG, _⟩ := hg_step t (mem_Ici.1 (interior_subset ht))
      exact hG.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨G, hG, hGle⟩ := hg_step t (mem_Ici.1 (interior_subset ht))
      rwa [hG.deriv]
  intro T hT
  have hgT : g T ≤ g 0 := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hT) hT
  have hφ0 : φ 0 = 2 * A := by
    dsimp [φ]
    rw [add_zero, Real.one_rpow, mul_one]
  have hg0 : g 0 = E 0 * Real.exp (2 * A) := by
    dsimp [g]
    rw [hφ0]
  have hφT_nn : 0 ≤ φ T := by
    dsimp [φ]
    have h1T : 0 ≤ 1 + T := by linarith
    positivity
  have hexp_ge1 : 1 ≤ Real.exp (φ T) := Real.one_le_exp hφT_nn
  have hET_le : E T ≤ g T := by
    dsimp [g]
    calc E T = E T * 1 := (mul_one _).symm
      _ ≤ E T * Real.exp (φ T) := mul_le_mul_of_nonneg_left hexp_ge1 (hEnn T hT)
  exact hET_le.trans (hgT.trans_eq hg0)

/-! ### 2. All-order post-overlap `H^k` and `supNormD j` propagation at fixed `ν` -/

/-- Pointwise bound on `|wordComp [β] f m z|` from `B0277.supNormD 1 f ≤ ENNReal.ofReal G` for
smooth `f : Plane → Vec` and `G ≥ 0`. -/
theorem abs_wordComp_singleton_le_of_supNormD_le {f : Plane → Vec} (hf : ContDiff ℝ ∞ f)
    {G : ℝ} (hG : 0 ≤ G) (hSup : B0277.supNormD 1 f ≤ ENNReal.ofReal G)
    (β : Bool) (m : Fin 2) (z : Plane) :
    |wordComp [β] f m z| ≤ G := by
  have hproj : ‖(EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x m)
  have hg : ContDiff ℝ ∞ (fun x => f x m) :=
    (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf
  have hw_le := (cylJetWord_proof (fun x => f x m) hg 1 z).1 [β] rfl
  have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (f := f) (x := z) (n := 1) hf.contDiffAt (by exact_mod_cast le_top)
  have h1 : ‖iteratedFDeriv ℝ 1 (fun x => f x m) z‖ ≤ ‖iteratedFDeriv ℝ 1 f z‖ := by
    calc ‖iteratedFDeriv ℝ 1 (fun x => f x m) z‖
        ≤ ‖(EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ 1 f z‖ := hcomp
      _ ≤ 1 * ‖iteratedFDeriv ℝ 1 f z‖ :=
          mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ 1 f z‖ := one_mul _
  have h2 : ‖iteratedFDeriv ℝ 1 f z‖ ≤ G :=
    B0277.norm_le_of_supNormD_le hG hSup z
  exact (hw_le.trans h1).trans h2

/-- **All-order post-overlap `H^k` propagation (`overlap_sobolevSq_fixed_of_grad_rpow`)**:
at any fixed `0 < ν` and `1 < c`, if `B0277.supNormD 1 (overlapField ν c tr.v t) ≤ ofReal (C₁ (1+t)^{-3/2})`
for all `t ≥ 0` (`C₁ ≥ 0`), then for every `k : ℕ` there exists `E_k > 0` (independent of `T ≥ 0`)
such that `cylSobolevSq k (overlapField ν c tr.v T) ≤ E_k` for all `T ≥ 0`. -/
theorem overlap_sobolevSq_fixed_of_grad_rpow {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))))
    (k : ℕ) :
    ∃ E_k : ℝ, 0 < E_k ∧
      ∀ T : ℝ, 0 ≤ T → cylSobolevSq k (overlapField ν c tr.v T) ≤ E_k := by
  obtain ⟨Ct, hCt, htame⟩ := overlap_tame_energy_inequality k
  set U := overlapField ν c tr.v
  let A : ℝ := 2 * Ct * eC ν c * C₁
  have hc0 : 0 < c := zero_lt_one.trans hc
  have heC_nn : 0 ≤ eC ν c := by
    unfold eC
    positivity
  have hA_nn : 0 ≤ A := by
    dsimp [A]
    positivity
  have hderiv : ∀ t : ℝ, 0 ≤ t →
      ∃ D : ℝ, HasDerivAt (fun s => cylSobolevSq k (U s)) D t ∧
        D ≤ A * (1 + t) ^ (-(3 / 2 : ℝ)) * cylSobolevSq k (U t) := by
    intro t ht
    have hcs := overlapField_cellSmoothL2 hν hc tr htr ht
    have hGt_nn : 0 ≤ C₁ * (1 + t) ^ (-(3 / 2 : ℝ)) := by
      have : 0 ≤ 1 + t := by linarith
      positivity
    have hG : ∀ (β : Bool) (m : Fin 2) (z : Plane),
        |wordComp [β] (U t) m z| ≤ C₁ * (1 + t) ^ (-(3 / 2 : ℝ)) :=
      fun β m z => abs_wordComp_singleton_le_of_supNormD_le hcs.1 hGt_nn (hGrad t ht) β m z
    obtain ⟨D, hD, hdiss⟩ := htame hν hc tr htr ht hG
    have hdiss_nn : 0 ≤ cylDissipationSq k (U t) := cylDissipationSq_nonneg k (U t)
    have hDle : D ≤ 2 * Ct * eC ν c * (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))) * cylSobolevSq k (U t) := by
      linarith
    refine ⟨D, hD, ?_⟩
    calc D ≤ 2 * Ct * eC ν c * (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))) * cylSobolevSq k (U t) := hDle
      _ = A * (1 + t) ^ (-(3 / 2 : ℝ)) * cylSobolevSq k (U t) := by dsimp [A]; ring
  have hgron := tame_gronwall_rpow hA_nn (fun t _ => cylSobolevSq_nonneg k (U t)) hderiv
  refine ⟨cylSobolevSq k (U 0) * Real.exp (2 * A) + 1, ?_, fun T hT => ?_⟩
  · have h0 : 0 ≤ cylSobolevSq k (U 0) := cylSobolevSq_nonneg k (U 0)
    positivity
  · linarith [hgron T hT]

/-- **All-order post-overlap `supNormD j` bound (`overlap_supNormD_fixed_of_grad_rpow`)**:
at any fixed `0 < ν` and `1 < c`, if `B0277.supNormD 1 (overlapField ν c tr.v t) ≤ ofReal (C₁ (1+t)^{-3/2})`
for all `t ≥ 0` (`C₁ ≥ 0`), then for every `j : ℕ` there exists `M_post > 0` (independent of `T ≥ 0`)
such that `B0277.supNormD j (overlapField ν c tr.v T) ≤ ENNReal.ofReal M_post` for all `T ≥ 0`. -/
theorem overlap_supNormD_fixed_of_grad_rpow {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hGrad : ∀ t : ℝ, 0 ≤ t →
      B0277.supNormD 1 (overlapField ν c tr.v t) ≤
        ENNReal.ofReal (C₁ * (1 + t) ^ (-(3 / 2 : ℝ))))
    (j : ℕ) :
    ∃ M_post : ℝ, 0 < M_post ∧
      ∀ T : ℝ, 0 ≤ T → B0277.supNormD j (overlapField ν c tr.v T) ≤ ENNReal.ofReal M_post := by
  let N' : ℕ := max (j + 2) 3
  obtain ⟨E₀, hE₀, hsob⟩ := overlap_sobolevSq_fixed_of_grad_rpow hν hc tr htr hC₁ hGrad N'
  obtain ⟨Csup, hCsup, hbridge_sup⟩ := jetSupBridge_proof j
  let M_post : ℝ := (2 * Csup + 1) * Real.sqrt E₀
  have hM_pos : 0 < M_post := by
    dsimp [M_post]
    positivity
  refine ⟨M_post, hM_pos, fun T hT => ?_⟩
  let U := overlapField ν c tr.v T
  have hcs := overlapField_cellSmoothL2 hν hc tr htr hT
  have hE := hsob T hT
  have hj0 : j ≤ N' := by omega
  have hj1 : j + 1 ≤ N' := by omega
  have hj2 : j + 2 ≤ N' := le_max_left _ _
  have hJ0 : jetEnergy 1 j U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj0 U).trans hE
  have hJ1 : jetEnergy 1 (j + 1) U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj1 U).trans hE
  have hJ2 : jetEnergy 1 (j + 2) U ≤ E₀ := (jetEnergy_le_cylSobolevSq hj2 U).trans hE
  calc B0277.supNormD j U
      ≤ ENNReal.ofReal (supRhs Csup 1 (jetEnergy 1 j U)
          (jetEnergy 1 (j + 1) U) (jetEnergy 1 (j + 2) U)) :=
        (hbridge_sup 1 le_rfl U hcs).2
    _ ≤ ENNReal.ofReal M_post := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := supRhs_one_le_sqrt hCsup hE₀.le hJ0 hJ1 hJ2
        have h2 : 2 * Csup * Real.sqrt E₀ ≤ M_post := by
          dsimp [M_post]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
        exact h1.trans h2

/-! ### 3. Base age order `ℓ = 0`: all spatial jets bounded on `s > 0` at fixed `ν ≤ ν₀` -/

/-- Fixed-parameter all-spatial-order boundedness of `ageJet r j tr.v` on `s > 0` at age order `r`. -/
def VelOrderBoundedFixed {ν c : ℝ} (tr : B0140.TrainSol ν c) (r : ℕ) : Prop :=
  ∀ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet r j tr.v s z‖ ≤ M

/-- From `TrainOverlap` (applied only at the single base order `j = 1`), for every `ρ > 1/2` there
exists `ν₀ > 0` such that for all `0 < ν ≤ ν₀` and every `BUC` train `tr`, `VelOrderBoundedFixed tr 0`
holds (i.e. all spatial derivatives `ageJet 0 j tr.v` are globally bounded on `s > 0` × `Plane`). -/
theorem trainJetsBoundedFixed_zero_of_overlap (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        VelOrderBoundedFixed tr 0 := by
  obtain ⟨Cj, ν_bd, hCj, hν_bd, hbd1⟩ := supNormD_pointwise_bound_j hOv ρ hρ 1 le_rfl
  refine ⟨min ν_bd (1 / 2), lt_min hν_bd (by norm_num), fun ν hν hν_le tr htr j => ?_⟩
  have hν_bd_le : ν ≤ ν_bd := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
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
  -- 1. Base-order (`j = 1`) decay of `U(t) = overlapField ν c tr.v t` for all `t ≥ 0`
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
  -- 2. Post-overlap bound on `B0277.supNormD j (overlapField ν c tr.v T)` for all `T ≥ 0`
  obtain ⟨M_post, hM_post, hPost⟩ :=
    overlap_supNormD_fixed_of_grad_rpow hν hc1 tr htr hCj.le hGrad j
  -- 3. Pre-overlap bound on `[0, s_c]` from `IsBUCTrain.deriv_bound`
  obtain ⟨M_pre, hPre⟩ := IsBUCTrain.deriv_bound htr hsc_pos.le j
  refine ⟨max M_pre M_post, fun s hs z => ?_⟩
  change ‖iteratedFDeriv ℝ j (tr.v s) z‖ ≤ max M_pre M_post
  rcases le_total s s_c with hs_le | hs_ge
  · exact (hPre s ⟨hs.le, hs_le⟩ z).trans (le_max_left _ _)
  · let T : ℝ := ν * (s - s_c) / c ^ 2
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
    have hv_scale : tr.v s = scaleField c⁻¹ U := by
      funext w
      rw [hU_scale]
      dsimp [scaleField]
      have hc_ne : c ≠ 0 := hc0.ne'
      have hcw : c • (c⁻¹ • w) = w := smul_inv_smul₀ hc_ne w
      rw [hcw, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hc_ne), one_smul]
    have hcinv_le1 : (c⁻¹) ^ 3 * (c⁻¹) ^ j ≤ 1 := by
      have hcinv1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1.le
      have hcinv_nn : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
      have h1 : (c⁻¹) ^ 3 ≤ 1 := pow_le_one₀ hcinv_nn hcinv1
      have h2 : (c⁻¹) ^ j ≤ 1 := pow_le_one₀ hcinv_nn hcinv1
      have h3 : 0 ≤ (c⁻¹) ^ j := pow_nonneg hcinv_nn j
      nlinarith
    have hv_sup : B0277.supNormD j (tr.v s) ≤ ENNReal.ofReal M_post := by
      have hle_scale : ENNReal.ofReal ((c⁻¹) ^ 3 * (c⁻¹) ^ j) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal hcinv_le1
      have hle_U : B0277.supNormD j U ≤ ENNReal.ofReal M_post := hPost T hT_nn
      calc B0277.supNormD j (tr.v s)
          = B0277.supNormD j (scaleField c⁻¹ U) := by rw [← hv_scale]
        _ ≤ ENNReal.ofReal ((c⁻¹) ^ 3 * (c⁻¹) ^ j) * B0277.supNormD j U :=
            supNormD_scaleField_le (inv_nonneg.2 hc0.le) j U
        _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal M_post := mul_le_mul' hle_scale hle_U
        _ = ENNReal.ofReal M_post := by rw [ENNReal.ofReal_one, one_mul]
    exact (B0277.norm_le_of_supNormD_le hM_post.le hv_sup z).trans (le_max_right _ _)

/-! ### 4. Higher age derivatives (`ℓ ≥ 1`): momentum identity and viscous step -/

/-- On `s > 0`, the time derivative of `tr.v` satisfies
`deriv (fun t => tr.v t z) s = ν • Train.vecLaplacian (tr.v s) z - Train.advection (tr.v s) z - Train.gradS (tr.p s) z`. -/
theorem deriv_vel_eq_momentum_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 < s) (z : Plane) :
    deriv (fun t => tr.v t z) s =
      ν • Train.vecLaplacian (tr.v s) z
      - Train.advection (tr.v s) z
      - Train.gradS (tr.p s) z := by
  have hmom : Train.momentumResidual ν tr.v tr.p s z = 0 := tr.isTrain.momentum s hs z
  unfold Train.momentumResidual at hmom
  ext k
  have hk := congrArg (fun v : Vec => v k) hmom
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply] at hk ⊢
  linarith

/-- Iterated age derivative of `tr.v` at order `ℓ + 1` on `s > 0` via the momentum equation. -/
theorem iteratedDeriv_succ_vel_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv (ℓ + 1) (fun r => tr.v r z) s =
      iteratedDeriv ℓ (fun r =>
        ν • Train.vecLaplacian (tr.v r) z
        - Train.advection (tr.v r) z
        - Train.gradS (tr.p r) z) s := by
  rw [iteratedDeriv_succ']
  have hev : deriv (fun r => tr.v r z) =ᶠ[nhds s]
      fun r =>
        ν • Train.vecLaplacian (tr.v r) z
        - Train.advection (tr.v r) z
        - Train.gradS (tr.p r) z := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_vel_eq_momentum_rhs tr hr z
  exact hev.iteratedDeriv_eq ℓ

/-- Exact decomposition of `ageJet (ℓ + 1) j tr.v s z` on `s > 0` into the viscous, advection,
and pressure-gradient age-jets at age order `ℓ`. -/
theorem ageJet_succ_vel_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet (ℓ + 1) j tr.v s z =
      ageJet ℓ j (fun r w => ν • Train.vecLaplacian (tr.v r) w) s z
      - ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z
      - ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z := by
  let F₁ : ℝ → Plane → Vec := fun r w => ν • Train.vecLaplacian (tr.v r) w
  let F₂ : ℝ → Plane → Vec := fun r w => Train.advection (tr.v r) w
  let F₃ : ℝ → Plane → Vec := fun r w => Train.gradS (tr.p r) w
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm₁ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2) :=
    PartI_T25_1.sm_smul_vecLaplacian hsm_v ν
  have hsm₂ : Sm (fun x : ℝ × Plane => F₂ x.1 x.2) :=
    PartI_T25_1.sm_advection hsm_v
  have hsm₃ : Sm (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    contDiffOn_gradS_of_smS hsm_p
  have hsm₁₂ : Sm (fun x : ℝ × Plane => F₁ x.1 x.2 - F₂ x.1 x.2) := hsm₁.sub hsm₂
  have hstep : ageJet (ℓ + 1) j tr.v s z =
      ageJet ℓ j (fun r w => F₁ r w - F₂ r w - F₃ r w) s z := by
    unfold ageJet
    congr 1
    funext w
    exact iteratedDeriv_succ_vel_eq tr ℓ hs w
  have hsub2 := vb_ageJet_sub (fun r w => F₁ r w - F₂ r w) F₃ hsm₁₂ hsm₃ hs ℓ j z
  have hsub1 := vb_ageJet_sub F₁ F₂ hsm₁ hsm₂ hs ℓ j z
  rw [hstep, hsub2, hsub1]

/-- Pointwise bound on `‖ageJet (ℓ + 1) j tr.v s z‖` for `s > 0` and `ν ≥ 0`:
`‖ageJet (ℓ + 1) j tr.v s z‖ ≤ (2 * ν) * ‖ageJet ℓ (j + 2) tr.v s z‖ + ‖ageJet ℓ j (advection tr.v) s z‖ + ‖ageJet ℓ j (gradS tr.p) s z‖`. -/
theorem norm_ageJet_succ_vel_le {ν c : ℝ} (tr : B0140.TrainSol ν c) (hν : 0 ≤ ν)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet (ℓ + 1) j tr.v s z‖ ≤
      (2 * ν) * ‖ageJet ℓ (j + 2) tr.v s z‖
      + ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z‖
      + ‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ := by
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hvisc := PartI_T25_1.norm_ageJet_smul_vecLaplacian_le hsm_v hν ℓ j hs z
  rw [ageJet_succ_vel_eq tr ℓ j hs z]
  have htri1 := norm_sub_le
    (ageJet ℓ j (fun r w => ν • Train.vecLaplacian (tr.v r) w) s z -
      ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z)
    (ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z)
  have htri2 := norm_sub_le
    (ageJet ℓ j (fun r w => ν • Train.vecLaplacian (tr.v r) w) s z)
    (ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z)
  linarith

/-- Pointwise domination of the pressure-gradient age-jet by the pressure age-jet at spatial order
`j + 1` on `s > 0`: `‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ ≤ 2 * ‖ageJet ℓ (j + 1) tr.p s z‖`. -/
theorem norm_ageJet_gradS_tr_p_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ ≤
      2 * ‖ageJet ℓ (j + 1) tr.p s z‖ := by
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  exact norm_ageJet_gradS_le hsm_p ℓ j hs z

/-! ### 5. Unconditional proof of the advection age-step (`TrainVelAgeStepAdvFixed`) -/

namespace PartI_HF_1

theorem SmS.add {P Q : ℝ × Plane → ℝ} (hP : SmS P) (hQ : SmS Q) : SmS (fun x => P x + Q x) :=
  ContDiffOn.add hP hQ

theorem SmS.mul {P Q : ℝ × Plane → ℝ} (hP : SmS P) (hQ : SmS Q) : SmS (fun x => P x * Q x) :=
  ContDiffOn.mul hP hQ

theorem ageJet_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) UU)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) UU)
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : Plane) :
    ageJet ℓ j (fun r v => F r v + G r v) s w =
      ageJet ℓ j F s w + ageJet ℓ j G s w := by
  have hadd : ∀ v : Plane, iteratedDeriv ℓ (fun r => F r v + G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s + iteratedDeriv ℓ (fun r => G r v) s := by
    intro v
    exact iteratedDeriv_add (vb_slice_smooth_at F hF hs v ℓ) (vb_slice_smooth_at G hG hs v ℓ)
  have hjet : (fun v : Plane => iteratedDeriv ℓ (fun r => F r v + G r v) s) =
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) +
        (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hadd
  have hA : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs w
  unfold ageJet jet
  rw [hjet, iteratedFDeriv_add_apply hA hB]

theorem contDiff_slice_of_smS {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (F t) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => mem_UU ht)

theorem partialQ_slice_eq_DxS {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialQ (F t) w = DxS eQ (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_smS hF ht
  rw [Cyl.partialQ_eq_fderiv (hu.differentiable (by simp)) w]
  exact slice_DvS hF ht ((1 : ℝ), (0 : ℝ)) w

theorem partialEta_slice_eq_DxS {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialEta (F t) w = DxS eE (fun x : ℝ × Plane => F x.1 x.2) (t, w) := by
  have hu : ContDiff ℝ ∞ (F t) := contDiff_slice_of_smS hF ht
  rw [Cyl.partialEta_eq_fderiv (hu.differentiable (by simp)) w]
  exact slice_DvS hF ht ((0 : ℝ), (1 : ℝ)) w

theorem smS_partialQ {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) :
    SmS (fun x : ℝ × Plane => Cyl.partialQ (F x.1) x.2) :=
  (hF.dx eQ).congr fun ⟨_t, w⟩ hx => partialQ_slice_eq_DxS hF hx.1 w

theorem smS_partialEta {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) :
    SmS (fun x : ℝ × Plane => Cyl.partialEta (F x.1) x.2) :=
  (hF.dx eE).congr fun ⟨_t, w⟩ hx => partialEta_slice_eq_DxS hF hx.1 w

theorem iteratedDeriv_partialQ_eq {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Cyl.partialQ (F r) w) s =
      Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hev : (fun r => Cyl.partialQ (F r) w) =ᶠ[nhds s] fun r => DxS eQ U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using partialQ_slice_eq_DxS hF hr w
  rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_slice_eq_DtS (hF.dx eQ) ℓ hs w,
    ← DtS_comm_DxS hF eQ ℓ (mem_UU hs)]
  have hsl := partialQ_slice_eq_DxS (F := fun r x => DtS ℓ U (r, x)) (SmS_DtS hF ℓ) hs w
  rw [← hsl]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtS hF ℓ hs x).symm

theorem iteratedDeriv_partialEta_eq {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2)) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => Cyl.partialEta (F r) w) s =
      Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) w := by
  let U : ℝ × Plane → ℝ := fun x => F x.1 x.2
  have hev : (fun r => Cyl.partialEta (F r) w) =ᶠ[nhds s] fun r => DxS eE U (r, w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr using partialEta_slice_eq_DxS hF hr w
  rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_slice_eq_DtS (hF.dx eE) ℓ hs w,
    ← DtS_comm_DxS hF eE ℓ (mem_UU hs)]
  have hsl := partialEta_slice_eq_DxS (F := fun r x => DtS ℓ U (r, x)) (SmS_DtS hF ℓ) hs w
  rw [← hsl]
  congr 1
  funext x
  exact (iteratedDeriv_slice_eq_DtS hF ℓ hs x).symm

theorem norm_jet_Dv_scalar_le {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (v : Plane) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (Dv v u) z‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) u z‖ := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hu).2
  have e : Dv v u = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ u) := rfl
  rw [e, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := z) (n := j)]
  refine ((ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left
    (hfd.contDiffAt) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  simpa [mul_comm] using f.le_opNorm v

theorem norm_ageJet_partialQ_le {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Cyl.partialQ (F r) w) s z‖ ≤
      ‖ageJet ℓ (j + 1) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Cyl.partialQ (F r) w) s) =
      Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext fun w => iteratedDeriv_partialQ_eq hF ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hQ : Cyl.partialQ (fun x => iteratedDeriv ℓ (fun r => F r x) s) =
      Dv ((1 : ℝ), (0 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext (Cyl.partialQ_eq_fderiv (hu.differentiable (by simp)))
  have n1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hb := norm_jet_Dv_scalar_le hu ((1 : ℝ), (0 : ℝ)) j z
  rw [n1, one_mul] at hb
  unfold ageJet jet
  rw [hslice, hQ]
  exact hb

theorem norm_ageJet_partialEta_le {F : ℝ → Plane → ℝ}
    (hF : SmS (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => Cyl.partialEta (F r) w) s z‖ ≤
      ‖ageJet ℓ (j + 1) F s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => Cyl.partialEta (F r) w) s) =
      Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext fun w => iteratedDeriv_partialEta_eq hF ℓ hs w
  have hu : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => F r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn F hF ℓ hs
  have hE : Cyl.partialEta (fun x => iteratedDeriv ℓ (fun r => F r x) s) =
      Dv ((0 : ℝ), (1 : ℝ)) (fun x => iteratedDeriv ℓ (fun r => F r x) s) :=
    funext (Cyl.partialEta_eq_fderiv (hu.differentiable (by simp)))
  have n2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hb := norm_jet_Dv_scalar_le hu ((0 : ℝ), (1 : ℝ)) j z
  rw [n2, one_mul] at hb
  unfold ageJet jet
  rw [hslice, hE]
  exact hb

theorem iteratedDeriv_vec_proj_eq {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2) :
    ∀ (ℓ : ℕ) {t : ℝ}, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => V r w k) t = (iteratedDeriv ℓ (fun r => V r w) t) k
  | 0, _, _, _ => rfl
  | ℓ + 1, t, ht, w => by
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => V r w k) =ᶠ[nhds t]
        fun r => (PartI_T25_1.DtU ℓ (fun x => V x.1 x.2) (r, w)) k := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      rw [iteratedDeriv_vec_proj_eq hV k ℓ hr w,
        PartI_T25_1.iteratedDeriv_slice_eq_DtU hV ℓ hr w]
    have hevV : iteratedDeriv ℓ (fun r => V r w) =ᶠ[nhds t]
        fun r => PartI_T25_1.DtU ℓ (fun x => V x.1 x.2) (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using
        PartI_T25_1.iteratedDeriv_slice_eq_DtU hV ℓ hr w
    rw [hev.deriv_eq, hevV.deriv_eq]
    have hd : HasDerivAt (fun r => (PartI_T25_1.DtU ℓ (fun x => V x.1 x.2) (r, w)) k)
        ((Dx eT (PartI_T25_1.DtU ℓ (fun x => V x.1 x.2)) (t, w)) k) t :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_slice (PartI_T25_1.sm_DtU hV ℓ) ht w)
    rw [hd.deriv, (hasDerivAt_slice (PartI_T25_1.sm_DtU hV ℓ) ht w).deriv]

theorem norm_ageJet_vec_proj_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => V r w k) s z‖ ≤ ‖ageJet ℓ j V s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => V r w k) s) =
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ fun w => iteratedDeriv ℓ (fun r => V r w) s) :=
    funext fun w => iteratedDeriv_vec_proj_eq hV k ℓ hs w
  have hu : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => V r w) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn V hV ℓ hs
  unfold ageJet jet
  rw [hslice]
  refine ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    hu.contDiffAt (by exact_mod_cast le_top)).trans ?_
  have hproj : ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using PiLp.norm_apply_le v k
  exact (mul_le_mul_of_nonneg_right hproj (norm_nonneg _)).trans (by linarith)

theorem norm_ageJet_vec_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j V s z‖ ≤
      ‖ageJet ℓ j (fun r w => V r w 0) s z‖ + ‖ageJet ℓ j (fun r w => V r w 1) s z‖ := by
  have hu : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => V r w) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn V hV ℓ hs
  have h0 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 0) =
      fun w => iteratedDeriv ℓ (fun r => V r w 0) s :=
    funext fun w => (iteratedDeriv_vec_proj_eq hV 0 ℓ hs w).symm
  have h1 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 1) =
      fun w => iteratedDeriv ℓ (fun r => V r w 1) s :=
    funext fun w => (iteratedDeriv_vec_proj_eq hV 1 ℓ hs w).symm
  have h := norm_jet_vec_le (fun w => iteratedDeriv ℓ (fun r => V r w) s) hu j z
  unfold ageJet jet
  rw [← h0, ← h1]
  exact h

/-- Auxiliary shifted product `(DtS m₁ A) * (DtS m₂ B)` on `ℝ → Plane → ℝ`. -/
def prodDt (m₁ m₂ : ℕ) (A B : ℝ → Plane → ℝ) : ℝ → Plane → ℝ :=
  fun r w =>
    DtS m₁ (fun x : ℝ × Plane => A x.1 x.2) (r, w) *
      DtS m₂ (fun x : ℝ × Plane => B x.1 x.2) (r, w)

theorem smS_prodDt {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2)) (m₁ m₂ : ℕ) :
    SmS (fun x : ℝ × Plane => prodDt m₁ m₂ A B x.1 x.2) :=
  (SmS_DtS hA m₁).mul (SmS_DtS hB m₂)

theorem deriv_prodDt_eq {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ : ℕ) {t : ℝ} (ht : 0 < t) (w : Plane) :
    deriv (fun r => prodDt m₁ m₂ A B r w) t =
      prodDt (m₁ + 1) m₂ A B t w + prodDt m₁ (m₂ + 1) A B t w := by
  have hdA := hasDerivAt_sliceS (SmS_DtS hA m₁) ht w
  have hdB := hasDerivAt_sliceS (SmS_DtS hB m₂) ht w
  have hmul := hdA.mul hdB
  have hderiv : deriv (fun r => prodDt m₁ m₂ A B r w) t =
      DxS eT (DtS m₁ fun x => A x.1 x.2) (t, w) * DtS m₂ (fun x => B x.1 x.2) (t, w) +
        DtS m₁ (fun x => A x.1 x.2) (t, w) * DxS eT (DtS m₂ fun x => B x.1 x.2) (t, w) :=
    hmul.deriv
  rw [hderiv]
  unfold prodDt DtS
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem ageJet_succ_prodDt_eq {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet (ℓ + 1) j (prodDt m₁ m₂ A B) s z =
      ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z + ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z := by
  have hstep : ageJet (ℓ + 1) j (prodDt m₁ m₂ A B) s =
      ageJet ℓ j (fun r w => prodDt (m₁ + 1) m₂ A B r w + prodDt m₁ (m₂ + 1) A B r w) s := by
    unfold ageJet
    congr 1
    funext w
    rw [iteratedDeriv_succ']
    have hev : deriv (fun r => prodDt m₁ m₂ A B r w) =ᶠ[nhds s]
        fun r => prodDt (m₁ + 1) m₂ A B r w + prodDt m₁ (m₂ + 1) A B r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using deriv_prodDt_eq hA hB m₁ m₂ hr w
    exact hev.iteratedDeriv_eq ℓ
  rw [hstep]
  exact ageJet_add (prodDt (m₁ + 1) m₂ A B) (prodDt m₁ (m₂ + 1) A B)
    (smS_prodDt hA hB (m₁ + 1) m₂) (smS_prodDt hA hB m₁ (m₂ + 1)) hs ℓ j z

theorem norm_ageJet_zero_prodDt_le {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2))
    (m₁ m₂ j : ℕ) {s M_A M_B : ℝ} (hs : 0 < s) (hMA : 0 ≤ M_A) (_hMB : 0 ≤ M_B) (z : Plane)
    (hA_bd : ∀ i ≤ j, ‖ageJet m₁ i A s z‖ ≤ M_A)
    (hB_bd : ∀ i ≤ j, ‖ageJet m₂ i B s z‖ ≤ M_B) :
    ‖ageJet 0 j (prodDt m₁ m₂ A B) s z‖ ≤ (2 : ℝ) ^ j * M_A * M_B := by
  let f : Plane → ℝ := fun w => iteratedDeriv m₁ (fun r => A r w) s
  let g : Plane → ℝ := fun w => iteratedDeriv m₂ (fun r => B r w) s
  have hprod_eq : prodDt m₁ m₂ A B s = fun w => f w * g w := by
    funext w
    unfold prodDt f g
    rw [iteratedDeriv_slice_eq_DtS hA m₁ hs w, iteratedDeriv_slice_eq_DtS hB m₂ hs w]
  have hf_sm : ContDiff ℝ ∞ f := contDiff_slice_iteratedDeriv_of_contDiffOn A hA m₁ hs
  have hg_sm : ContDiff ℝ ∞ g := contDiff_slice_iteratedDeriv_of_contDiffOn B hB m₂ hs
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := f) (g := g)
    hf_sm.contDiffOn hg_sm.contDiffOn uniqueDiffOn_univ (mem_univ z) (n := j) (by exact_mod_cast le_top)
  simp only [iteratedFDerivWithin_univ] at hmul
  have hsum : ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M_A * M_B) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hji : j - i ≤ j := Nat.sub_le j i
    have hAi : ‖iteratedFDeriv ℝ i f z‖ ≤ M_A := hA_bd i hij
    have hBi : ‖iteratedFDeriv ℝ (j - i) g z‖ ≤ M_B := hB_bd (j - i) hji
    have hch : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hAi hBi (norm_nonneg _) hMA) hch
  have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  unfold ageJet jet
  simp only [iteratedDeriv_zero]
  rw [hprod_eq]
  calc ‖iteratedFDeriv ℝ j (fun w => f w * g w) z‖
      ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ := hmul
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M_A * M_B) := hsum
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * (M_A * M_B) :=
        (Finset.sum_mul _ _ _).symm
    _ = (2 : ℝ) ^ j * M_A * M_B := by rw [hchoose]; ring

theorem norm_ageJet_prodDt_le {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2)) :
    ∀ (ℓ m₁ m₂ j : ℕ) {s M_A M_B : ℝ}, 0 < s → 0 ≤ M_A → 0 ≤ M_B → ∀ z : Plane,
      (∀ r ≤ m₁ + ℓ, ∀ i ≤ j, ‖ageJet r i A s z‖ ≤ M_A) →
      (∀ r ≤ m₂ + ℓ, ∀ i ≤ j, ‖ageJet r i B s z‖ ≤ M_B) →
      ‖ageJet ℓ j (prodDt m₁ m₂ A B) s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B
  | 0, m₁, m₂, j, s, M_A, M_B, hs, hMA, hMB, z, hA_bd, hB_bd => by
    rw [zero_add]
    exact norm_ageJet_zero_prodDt_le hA hB m₁ m₂ j hs hMA hMB z
      (fun i hi => hA_bd m₁ (by omega) i hi)
      (fun i hi => hB_bd m₂ (by omega) i hi)
  | ℓ + 1, m₁, m₂, j, s, M_A, M_B, hs, hMA, hMB, z, hA_bd, hB_bd => by
    rw [ageJet_succ_prodDt_eq hA hB m₁ m₂ ℓ j hs z]
    have h1 := norm_ageJet_prodDt_le hA hB ℓ (m₁ + 1) m₂ j hs hMA hMB z
      (fun r hr i hi => hA_bd r (by omega) i hi)
      (fun r hr i hi => hB_bd r (by omega) i hi)
    have h2 := norm_ageJet_prodDt_le hA hB ℓ m₁ (m₂ + 1) j hs hMA hMB z
      (fun r hr i hi => hA_bd r (by omega) i hi)
      (fun r hr i hi => hB_bd r (by omega) i hi)
    calc ‖ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z + ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z‖
        ≤ ‖ageJet ℓ j (prodDt (m₁ + 1) m₂ A B) s z‖ + ‖ageJet ℓ j (prodDt m₁ (m₂ + 1) A B) s z‖ :=
          norm_add_le _ _
      _ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B + (2 : ℝ) ^ (ℓ + j) * M_A * M_B := add_le_add h1 h2
      _ = (2 : ℝ) ^ (ℓ + 1 + j) * M_A * M_B := by
          rw [add_right_comm ℓ 1 j, pow_succ']
          ring

/-- **Spacetime Leibniz product bound for `ageJet ℓ j`:**
if `A, B : ℝ → Plane → ℝ` are jointly smooth on `(0, ∞) × Plane` and have mixed jets up to order
`(ℓ, j)` at `(s, z)` bounded by `M_A` and `M_B`, then `ageJet ℓ j (A * B) s z` is bounded by
`2 ^ (ℓ + j) * M_A * M_B`. -/
theorem norm_ageJet_mul_le {A B : ℝ → Plane → ℝ}
    (hA : SmS (fun x : ℝ × Plane => A x.1 x.2))
    (hB : SmS (fun x : ℝ × Plane => B x.1 x.2))
    (ℓ j : ℕ) {s M_A M_B : ℝ} (hs : 0 < s) (hMA : 0 ≤ M_A) (hMB : 0 ≤ M_B) (z : Plane)
    (hA_bd : ∀ r ≤ ℓ, ∀ i ≤ j, ‖ageJet r i A s z‖ ≤ M_A)
    (hB_bd : ∀ r ≤ ℓ, ∀ i ≤ j, ‖ageJet r i B s z‖ ≤ M_B) :
    ‖ageJet ℓ j (fun r w => A r w * B r w) s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_A * M_B :=
  norm_ageJet_prodDt_le hA hB ℓ 0 0 j hs hMA hMB z
    (fun r hr i hi => hA_bd r (by omega) i hi)
    (fun r hr i hi => hB_bd r (by omega) i hi)

theorem advection_apply (u : Plane → Vec) (z : Plane) (k : Fin 2) :
    Train.advection u z k =
      u z 0 * Cyl.partialQ (fun w => u w k) z + u z 1 * Cyl.partialEta (fun w => u w k) z := by
  fin_cases k <;> rfl

/-- Uniform bound across spatial orders `i ≤ K` at a fixed age order `r`. -/
theorem uniform_vel_spatial {ν c : ℝ} {tr : B0140.TrainSol ν c} {r : ℕ}
    (hr : VelOrderBoundedFixed tr r) :
    ∀ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ i ≤ K, ‖ageJet r i tr.v s z‖ ≤ M
  | 0 => by
    obtain ⟨M₀, h0⟩ := hr 0
    refine ⟨max M₀ 0, le_max_right _ _, fun s hs z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact (h0 s hs z).trans (le_max_left _ _)
  | K + 1 => by
    obtain ⟨M₁, hM₁, hIH⟩ := uniform_vel_spatial hr K
    obtain ⟨M₂, hK1⟩ := hr (K + 1)
    refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), fun s hs z i hi => ?_⟩
    rcases Nat.of_le_succ hi with hiK | rfl
    · exact (hIH s hs z i hiK).trans (le_max_left _ _)
    · exact (hK1 s hs z).trans (le_max_right _ _)

/-- Uniform bound across all `r ≤ L` and `i ≤ K`. -/
theorem uniform_vel_rect {ν c : ℝ} {tr : B0140.TrainSol ν c} (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, VelOrderBoundedFixed tr r) →
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ s : ℝ, 0 < s → ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K, ‖ageJet r i tr.v s z‖ ≤ M
  | 0, hIH => by
    obtain ⟨M₀, hM₀, h0⟩ := uniform_vel_spatial (hIH 0 le_rfl) K
    refine ⟨M₀, hM₀, fun s hs z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 s hs z i hi
  | L + 1, hIH => by
    obtain ⟨M₁, hM₁, h1⟩ := uniform_vel_rect K L (fun r hr => hIH r (Nat.le_succ_of_le hr))
    obtain ⟨M₂, _hM₂, h2⟩ := uniform_vel_spatial (hIH (L + 1) le_rfl) K
    refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), fun s hs z r hr i hi => ?_⟩
    rcases Nat.of_le_succ hr with hrL | rfl
    · exact (h1 s hs z r hrL i hi).trans (le_max_left _ _)
    · exact (h2 s hs z i hi).trans (le_max_right _ _)

end PartI_HF_1

/-- **Advection age-step (`TrainVelAgeStepAdvFixed`)**:
source lines 326–359, 427–435 of `the November 2 reference manuscript`.
At fixed `0 < ν` and `1 < c`, if a `BUC` train `tr : B0140.TrainSol ν c` satisfies
`∀ r ≤ ℓ, VelOrderBoundedFixed tr r` (all spatial jets of `tr.v` up to age order `ℓ` are bounded
on `s > 0`), then for every spatial order `j : ℕ`, the advection age-jet
`ageJet ℓ j (fun r w => Train.advection (tr.v r) w)` is bounded on `s > 0` × `Plane`. -/
def TrainVelAgeStepAdvFixed : Prop :=
  ∀ {ν c : ℝ}, 0 < ν → 1 < c →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → VelOrderBoundedFixed tr r) →
        ∀ j : ℕ, ∃ M_adv : ℝ,
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w) s z‖ ≤ M_adv

/-- **Unconditional proof of `TrainVelAgeStepAdvFixed`** via the spacetime Leibniz product rule
`PartI_HF_1.norm_ageJet_mul_le` on the components of `Train.advection (tr.v r)`. -/
theorem trainVelAgeStepAdvFixed_proof : TrainVelAgeStepAdvFixed := by
  intro ν c _hν _hc tr _htr ℓ hIH j
  obtain ⟨M, hM, hbd⟩ := PartI_HF_1.uniform_vel_rect (j + 1) ℓ hIH
  refine ⟨4 * (2 : ℝ) ^ (ℓ + j) * M * M, fun s hs z => ?_⟩
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_adv : Sm (fun x : ℝ × Plane => Train.advection (tr.v x.1) x.2) :=
    PartI_T25_1.sm_advection hsm_v
  have hsm_vk : ∀ k : Fin 2, SmS (fun x : ℝ × Plane => tr.v x.1 x.2 k) := fun k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hcomp_bd : ∀ k : Fin 2,
      ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w k) s z‖ ≤
        2 * (2 : ℝ) ^ (ℓ + j) * M * M := by
    intro k
    let P₀ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (fun x => tr.v r x k) w
    let P₁ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (fun x => tr.v r x k) w
    have hsm_Q : SmS (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y k) x.2) :=
      PartI_HF_1.smS_partialQ (F := fun r y => tr.v r y k) (hsm_vk k)
    have hsm_E : SmS (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y k) x.2) :=
      PartI_HF_1.smS_partialEta (F := fun r y => tr.v r y k) (hsm_vk k)
    have hsm_P₀ : SmS (fun x : ℝ × Plane => P₀ x.1 x.2) := (hsm_vk 0).mul hsm_Q
    have hsm_P₁ : SmS (fun x : ℝ × Plane => P₁ x.1 x.2) := (hsm_vk 1).mul hsm_E
    have heq : (fun r w => Train.advection (tr.v r) w k) = fun r w => P₀ r w + P₁ r w := by
      funext r w
      exact PartI_HF_1.advection_apply (tr.v r) w k
    rw [heq, PartI_HF_1.ageJet_add P₀ P₁ hsm_P₀ hsm_P₁ hs ℓ j z]
    have hP₀_bd : ‖ageJet ℓ j P₀ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M := by
      refine PartI_HF_1.norm_ageJet_mul_le
        (A := fun r w => tr.v r w 0) (B := fun r w => Cyl.partialQ (fun x => tr.v r x k) w)
        (hsm_vk 0) hsm_Q ℓ j hs hM hM z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
      · exact (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 0 r i hs z).trans
          (hbd s hs z r hr i (by omega))
      · exact (PartI_HF_1.norm_ageJet_partialQ_le (F := fun r x => tr.v r x k)
            (hsm_vk k) r i hs z).trans
          ((PartI_HF_1.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs z).trans
            (hbd s hs z r hr (i + 1) (by omega)))
    have hP₁_bd : ‖ageJet ℓ j P₁ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M := by
      refine PartI_HF_1.norm_ageJet_mul_le
        (A := fun r w => tr.v r w 1) (B := fun r w => Cyl.partialEta (fun x => tr.v r x k) w)
        (hsm_vk 1) hsm_E ℓ j hs hM hM z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
      · exact (PartI_HF_1.norm_ageJet_vec_proj_le hsm_v 1 r i hs z).trans
          (hbd s hs z r hr i (by omega))
      · exact (PartI_HF_1.norm_ageJet_partialEta_le (F := fun r x => tr.v r x k)
            (hsm_vk k) r i hs z).trans
          ((PartI_HF_1.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs z).trans
            (hbd s hs z r hr (i + 1) (by omega)))
    have htri := norm_add_le (ageJet ℓ j P₀ s z) (ageJet ℓ j P₁ s z)
    linarith
  have hvec := PartI_HF_1.norm_ageJet_vec_le (V := fun r w => Train.advection (tr.v r) w) hsm_adv ℓ j hs z
  have h0 := hcomp_bd 0
  have h1 := hcomp_bd 1
  linarith

/-! ### 6. Pressure age-step leaf (`PartI:HF/1/1`) and inductive assembly of `TrainJetsBoundedFixed` -/

/-- **Leaf (`PartI:HF/1/1`, `TrainVelAgeStepPressFixed`)**:
source lines 318–322, 326–359, 427–435 of `the November 2 reference manuscript`.
At fixed `0 < ν` and `1 < c`, if a `BUC` train `tr : B0140.TrainSol ν c` satisfies
`∀ r ≤ ℓ, VelOrderBoundedFixed tr r` (all spatial jets of `tr.v` up to age order `ℓ` are bounded
on `s > 0`), then for every spatial order `j : ℕ`, the pressure-gradient age-jet
`ageJet ℓ j (fun r w => Train.gradS (tr.p r) w)` is bounded on `s > 0` × `Plane`. -/
def TrainVelAgeStepPressFixed : Prop :=
  ∀ {ν c : ℝ}, 0 < ν → 1 < c →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ ℓ : ℕ, (∀ r : ℕ, r ≤ ℓ → VelOrderBoundedFixed tr r) →
        ∀ j : ℕ, ∃ M_press : ℝ,
          ∀ s : ℝ, 0 < s → ∀ z : Plane,
            ‖ageJet ℓ j (fun r w => Train.gradS (tr.p r) w) s z‖ ≤ M_press

/-- Inductive step (`ℓ → ℓ + 1`) for `VelOrderBoundedFixed` from `TrainVelAgeStepPressFixed`. -/
theorem velOrderBoundedFixed_succ
    (hPress : TrainVelAgeStepPressFixed)
    {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ : ℕ) (hIH : ∀ r : ℕ, r ≤ ℓ → VelOrderBoundedFixed tr r) :
    VelOrderBoundedFixed tr (ℓ + 1) := by
  intro j
  obtain ⟨M_visc, hVisc⟩ := hIH ℓ le_rfl (j + 2)
  obtain ⟨M_adv, hAdv_bd⟩ := trainVelAgeStepAdvFixed_proof hν hc tr htr ℓ hIH j
  obtain ⟨M_press, hPress_bd⟩ := hPress hν hc tr htr ℓ hIH j
  refine ⟨(2 * ν) * M_visc + M_adv + M_press, fun s hs z => ?_⟩
  have h1 := norm_ageJet_succ_vel_le tr hν.le ℓ j hs z
  have h2 : (2 * ν) * ‖ageJet ℓ (j + 2) tr.v s z‖ ≤ (2 * ν) * M_visc :=
    mul_le_mul_of_nonneg_left (hVisc s hs z) (by positivity)
  have h3 := hAdv_bd s hs z
  have h4 := hPress_bd s hs z
  linarith

/-- Strong induction on `ℓ : ℕ` deriving `∀ ℓ, VelOrderBoundedFixed tr ℓ` from the base order
`VelOrderBoundedFixed tr 0` and `TrainVelAgeStepPressFixed`. -/
theorem velOrderBoundedFixed_all
    (hPress : TrainVelAgeStepPressFixed)
    {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (h0 : VelOrderBoundedFixed tr 0) :
    ∀ ℓ : ℕ, VelOrderBoundedFixed tr ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ m =>
      exact velOrderBoundedFixed_succ hPress hν hc tr htr m
        (fun r hr => ih r (Nat.lt_succ_of_le hr))

/-- **Conditional assembly of `TrainJetsBoundedFixed` from `TrainOverlap` and
`TrainVelAgeStepPressFixed`.** -/
theorem trainJetsBoundedFixed_of_overlap
    (hOv : TrainOverlap)
    (hPress : TrainVelAgeStepPressFixed) :
    TrainJetsBoundedFixed := by
  intro ρ hρ
  obtain ⟨ν₁, hν₁, hZero⟩ := trainJetsBoundedFixed_zero_of_overlap hOv ρ hρ
  refine ⟨min ν₁ (1 / 2), lt_min hν₁ (by norm_num), fun ν hν hν_le tr htr ℓ j => ?_⟩
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hc1 : 1 < trainPeriod ρ ν := by
    unfold trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  exact velOrderBoundedFixed_all hPress hν hc1 tr htr (hZero ν hν hν₁_le tr htr) ℓ j

/-- **Conditional assembly of `TrainJetsBoundedFixed` (`PartI:HF/1`)** from
`OverlapMeanDuhamelSplit` (`PartI:T15/1`, which completes `TrainOverlap`) and
`TrainVelAgeStepPressFixed` (`PartI:HF/1/1`). -/
theorem trainJetsBoundedFixed_of
    (hSplit : OverlapMeanDuhamelSplit)
    (hPress : TrainVelAgeStepPressFixed) :
    TrainJetsBoundedFixed := by
  have hFD : OverlapFluctuationDecay := overlap_fluctuation_decay overlapHighNormUniform_proof
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD
      (overlap_mean_decay_of overlapHighNormUniform_proof hFD overlap_mean_primitive hSplit)
  exact trainJetsBoundedFixed_of_overlap hOv hPress

end UnforcedLeray.Short.PartI
