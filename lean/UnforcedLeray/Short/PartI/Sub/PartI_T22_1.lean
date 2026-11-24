import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import UnforcedLeray.Short.PartI.Sub.PartI_T21
import UnforcedLeray.Short.PartI.Sub.PartI_T22
import UnforcedLeray.Short.PartI.Tasks.TrainClass.FluctStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# `PartI:T22/1` Sub-module: Post-overlap (`ℓ = 0`) stream fluctuation and pressure decay

Source of record: `the November 2 reference manuscript`, lines 439-446, 499-503,
515-522.

This module proves:
1. **Unconditional upgrade from `wSupNorm 0` exponential decay to `wCellL2 c 0 ∧ wSupNorm 0`**
   (`PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero`):
   combining any polynomial weight-`4` bound `wSupNorm 4 f ≤ ofReal (polyPS C₁ N₁ ν c s)` with an
   unweighted exponential bound `wSupNorm 0 f ≤ ofReal (polyP C₂ N₂ ν c * exp(-(lam * ν * s / c²)))`
   via `PartI_T22.wSupNorm_interp 2`, `PartI_T22.polyPS_mul_exp_absorb`, and
   `PartI_T21.wCellL2_le_of_wSupNorm_add_two` yields the post-overlap exponential bound for both
   `wCellL2 c 0 f` and `wSupNorm 0 f` at rate `lam / 4`.
2. **Stream-fluctuation pair (`PartI_T22.isStreamPair_ψ_fluct_v_fluct`)**:
   for any BUC train `tr`, `ψ_fluct(r, z) = tr.ψ r z - hmean c (tr.ψ r) z.2` and
   `v_fluct(r, z) = hfluct c (tr.v r) z` form a jointly smooth stream pair `IsStreamPair` on
   `(0, ∞) × Plane`, with `ψ_fluct` `c`-periodic in `q` and of zero horizontal mean at all age
   derivative orders `ℓ : ℕ`.
3. **General-`ℓ` stream-fluctuation jet domination by velocity-fluctuation jets**
   (`PartI_T22.wSupNorm_zero_ageJet_streamFluct_zero_le`,
   `PartI_T22.wSupNorm_zero_ageJet_streamFluct_succ_le`,
   `PartI_T22.postOverlap_streamFluct_of_velFluct_sup`).
4. **Unconditional post-overlap `ℓ = 0` stream fluctuation decay (`trainPostOverlapStreamZero_proof`)**:
   combining (1)–(3) with `trainPostOverlapVelZero_of hFD` and `hTails.2.2` proves the full stream
   fluctuation half of `TrainPostOverlapStreamPressureZero` for all `j : ℕ` unconditionally.
5. **Mean / nonzero-mode pressure decomposition (`PartI_T22.wSupNorm_ageJet_p_le_add_fluct_mean`)**:
   proves joint smoothness of `tr.p`, `p_mean(r, z) = hmean c (tr.p r) z.2`, and
   `p_fluct(r, z) = tr.p r z - hmean c (tr.p r) z.2` on `(0, ∞) × Plane`, linearity of `ageJet ℓ j`
   on sums/differences, and `wSupNorm` subadditivity decomposing `tr.p = p_fluct + p_mean`.
6. **Conditional assembly (`trainPostOverlapStreamPressureZero_of`)**:
   reduces `TrainPostOverlapStreamPressureZero` to the two unweighted `L^∞` pressure leaves
   `TrainPostOverlapPressureMeanSupZero` (`PartI:T22/1/1`, horizontal mean `\bar p = -\overline{v₂²}`)
   and `TrainPostOverlapPressureFluctSupZero` (`PartI:T22/1/2`, nonzero-mode cylinder Poisson kernel
   for `\tilde p = p - \bar p`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet cellL2 wCellL2 jap)
open UnforcedLeray.Short.IIb (IsStreamPair psiJet_slice_contDiffAt vb_slice_contDiffAt)

namespace PartI_T22

/-! ### 1. Upgrade from `wSupNorm 0` + `wSupNorm 4` to `wCellL2 c 0 ∧ wSupNorm 0` -/

/-- Monotonicity `wSupNorm 0 f ≤ wSupNorm m f` for any `m : ℕ`. -/
theorem wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : Plane → E) :
    wSupNorm 0 f ≤ wSupNorm m f := by
  unfold wSupNorm
  refine iSup_mono fun z => ?_
  gcongr
  have hj0 : jap 0 z = 1 := by simp [jap]
  rw [hj0]
  exact one_le_pow₀ (by nlinarith [sq_nonneg z.2])

/-- Triangle inequality for `wSupNorm m` on a sum of functions. -/
theorem wSupNorm_add_le {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f g : Plane → E) :
    wSupNorm m (fun z => f z + g z) ≤ wSupNorm m f + wSupNorm m g := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  calc ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z + g z‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (jap m z)) * (‖f z‖ₑ + ‖g z‖ₑ) :=
        mul_le_mul_right (enorm_add_le _ _) _
    _ = ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ +
          ENNReal.ofReal (Real.sqrt (jap m z)) * ‖g z‖ₑ := left_distrib _ _ _
    _ ≤ (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) +
          (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) :=
        add_le_add
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z)
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) z)

/-- Triangle inequality for `wSupNorm m` on a difference of functions. -/
theorem wSupNorm_sub_le {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f g : Plane → E) :
    wSupNorm m (fun z => f z - g z) ≤ wSupNorm m f + wSupNorm m g := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  calc ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z - g z‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (jap m z)) * (‖f z‖ₑ + ‖g z‖ₑ) :=
        mul_le_mul_right enorm_sub_le _
    _ = ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ +
          ENNReal.ofReal (Real.sqrt (jap m z)) * ‖g z‖ₑ := left_distrib _ _ _
    _ ≤ (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) +
          (⨆ w : Plane, ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) :=
        add_le_add
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z)
          (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖g w‖ₑ) z)

/-- Given a polynomial weight-`4` bound `wSupNorm 4 f ≤ ofReal (polyPS C₁ N₁ ν c s)` and an
unweighted post-overlap exponential bound
`wSupNorm 0 f ≤ ofReal (polyP C₂ N₂ ν c * exp(-(lam * ν * s / c²)))`, interpolation at `m = 2`
(`wSupNorm_interp 2`), polynomial-in-age absorption (`polyPS_mul_exp_absorb`), and the cell-`L²`
embedding (`PartI_T21.wCellL2_le_of_wSupNorm_add_two`) yield post-overlap exponential decay for
both `wCellL2 c 0 f` and `wSupNorm 0 f` at rate `lam / 4`. -/
theorem wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N₁ N₂ : ℕ) {C₁ C₂ lam ν c s : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hlam : 0 < lam)
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hs : 0 ≤ s) (f : Plane → E)
    (h4 : wSupNorm 4 f ≤ ENNReal.ofReal (polyPS C₁ N₁ ν c s))
    (h0 : wSupNorm 0 f ≤ ENNReal.ofReal (polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)))) :
    let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam / 2) ^ N₁)⁻¹ * Real.exp (lam / 2)
    let C₃ : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
    let C_out := (PartI_T21.unitCellInvSqL2 + 1) * C₃
    let N_out := 2 * N₁ + N₂ + 1
    let K := ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2)))
    wCellL2 c 0 f ≤ K ∧ wSupNorm 0 f ≤ K := by
  intro K_abs C₃ C_out N_out K
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have h1s : 1 ≤ 1 + s := by linarith
  have h1Xs : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by nlinarith
  have hA_pos : 0 < polyPS C₁ N₁ ν c s := by unfold polyPS; positivity
  have hB_pos : 0 < polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)) := by
    unfold polyP; positivity
  have h4' : wSupNorm (2 * 2) f ≤ ENNReal.ofReal (polyPS C₁ N₁ ν c s) := h4
  have hinterp := wSupNorm_interp 2 f hA_pos hB_pos h4' h0
  have habs : Real.sqrt (2 * polyPS C₁ N₁ ν c s *
      (polyP C₂ N₂ ν c * Real.exp (-(lam * ν * s / c ^ 2)))) ≤
      polyP C₃ (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2)) :=
    polyPS_mul_exp_absorb N₁ N₂ hC₁ hC₂ hlam hν hc1 hs
  set B₂ : ℝ := polyP C₃ (2 * N₁ + N₂) ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2))
  have hfac_pos : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
  have hK_abs_pos : 0 < K_abs := by dsimp [K_abs]; positivity
  have hC₃_pos : 0 < C₃ := by dsimp [C₃]; positivity
  have hB₂_nn : 0 ≤ B₂ := by dsimp [B₂, polyP]; positivity
  have hSup2 : wSupNorm 2 f ≤ ENNReal.ofReal B₂ :=
    hinterp.trans (ENNReal.ofReal_le_ofReal habs)
  have hL2 := PartI_T21.wCellL2_le_of_wSupNorm_add_two hc1 hB₂_nn 0 f hSup2
  have hW_pos : 0 < PartI_T21.unitCellInvSqL2 := PartI_T21.unitCellInvSqL2_pos
  have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
  have hL2_le : PartI_T21.unitCellInvSqL2 * c * B₂ ≤
      polyP C_out N_out ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2)) := by
    dsimp [B₂, C_out, N_out, polyP]
    have hpow : c * (1 + c + ν⁻¹) ^ (2 * N₁ + N₂) ≤ (1 + c + ν⁻¹) ^ (2 * N₁ + N₂ + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right hcX (by positivity)
    have hW : PartI_T21.unitCellInvSqL2 ≤ PartI_T21.unitCellInvSqL2 + 1 := by linarith
    calc PartI_T21.unitCellInvSqL2 * c *
          (C₃ * (1 + c + ν⁻¹) ^ (2 * N₁ + N₂) * Real.exp (-((lam / 4) * ν * s / c ^ 2)))
        = PartI_T21.unitCellInvSqL2 * C₃ * (c * (1 + c + ν⁻¹) ^ (2 * N₁ + N₂)) *
            Real.exp (-((lam / 4) * ν * s / c ^ 2)) := by ring
      _ ≤ (PartI_T21.unitCellInvSqL2 + 1) * C₃ * (1 + c + ν⁻¹) ^ (2 * N₁ + N₂ + 1) *
            Real.exp (-((lam / 4) * ν * s / c ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          apply mul_le_mul _ hpow (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hW hC₃_pos.le
  have hSup0_le : B₂ ≤ polyP C_out N_out ν c * Real.exp (-((lam / 4) * ν * s / c ^ 2)) := by
    dsimp [B₂, C_out, N_out, polyP]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    have hpow : (1 + c + ν⁻¹) ^ (2 * N₁ + N₂) ≤ (1 + c + ν⁻¹) ^ (2 * N₁ + N₂ + 1) :=
      pow_le_pow_right₀ h1X (Nat.le_succ _)
    have hW1 : C₃ ≤ (PartI_T21.unitCellInvSqL2 + 1) * C₃ := by nlinarith
    exact mul_le_mul hW1 hpow (by positivity) (by positivity)
  exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hL2_le),
    (wSupNorm_zero_le 2 f).trans (hSup2.trans (ENNReal.ofReal_le_ofReal hSup0_le))⟩

/-! ### 2. Stream-fluctuation pair and `c`-periodicity / zero horizontal mean -/

theorem hmean_apply_vec' (c : ℝ) {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (k : Fin 2) :
    (hmean c a η) k = hmean c (fun z => a z k) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- Joint smoothness of `v_fluct(r, z) = hfluct c (tr.v r) z` on `(0, ∞) × Plane`. -/
theorem contDiffOn_hfluct_v {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) (Ioi 0 ×ˢ univ) := by
  have hv_joint : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hmean_k : ∀ k : Fin 2,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (tr.v x.1) x.2.2 k) (Ioi 0 ×ˢ univ) := by
    intro k
    have hvk : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
    have hmk : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (fun z => tr.v x.1 z k) x.2)
        (Ioi 0 ×ˢ univ) :=
      hmeanContDiff c hc (fun r z => tr.v r z k) hvk
    have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
    have hcomp := hmk.comp hproj.contDiffOn
      (fun x (hx : x.1 ∈ Ioi (0 : ℝ) ∧ x.2 ∈ (univ : Set Plane)) => ⟨hx.1, mem_univ _⟩)
    refine hcomp.congr ?_
    rintro ⟨r, z⟩ ⟨hr, -⟩
    have hv_cont : Continuous (tr.v r) := by
      have hmap : Continuous (fun w : Plane => ((r, w) : ℝ × Plane)) :=
        continuous_const.prodMk continuous_id
      exact hv_joint.continuousOn.comp_continuous hmap (fun w => ⟨hr, mem_univ w⟩)
    exact hmean_apply_vec' c hv_cont z.2 k
  have hpi : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => fun k : Fin 2 => hmean c (tr.v x.1) x.2.2 k) (Ioi 0 ×ˢ univ) :=
    contDiffOn_pi.2 hmean_k
  have hmean_vec : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => hmean c (tr.v x.1) x.2.2) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn hpi
  exact hv_joint.sub hmean_vec

/-- `(ψ_fluct, v_fluct)` is a jointly smooth stream pair on `(0, ∞) × Plane`. -/
theorem isStreamPair_ψ_fluct_v_fluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) :
    IsStreamPair (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2)
      (fun r => hfluct c (tr.v r)) := by
  refine ⟨fluctStreamSmooth ν c hν hc tr, contDiffOn_hfluct_v hc tr, ?_⟩
  intro s hs z
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs.le
  have hstream := tr.isTrain.stream s hs.le
  have hvc : Continuous (tr.v s) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun w => ⟨hs.le, mem_univ w⟩)
  have hv0 : Continuous (fun w : Plane => tr.v s w 0) :=
    (PiLp.continuous_apply _ _ 0).comp hvc
  have hpartY : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => tr.ψ s (q, y)) (-(tr.v s (q, e) 0)) e := by
    intro q e
    have hpath : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    have hdiffAt : DifferentiableAt ℝ (fun y : ℝ => tr.ψ s (q, y)) e :=
      (hψd (q, e)).comp e hpath.differentiableAt
    have hval : tr.v s (q, e) 0 = -deriv (fun y : ℝ => tr.ψ s (q, y)) e := by
      rw [hstream (q, e), toVec_zero]; rfl
    rw [hval, neg_neg]
    exact hdiffAt.hasDerivAt
  have hpartX : HasDerivAt (fun q : ℝ => tr.ψ s (q, z.2)) (tr.v s z 1) z.1 := by
    have hpath : HasDerivAt (fun q : ℝ => ((q, z.2) : Plane)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    have hdiffAt : DifferentiableAt ℝ (fun q : ℝ => tr.ψ s (q, z.2)) z.1 :=
      (hψd z).comp z.1 hpath.differentiableAt
    have hval : tr.v s z 1 = deriv (fun q : ℝ => tr.ψ s (q, z.2)) z.1 := by
      rw [hstream z, toVec_one]; rfl
    rw [hval]
    exact hdiffAt.hasDerivAt
  have hmY : HasDerivAt (fun y : ℝ => hmean c (tr.ψ s) y)
      (-(hmean c (fun w => tr.v s w 0) z.2)) z.2 := by
    have h := trainMeanV1_hasDerivAt_hmean (c := c) (f := tr.ψ s)
      (g := fun w : Plane => -(tr.v s w 0)) hψd.continuous hv0.neg hpartY z.2
    rwa [trainMeanV1_hmean_neg] at h
  have hdY : deriv (fun y : ℝ => tr.ψ s (z.1, y) - hmean c (tr.ψ s) y) z.2 =
      -(tr.v s z 0) - -(hmean c (fun w => tr.v s w 0) z.2) :=
    ((hpartY z.1 z.2).sub hmY).deriv
  have hdX : deriv (fun q : ℝ => tr.ψ s (q, z.2) - hmean c (tr.ψ s) z.2) z.1 = tr.v s z 1 :=
    (hpartX.sub_const (hmean c (tr.ψ s) z.2)).deriv
  have hm0 := hmean_apply_vec' c hvc z.2 0
  have hm1 := hmean_apply_vec' c hvc z.2 1
  have hv2_0 : hmean c (fun w => tr.v s w 1) z.2 = 0 := trainMeanV2 ν c hν hc tr s hs z.2
  ext i
  fin_cases i
  · change (tr.v s z - hmean c (tr.v s) z.2) 0 =
      (toVec (GaussianVortex.perpendicularGradient
        (fun w : Plane => tr.ψ s w - hmean c (tr.ψ s) w.2) z)) 0
    rw [PiLp.sub_apply, hm0, toVec_zero]
    unfold GaussianVortex.perpendicularGradient GaussianVortex.partialY
    dsimp only
    rw [hdY]
    ring
  · change (tr.v s z - hmean c (tr.v s) z.2) 1 =
      (toVec (GaussianVortex.perpendicularGradient
        (fun w : Plane => tr.ψ s w - hmean c (tr.ψ s) w.2) z)) 1
    rw [PiLp.sub_apply, hm1, hv2_0, sub_zero, toVec_one]
    unfold GaussianVortex.perpendicularGradient GaussianVortex.partialX
    dsimp only
    exact hdX.symm

/-- `tr.ψ s` is `c`-periodic in `q` for `s > 0`. -/
theorem stream_periodic_q {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s)
    (q η : ℝ) : tr.ψ s (q + c, η) = tr.ψ s (q, η) := by
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs.le
  have hstream := tr.isTrain.stream s hs.le
  have hper0 : ∀ a y : ℝ, tr.v s (a + c, y) 0 = tr.v s (a, y) 0 := fun a y =>
    congrArg (fun w : Vec => w 0) (tr.isTrain.periodic_v s hs.le (a, y))
  have hHasY : ∀ a y : ℝ, HasDerivAt (fun y' => tr.ψ s (a, y')) (-(tr.v s (a, y) 0)) y := by
    intro a y
    have hd : DifferentiableAt ℝ (fun y' => tr.ψ s (a, y')) y :=
      (hψd (a, y)).comp y ((differentiableAt_const a).prodMk differentiableAt_id)
    have he : tr.v s (a, y) 0 = -deriv (fun y' => tr.ψ s (a, y')) y := by
      rw [hstream (a, y)]; rfl
    rw [he, neg_neg]
    exact hd.hasDerivAt
  have hD : ∀ y' : ℝ, HasDerivAt (fun y'' => tr.ψ s (q + c, y'') - tr.ψ s (q, y'')) 0 y' := by
    intro y'
    have h := (hHasY (q + c) y').sub (hHasY q y')
    have e : -(tr.v s (q + c, y') 0) - -(tr.v s (q, y') 0) = 0 := by rw [hper0 q y']; ring
    rwa [e] at h
  have hconst : ∀ y' : ℝ,
      tr.ψ s (q + c, y') - tr.ψ s (q, y') = tr.ψ s (q + c, 0) - tr.ψ s (q, 0) :=
    fun y' => is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
      (fun t => (hD t).deriv) y' 0
  have hl : ∀ a : ℝ, Tendsto (fun y' : ℝ => tr.ψ s (a, y')) atTop (𝓝 0) := by
    intro a
    have hmap : Tendsto (fun y' : ℝ => ((a, y') : Plane)) atTop
        (comap (fun z : Plane => |z.2|) atTop) := by
      rw [tendsto_comap_iff]; exact tendsto_abs_atTop_atTop
    exact (tr.isTrain.stream_decay s hs.le).comp hmap
  have hlim : Tendsto (fun y' : ℝ => tr.ψ s (q + c, y') - tr.ψ s (q, y')) atTop (𝓝 0) := by
    simpa only [sub_zero] using (hl (q + c)).sub (hl q)
  have hzero : tr.ψ s (q + c, 0) - tr.ψ s (q, 0) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (Tendsto.congr hconst hlim)
  exact sub_eq_zero.1 ((hconst η).trans hzero)

/-- `ψ_fluct` has zero horizontal mean at every `s > 0` and `η : ℝ`. -/
theorem hmean_ψ_fluct_eq_zero {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 < s) (η : ℝ) :
    hmean c (fun z : Plane => tr.ψ s z - hmean c (tr.ψ s) z.2) η = 0 := by
  have hψ_cont : Continuous (fun q : ℝ => tr.ψ s (q, η)) :=
    (tr.isTrain.stream_differentiable s hs.le).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hle : -c / 2 ≤ c / 2 := by linarith
  show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), (tr.ψ s (q, η) - hmean c (tr.ψ s) η) = 0
  rw [← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_sub (hψ_cont.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  unfold hmean
  rw [← intervalIntegral.integral_of_le hle, smul_eq_mul]
  have hlen : c / 2 - -c / 2 = c := by ring
  rw [hlen, mul_sub, inv_mul_cancel_left₀ hc.ne', sub_self]

/-- Joint smoothness of `(r, z) ↦ iteratedDeriv ℓ (fun r' => f r' z) r` on `(0, ∞) × Plane`. -/
theorem contDiffOn_iteratedDeriv_age {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ)) (ℓ : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => iteratedDeriv ℓ (fun r => f r x.2) x.1)
      (Ioi 0 ×ˢ univ) := by
  refine contDiffOn_infty.2 fun m => ?_
  rintro ⟨r, z⟩ ⟨hr, -⟩
  exact (psiJet_slice_contDiffAt (fun y : ℝ × Plane => f y.1 y.2) hf ℓ m hr z).contDiffWithinAt

/-- If `f` is jointly `C^∞` on `(0, ∞) × Plane` and `hmean c (f r) η = 0` for all `r > 0`, then
for every `ℓ : ℕ` and `s > 0`, `hmean c (fun z => iteratedDeriv ℓ (fun r => f r z) s) η = 0`. -/
theorem hmean_iteratedDeriv_eq_zero {c : ℝ} (hc : 0 < c) {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    (h0 : ∀ r : ℝ, 0 < r → ∀ η : ℝ, hmean c (f r) η = 0) :
    ∀ (ℓ : ℕ) {s : ℝ}, 0 < s → ∀ η : ℝ,
      hmean c (fun z : Plane => iteratedDeriv ℓ (fun r => f r z) s) η = 0
  | 0, s, hs, η => h0 s hs η
  | ℓ + 1, s, hs, η => by
    have hev : (fun r => hmean c (fun z : Plane => iteratedDeriv ℓ (fun r' => f r' z) r) η) =ᶠ[𝓝 s]
        fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using hmean_iteratedDeriv_eq_zero hc hf h0 ℓ hr η
    have hd0 : deriv (fun r =>
        hmean c (fun z : Plane => iteratedDeriv ℓ (fun r' => f r' z) r) η) s = 0 := by
      rw [hev.deriv_eq, deriv_const]
    rw [hmeanDerivS c hc (fun r z => iteratedDeriv ℓ (fun r' => f r' z) r)
      (contDiffOn_iteratedDeriv_age hf ℓ) s hs η] at hd0
    simpa [iteratedDeriv_succ] using hd0

/-! ### 3. General-`ℓ` stream-fluctuation jet bounds from velocity-fluctuation jet bounds -/

/-- Periodic 1D fundamental theorem of calculus: if `g : ℝ → ℝ` is `c`-periodic (`c > 0`), has
zero integral over `(-c/2, c/2]`, and has continuous derivative `g'` bounded by `B ≥ 0`, then
`|g q| ≤ c * B` for all `q : ℝ`. -/
theorem abs_le_period_mul_of_periodic_mean_zero {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    {g g' : ℝ → ℝ} (hper : Function.Periodic g c)
    (hmean0 : hmean c (fun z : Plane => g z.1) 0 = 0)
    (hderiv : ∀ q : ℝ, HasDerivAt g (g' q) q)
    (hcont' : Continuous g')
    (hbound : ∀ q : ℝ, |g' q| ≤ B) (q : ℝ) :
    |g q| ≤ c * B := by
  have hg_cont : Continuous g := continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt
  have hle_c2 : -c / 2 ≤ c / 2 := by linarith
  have hint0 : ∫ x in (-c / 2)..(c / 2), g x = 0 := by
    unfold hmean at hmean0
    rw [← intervalIntegral.integral_of_le hle_c2, smul_eq_mul,
      mul_eq_zero, inv_eq_zero] at hmean0
    exact hmean0.resolve_left hc.ne'
  have hint_q : ∫ x in q..(q + c), g x = 0 := by
    have hshift := hper.intervalIntegral_add_eq q (-c / 2)
    have hadd : -c / 2 + c = c / 2 := by ring
    rwa [hadd, hint0] at hshift
  have hdiff_le : ∀ x ∈ Set.uIoc q (q + c), ‖g q - g x‖ ≤ c * B := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hqx : q ≤ x := hx.1.le
    have hxc : x - q ≤ c := by linarith [hx.2]
    have hftc : ∫ t in q..x, g' t = g x - g q :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hcont'.intervalIntegrable q x)
    have hnorm_ftc : ‖∫ t in q..x, g' t‖ ≤ B * |x - q| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
        rw [Real.norm_eq_abs]; exact hbound t
    rw [hftc, abs_of_nonneg (sub_nonneg.2 hqx), norm_sub_rev] at hnorm_ftc
    calc ‖g q - g x‖
        ≤ B * (x - q) := hnorm_ftc
      _ ≤ B * c := mul_le_mul_of_nonneg_left hxc hB
      _ = c * B := mul_comm B c
  have hint_sub : ∫ x in q..(q + c), (g q - g x) = c * g q := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hg_cont.intervalIntegrable _ _),
      intervalIntegral.integral_const, hint_q, sub_zero, smul_eq_mul]
    ring
  have hnorm_sub : ‖∫ x in q..(q + c), (g q - g x)‖ ≤ (c * B) * |q + c - q| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hdiff_le
  rw [hint_sub, show q + c - q = c by ring, abs_of_pos hc, Real.norm_eq_abs, abs_mul,
    abs_of_pos hc] at hnorm_sub
  exact le_of_mul_le_mul_left (by linarith) hc

/-- For `j = 0` and any `ℓ : ℕ`, if `wSupNorm 0 (ageJet ℓ 0 v_fluct s) ≤ ofReal B` (`B ≥ 0`),
then `wSupNorm 0 (ageJet ℓ 0 ψ_fluct s) ≤ ofReal (c * B)`. -/
theorem wSupNorm_zero_ageJet_streamFluct_zero_le {ν c B : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B)
    (tr : B0140.TrainSol ν c) (ℓ : ℕ) {s : ℝ} (hs : 0 < s)
    (hSupV : wSupNorm 0 (ageJet ℓ 0 (fun r => hfluct c (tr.v r)) s) ≤ ENNReal.ofReal B) :
    wSupNorm 0 (ageJet ℓ 0 (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤
      ENNReal.ofReal (c * B) := by
  let ψ_fluct : ℝ → Plane → ℝ := fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2
  let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
  have hsp : IsStreamPair ψ_fluct v_fluct := isStreamPair_ψ_fluct_v_fluct hν hc tr
  have hV_pt : ∀ w : Plane, ‖iteratedDeriv ℓ (fun r => v_fluct r w) s‖ ≤ B := by
    intro w
    have hw : ENNReal.ofReal (Real.sqrt (jap 0 w)) *
        ‖ageJet ℓ 0 v_fluct s w‖ₑ ≤ ENNReal.ofReal B :=
      (le_iSup (fun z : Plane => ENNReal.ofReal (Real.sqrt (jap 0 z)) *
        ‖ageJet ℓ 0 v_fluct s z‖ₑ) w).trans hSupV
    have hj0 : Real.sqrt (jap 0 w) = 1 := by simp [jap]
    rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm] at hw
    have h1 := (ENNReal.ofReal_le_ofReal_iff hB).1 hw
    unfold ageJet jet at h1
    rwa [norm_iteratedFDeriv_zero] at h1
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  unfold ageJet jet
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  let g : ℝ → ℝ := fun q => iteratedDeriv ℓ (fun r => ψ_fluct r (q, z.2)) s
  let g' : ℝ → ℝ := fun q => iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s 1
  have hper : Function.Periodic g c := by
    intro q
    have hev : (fun r => ψ_fluct r (q + c, z.2)) =ᶠ[𝓝 s] (fun r => ψ_fluct r (q, z.2)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      dsimp [ψ_fluct]
      rw [stream_periodic_q tr hr q z.2]
    exact hev.iteratedDeriv_eq ℓ
  have hmean0 : hmean c (fun w : Plane => g w.1) 0 = 0 := by
    have h0 := hmean_iteratedDeriv_eq_zero hc hsp.1
      (fun r hr η => hmean_ψ_fluct_eq_zero hc tr hr η) ℓ hs z.2
    exact h0
  have hderiv : ∀ q : ℝ, HasDerivAt g (g' q) q :=
    fun q => _root_.psiQSwap_proof ψ_fluct v_fluct hsp ℓ s hs q z.2
  have hcont_V : Continuous (fun w : Plane => iteratedDeriv ℓ (fun r => v_fluct r w) s) := by
    have hcd : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => v_fluct r w) s) :=
      contDiff_infty.2 fun n => contDiff_iff_contDiffAt.2 fun w =>
        vb_slice_contDiffAt (fun x : ℝ × Plane => v_fluct x.1 x.2) hsp.2.1 ℓ n hs w
    exact hcd.continuous
  have hcont' : Continuous g' :=
    ((PiLp.continuous_apply _ _ 1).comp hcont_V).comp (continuous_id.prodMk continuous_const)
  have hbound : ∀ q : ℝ, |g' q| ≤ B := by
    intro q
    have h1 : |g' q| ≤ ‖iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (iteratedDeriv ℓ (fun r => v_fluct r (q, z.2)) s) 1
    exact h1.trans (hV_pt (q, z.2))
  exact abs_le_period_mul_of_periodic_mean_zero hc hB hper hmean0 hderiv hcont' hbound z.1

/-- Linear map `w ↦ (h ↦ h₁ w₁ - h₂ w₀)` sending a velocity vector to the perpendicular gradient
functional on `Plane`. -/
def streamFluctGradMap : Vec →L[ℝ] (Plane →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        (w 1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (w 0) • ContinuousLinearMap.snd ℝ ℝ ℝ
      map_add' := fun a b => by
        refine ContinuousLinearMap.ext fun h => ?_
        simp [PiLp.add_apply]; ring
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext fun h => ?_
        simp [PiLp.smul_apply]; ring }

theorem streamFluctGradMap_apply (w : Vec) (h : Plane) :
    streamFluctGradMap w h = h.1 * w 1 - h.2 * w 0 := by
  simp [streamFluctGradMap]; ring

theorem norm_streamFluctGradMap_le_two : ‖streamFluctGradMap‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [streamFluctGradMap_apply, Real.norm_eq_abs]
  have h1 : |w 1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 1
  have h0 : |w 0| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 0
  have hh1 : |h.1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_fst_le h
  have hh2 : |h.2| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_snd_le h
  calc |h.1 * w 1 - h.2 * w 0| ≤ |h.1 * w 1| + |h.2 * w 0| := abs_sub _ _
    _ = |h.1| * |w 1| + |h.2| * |w 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖h‖ * ‖w‖ + ‖h‖ * ‖w‖ :=
        add_le_add (mul_le_mul hh1 h1 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hh2 h0 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖h‖ := by ring

/-- Pointwise bound `‖ageJet ℓ (k + 1) ψ_fluct s z‖ ≤ 2 * ‖ageJet ℓ k v_fluct s z‖` for all
`ℓ, k : ℕ`, `s > 0`, and `z : Plane`. -/
theorem norm_ageJet_streamFluct_succ_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖ ≤
      2 * ‖ageJet ℓ k (fun r => hfluct c (tr.v r)) s z‖ := by
  let ψ_fluct : ℝ → Plane → ℝ := fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2
  let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
  have hsp : IsStreamPair ψ_fluct v_fluct := isStreamPair_ψ_fluct_v_fluct hν hc tr
  set g : Plane → ℝ := fun z'' => iteratedDeriv ℓ (fun r => ψ_fluct r z'') s
  set V : Plane → Vec := fun z'' => iteratedDeriv ℓ (fun r => v_fluct r z'') s
  have hgC : ∀ z' : Plane, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g z' := fun z' =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => ψ_fluct x.1 x.2) hsp.1 ℓ (k + 1) hs z'
  have hVC : ∀ z' : Plane, ContDiffAt ℝ (k : WithTop ℕ∞) V z' := fun z' =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => v_fluct x.1 x.2) hsp.2.1 ℓ k hs z'
  have hdiff : ∀ z' : Plane, DifferentiableAt ℝ g z' := fun z' =>
    (hgC z').differentiableAt (by exact_mod_cast Nat.succ_ne_zero k)
  have hfd : ∀ z' : Plane, fderiv ℝ g z' = streamFluctGradMap (V z') := by
    intro z'
    refine ContinuousLinearMap.ext fun h => ?_
    have hq : HasDerivAt (fun q : ℝ => g (q, z'.2)) (fderiv ℝ g z' ((1 : ℝ), (0 : ℝ))) z'.1 := by
      have hl : HasDerivAt (fun q : ℝ => (q, z'.2)) ((1 : ℝ), (0 : ℝ)) z'.1 :=
        (hasDerivAt_id' z'.1).prodMk (hasDerivAt_const z'.1 z'.2)
      exact (hdiff z').hasFDerivAt.comp_hasDerivAt z'.1 hl
    have ht : HasDerivAt (fun t : ℝ => g (z'.1, t)) (fderiv ℝ g z' ((0 : ℝ), (1 : ℝ))) z'.2 := by
      have hl : HasDerivAt (fun t : ℝ => (z'.1, t)) ((0 : ℝ), (1 : ℝ)) z'.2 :=
        (hasDerivAt_const z'.2 z'.1).prodMk (hasDerivAt_id' z'.2)
      exact (hdiff z').hasFDerivAt.comp_hasDerivAt z'.2 hl
    have hq' := _root_.psiQSwap_proof ψ_fluct v_fluct hsp ℓ s hs z'.1 z'.2
    have ht' := _root_.psiEtaSwap_proof ψ_fluct v_fluct hsp ℓ s hs z'.1 z'.2
    have e1 : fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) = V z' 1 := hq.unique hq'
    have e2 : fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) = -(V z' 0) := ht.unique ht'
    have step : fderiv ℝ g z' h =
        h.1 * fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) + h.2 * fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) := by
      have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [step, e1, e2, streamFluctGradMap_apply]
    ring
  have hfun : fderiv ℝ g = fun z' => streamFluctGradMap (V z') := funext hfd
  show ‖iteratedFDeriv ℝ (k + 1) g z‖ ≤ 2 * ‖iteratedFDeriv ℝ k V z‖
  calc ‖iteratedFDeriv ℝ (k + 1) g z‖
      = ‖iteratedFDeriv ℝ k (fun z' => streamFluctGradMap (V z')) z‖ := by
        rw [← norm_iteratedFDeriv_fderiv, hfun]
    _ = ‖streamFluctGradMap.compContinuousMultilinearMap (iteratedFDeriv ℝ k V z)‖ := by
        rw [show (fun z' => streamFluctGradMap (V z')) = streamFluctGradMap ∘ V from rfl,
          ContinuousLinearMap.iteratedFDeriv_comp_left streamFluctGradMap (hVC z) (le_refl _)]
    _ ≤ ‖streamFluctGradMap‖ * ‖iteratedFDeriv ℝ k V z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 2 * ‖iteratedFDeriv ℝ k V z‖ :=
        mul_le_mul_of_nonneg_right norm_streamFluctGradMap_le_two (norm_nonneg _)

/-- For `j = k + 1` and any `ℓ : ℕ`, if `wSupNorm 0 (ageJet ℓ k v_fluct s) ≤ ofReal B` (`B ≥ 0`),
then `wSupNorm 0 (ageJet ℓ (k + 1) ψ_fluct s) ≤ ofReal (2 * B)`. -/
theorem wSupNorm_zero_ageJet_streamFluct_succ_le {ν c B : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s)
    (hSupV : wSupNorm 0 (ageJet ℓ k (fun r => hfluct c (tr.v r)) s) ≤ ENNReal.ofReal B) :
    wSupNorm 0 (ageJet ℓ (k + 1) (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤
      ENNReal.ofReal (2 * B) := by
  let ψ_fluct : ℝ → Plane → ℝ := fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2
  let v_fluct : ℝ → Plane → Vec := fun r => hfluct c (tr.v r)
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  have hz : ENNReal.ofReal (Real.sqrt (jap 0 z)) *
      ‖ageJet ℓ k v_fluct s z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 0 w)) *
      ‖ageJet ℓ k v_fluct s w‖ₑ) z).trans hSupV
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm] at hz
  have hz_real : ‖ageJet ℓ k v_fluct s z‖ ≤ B := (ENNReal.ofReal_le_ofReal_iff hB).1 hz
  have hpt := norm_ageJet_streamFluct_succ_le hν hc tr ℓ k hs z
  exact ENNReal.ofReal_le_ofReal (hpt.trans (mul_le_mul_of_nonneg_left hz_real (by norm_num)))

/-- **General-`ℓ` post-overlap stream fluctuation bound from velocity fluctuation `wSupNorm 0`:**
for any `ℓ, j : ℕ`, if `ageJet ℓ (j - 1) v_fluct` has post-overlap `wSupNorm 0` exponential decay,
then `ageJet ℓ j ψ_fluct` has post-overlap exponential decay in both `wCellL2 c 0` and
`wSupNorm 0`. -/
theorem postOverlap_streamFluct_of_velFluct_sup
    (hTails : TrainStreamVelocityPressureTails)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ j : ℕ)
    {C_v : ℝ} {N_v : ℕ} {lam_v ν_v : ℝ}
    (hC_v : 0 < C_v) (hlam_v : 0 < lam_v) (hν_v : 0 < ν_v)
    (hVel : ∀ ν : ℝ, 0 < ν → ν ≤ ν_v →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
          let c := trainPeriod ρ ν
          wSupNorm 0 (ageJet ℓ (j - 1) (fun r => hfluct c (tr.v r)) s) ≤
            ENNReal.ofReal (polyP C_v N_v ν c * Real.exp (-(lam_v * ν * s / c ^ 2)))) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            let c := trainPeriod ρ ν
            let K := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
            let ψ_fluct : ℝ → Plane → ℝ := fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2
            wCellL2 c 0 (ageJet ℓ j ψ_fluct s) ≤ K ∧
            wSupNorm 0 (ageJet ℓ j ψ_fluct s) ≤ K := by
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT4⟩ := hTails.2.2 ρ hρ 4 ℓ j
  obtain ⟨νp, hνp, _hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 1 one_pos
  let C₂ : ℝ := 2 * C_v
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  let N₂ : ℕ := N_v + 1
  let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam_v / 2) ^ N₁)⁻¹ * Real.exp (lam_v / 2)
  let C₃ : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
  let C_out := (PartI_T21.unitCellInvSqL2 + 1) * C₃
  let N_out := 2 * N₁ + N₂ + 1
  have hfac_pos : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hW : 0 < PartI_T21.unitCellInvSqL2 := PartI_T21.unitCellInvSqL2_pos
  have hC_out : 0 < C_out := mul_pos (by linarith) hC₃
  refine ⟨C_out, N_out, lam_v / 4, min ν₁ (min ν_v νp), hC_out,
    by positivity, lt_min hν₁ (lt_min hν_v hνp), ?_⟩
  intro ν hν hν_le tr htr s hs _hsc
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hνv_le : ν ≤ ν_v := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνp_le : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hc1, _⟩ := hp ν hν hνp_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have h4 : wSupNorm 4 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤
      ENNReal.ofReal (polyPS C₁ N₁ ν c s) :=
    (hT4 ν hν hν₁_le tr htr s hs).1.2
  have hVel_s := hVel ν hν hνv_le tr htr s hs _hsc
  set B_v : ℝ := polyP C_v N_v ν c * Real.exp (-(lam_v * ν * s / c ^ 2))
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hBv_nn : 0 ≤ B_v := by dsimp [B_v, polyP]; positivity
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
  have h0 : wSupNorm 0 (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤
      ENNReal.ofReal (polyP C₂ N₂ ν c * Real.exp (-(lam_v * ν * s / c ^ 2))) := by
    cases j with
    | zero =>
      have hψ0 := wSupNorm_zero_ageJet_streamFluct_zero_le hν hc_pos hBv_nn tr ℓ hs hVel_s
      refine hψ0.trans (ENNReal.ofReal_le_ofReal ?_)
      dsimp [B_v, C₂, N₂, polyP]
      have hpow : c * (1 + c + ν⁻¹) ^ N_v ≤ (1 + c + ν⁻¹) ^ (N_v + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right hcX (by positivity)
      calc c * (C_v * (1 + c + ν⁻¹) ^ N_v * Real.exp (-(lam_v * ν * s / c ^ 2)))
          = C_v * (c * (1 + c + ν⁻¹) ^ N_v) * Real.exp (-(lam_v * ν * s / c ^ 2)) := by ring
        _ ≤ (2 * C_v) * (1 + c + ν⁻¹) ^ (N_v + 1) *
              Real.exp (-(lam_v * ν * s / c ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact mul_le_mul (by linarith) hpow (by positivity) (by positivity)
    | succ k =>
      have hψk := wSupNorm_zero_ageJet_streamFluct_succ_le hν hc_pos hBv_nn tr ℓ k hs hVel_s
      refine hψk.trans (ENNReal.ofReal_le_ofReal ?_)
      dsimp [B_v, C₂, N₂, polyP]
      have hpow : (1 + c + ν⁻¹) ^ N_v ≤ (1 + c + ν⁻¹) ^ (N_v + 1) :=
        pow_le_pow_right₀ h1X (Nat.le_succ _)
      calc 2 * (C_v * (1 + c + ν⁻¹) ^ N_v * Real.exp (-(lam_v * ν * s / c ^ 2)))
          = (2 * C_v) * (1 + c + ν⁻¹) ^ N_v * Real.exp (-(lam_v * ν * s / c ^ 2)) := by ring
        _ ≤ (2 * C_v) * (1 + c + ν⁻¹) ^ (N_v + 1) *
              Real.exp (-(lam_v * ν * s / c ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero N₁ N₂ hC₁ hC₂ hlam_v hν hc1 hs.le
    (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) h4 h0

/-! ### 4. Linearity of `ageJet` and decomposition of `tr.p = p_fluct + p_mean` -/

/-- Spatial `C^∞` smoothness of `w ↦ iteratedDeriv ℓ (fun r => F r w) s` at fixed `s > 0`. -/
theorem contDiff_slice_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ)) (ℓ : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) :=
  contDiff_infty.2 fun n => contDiff_iff_contDiffAt.2 fun w =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ n hs w

/-- Age `C^m` smoothness of `r ↦ F r w` at `s > 0`. -/
theorem contDiffAt_age_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (w : Plane) (m : ℕ) :
    ContDiffAt ℝ m (fun r => F r w) s := by
  have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (s, w) :=
    hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  exact ContDiffAt.of_le (m := (m : WithTop ℕ∞))
    (h0.comp s (contDiffAt_id.prodMk contDiffAt_const)) (mod_cast le_top)

/-- Linearity of `ageJet ℓ j` over a sum of jointly smooth families at `s > 0`. -/
theorem ageJet_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j (fun r w => F r w + G r w) s z =
      ageJet ℓ j F s z + ageJet ℓ j G s z := by
  have hadd : (fun w : Plane => iteratedDeriv ℓ (fun r => F r w + G r w) s) =
      (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) +
        (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) := by
    funext w
    exact iteratedDeriv_add (contDiffAt_age_slice hF hs w ℓ) (contDiffAt_age_slice hG hs w ℓ)
  have hA : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) z :=
    ((contDiff_slice_iteratedDeriv hF ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  have hB : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) z :=
    ((contDiff_slice_iteratedDeriv hG ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w + G r w) s) z = _
  rw [hadd, iteratedFDeriv_add_apply hA hB]

/-- Linearity of `ageJet ℓ j` over a difference of jointly smooth families at `s > 0`. -/
theorem ageJet_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j (fun r w => F r w - G r w) s z =
      ageJet ℓ j F s z - ageJet ℓ j G s z := by
  have hsub : (fun w : Plane => iteratedDeriv ℓ (fun r => F r w - G r w) s) =
      (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) -
        (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) := by
    funext w
    exact iteratedDeriv_sub (contDiffAt_age_slice hF hs w ℓ) (contDiffAt_age_slice hG hs w ℓ)
  have hA : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) z :=
    ((contDiff_slice_iteratedDeriv hF ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  have hB : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) z :=
    ((contDiff_slice_iteratedDeriv hG ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w - G r w) s) z = _
  rw [hsub, iteratedFDeriv_sub_apply hA hB]

/-- Joint smoothness of `tr.p` on `(0, ∞) × Plane`. -/
theorem contDiffOn_p {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
  tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)

/-- Joint smoothness of `(r, z) ↦ hmean c (tr.p r) z.2` on `(0, ∞) × Plane`. -/
theorem contDiffOn_hmean_p {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (tr.p x.1) x.2.2) (Ioi 0 ×ˢ univ) := by
  have hm := hmeanContDiff c hc tr.p (contDiffOn_p tr)
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  exact hm.comp hproj.contDiffOn (fun _ hx => ⟨hx.1, mem_univ _⟩)

/-- Joint smoothness of `p_fluct(r, z) = tr.p r z - hmean c (tr.p r) z.2` on `(0, ∞) × Plane`. -/
theorem contDiffOn_p_fluct {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2 - hmean c (tr.p x.1) x.2.2)
      (Ioi 0 ×ˢ univ) :=
  (contDiffOn_p tr).sub (contDiffOn_hmean_p hc tr)

/-- Triangle inequality decomposing `wSupNorm m (ageJet ℓ j tr.p s)` into the nonzero-mode
pressure fluctuation `p_fluct(r, z) = tr.p r z - hmean c (tr.p r) z.2` and the horizontal mean
pressure `p_mean(r, z) = hmean c (tr.p r) z.2`. -/
theorem wSupNorm_ageJet_p_le_add_fluct_mean {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (m ℓ j : ℕ) {s : ℝ} (hs : 0 < s) :
    wSupNorm m (ageJet ℓ j tr.p s) ≤
      wSupNorm m (ageJet ℓ j (fun r z => tr.p r z - hmean c (tr.p r) z.2) s) +
        wSupNorm m (ageJet ℓ j (fun r z => hmean c (tr.p r) z.2) s) := by
  let p_fluct : ℝ → Plane → ℝ := fun r z => tr.p r z - hmean c (tr.p r) z.2
  let p_mean : ℝ → Plane → ℝ := fun r z => hmean c (tr.p r) z.2
  have hsum : tr.p = fun r z => p_fluct r z + p_mean r z := by
    funext r z; dsimp [p_fluct, p_mean]; ring
  have hjet : ageJet ℓ j tr.p s = fun z => ageJet ℓ j p_fluct s z + ageJet ℓ j p_mean s z := by
    funext z
    conv_lhs => rw [hsum]
    exact ageJet_add p_fluct p_mean (contDiffOn_p_fluct hc tr) (contDiffOn_hmean_p hc tr) hs ℓ j z
  rw [hjet]
  exact wSupNorm_add_le m (ageJet ℓ j p_fluct s) (ageJet ℓ j p_mean s)

end PartI_T22

/-! ### 5. Unconditional `ℓ = 0` stream fluctuation decay and leaf propositions for `PartI:T22/1` -/

/-- **Unconditional post-overlap (`ℓ = 0`) stream fluctuation decay:**
for all `ρ > 1/2` and `j : ℕ`, the stream fluctuation `ψ_fluct = tr.ψ - hmean c tr.ψ` satisfies
post-overlap exponential decay in both `wCellL2 c 0` and `wSupNorm 0`. -/
theorem trainPostOverlapStreamZero_proof
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : OverlapFluctuationDecay) :
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              let K := ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))
              let ψ_fluct : ℝ → Plane → ℝ := fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2
              wCellL2 c 0 (ageJet 0 j ψ_fluct s) ≤ K ∧
              wSupNorm 0 (ageJet 0 j ψ_fluct s) ≤ K := by
  intro ρ hρ j
  obtain ⟨C_v, N_v, lam_v, ν_v, hC_v, hlam_v, hν_v, hVel⟩ :=
    trainPostOverlapVelZero_of hFD ρ hρ (j - 1)
  exact PartI_T22.postOverlap_streamFluct_of_velFluct_sup hTails ρ hρ 0 j hC_v hlam_v hν_v
    fun ν hν hν_le tr htr s hs hsc => (hVel ν hν hν_le tr htr s hs hsc).2

/-- **Leaf 1 (`PartI:T22/1/1`, `TrainPostOverlapPressureMeanSupZero`):**
source lines 439-446, 515-522 of `the November 2 reference manuscript`.
On `s ≥ overlapAge ν c`, the horizontal-mean pressure `p_mean(r, z) = hmean c (tr.p r) z.2`
satisfies `\bar p(s, η) = -\overline{v₂(s, ·, η)²} = -\overline{\tilde v₂(s, ·, η)²}` (from the
horizontally averaged vertical momentum equation with `\bar v₂ = 0`, `trainMeanV2`, and decay at
`|η| → ∞`), so `wSupNorm 0 (ageJet 0 j p_mean s)` decays exponentially in `ν s / c²` from
`trainPostOverlapVelZero_of hFD`. -/
def TrainPostOverlapPressureMeanSupZero : Prop :=
  TrainStreamVelocityPressureTails → OverlapFluctuationDecay → TrainOverlap →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              wSupNorm 0 (ageJet 0 j (fun r z => hmean c (tr.p r) z.2) s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))

/-- **Leaf 2 (`PartI:T22/1/2`, `TrainPostOverlapPressureFluctSupZero`):**
source lines 439-446, 515-522 of `the November 2 reference manuscript`.
On `s ≥ overlapAge ν c`, the nonzero-mode pressure fluctuation
`p_fluct(r, z) = tr.p r z - hmean c (tr.p r) z.2` solves `-Δ p_fluct = ∂_i ∂_j (v_i v_j) -
hmean c (∂_i ∂_j (v_i v_j))` on `ℝ/cℤ × ℝ` with zero horizontal mean (where every nonzero mode of
`∂_i ∂_j (v_i v_j)` retains a velocity fluctuation factor `v_fluct = hfluct c (tr.v s)`), so
`wSupNorm 0 (ageJet 0 j p_fluct s)` decays exponentially in `ν s / c²` via the nonzero-mode
cylinder Poisson kernel, `trainPostOverlapVelZero_of hFD`, and `hTails.2.2`. -/
def TrainPostOverlapPressureFluctSupZero : Prop :=
  TrainStreamVelocityPressureTails → OverlapFluctuationDecay → TrainOverlap →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              wSupNorm 0 (ageJet 0 j (fun r z => tr.p r z - hmean c (tr.p r) z.2) s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))

/-- **Combined unweighted `L^∞` bound for post-overlap (`ℓ = 0`) Leray pressure jets:**
on `s ≥ overlapAge ν c`, `wSupNorm 0 (ageJet 0 j tr.p s)` decays exponentially in `ν s / c²`. -/
def TrainPostOverlapPressureSupZero : Prop :=
  TrainStreamVelocityPressureTails → OverlapFluctuationDecay → TrainOverlap →
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ j : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
              let c := trainPeriod ρ ν
              wSupNorm 0 (ageJet 0 j tr.p s) ≤
                ENNReal.ofReal (polyP C N ν c * Real.exp (-(lam * ν * s / c ^ 2)))

/-- Combines `TrainPostOverlapPressureMeanSupZero` and `TrainPostOverlapPressureFluctSupZero`
via `PartI_T22.wSupNorm_ageJet_p_le_add_fluct_mean` to establish `TrainPostOverlapPressureSupZero`. -/
theorem trainPostOverlapPressureSupZero_of
    (hMean : TrainPostOverlapPressureMeanSupZero)
    (hFluct : TrainPostOverlapPressureFluctSupZero) :
    TrainPostOverlapPressureSupZero := by
  intro hTails hFD hOv ρ hρ j
  obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hF⟩ := hFluct hTails hFD hOv ρ hρ j
  obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hM⟩ := hMean hTails hFD hOv ρ hρ j
  refine ⟨C₁ + C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
    add_pos hC₁ hC₂, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  have hc0 : 0 ≤ c := hc_pos.le
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have hF_s := hF ν hν hν₁_le tr htr s hs hsc
  have hM_s := hM ν hν hν₂_le tr htr s hs hsc
  have htri := PartI_T22.wSupNorm_ageJet_p_le_add_fluct_mean hc_pos tr 0 0 j hs
  let lam_out := min lam₁ lam₂
  let N_out := max N₁ N₂
  have hK₁ : polyP C₁ N₁ ν c * Real.exp (-(lam₁ * ν * s / c ^ 2)) ≤
      polyP C₁ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (le_max_left _ _)) hC₁.le
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hK₂ : polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) ≤
      polyP C₂ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (le_max_right _ _)) hC₂.le
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hadd_eq : polyP C₁ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) +
      polyP C₂ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) =
      polyP (C₁ + C₂) N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    unfold polyP; ring
  calc wSupNorm 0 (ageJet 0 j tr.p s)
      ≤ wSupNorm 0 (ageJet 0 j (fun r z => tr.p r z - hmean c (tr.p r) z.2) s) +
          wSupNorm 0 (ageJet 0 j (fun r z => hmean c (tr.p r) z.2) s) := htri
    _ ≤ ENNReal.ofReal (polyP C₁ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2))) +
          ENNReal.ofReal (polyP C₂ N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2))) :=
        add_le_add (hF_s.trans (ENNReal.ofReal_le_ofReal hK₁))
          (hM_s.trans (ENNReal.ofReal_le_ofReal hK₂))
    _ = ENNReal.ofReal (polyP (C₁ + C₂) N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2))) := by
        rw [← ENNReal.ofReal_add (by unfold polyP; positivity) (by unfold polyP; positivity),
          hadd_eq]

/-- Reduces `TrainPostOverlapStreamPressureZero` to `TrainPostOverlapPressureSupZero` using
`trainPostOverlapStreamZero_proof` and `PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero`. -/
theorem trainPostOverlapStreamPressureZero_of_sup
    (hPress : TrainPostOverlapPressureSupZero)
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : OverlapFluctuationDecay)
    (hOv : TrainOverlap) :
    TrainPostOverlapStreamPressureZero := by
  intro ρ hρ j
  obtain ⟨C_ψ, N_ψ, lam_ψ, ν_ψ, hC_ψ, hlam_ψ, hν_ψ, hψ⟩ :=
    trainPostOverlapStreamZero_proof hTails hFD ρ hρ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT4⟩ := hTails.2.2 ρ hρ 4 0 j
  obtain ⟨C₂, N₂, lam_p, ν_p, hC₂, hlam_p, hν_p, hp0⟩ := hPress hTails hFD hOv ρ hρ j
  obtain ⟨νp, hνp, _hνp1, hp_asymp⟩ := trainPeriodAsymptotics_proof ρ hρ 1 one_pos
  let K_abs : ℝ := (N₁.factorial : ℝ) * ((lam_p / 2) ^ N₁)⁻¹ * Real.exp (lam_p / 2)
  let C₃ : ℝ := Real.sqrt (2 * C₁ * C₂ * K_abs)
  let C_p := (PartI_T21.unitCellInvSqL2 + 1) * C₃
  let N_p := 2 * N₁ + N₂ + 1
  have hfac_pos : (0 : ℝ) < N₁.factorial := by exact_mod_cast N₁.factorial_pos
  have hK_abs : 0 < K_abs := by dsimp [K_abs]; positivity
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hW : 0 < PartI_T21.unitCellInvSqL2 := PartI_T21.unitCellInvSqL2_pos
  have hC_p : 0 < C_p := mul_pos (by linarith) hC₃
  let C_out := max C_ψ C_p
  let N_out := max N_ψ N_p
  let lam_out := min lam_ψ (lam_p / 4)
  let ν_out := min ν_ψ (min ν₁ (min ν_p νp))
  refine ⟨C_out, N_out, lam_out, ν_out, lt_max_of_lt_left hC_ψ,
    lt_min hlam_ψ (by positivity), lt_min hν_ψ (lt_min hν₁ (lt_min hν_p hνp)), ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hνψ_le : ν ≤ ν_ψ := hν_le.trans (min_le_left _ _)
  have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνp_le : ν ≤ ν_p :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνpa_le : ν ≤ νp :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hc1, _⟩ := hp_asymp ν hν hνpa_le
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
  obtain ⟨hψ_L2, hψ_Sup⟩ := hψ ν hν hνψ_le tr htr s hs hsc
  have hp4 : wSupNorm 4 (ageJet 0 j tr.p s) ≤ ENNReal.ofReal (polyPS C₁ N₁ ν c s) :=
    (hT4 ν hν hν₁_le tr htr s hs).2.2.2.2.2
  have hp0_s := hp0 ν hν hνp_le tr htr s hs hsc
  obtain ⟨hp_L2, hp_Sup⟩ := PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero
    N₁ N₂ hC₁ hC₂ hlam_p hν hc1 hs.le (ageJet 0 j tr.p s) hp4 hp0_s
  have hK_ψ : polyP C_ψ N_ψ ν c * Real.exp (-(lam_ψ * ν * s / c ^ 2)) ≤
      polyP C_out N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  have hK_p : polyP C_p N_p ν c * Real.exp (-((lam_p / 4) * ν * s / c ^ 2)) ≤
      polyP C_out N_out ν c * Real.exp (-(lam_out * ν * s / c ^ 2)) := by
    apply mul_le_mul
    · unfold polyP
      exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
        (by positivity) (by positivity)
    · apply Real.exp_le_exp.2
      apply neg_le_neg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)
    · exact Real.exp_nonneg _
    · unfold polyP; positivity
  exact ⟨⟨hψ_L2.trans (ENNReal.ofReal_le_ofReal hK_ψ),
      hψ_Sup.trans (ENNReal.ofReal_le_ofReal hK_ψ)⟩,
    ⟨hp_L2.trans (ENNReal.ofReal_le_ofReal hK_p),
      hp_Sup.trans (ENNReal.ofReal_le_ofReal hK_p)⟩⟩

/-- **Conditional assembly of `TrainPostOverlapStreamPressureZero` (`PartI:T22/1`):**
combines `trainPostOverlapStreamZero_proof`, `trainPostOverlapPressureSupZero_of`, and
`PartI_T22.wCellL2_zero_and_wSupNorm_zero_of_wSupNorm_zero` with the two leaves
`TrainPostOverlapPressureMeanSupZero` (`PartI:T22/1/1`) and
`TrainPostOverlapPressureFluctSupZero` (`PartI:T22/1/2`). -/
theorem trainPostOverlapStreamPressureZero_of
    (hMean : TrainPostOverlapPressureMeanSupZero)
    (hFluct : TrainPostOverlapPressureFluctSupZero)
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : OverlapFluctuationDecay)
    (hOv : TrainOverlap) :
    TrainPostOverlapStreamPressureZero :=
  trainPostOverlapStreamPressureZero_of_sup
    (trainPostOverlapPressureSupZero_of hMean hFluct) hTails hFD hOv

end UnforcedLeray.Short.PartI

end
