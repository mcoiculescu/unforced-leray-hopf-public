import UnforcedLeray.Short.PartI.Sub.PartI_T21_2
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail.Jet1D
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.NonzeroModeTail.LocalMP
import UnforcedLeray.Short.PartI.Sub.PartI_T20
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail.AgeDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.OverlapRescaling
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.VelocityWordLap
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.Spine.Proofs.EstDerivWordBridge
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSegment
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# `PartI:T21/2/1` (`Sub/PartI_T21_2/InteriorStripBounds.lean`): interior-strip jet bounds for `(ψ, v, p)`

Source of record: `the November 2 reference manuscript`, lines 499-526 (old 493-515).

This module proves:
1. **Stream pair structure for `(tr.ψ, tr.v)` and `(tr.p, perpGradP tr)`
   (`PartI_T21_2.isStreamPair_train_ψ_v`, `PartI_T21_2.isStreamPair_train_p_perpGradP`)**:
   for any BUC train `tr`, both `(tr.ψ, tr.v)` and `(tr.p, perpGradP tr)` form jointly `C^∞`
   stream pairs `IsStreamPair` on `(0, ∞) × Plane`.
2. **All-order stream-pair jet domination on any interior strip
   (`PartI_T21_2.norm_ageJet_streamPair_succ_le`,
   `PartI_T21_2.norm_ageJet_streamPair_zero_le_of_edge_and_vel`,
   `PartI_T21_2.trainInteriorStripStreamJetBounds_of_vel_at`)**:
   * for `j = k + 1` and all `ℓ : ℕ`, `∇^⊥(∂_s^ℓ F) = ∂_s^ℓ V` gives pointwise
     `‖ageJet ℓ (k + 1) F s z‖ ≤ 2 * ‖ageJet ℓ k V s z‖`;
   * for `j = 0` and all `ℓ : ℕ`, integrating `∂_η(∂_s^ℓ F) = -(∂_s^ℓ V)_0` along the
     vertical segment from `z.2` to the strip edge `R = max C' C'_{ℓ,0} / ν + 2`
     (`psiEtaSegment_proof`) and bounding the edge value `‖ageJet ℓ 0 F s (z.1, R)‖` via
     `hTail` at `(ℓ, 0)`, `l = 0`, `S_ = s` yields `‖ageJet ℓ 0 F s z‖ ≤ polyPS C_F N_F ν c s`
     on `|z.2| ≤ C' / ν + 2`.
3. **Elimination of the pressure interior-strip leaf from velocity interior-strip bounds + `hTail`
   (`PartI_T21_2.norm_ageJet_perpGradP_le`,
   `PartI_T21_2.trainInteriorStripPressJetBounds_of_vel`)**:
   by the train momentum equation `∇p = ν Δv - ∂_s v - (v · ∇)v` (`tr.isTrain.momentum`),
   `ageJet ℓ m (perpGradP tr)` is bounded by `ageJet r i tr.v` for `r ≤ ℓ + 1, i ≤ m + 2`,
   proving `TrainInteriorStripPressJetBounds` unconditionally from `hTail` and
   `TrainInteriorStripVelJetBounds`.
4. **Unconditional `ℓ = 0` interior-strip bounds and reduction to higher-age velocity bounds
   (`PartI_T21_2.trainInteriorStripVelZeroAge_proof`,
   `PartI_T21_2.trainInteriorStripStreamZeroAge_proof`,
   `PartI_T21_2.trainInteriorStripVelJetBounds_of_higher`,
   `trainInteriorStripJetBounds_of_higherVel`)**:
   combining `PartI_T20.train_v_jet_sup_bound` (`ℓ = 0`) with the stream and pressure reductions
   reduces `TrainInteriorStripJetBounds` to the single higher-age velocity leaf
   `TrainInteriorStripVelHigherAgeJetBounds` (`ℓ = m + 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVecL toVec_zero toVec_one norm_toVec jet
  lapS vecLaplacian gradS advection momentumResidual)
open UnforcedLeray.Short.IIb (IsStreamPair vb_slice_iteratedDeriv_eq vb_slice_contDiffAt)

namespace PartI_T21_2

/-! ### 1. Stream-pair structure and pointwise jet bounds for any `IsStreamPair F V` -/

/-- `(tr.ψ, tr.v)` is a jointly smooth stream pair on `(0, ∞) × Plane` for any BUC train `tr`. -/
theorem isStreamPair_train_ψ_v {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    IsStreamPair tr.ψ tr.v := by
  refine ⟨trainStreamSmooth ν c hν hc tr htr,
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl),
    fun s hs z => tr.isTrain.stream s hs.le z⟩

/-- Linear map `w ↦ (h ↦ h₁ w₁ - h₂ w₀)` sending a velocity vector to the perpendicular gradient
functional on `Plane`, with operator norm `≤ 2`. -/
def streamGradMap : Vec →L[ℝ] (Plane →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        (w 1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (w 0) • ContinuousLinearMap.snd ℝ ℝ ℝ
      map_add' := fun a b => by
        refine ContinuousLinearMap.ext fun h => ?_
        simp [PiLp.add_apply]; ring
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext fun h => ?_
        simp [PiLp.smul_apply]; ring }

theorem streamGradMap_apply (w : Vec) (h : Plane) :
    streamGradMap w h = h.1 * w 1 - h.2 * w 0 := by
  simp [streamGradMap]; ring

theorem norm_streamGradMap_le_two : ‖streamGradMap‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [streamGradMap_apply, Real.norm_eq_abs]
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

/-- For any stream pair `IsStreamPair F V`, `j = k + 1`, and all `ℓ : ℕ`, `s > 0`, `z : Plane`,
`‖ageJet ℓ (k + 1) F s z‖ ≤ 2 * ‖ageJet ℓ k V s z‖`. -/
theorem norm_ageJet_streamPair_succ_le {F : ℝ → Plane → ℝ} {V : ℝ → Plane → Vec}
    (hsp : IsStreamPair F V) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) F s z‖ ≤ 2 * ‖ageJet ℓ k V s z‖ := by
  set g : Plane → ℝ := fun z'' => iteratedDeriv ℓ (fun r => F r z'') s
  set W : Plane → Vec := fun z'' => iteratedDeriv ℓ (fun r => V r z'') s
  have hgC : ∀ z' : Plane, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g z' := fun z' =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hsp.1 ℓ (k + 1) hs z'
  have hWC : ∀ z' : Plane, ContDiffAt ℝ (k : WithTop ℕ∞) W z' := fun z' =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => V x.1 x.2) hsp.2.1 ℓ k hs z'
  have hdiff : ∀ z' : Plane, DifferentiableAt ℝ g z' := fun z' =>
    (hgC z').differentiableAt (by exact_mod_cast Nat.succ_ne_zero k)
  have hfd : ∀ z' : Plane, fderiv ℝ g z' = streamGradMap (W z') := by
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
    have hq' := _root_.psiQSwap_proof F V hsp ℓ s hs z'.1 z'.2
    have ht' := _root_.psiEtaSwap_proof F V hsp ℓ s hs z'.1 z'.2
    have e1 : fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) = W z' 1 := hq.unique hq'
    have e2 : fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) = -(W z' 0) := ht.unique ht'
    have step : fderiv ℝ g z' h =
        h.1 * fderiv ℝ g z' ((1 : ℝ), (0 : ℝ)) + h.2 * fderiv ℝ g z' ((0 : ℝ), (1 : ℝ)) := by
      have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [step, e1, e2, streamGradMap_apply]
    ring
  have hfun : fderiv ℝ g = fun z' => streamGradMap (W z') := funext hfd
  show ‖iteratedFDeriv ℝ (k + 1) g z‖ ≤ 2 * ‖iteratedFDeriv ℝ k W z‖
  calc ‖iteratedFDeriv ℝ (k + 1) g z‖
      = ‖iteratedFDeriv ℝ k (fun z' => streamGradMap (W z')) z‖ := by
        rw [← norm_iteratedFDeriv_fderiv, hfun]
    _ = ‖streamGradMap.compContinuousMultilinearMap (iteratedFDeriv ℝ k W z)‖ := by
        rw [show (fun z' => streamGradMap (W z')) = streamGradMap ∘ W from rfl,
          ContinuousLinearMap.iteratedFDeriv_comp_left streamGradMap (hWC z) le_rfl]
    _ ≤ ‖streamGradMap‖ * ‖iteratedFDeriv ℝ k W z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 2 * ‖iteratedFDeriv ℝ k W z‖ :=
        mul_le_mul_of_nonneg_right norm_streamGradMap_le_two (norm_nonneg _)

/-- For `j = k + 1` and all `ℓ : ℕ`, `s > 0`, `z : Plane`,
`‖ageJet ℓ (k + 1) tr.ψ s z‖ ≤ 2 * ‖ageJet ℓ k tr.v s z‖`. -/
theorem norm_ageJet_train_ψ_succ_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (k + 1) tr.ψ s z‖ ≤ 2 * ‖ageJet ℓ k tr.v s z‖ :=
  norm_ageJet_streamPair_succ_le (isStreamPair_train_ψ_v hν hc tr htr) ℓ k hs z

/-- For any stream pair `IsStreamPair F V` and `j = 0`, integrating along the vertical segment from
`z.2` to `R` bounds `‖ageJet ℓ 0 F s z‖ ≤ K_edge + 2 * R * K_vel` whenever `|z.2| ≤ R`,
`‖ageJet ℓ 0 F s (z.1, R)‖ ≤ K_edge`, and `‖ageJet ℓ 0 V s (z.1, η)‖ ≤ K_vel` for `|η| ≤ R`. -/
theorem norm_ageJet_streamPair_zero_le_of_edge_and_vel {F : ℝ → Plane → ℝ} {V : ℝ → Plane → Vec}
    {R K_edge K_vel : ℝ} (hsp : IsStreamPair F V) (hK_vel : 0 ≤ K_vel)
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) {z : Plane} (hz : |z.2| ≤ R)
    (hedge : ‖ageJet ℓ 0 F s (z.1, R)‖ ≤ K_edge)
    (hvel : ∀ η : ℝ, |η| ≤ R → ‖ageJet ℓ 0 V s (z.1, η)‖ ≤ K_vel) :
    ‖ageJet ℓ 0 F s z‖ ≤ K_edge + 2 * R * K_vel := by
  have hz' := abs_le.1 hz
  have hseg : ∀ t ∈ Set.uIcc z.2 R, ‖ageJet ℓ 0 V s (z.1, t)‖ ≤ K_vel := by
    intro t ht
    have ht' : |t| ≤ R := by
      rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.2 ⟨by linarith, by linarith⟩
      · exact abs_le.2 ⟨by linarith, by linarith⟩
    exact hvel t ht'
  have h1 := _root_.psiEtaSegment_proof F V hsp ℓ s hs z.1 z.2 R K_vel hseg
  have h3 : |z.2 - R| ≤ 2 * R := by
    rw [abs_le]; constructor <;> linarith
  have h4 : K_vel * |z.2 - R| ≤ K_vel * (2 * R) :=
    mul_le_mul_of_nonneg_left h3 hK_vel
  simp only [Prod.mk.eta] at h1
  linarith

/-- For `j = 0`, integrating along the vertical segment from `z.2` to `R` bounds
`‖ageJet ℓ 0 tr.ψ s z‖ ≤ K_edge + 2 * R * K_vel` whenever `|z.2| ≤ R`,
`‖ageJet ℓ 0 tr.ψ s (z.1, R)‖ ≤ K_edge`, and `‖ageJet ℓ 0 tr.v s (z.1, η)‖ ≤ K_vel` for `|η| ≤ R`. -/
theorem norm_ageJet_train_ψ_zero_le_of_edge_and_vel {ν c R K_edge K_vel : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hK_vel : 0 ≤ K_vel)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) (ℓ : ℕ) {s : ℝ} (hs : 0 < s)
    {z : Plane} (hz : |z.2| ≤ R)
    (hedge : ‖ageJet ℓ 0 tr.ψ s (z.1, R)‖ ≤ K_edge)
    (hvel : ∀ η : ℝ, |η| ≤ R → ‖ageJet ℓ 0 tr.v s (z.1, η)‖ ≤ K_vel) :
    ‖ageJet ℓ 0 tr.ψ s z‖ ≤ K_edge + 2 * R * K_vel :=
  norm_ageJet_streamPair_zero_le_of_edge_and_vel
    (isStreamPair_train_ψ_v hν hc tr htr) hK_vel ℓ hs hz hedge hvel

/-! ### 2. Reduction of `tr.ψ` interior-strip bounds to `tr.v` interior-strip bounds + `hTail` -/

/-- **Interior-strip bound for `tr.v` (`ageJet ℓ j tr.v`)**:
for every `ρ > 1/2`, derivative orders `ℓ, j : ℕ`, and half-width parameter `C' > 0`,
`‖ageJet ℓ j tr.v s z‖ ≤ polyPS C_v N_v ν c s` on `|z.2| ≤ C' / ν + 2`. -/
def TrainInteriorStripVelJetBounds : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∀ C' : ℝ, 0 < C' →
    ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet ℓ j tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s

/-- **Interior-strip bound for `tr.p` (`ageJet ℓ j tr.p`)**:
for every `ρ > 1/2`, derivative orders `ℓ, j : ℕ`, and half-width parameter `C' > 0`,
`‖ageJet ℓ j tr.p s z‖ ≤ polyPS C_p N_p ν c s` on `|z.2| ≤ C' / ν + 2`. -/
def TrainInteriorStripPressJetBounds : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∀ C' : ℝ, 0 < C' →
    ∃ C_p : ℝ, ∃ N_p : ℕ, ∃ ν₀ : ℝ, 0 < C_p ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet ℓ j tr.p s z‖ ≤ polyPS C_p N_p ν (trainPeriod ρ ν) s

/-- Given `hTail : TrainStreamVelocityPressureTransverseTail` and an interior-strip bound for
`ageJet ℓ (j - 1) tr.v` on every strip `|z.2| ≤ C'' / ν + 2`, the stream jet `ageJet ℓ j tr.ψ`
satisfies `‖ageJet ℓ j tr.ψ s z‖ ≤ polyPS C_ψ N_ψ ν c s` on `|z.2| ≤ C' / ν + 2`. -/
theorem trainInteriorStripStreamJetBounds_of_vel_at
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ j : ℕ) (C' : ℝ) (hC' : 0 < C')
    (hVel : ∀ C'' : ℝ, 0 < C'' →
      ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν_v : ℝ, 0 < C_v ∧ 0 < ν_v ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν_v →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
            ∀ z : Plane, |z.2| ≤ C'' / ν + 2 →
              ‖ageJet ℓ (j - 1) tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s) :
    ∃ C_ψ : ℝ, ∃ N_ψ : ℕ, ∃ ν₀ : ℝ, 0 < C_ψ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet ℓ j tr.ψ s z‖ ≤ polyPS C_ψ N_ψ ν (trainPeriod ρ ν) s := by
  cases j with
  | zero =>
    obtain ⟨b₀, C₀, C'_t, hb₀, hC₀, hC'_t, C_t, N_t, ν_t, hC_t, hν_t, hT0⟩ := hTail ρ hρ ℓ 0
    let C'' : ℝ := max C' C'_t
    have hC'' : 0 < C'' := lt_max_of_lt_left hC'
    obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hV0⟩ := hVel C'' hC''
    let C_ψ : ℝ := 2 * C_t + (2 * C'' + 4) * C_v
    let N_ψ : ℕ := max N_t (N_v + 1)
    have hC_ψ : 0 < C_ψ := by dsimp [C_ψ]; positivity
    refine ⟨C_ψ, N_ψ, min ν_t ν_v, hC_ψ, lt_min hν_t hν_v, ?_⟩
    intro ν hν hν_le tr htr s hs z hz
    have hν_t_le : ν ≤ ν_t := hν_le.trans (min_le_left _ _)
    have hν_v_le : ν ≤ ν_v := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let R : ℝ := C'' / ν + 2
    have hR_pos : 0 < R := by dsimp [R]; positivity
    have hzR : |z.2| ≤ R := by
      have hle : C' / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      dsimp [R]; linarith
    have hedge_R : C'_t / ν + 2 + 0 ≤ |((z.1, R) : Plane).2| := by
      change C'_t / ν + 2 + 0 ≤ |R|
      rw [abs_of_pos hR_pos, add_zero]
      have hle : C'_t / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      dsimp [R]; linarith
    have hedge_raw := (hT0 s hs.le ν hν hν_t_le tr htr 0 le_rfl s hs le_rfl (z.1, R) hedge_R).1
    have hedge : ‖ageJet ℓ 0 tr.ψ s (z.1, R)‖ ≤ 2 * polyPS C_t N_t ν c s := by
      refine hedge_raw.trans ?_
      have hexp : Real.exp (-(b₀ * 0 / c)) + Real.exp (-(b₀ * 0 ^ 2 / (C₀ + ν * s))) = 2 := by
        simp; norm_num
      rw [hexp]
      linarith
    have hK_vel_nn : 0 ≤ polyPS C_v N_v ν c s := by unfold polyPS; positivity
    have hvel_R : ∀ η : ℝ, |η| ≤ R → ‖ageJet ℓ 0 tr.v s (z.1, η)‖ ≤ polyPS C_v N_v ν c s :=
      fun η hη => hV0 ν hν hν_v_le tr htr s hs (z.1, η) hη
    have hpt := norm_ageJet_train_ψ_zero_le_of_edge_and_vel hν hc hK_vel_nn tr htr ℓ hs hzR
      hedge hvel_R
    refine hpt.trans ?_
    have h1Xs : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by
      have : 1 ≤ 1 + c + ν⁻¹ := by
        have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
        linarith
      have : 1 ≤ 1 + s := by linarith
      nlinarith
    have hpow_t : ((1 + c + ν⁻¹) * (1 + s)) ^ N_t ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ :=
      pow_le_pow_right₀ h1Xs (le_max_left _ _)
    have hpow_v : ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + 1) ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ :=
      pow_le_pow_right₀ h1Xs (le_max_right _ _)
    have h2R : 2 * R ≤ (2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s)) := by
      have hR_eq : 2 * R = 2 * C'' * ν⁻¹ + 4 := by dsimp [R]; ring
      rw [hR_eq]
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have h1 : 2 * C'' * ν⁻¹ + 4 ≤ (2 * C'' + 4) * (1 + c + ν⁻¹) := by nlinarith
      have h2 : (2 * C'' + 4) * (1 + c + ν⁻¹) * 1 ≤
          (2 * C'' + 4) * (1 + c + ν⁻¹) * (1 + s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hterm1 : 2 * polyPS C_t N_t ν c s ≤
        2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ := by
      unfold polyPS
      calc 2 * (C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t)
          = 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t := by ring
        _ ≤ 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ :=
            mul_le_mul_of_nonneg_left hpow_t (by positivity)
    have hterm2 : 2 * R * polyPS C_v N_v ν c s ≤
        (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ := by
      unfold polyPS
      calc 2 * R * (C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_v)
          ≤ ((2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s))) *
              (C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_v) :=
            mul_le_mul_of_nonneg_right h2R (by positivity)
        _ = (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + 1) := by
            rw [pow_succ']; ring
        _ ≤ (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ψ :=
            mul_le_mul_of_nonneg_left hpow_v (by positivity)
    unfold polyPS at hterm1 hterm2 ⊢
    dsimp [C_ψ, c] at hterm1 hterm2 ⊢
    linarith
  | succ k =>
    obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hVk⟩ := hVel C' hC'
    refine ⟨2 * C_v, N_v, ν_v, by positivity, hν_v, ?_⟩
    intro ν hν hν_le tr htr s hs z hz
    have hc : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
    have h1 := norm_ageJet_train_ψ_succ_le hν hc tr htr ℓ k hs z
    have h2 := hVk ν hν hν_le tr htr s hs z hz
    calc ‖ageJet ℓ (k + 1) tr.ψ s z‖
        ≤ 2 * ‖ageJet ℓ k tr.v s z‖ := h1
      _ ≤ 2 * polyPS C_v N_v ν (trainPeriod ρ ν) s :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = polyPS (2 * C_v) N_v ν (trainPeriod ρ ν) s := by
          unfold polyPS; ring

/-! ### 3. Unconditional `ℓ = 0` interior-strip bounds for `tr.v` and `tr.ψ` -/

/-- **Unconditional `ℓ = 0` velocity interior-strip bound**:
for all `ρ > 1/2`, `j : ℕ`, and `C' > 0`, `‖ageJet 0 j tr.v s z‖ ≤ polyPS C_v 1 ν c s`
for all `s > 0` and `z : Plane` (hence on `|z.2| ≤ C' / ν + 2`), proved from
`PartI_T20.train_v_jet_sup_bound`. -/
theorem trainInteriorStripVelZeroAge_proof (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ)
    (C' : ℝ) (_hC' : 0 < C') :
    ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet 0 j tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s := by
  obtain ⟨C_v, ν₀, hC_v, hν₀, hv⟩ := PartI_T20.train_v_jet_sup_bound ρ hρ j
  refine ⟨C_v, 1, ν₀, hC_v, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs z _hz
  have h1 : ‖ageJet 0 j tr.v s z‖ ≤ polyP C_v 1 ν (trainPeriod ρ ν) := hv ν hν hν_le tr htr s hs z
  refine h1.trans ?_
  unfold polyP polyPS
  rw [pow_one, pow_one]
  have hc0 : 0 ≤ trainPeriod ρ ν := (Real.rpow_pos_of_pos hν _).le
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have : C_v * (1 + trainPeriod ρ ν + ν⁻¹) * 1 ≤
      C_v * (1 + trainPeriod ρ ν + ν⁻¹) * (1 + s) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **Unconditional `ℓ = 0` stream interior-strip bound**:
for all `ρ > 1/2`, `j : ℕ`, and `C' > 0`, `‖ageJet 0 j tr.ψ s z‖ ≤ polyPS C_ψ N_ψ ν c s`
on `|z.2| ≤ C' / ν + 2`, proved from `trainInteriorStripVelZeroAge_proof` and `hTail`. -/
theorem trainInteriorStripStreamZeroAge_proof
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) (C' : ℝ) (hC' : 0 < C') :
    ∃ C_ψ : ℝ, ∃ N_ψ : ℕ, ∃ ν₀ : ℝ, 0 < C_ψ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet 0 j tr.ψ s z‖ ≤ polyPS C_ψ N_ψ ν (trainPeriod ρ ν) s :=
  trainInteriorStripStreamJetBounds_of_vel_at hTail ρ hρ 0 j C' hC'
    (fun C'' hC'' => trainInteriorStripVelZeroAge_proof ρ hρ (j - 1) C'' hC'')

/-! ### 4. Elimination of `TrainInteriorStripPressJetBounds` from `tr.v` interior-strip bounds -/

/-- Perpendicular gradient `∇^⊥ p = (-∂_η p, ∂_q p)` of the train pressure `tr.p`. -/
def perpGradP {ν c : ℝ} (tr : B0140.TrainSol ν c) : ℝ → Plane → Vec :=
  fun r z => toVec (UnforcedLeray.GaussianVortex.perpendicularGradient (tr.p r) z)

/-- `(tr.p, perpGradP tr)` is a jointly smooth stream pair on `(0, ∞) × Plane`. -/
theorem isStreamPair_train_p_perpGradP {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    IsStreamPair tr.p (perpGradP tr) := by
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (tr.p x.1) x.2) :=
    PartI_T20.smR_partialQ (F := tr.p) hsm_p
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (tr.p x.1) x.2) :=
    PartI_T20.smR_partialEta (F := tr.p) hsm_p
  refine ⟨hsm_p, ?_, fun _ _ _ => rfl⟩
  exact toVecL.contDiff.comp_contDiffOn (hsm_E.neg.prodMk hsm_Q)

/-- Linear embedding `a ↦ toVec (-a, 0)` from `ℝ` to `Vec`, with operator norm `≤ 1`. -/
def perpEmbed0 : ℝ →L[ℝ] Vec :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (toVec (-1, 0))

/-- Linear embedding `b ↦ toVec (0, b)` from `ℝ` to `Vec`, with operator norm `≤ 1`. -/
def perpEmbed1 : ℝ →L[ℝ] Vec :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (toVec (0, 1))

theorem norm_perpEmbed0_le_one : ‖perpEmbed0‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  change ‖a • toVec (-1, 0)‖ ≤ 1 * ‖a‖
  rw [norm_smul, norm_toVec (-1, 0)]
  have h1 : ((-1 : ℝ), (0 : ℝ)).1 ^ 2 + ((-1 : ℝ), (0 : ℝ)).2 ^ 2 = 1 := by norm_num
  rw [h1, Real.sqrt_one]
  linarith

theorem norm_perpEmbed1_le_one : ‖perpEmbed1‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_
  change ‖b • toVec (0, 1)‖ ≤ 1 * ‖b‖
  rw [norm_smul, norm_toVec (0, 1)]
  have h1 : ((0 : ℝ), (1 : ℝ)).1 ^ 2 + ((0 : ℝ), (1 : ℝ)).2 ^ 2 = 1 := by norm_num
  rw [h1, Real.sqrt_one]
  linarith

theorem toVec_neg_fst_eq_perpEmbed (a b : ℝ) :
    toVec (-a, b) = perpEmbed0 a + perpEmbed1 b := by
  refine UnforcedLeray.Train.Vec.ext ?_ ?_
  · simp [perpEmbed0, perpEmbed1]
  · simp [perpEmbed0, perpEmbed1]

theorem iteratedDeriv_clm_comp_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (G : ℝ → Plane → E)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (w : Plane) :
    iteratedDeriv ℓ (fun r => L (G r w)) s = L (iteratedDeriv ℓ (fun r => G r w) s) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hx : (s, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs, Set.mem_univ _⟩
  have hLG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => L (G x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    L.contDiff.comp_contDiffOn hG
  have e1 := vb_slice_iteratedDeriv_eq (fun x : ℝ × Plane => L (G x.1 x.2)) hLG ℓ hs w
  have e2 := vb_slice_iteratedDeriv_eq (fun x : ℝ × Plane => G x.1 x.2) hG ℓ hs w
  have hcomp : iteratedFDeriv ℝ ℓ (fun x : ℝ × Plane => L (G x.1 x.2)) (s, w) =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ ℓ (fun x : ℝ × Plane => G x.1 x.2) (s, w)) := by
    have h := ContinuousLinearMap.iteratedFDerivWithin_comp_left L (hG.contDiffWithinAt hx)
      hU.uniqueDiffOn hx (i := ℓ) (mod_cast le_top)
    rwa [iteratedFDerivWithin_of_isOpen ℓ hU hx, iteratedFDerivWithin_of_isOpen ℓ hU hx] at h
  rw [e1, hcomp, e2]
  rfl

theorem norm_ageJet_clm_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (G : ℝ → Plane → E)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (fun r w => L (G r w)) s z‖ ≤ ‖L‖ * ‖ageJet ℓ j G s z‖ := by
  have hslice : (fun w => iteratedDeriv ℓ (fun r => L (G r w)) s) =
      (L ∘ fun w => iteratedDeriv ℓ (fun r => G r w) s) :=
    funext fun w => iteratedDeriv_clm_comp_eq L G hG ℓ hs w
  have hu : ContDiffAt ℝ (j : WithTop ℕ∞) (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) z :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs z
  unfold ageJet jet
  rw [hslice]
  exact L.norm_iteratedFDeriv_comp_left hu le_rfl

theorem norm_ageJet_perpGradP_le_partials {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j (perpGradP tr) s z‖ ≤
      ‖ageJet ℓ j (fun r w => Cyl.partialEta (tr.p r) w) s z‖ +
        ‖ageJet ℓ j (fun r w => Cyl.partialQ (tr.p r) w) s z‖ := by
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (tr.p x.1) x.2) :=
    PartI_T20.smR_partialEta (F := tr.p) hsm_p
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (tr.p x.1) x.2) :=
    PartI_T20.smR_partialQ (F := tr.p) hsm_p
  have heq : perpGradP tr = fun r w =>
      perpEmbed0 (Cyl.partialEta (tr.p r) w) + perpEmbed1 (Cyl.partialQ (tr.p r) w) := by
    funext r w
    exact toVec_neg_fst_eq_perpEmbed (Cyl.partialEta (tr.p r) w) (Cyl.partialQ (tr.p r) w)
  have hadd := PartI_T20.ageJet_add
    (fun r w => perpEmbed0 (Cyl.partialEta (tr.p r) w))
    (fun r w => perpEmbed1 (Cyl.partialQ (tr.p r) w))
    (perpEmbed0.contDiff.comp_contDiffOn hsm_E)
    (perpEmbed1.contDiff.comp_contDiffOn hsm_Q) hs ℓ j z
  have h0 := (norm_ageJet_clm_comp_le perpEmbed0
    (fun r w => Cyl.partialEta (tr.p r) w) hsm_E ℓ j hs z).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_perpEmbed0_le_one)
  have h1 := (norm_ageJet_clm_comp_le perpEmbed1
    (fun r w => Cyl.partialQ (tr.p r) w) hsm_Q ℓ j hs z).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_perpEmbed1_le_one)
  rw [heq, hadd]
  exact (norm_add_le _ _).trans (add_le_add h0 h1)

/-- Component `k : Fin 2` of the momentum-equation RHS `ν Δv_k - ∂_s v_k - v_0 ∂_q v_k - v_1 ∂_η v_k`. -/
def momGradRHS (ν : ℝ) (v : ℝ → Plane → Vec) (k : Fin 2) (t : ℝ) (w : Plane) : ℝ :=
  ν * lapS (fun y => v t y k) w
  - PartI_T20.DtR 1 (fun y : ℝ × Plane => v y.1 y.2 k) (t, w)
  - v t w 0 * Cyl.partialQ (fun y => v t y k) w
  - v t w 1 * Cyl.partialEta (fun y => v t y k) w

theorem partialQ_train_p_eq_momGradRHS {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialQ (tr.p t) w = momGradRHS ν tr.v 0 t w := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have m := congrArg (fun X : Vec => X 0) (tr.isTrain.momentum t ht w)
  simp only [momentumResidual, advection, vecLaplacian, gradS,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    toVec_zero, PiLp.zero_apply] at m
  have hd1 := PartI_T20.iteratedDeriv_vec_proj_eq hsm_v 0 1 ht w
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  have hd2 := PartI_T20.iteratedDeriv_slice_eq_DtR (F := fun y : ℝ × Plane => tr.v y.1 y.2 0)
    hsm_v0 1 ht w
  rw [iteratedDeriv_one] at hd2
  unfold momGradRHS
  linarith

theorem partialEta_train_p_eq_momGradRHS {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (w : Plane) :
    Cyl.partialEta (tr.p t) w = momGradRHS ν tr.v 1 t w := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have m := congrArg (fun X : Vec => X 1) (tr.isTrain.momentum t ht w)
  simp only [momentumResidual, advection, vecLaplacian, gradS,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    toVec_one, PiLp.zero_apply] at m
  have hd1 := PartI_T20.iteratedDeriv_vec_proj_eq hsm_v 1 1 ht w
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  have hd2 := PartI_T20.iteratedDeriv_slice_eq_DtR (F := fun y : ℝ × Plane => tr.v y.1 y.2 1)
    hsm_v1 1 ht w
  rw [iteratedDeriv_one] at hd2
  unfold momGradRHS
  linarith

theorem ageJet_DtR_one_eq {F : ℝ → Plane → ℝ}
    (hF : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet ℓ j (fun r w => PartI_T20.DtR 1 (fun y : ℝ × Plane => F y.1 y.2) (r, w)) s z =
      ageJet (ℓ + 1) j F s z := by
  unfold ageJet
  congr 1
  funext w
  rw [iteratedDeriv_succ']
  have hev : (fun r => PartI_T20.DtR 1 (fun y : ℝ × Plane => F y.1 y.2) (r, w)) =ᶠ[nhds s]
      deriv (fun t => F t w) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    rw [← PartI_T20.iteratedDeriv_slice_eq_DtR hF 1 hr w, iteratedDeriv_one]
  exact hev.iteratedDeriv_eq ℓ

theorem norm_ageJet_momGradRHS_le {ν c M_v : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hMv : 0 ≤ M_v)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hbd : ∀ r ≤ ℓ + 1, ∀ i ≤ j + 2, ‖ageJet r i tr.v s z‖ ≤ M_v) :
    ‖ageJet ℓ j (momGradRHS ν tr.v k) s z‖ ≤
      3 * M_v + 2 * (2 : ℝ) ^ (ℓ + j) * M_v * M_v := by
  have hsm_v : UnforcedLeray.Short.IIb.Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  let F₁ : ℝ → Plane → ℝ := fun r w => ν * lapS (fun y => tr.v r y k) w
  let F₂ : ℝ → Plane → ℝ := fun r w => PartI_T20.DtR 1 (fun y : ℝ × Plane => tr.v y.1 y.2 k) (r, w)
  let F₃ : ℝ → Plane → ℝ := fun r w => tr.v r w 0 * Cyl.partialQ (fun y => tr.v r y k) w
  let F₄ : ℝ → Plane → ℝ := fun r w => tr.v r w 1 * Cyl.partialEta (fun y => tr.v r y k) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => F₁ x.1 x.2) :=
    PartI_T20.smR_mul_lapS (F := fun r w => tr.v r w k) hsm_vk ν
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => F₂ x.1 x.2) :=
    PartI_T20.smR_DtR hsm_vk 1
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => F₃ x.1 x.2) :=
    hsm_v0.mul (PartI_T20.smR_partialQ (F := fun r w => tr.v r w k) hsm_vk)
  have hsm₄ : PartI_T20.SmR (fun x : ℝ × Plane => F₄ x.1 x.2) :=
    hsm_v1.mul (PartI_T20.smR_partialEta (F := fun r w => tr.v r w k) hsm_vk)
  have hsub3 := PartI_T20.ageJet_sub (fun r w => F₁ r w - F₂ r w - F₃ r w) F₄
    ((hsm₁.sub hsm₂).sub hsm₃) hsm₄ hs ℓ j z
  have hsub2 := PartI_T20.ageJet_sub (fun r w => F₁ r w - F₂ r w) F₃
    (hsm₁.sub hsm₂) hsm₃ hs ℓ j z
  have hsub1 := PartI_T20.ageJet_sub F₁ F₂ hsm₁ hsm₂ hs ℓ j z
  have hsplit : ageJet ℓ j (momGradRHS ν tr.v k) s z =
      ageJet ℓ j F₁ s z - ageJet ℓ j F₂ s z - ageJet ℓ j F₃ s z - ageJet ℓ j F₄ s z := by
    change ageJet ℓ j (fun r w => F₁ r w - F₂ r w - F₃ r w - F₄ r w) s z = _
    rw [hsub3, hsub2, hsub1]
  have hb₁ : ‖ageJet ℓ j F₁ s z‖ ≤ 2 * M_v := by
    calc ‖ageJet ℓ j F₁ s z‖
        ≤ (2 * ν) * ‖ageJet ℓ (j + 2) (fun r w => tr.v r w k) s z‖ :=
          PartI_T20.norm_ageJet_mul_lapS_le (F := fun r w => tr.v r w k) hsm_vk hν ℓ j hs z
      _ ≤ 2 * ‖ageJet ℓ (j + 2) (fun r w => tr.v r w k) s z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ 2 * ‖ageJet ℓ (j + 2) tr.v s z‖ :=
          mul_le_mul_of_nonneg_left (PartI_T20.norm_ageJet_vec_proj_le hsm_v k ℓ (j + 2) hs z) (by norm_num)
      _ ≤ 2 * M_v :=
          mul_le_mul_of_nonneg_left (hbd ℓ (Nat.le_succ ℓ) (j + 2) le_rfl) (by norm_num)
  have hb₂ : ‖ageJet ℓ j F₂ s z‖ ≤ M_v := by
    rw [ageJet_DtR_one_eq (F := fun r w => tr.v r w k) hsm_vk ℓ j hs z]
    exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v k (ℓ + 1) j hs z).trans
      (hbd (ℓ + 1) le_rfl j (by omega))
  have hb₃ : ‖ageJet ℓ j F₃ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_v * M_v := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 0) (B := fun r w => Cyl.partialQ (fun y => tr.v r y k) w)
      hsm_v0 (PartI_T20.smR_partialQ (F := fun r w => tr.v r w k) hsm_vk)
      ℓ j hs hMv hMv z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 0 r i hs z).trans
        (hbd r (by omega) i (by omega))
    · exact (PartI_T20.norm_ageJet_partialQ_le (F := fun r w => tr.v r w k) hsm_vk r i hs z).trans
        ((PartI_T20.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs z).trans
          (hbd r (by omega) (i + 1) (by omega)))
  have hb₄ : ‖ageJet ℓ j F₄ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_v * M_v := by
    refine PartI_T20.norm_ageJet_mul_le
      (A := fun r w => tr.v r w 1) (B := fun r w => Cyl.partialEta (fun y => tr.v r y k) w)
      hsm_v1 (PartI_T20.smR_partialEta (F := fun r w => tr.v r w k) hsm_vk)
      ℓ j hs hMv hMv z (fun r hr i hi => ?_) (fun r hr i hi => ?_)
    · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs z).trans
        (hbd r (by omega) i (by omega))
    · exact (PartI_T20.norm_ageJet_partialEta_le (F := fun r w => tr.v r w k) hsm_vk r i hs z).trans
        ((PartI_T20.norm_ageJet_vec_proj_le hsm_v k r (i + 1) hs z).trans
          (hbd r (by omega) (i + 1) (by omega)))
  rw [hsplit]
  have hn1 := norm_sub_le (ageJet ℓ j F₁ s z - ageJet ℓ j F₂ s z - ageJet ℓ j F₃ s z)
    (ageJet ℓ j F₄ s z)
  have hn2 := norm_sub_le (ageJet ℓ j F₁ s z - ageJet ℓ j F₂ s z) (ageJet ℓ j F₃ s z)
  have hn3 := norm_sub_le (ageJet ℓ j F₁ s z) (ageJet ℓ j F₂ s z)
  linarith

/-- Pointwise bound on `ageJet ℓ j (perpGradP tr) s z` from velocity mixed jets up to `(ℓ + 1, j + 2)`. -/
theorem norm_ageJet_perpGradP_le {ν c M_v : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hMv : 0 ≤ M_v)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hbd : ∀ r ≤ ℓ + 1, ∀ i ≤ j + 2, ‖ageJet r i tr.v s z‖ ≤ M_v) :
    ‖ageJet ℓ j (perpGradP tr) s z‖ ≤
      6 * M_v + 4 * (2 : ℝ) ^ (ℓ + j) * M_v * M_v := by
  have hQ_eq : ageJet ℓ j (fun r w => Cyl.partialQ (tr.p r) w) s z =
      ageJet ℓ j (momGradRHS ν tr.v 0) s z := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => Cyl.partialQ (tr.p r) w) =ᶠ[nhds s]
        fun r => momGradRHS ν tr.v 0 r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using partialQ_train_p_eq_momGradRHS tr hr w
    exact hev.iteratedDeriv_eq ℓ
  have hE_eq : ageJet ℓ j (fun r w => Cyl.partialEta (tr.p r) w) s z =
      ageJet ℓ j (momGradRHS ν tr.v 1) s z := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => Cyl.partialEta (tr.p r) w) =ᶠ[nhds s]
        fun r => momGradRHS ν tr.v 1 r w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using partialEta_train_p_eq_momGradRHS tr hr w
    exact hev.iteratedDeriv_eq ℓ
  have hQ := norm_ageJet_momGradRHS_le hν hν1 hMv tr 0 ℓ j hs z hbd
  have hE := norm_ageJet_momGradRHS_le hν hν1 hMv tr 1 ℓ j hs z hbd
  have hperp := norm_ageJet_perpGradP_le_partials tr ℓ j hs z
  rw [hQ_eq, hE_eq] at hperp
  linarith

/-- Given `hTail : TrainStreamVelocityPressureTransverseTail` and an interior-strip bound for
`ageJet ℓ (j - 1) (perpGradP tr)` on every strip `|z.2| ≤ C'' / ν + 2`, the pressure jet
`ageJet ℓ j tr.p` satisfies `‖ageJet ℓ j tr.p s z‖ ≤ polyPS C_p N_p ν c s` on `|z.2| ≤ C' / ν + 2`. -/
theorem trainInteriorStripPressJetBounds_of_perpGradP_at
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ j : ℕ) (C' : ℝ) (hC' : 0 < C')
    (hPerp : ∀ C'' : ℝ, 0 < C'' →
      ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν_v : ℝ, 0 < C_v ∧ 0 < ν_v ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν_v →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
            ∀ z : Plane, |z.2| ≤ C'' / ν + 2 →
              ‖ageJet ℓ (j - 1) (perpGradP tr) s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s) :
    ∃ C_p : ℝ, ∃ N_p : ℕ, ∃ ν₀ : ℝ, 0 < C_p ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet ℓ j tr.p s z‖ ≤ polyPS C_p N_p ν (trainPeriod ρ ν) s := by
  cases j with
  | zero =>
    obtain ⟨b₀, C₀, C'_t, hb₀, hC₀, hC'_t, C_t, N_t, ν_t, hC_t, hν_t, hT0⟩ := hTail ρ hρ ℓ 0
    let C'' : ℝ := max C' C'_t
    have hC'' : 0 < C'' := lt_max_of_lt_left hC'
    obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hV0⟩ := hPerp C'' hC''
    let C_p : ℝ := 2 * C_t + (2 * C'' + 4) * C_v
    let N_p : ℕ := max N_t (N_v + 1)
    have hC_p : 0 < C_p := by dsimp [C_p]; positivity
    refine ⟨C_p, N_p, min ν_t ν_v, hC_p, lt_min hν_t hν_v, ?_⟩
    intro ν hν hν_le tr htr s hs z hz
    have hν_t_le : ν ≤ ν_t := hν_le.trans (min_le_left _ _)
    have hν_v_le : ν ≤ ν_v := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let R : ℝ := C'' / ν + 2
    have hR_pos : 0 < R := by dsimp [R]; positivity
    have hzR : |z.2| ≤ R := by
      have hle : C' / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      dsimp [R]; linarith
    have hedge_R : C'_t / ν + 2 + 0 ≤ |((z.1, R) : Plane).2| := by
      change C'_t / ν + 2 + 0 ≤ |R|
      rw [abs_of_pos hR_pos, add_zero]
      have hle : C'_t / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      dsimp [R]; linarith
    have hedge_raw := (hT0 s hs.le ν hν hν_t_le tr htr 0 le_rfl s hs le_rfl (z.1, R) hedge_R).2.2
    have hedge : ‖ageJet ℓ 0 tr.p s (z.1, R)‖ ≤ 2 * polyPS C_t N_t ν c s := by
      refine hedge_raw.trans ?_
      have hexp : Real.exp (-(b₀ * 0 / c)) + Real.exp (-(b₀ * 0 ^ 2 / (C₀ + ν * s))) = 2 := by
        simp; norm_num
      rw [hexp]
      linarith
    have hK_vel_nn : 0 ≤ polyPS C_v N_v ν c s := by unfold polyPS; positivity
    have hvel_R : ∀ η : ℝ, |η| ≤ R → ‖ageJet ℓ 0 (perpGradP tr) s (z.1, η)‖ ≤ polyPS C_v N_v ν c s :=
      fun η hη => hV0 ν hν hν_v_le tr htr s hs (z.1, η) hη
    have hpt := norm_ageJet_streamPair_zero_le_of_edge_and_vel
      (isStreamPair_train_p_perpGradP tr) hK_vel_nn ℓ hs hzR hedge hvel_R
    refine hpt.trans ?_
    have h1Xs : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by
      have : 1 ≤ 1 + c + ν⁻¹ := by
        have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
        have : 0 ≤ c := (Real.rpow_pos_of_pos hν _).le
        linarith
      have : 1 ≤ 1 + s := by linarith
      nlinarith
    have hpow_t : ((1 + c + ν⁻¹) * (1 + s)) ^ N_t ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_p :=
      pow_le_pow_right₀ h1Xs (le_max_left _ _)
    have hpow_v : ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + 1) ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_p :=
      pow_le_pow_right₀ h1Xs (le_max_right _ _)
    have h2R : 2 * R ≤ (2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s)) := by
      have hR_eq : 2 * R = 2 * C'' * ν⁻¹ + 4 := by dsimp [R]; ring
      rw [hR_eq]
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have hc0 : 0 ≤ c := (Real.rpow_pos_of_pos hν _).le
      have h1 : 2 * C'' * ν⁻¹ + 4 ≤ (2 * C'' + 4) * (1 + c + ν⁻¹) := by nlinarith
      have h2 : (2 * C'' + 4) * (1 + c + ν⁻¹) * 1 ≤
          (2 * C'' + 4) * (1 + c + ν⁻¹) * (1 + s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hterm1 : 2 * polyPS C_t N_t ν c s ≤
        2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_p := by
      unfold polyPS
      calc 2 * (C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t)
          = 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t := by ring
        _ ≤ 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_p :=
            mul_le_mul_of_nonneg_left hpow_t (by positivity)
    have hterm2 : 2 * R * polyPS C_v N_v ν c s ≤
        (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_p := by
      unfold polyPS
      calc 2 * R * (C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_v)
          ≤ ((2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s))) *
              (C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_v) :=
            mul_le_mul_of_nonneg_right h2R (by positivity)
        _ = (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + 1) := by
            rw [pow_succ']; ring
        _ ≤ (2 * C'' + 4) * C_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_p :=
            mul_le_mul_of_nonneg_left hpow_v (by positivity)
    unfold polyPS at hterm1 hterm2 ⊢
    dsimp [C_p, c] at hterm1 hterm2 ⊢
    linarith
  | succ k =>
    obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hVk⟩ := hPerp C' hC'
    refine ⟨2 * C_v, N_v, ν_v, by positivity, hν_v, ?_⟩
    intro ν hν hν_le tr htr s hs z hz
    have h1 := norm_ageJet_streamPair_succ_le (isStreamPair_train_p_perpGradP tr) ℓ k hs z
    have h2 := hVk ν hν hν_le tr htr s hs z hz
    calc ‖ageJet ℓ (k + 1) tr.p s z‖
        ≤ 2 * ‖ageJet ℓ k (perpGradP tr) s z‖ := h1
      _ ≤ 2 * polyPS C_v N_v ν (trainPeriod ρ ν) s :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = polyPS (2 * C_v) N_v ν (trainPeriod ρ ν) s := by
          unfold polyPS; ring

/-- Uniform interior-strip velocity bound across all `i ≤ K` at a fixed age order `r`. -/
theorem uniform_vel_strip_spatial (hVel : TrainInteriorStripVelJetBounds)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (r : ℕ) {C'' : ℝ} (hC'' : 0 < C'') :
    ∀ K : ℕ, ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane, |z.2| ≤ C'' / ν + 2 → ∀ i ≤ K,
            ‖ageJet r i tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s
  | 0 => by
    obtain ⟨C_v, N_v, ν₀, hC_v, hν₀, h0⟩ := hVel ρ hρ r 0 C'' hC''
    refine ⟨C_v, N_v, ν₀, hC_v, hν₀, fun ν hν hν_le tr htr s hs z hz i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 ν hν hν_le tr htr s hs z hz
  | K + 1 => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ := uniform_vel_strip_spatial hVel hρ r hC'' K
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hK1⟩ := hVel ρ hρ r (K + 1) C'' hC''
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z hz i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hi with hiK | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z hz i hiK).trans
        (PartI_T21.polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0 hs.le)
    · exact (hK1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z hz).trans
        (PartI_T21.polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0 hs.le)

/-- Uniform interior-strip velocity bound across all `r ≤ L` and `i ≤ K`. -/
theorem uniform_vel_strip_rect (hVel : TrainInteriorStripVelJetBounds)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (K : ℕ) {C'' : ℝ} (hC'' : 0 < C'') :
    ∀ L : ℕ, ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → ∀ z : Plane, |z.2| ≤ C'' / ν + 2 → ∀ r ≤ L, ∀ i ≤ K,
            ‖ageJet r i tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s
  | 0 => by
    obtain ⟨C_v, N_v, ν₀, hC_v, hν₀, h0⟩ := uniform_vel_strip_spatial hVel hρ 0 hC'' K
    refine ⟨C_v, N_v, ν₀, hC_v, hν₀, fun ν hν hν_le tr htr s hs z hz r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs z hz i hi
  | L + 1 => by
    obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hIH⟩ := uniform_vel_strip_rect hVel hρ K hC'' L
    obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hL1⟩ := uniform_vel_strip_spatial hVel hρ (L + 1) hC'' K
    refine ⟨max C₁ C₂, max N₁ N₂, min ν₁ ν₂, lt_max_of_lt_left hC₁, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs z hz r hr i hi
    have hc0 : 0 ≤ trainPeriod ρ ν := Real.rpow_nonneg hν.le _
    rcases Nat.of_le_succ hr with hrL | rfl
    · exact (hIH ν hν (hν_le.trans (min_le_left _ _)) tr htr s hs z hz r hrL i hi).trans
        (PartI_T21.polyPS_mono hC₁.le (le_max_left _ _) (le_max_left _ _) hν hc0 hs.le)
    · exact (hL1 ν hν (hν_le.trans (min_le_right _ _)) tr htr s hs z hz i hi).trans
        (PartI_T21.polyPS_mono hC₂.le (le_max_right _ _) (le_max_right _ _) hν hc0 hs.le)

/-- **Unconditional reduction of `TrainInteriorStripPressJetBounds` to `TrainInteriorStripVelJetBounds`
and `hTail`**: combines `trainInteriorStripPressJetBounds_of_perpGradP_at` with
`norm_ageJet_perpGradP_le` and `uniform_vel_strip_rect`. -/
theorem trainInteriorStripPressJetBounds_of_vel
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (hVel : TrainInteriorStripVelJetBounds) :
    TrainInteriorStripPressJetBounds := by
  intro ρ hρ ℓ j C' hC'
  refine trainInteriorStripPressJetBounds_of_perpGradP_at hTail ρ hρ ℓ j C' hC' ?_
  intro C'' hC''
  obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hV_rect⟩ :=
    uniform_vel_strip_rect hVel hρ ((j - 1) + 2) hC'' (ℓ + 1)
  let C_perp : ℝ := 6 * C_v + 4 * (2 : ℝ) ^ (ℓ + (j - 1)) * C_v * C_v
  let N_perp : ℕ := N_v + N_v
  refine ⟨C_perp, N_perp, min ν_v 1, by dsimp [C_perp]; positivity, lt_min hν_v one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs z hz
  have hν_v_le : ν ≤ ν_v := hν_le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  let M_v := polyPS C_v N_v ν c s
  have hMv_nn : 0 ≤ M_v := by dsimp [M_v, polyPS]; positivity
  have hpt := norm_ageJet_perpGradP_le hν.le hν1 hMv_nn tr ℓ (j - 1) hs z
    (fun r hr i hi => hV_rect ν hν hν_v_le tr htr s hs z hz r hr i hi)
  refine hpt.trans ?_
  have h1Xs : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by
    have : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have : 0 ≤ c := (Real.rpow_pos_of_pos hν _).le
      linarith
    have : 1 ≤ 1 + s := by linarith
    nlinarith
  have hpow : ((1 + c + ν⁻¹) * (1 + s)) ^ N_v ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + N_v) :=
    pow_le_pow_right₀ h1Xs (Nat.le_add_right N_v N_v)
  have hmul_pow :
      ((1 + c + ν⁻¹) * (1 + s)) ^ N_v * ((1 + c + ν⁻¹) * (1 + s)) ^ N_v =
        ((1 + c + ν⁻¹) * (1 + s)) ^ (N_v + N_v) :=
    (pow_add _ N_v N_v).symm
  dsimp [M_v, C_perp, N_perp, polyPS, c] at hpow hmul_pow ⊢
  calc 6 * (C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v) +
        4 * (2 : ℝ) ^ (ℓ + (j - 1)) *
          (C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v) *
          (C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v)
      = 6 * C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v +
        4 * (2 : ℝ) ^ (ℓ + (j - 1)) * C_v * C_v *
          (((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v *
            ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v) := by ring
    _ = 6 * C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ N_v +
        4 * (2 : ℝ) ^ (ℓ + (j - 1)) * C_v * C_v *
          ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ (N_v + N_v) := by rw [hmul_pow]
    _ ≤ 6 * C_v * ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ (N_v + N_v) +
        4 * (2 : ℝ) ^ (ℓ + (j - 1)) * C_v * C_v *
          ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ (N_v + N_v) := by
        linarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 6 * C_v)]
    _ = (6 * C_v + 4 * (2 : ℝ) ^ (ℓ + (j - 1)) * C_v * C_v) *
          ((1 + trainPeriod ρ ν + ν⁻¹) * (1 + s)) ^ (N_v + N_v) := by ring

/-! ### 5. Reduction of `TrainInteriorStripVelJetBounds` to higher-age (`ℓ = m + 1`) bounds -/

/-- **Interior-strip bound for higher age derivatives (`ℓ = m + 1`) of `tr.v`**:
for every `ρ > 1/2`, derivative orders `m, j : ℕ`, and half-width parameter `C' > 0`,
`‖ageJet (m + 1) j tr.v s z‖ ≤ polyPS C_v N_v ν c s` on `|z.2| ≤ C' / ν + 2`. -/
def TrainInteriorStripVelHigherAgeJetBounds : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m j : ℕ, ∀ C' : ℝ, 0 < C' →
    ∃ C_v : ℝ, ∃ N_v : ℕ, ∃ ν₀ : ℝ, 0 < C_v ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet (m + 1) j tr.v s z‖ ≤ polyPS C_v N_v ν (trainPeriod ρ ν) s

/-- Combines the unconditional `ℓ = 0` bound `trainInteriorStripVelZeroAge_proof` with
`TrainInteriorStripVelHigherAgeJetBounds` (`ℓ = m + 1`) to give `TrainInteriorStripVelJetBounds`. -/
theorem trainInteriorStripVelJetBounds_of_higher
    (hHigher : TrainInteriorStripVelHigherAgeJetBounds) :
    TrainInteriorStripVelJetBounds := by
  intro ρ hρ ℓ j C' hC'
  cases ℓ with
  | zero => exact trainInteriorStripVelZeroAge_proof ρ hρ j C' hC'
  | succ m => exact hHigher ρ hρ m j C' hC'

/-- Any global higher-age velocity sup bound `TrainVelocityHigherAgeJetSupBound` immediately
implies the interior-strip higher-age velocity bound `TrainInteriorStripVelHigherAgeJetBounds`. -/
theorem trainInteriorStripVelHigherAgeJetBounds_of_supBound
    (hSup : TrainVelocityHigherAgeJetSupBound) :
    TrainInteriorStripVelHigherAgeJetBounds := by
  intro ρ hρ m j _C' _hC'
  obtain ⟨C_v, N_v, ν₀, hC_v, hν₀, hv⟩ := hSup m ρ hρ j
  refine ⟨C_v, N_v, ν₀, hC_v, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs z _hz
  refine (hv ν hν hν_le tr htr s hs z).trans ?_
  unfold polyP polyPS
  have hc0 : 0 ≤ trainPeriod ρ ν := (Real.rpow_pos_of_pos hν _).le
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX : 1 + trainPeriod ρ ν + ν⁻¹ ≤ (1 + trainPeriod ρ ν + ν⁻¹) * (1 + s) := by
    have : (1 + trainPeriod ρ ν + ν⁻¹) * 1 ≤ (1 + trainPeriod ρ ν + ν⁻¹) * (1 + s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hX N_v) hC_v.le

end PartI_T21_2

open PartI_T21_2 in
/-- **Conditional assembly of `TrainInteriorStripJetBounds` (`PartI:T21/2/1`)**:
combines `trainInteriorStripStreamJetBounds_of_vel_at` (which proves the `tr.ψ` bound from `hTail`
and `hVel`) with `TrainInteriorStripVelJetBounds` and `TrainInteriorStripPressJetBounds`. -/
theorem trainInteriorStripJetBounds_of
    (hVel : TrainInteriorStripVelJetBounds)
    (hPress : TrainInteriorStripPressJetBounds)
    (_hOv : TrainOverlap)
    (_hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    TrainInteriorStripJetBounds := by
  intro ρ hρ ℓ j C' hC'
  obtain ⟨C_ψ, N_ψ, ν_ψ, hC_ψ, hν_ψ, hΨ⟩ :=
    trainInteriorStripStreamJetBounds_of_vel_at hTail ρ hρ ℓ j C' hC'
      (fun C'' hC'' => hVel ρ hρ ℓ (j - 1) C'' hC'')
  obtain ⟨C_v, N_v, ν_v, hC_v, hν_v, hV⟩ := hVel ρ hρ ℓ j C' hC'
  obtain ⟨C_p, N_p, ν_p, hC_p, hν_p, hP⟩ := hPress ρ hρ ℓ j C' hC'
  let C_int : ℝ := max C_ψ (max C_v C_p)
  let N_int : ℕ := max N_ψ (max N_v N_p)
  let ν₀ : ℝ := min ν_ψ (min ν_v ν_p)
  refine ⟨C_int, N_int, ν₀, lt_max_of_lt_left hC_ψ, lt_min hν_ψ (lt_min hν_v hν_p), ?_⟩
  intro ν hν hν_le tr htr s hs z hz
  have hν_ψ_le : ν ≤ ν_ψ := hν_le.trans (min_le_left _ _)
  have hν_v_le : ν ≤ ν_v := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p_le : ν ≤ ν_p := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := (Real.rpow_pos_of_pos hν _).le
  refine ⟨(hΨ ν hν hν_ψ_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_ψ.le (le_max_left _ _) (le_max_left _ _) hν hc0 hs.le),
    (hV ν hν hν_v_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_v.le
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) hν hc0 hs.le),
    (hP ν hν hν_p_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_p.le
        ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)) hν hc0 hs.le)⟩

open PartI_T21_2 in
/-- **Conditional assembly of `TrainInteriorStripJetBounds` from `TrainInteriorStripVelHigherAgeJetBounds`
alone (`PartI:T21/2/1`)**: combines `trainInteriorStripVelJetBounds_of_higher` and
`trainInteriorStripPressJetBounds_of_vel` with `trainInteriorStripJetBounds_of`. -/
theorem trainInteriorStripJetBounds_of_higherVel
    (hHigher : TrainInteriorStripVelHigherAgeJetBounds)
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    TrainInteriorStripJetBounds := by
  have hVel : TrainInteriorStripVelJetBounds := trainInteriorStripVelJetBounds_of_higher hHigher
  exact trainInteriorStripJetBounds_of hVel
    (trainInteriorStripPressJetBounds_of_vel hTail hVel) hOv hVort hTail

namespace PartI_T21_2.VelHigherAgeAux

open UnforcedLeray.Short.IIb (Sm)

/-- Monotonicity `polyP C N ν c ≤ polyPS C N ν c s` for `C ≥ 0, ν > 0, c ≥ 0, s ≥ 0`. -/
theorem vha_polyP_le_polyPS {C ν c s : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hν : 0 < ν) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    polyP C N ν c ≤ polyPS C N ν c s := by
  unfold polyP polyPS
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hX_nn : 0 ≤ 1 + c + ν⁻¹ := by linarith
  have hX : 1 + c + ν⁻¹ ≤ (1 + c + ν⁻¹) * (1 + s) := by
    have : (1 + c + ν⁻¹) * 1 ≤ (1 + c + ν⁻¹) * (1 + s) :=
      mul_le_mul_of_nonneg_left (by linarith) hX_nn
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX_nn hX N) hC

/-- `(meanVel1, fstVecMap (hmean c curl))` forms a jointly smooth `IsStreamPair` on `(0, ∞) × Plane`. -/
theorem isStreamPair_meanVel1_hmean_curl {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) :
    IsStreamPair (fun r w => meanVel1 tr r w.2)
      (fun r w => PartI_T21.fstVecMap (hmean c (Cyl.curl (tr.v r)) w.2)) := by
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => meanVel1 tr x.1 x.2.2) (Ioi 0 ×ˢ univ) :=
    PartI_T21.contDiffOn_snd_lift (PartI_T21.contDiffOn_meanVel1 hc tr)
  have hW : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (Cyl.curl (tr.v x.1)) x.2.2) (Ioi 0 ×ˢ univ) :=
    PartI_T21.contDiffOn_snd_lift (g := fun r η => hmean c (Cyl.curl (tr.v r)) η)
      (PartI_T21.contDiffOn_hmean_curl hc tr)
  refine ⟨hF, PartI_T21.fstVecMap.contDiff.comp_contDiffOn hW, fun s hs z => ?_⟩
  have hd_eta : deriv (fun y : ℝ => meanVel1 tr s y) z.2 = -hmean c (Cyl.curl (tr.v s)) z.2 :=
    (PartI_T21.hasDerivAt_meanVel1_curl hc tr hs.le z.2).deriv
  have hd_q : deriv (fun x : ℝ => meanVel1 tr s z.2) z.1 = 0 := deriv_const z.1 _
  ext i
  fin_cases i
  · change (PartI_T21.fstVecMap (hmean c (Cyl.curl (tr.v s)) z.2)) 0 =
      (toVec (UnforcedLeray.GaussianVortex.perpendicularGradient
        (fun w : Plane => meanVel1 tr s w.2) z)) 0
    rw [PartI_T21.fstVecMap_apply, toVec_zero, toVec_zero]
    unfold UnforcedLeray.GaussianVortex.perpendicularGradient UnforcedLeray.GaussianVortex.partialY
    dsimp only
    rw [hd_eta, neg_neg]
  · change (PartI_T21.fstVecMap (hmean c (Cyl.curl (tr.v s)) z.2)) 1 =
      (toVec (UnforcedLeray.GaussianVortex.perpendicularGradient
        (fun w : Plane => meanVel1 tr s w.2) z)) 1
    rw [PartI_T21.fstVecMap_apply, toVec_one, toVec_one]
    unfold UnforcedLeray.GaussianVortex.perpendicularGradient UnforcedLeray.GaussianVortex.partialX
    dsimp only
    exact hd_q.symm

/-- Global bound on `‖ageJet ℓ k (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖` from `hVort`. -/
theorem norm_ageJet_hmean_curl_le
    {ν c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (tr : B0140.TrainSol ν c)
    (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hω : ∀ w : Plane, ‖ageJet ℓ k (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ B) :
    ‖ageJet ℓ k (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) s z‖ ≤ B := by
  have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  exact PartI_T21.norm_ageJet_hmean_scalar_le hc hB (PartI_T20.smR_curl hv_joint) ℓ k hs z
    (fun q _ => hω (q, z.2))

/-- Interior-strip bound for the horizontal mean velocity `ageJet ℓ j (fun r w => hmean c (tr.v r) w.2)`
at any orders `ℓ, j : ℕ` from `hVort` and `hTail`. -/
theorem trainInteriorStripMeanVelJetBounds
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (ℓ j : ℕ) (C' : ℝ) (hC' : 0 < C') :
    ∃ C_m : ℝ, ∃ N_m : ℕ, ∃ ν₀ : ℝ, 0 < C_m ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            ‖ageJet ℓ j (fun r w => hmean (trainPeriod ρ ν) (tr.v r) w.2) s z‖ ≤
              polyPS C_m N_m ν (trainPeriod ρ ν) s := by
  cases j with
  | zero =>
    obtain ⟨b₀_t, C₀_t, C'_t, _hb₀_t, _hC₀_t, hC'_t, C_t, N_t, ν_t, hC_t, hν_t, hT0⟩ :=
      hTail ρ hρ ℓ 0
    obtain ⟨b₀_ω, C₀_ω, C'_ω, hb₀_ω, hC₀_ω, _hC'_ω, C_ω, N_ω, ν_ω, hC_ω, hν_ω, hW0⟩ :=
      hVort ρ hρ ℓ 0
    let C'' : ℝ := max C' C'_t
    let C_m : ℝ := 2 * C_t + (2 * C'' + 4) * C_ω
    let N_m : ℕ := max N_t (N_ω + 1)
    have hC'' : 0 < C'' := lt_max_of_lt_left hC'
    have hC_m : 0 < C_m := by dsimp [C_m]; positivity
    refine ⟨C_m, N_m, min ν_t ν_ω, hC_m, lt_min hν_t hν_ω, ?_⟩
    intro ν hν hν_le tr htr s hs z hz
    have hν_t_le : ν ≤ ν_t := hν_le.trans (min_le_left _ _)
    have hν_ω_le : ν ≤ ν_ω := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    let R : ℝ := C'' / ν + 2
    have hR_pos : 0 < R := by dsimp [R]; positivity
    have hzR : |z.2| ≤ R := by
      have hle : C' / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      dsimp [R]; linarith
    have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
      tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
    have hv0_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 0) (Ioi 0 ×ˢ univ) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
    have hBt_nn : 0 ≤ 2 * polyPS C_t N_t ν c s := by unfold polyPS; positivity
    have hedge : ‖ageJet ℓ 0 (fun r w => meanVel1 tr r w.2) s (z.1, R)‖ ≤
        2 * polyPS C_t N_t ν c s := by
      refine PartI_T21.norm_ageJet_hmean_scalar_le hc hBt_nn hv0_sm ℓ 0 hs (z.1, R) (fun q _hq => ?_)
      have hedge_q : C'_t / ν + 2 + 0 ≤ |((q, R) : Plane).2| := by
        change C'_t / ν + 2 + 0 ≤ |R|
        rw [abs_of_pos hR_pos, add_zero]
        have hle : C'_t / ν ≤ C'' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
        dsimp [R]; linarith
      have hraw := (hT0 s hs.le ν hν hν_t_le tr htr 0 le_rfl s hs le_rfl (q, R) hedge_q).2.1
      have hexp : Real.exp (-(b₀_t * 0 / c)) + Real.exp (-(b₀_t * 0 ^ 2 / (C₀_t + ν * s))) = 2 := by
        simp; norm_num
      rw [hexp] at hraw
      exact (PartI_T20.norm_ageJet_vec_proj_le hv_joint 0 ℓ 0 hs (q, R)).trans
        (hraw.trans (by linarith))
    have hBω_nn : 0 ≤ polyP C_ω N_ω ν c := by unfold polyP; positivity
    have hω_all : ∀ w : Plane, ‖ageJet ℓ 0 (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤
        polyP C_ω N_ω ν c := by
      intro w
      have hw := hW0 ν hν hν_ω_le tr htr s hs w
      have hexp1 : Real.exp (-(b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 : 0 ≤ b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s) :=
          div_nonneg (mul_nonneg hb₀_ω.le (sq_nonneg _)) (by positivity)
        linarith
      exact hw.trans (mul_le_of_le_one_right hBω_nn hexp1)
    have hW_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (Cyl.curl (tr.v x.1)) x.2.2)
        (Ioi 0 ×ˢ univ) :=
      PartI_T21.contDiffOn_snd_lift (g := fun r η => hmean c (Cyl.curl (tr.v r)) η)
        (PartI_T21.contDiffOn_hmean_curl hc tr)
    have hvel_R : ∀ η : ℝ, |η| ≤ R →
        ‖ageJet ℓ 0 (fun r w => PartI_T21.fstVecMap (hmean c (Cyl.curl (tr.v r)) w.2)) s (z.1, η)‖ ≤
          polyPS C_ω N_ω ν c s := by
      intro η _hη
      have h1 := (norm_ageJet_clm_comp_le PartI_T21.fstVecMap
        (fun r w => hmean c (Cyl.curl (tr.v r)) w.2) hW_sm ℓ 0 hs (z.1, η)).trans
        (mul_le_of_le_one_left (norm_nonneg _) PartI_T21.norm_fstVecMap_le_one)
      have h2 := norm_ageJet_hmean_curl_le hc hBω_nn tr ℓ 0 hs (z.1, η) hω_all
      refine (h1.trans h2).trans ?_
      exact vha_polyP_le_polyPS hC_ω.le hν hc.le hs.le
    have hK_vel_nn : 0 ≤ polyPS C_ω N_ω ν c s := by unfold polyPS; positivity
    have hpt0 := PartI_T21.norm_ageJet_hmean_v_le_meanVel1 hν hc tr ℓ 0 hs z
    have hpt := (hpt0.trans (norm_ageJet_streamPair_zero_le_of_edge_and_vel
      (isStreamPair_meanVel1_hmean_curl hc tr) hK_vel_nn ℓ hs hzR hedge hvel_R))
    refine hpt.trans ?_
    have h1Xs : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by
      have : 1 ≤ 1 + c + ν⁻¹ := by
        have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
        linarith
      have : 1 ≤ 1 + s := by linarith
      nlinarith
    have hpow_t : ((1 + c + ν⁻¹) * (1 + s)) ^ N_t ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_m :=
      pow_le_pow_right₀ h1Xs (le_max_left _ _)
    have hpow_v : ((1 + c + ν⁻¹) * (1 + s)) ^ (N_ω + 1) ≤ ((1 + c + ν⁻¹) * (1 + s)) ^ N_m :=
      pow_le_pow_right₀ h1Xs (le_max_right _ _)
    have h2R : 2 * R ≤ (2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s)) := by
      have hR_eq : 2 * R = 2 * C'' * ν⁻¹ + 4 := by dsimp [R]; ring
      rw [hR_eq]
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have h1 : 2 * C'' * ν⁻¹ + 4 ≤ (2 * C'' + 4) * (1 + c + ν⁻¹) := by nlinarith
      have h2 : (2 * C'' + 4) * (1 + c + ν⁻¹) * 1 ≤
          (2 * C'' + 4) * (1 + c + ν⁻¹) * (1 + s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hterm1 : 2 * polyPS C_t N_t ν c s ≤
        2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_m := by
      unfold polyPS
      calc 2 * (C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t)
          = 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_t := by ring
        _ ≤ 2 * C_t * ((1 + c + ν⁻¹) * (1 + s)) ^ N_m :=
            mul_le_mul_of_nonneg_left hpow_t (by positivity)
    have hterm2 : 2 * R * polyPS C_ω N_ω ν c s ≤
        (2 * C'' + 4) * C_ω * ((1 + c + ν⁻¹) * (1 + s)) ^ N_m := by
      unfold polyPS
      calc 2 * R * (C_ω * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ω)
          ≤ ((2 * C'' + 4) * ((1 + c + ν⁻¹) * (1 + s))) *
              (C_ω * ((1 + c + ν⁻¹) * (1 + s)) ^ N_ω) :=
            mul_le_mul_of_nonneg_right h2R (by positivity)
        _ = (2 * C'' + 4) * C_ω * ((1 + c + ν⁻¹) * (1 + s)) ^ (N_ω + 1) := by
            rw [pow_succ']; ring
        _ ≤ (2 * C'' + 4) * C_ω * ((1 + c + ν⁻¹) * (1 + s)) ^ N_m :=
            mul_le_mul_of_nonneg_left hpow_v (by positivity)
    unfold polyPS at hterm1 hterm2 ⊢
    dsimp [C_m, c] at hterm1 hterm2 ⊢
    linarith
  | succ k =>
    obtain ⟨b₀_ω, C₀_ω, C'_ω, hb₀_ω, hC₀_ω, _hC'_ω, C_ω, N_ω, ν_ω, hC_ω, hν_ω, hWk⟩ :=
      hVort ρ hρ ℓ k
    refine ⟨C_ω, N_ω, ν_ω, hC_ω, hν_ω, ?_⟩
    intro ν hν hν_le tr htr s hs z _hz
    let c := trainPeriod ρ ν
    have hc : 0 < c := Real.rpow_pos_of_pos hν _
    have hBω_nn : 0 ≤ polyP C_ω N_ω ν c := by unfold polyP; positivity
    have hω_all : ∀ w : Plane, ‖ageJet ℓ k (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤
        polyP C_ω N_ω ν c := by
      intro w
      have hw := hWk ν hν hν_le tr htr s hs w
      have hexp1 : Real.exp (-(b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 : 0 ≤ b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s) :=
          div_nonneg (mul_nonneg hb₀_ω.le (sq_nonneg _)) (by positivity)
        linarith
      exact hw.trans (mul_le_of_le_one_right hBω_nn hexp1)
    have h1 := PartI_T21.norm_ageJet_hmean_v_le_meanVel1 hν hc tr ℓ (k + 1) hs z
    have h2 := PartI_T21.norm_ageJet_meanVel1_succ_le hc tr ℓ k hs z
    have h3 := norm_ageJet_hmean_curl_le hc hBω_nn tr ℓ k hs z hω_all
    exact ((h1.trans h2).trans h3).trans (vha_polyP_le_polyPS hC_ω.le hν hc.le hs.le)

/-- Absolute constant `(3 / (2 π²)) ∑_{n ∈ ℤ} 1 / n² + 1 > 0` for the cylinder Poisson oscillation bound. -/
def vhaOscConst : ℝ :=
  3 / (2 * Real.pi ^ 2) * (∑' n : ℤ, 1 / (n : ℝ) ^ 2) + 1

theorem vhaOscConst_pos : 0 < vhaOscConst := by
  unfold vhaOscConst
  have hsum : 0 ≤ ∑' n : ℤ, 1 / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => by positivity
  positivity

/-- Global oscillation bound on `(ℝ / cℤ) × ℝ`: for any bounded `c`-periodic `C^∞` scalar field
`q : Plane → ℝ` with `|Train.lapS q w| ≤ G` globally (`G ≥ 0`),
`|q z - hmean c q z.2| ≤ vhaOscConst * c ^ 2 * G` for all `z : Plane`. -/
theorem cylPoisOscGlobalBound_of_bdd {c G : ℝ} (hc : 0 < c) (hG : 0 ≤ G)
    {q : Plane → ℝ} (hq : ContDiff ℝ ∞ q) (hqp : Cyl.IsPeriodic c q) (z : Plane)
    (hLap : ∀ w : Plane, |Train.lapS q w| ≤ G)
    (hBdd : ∃ M : ℝ, ∀ w : Plane, |q w| ≤ M) :
    |q z - hmean c q z.2| ≤ vhaOscConst * c ^ 2 * G := by
  obtain ⟨M, hM⟩ := hBdd
  let M' : ℝ := max M 0
  have hmodeBdd : ∀ (n : ℤ), n ≠ 0 →
      ∃ B : ℝ, ∀ η : ℝ, ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) η‖ ≤ B := by
    intro n _hn
    refine ⟨M', fun η => ?_⟩
    refine (cylPoisQModeEstimates c hc n (fun w : Plane => ((q w : ℝ) : ℂ))).1 M'
      (fun w => ?_) η
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hM w).trans (le_max_left _ _)
  have hloc := PartI_T21.cylPoisOscPartLocalBound_of_modeBdd hc (le_refl (0 : ℝ)) hG hG
    (hq.of_le (by norm_num)) hqp z hLap (fun w _ => hLap w) hmodeBdd
  refine hloc.trans ?_
  have hexp0 : Real.exp (-(2 * Real.pi * 0 / c)) = 1 := by simp
  rw [hexp0]
  unfold vhaOscConst
  have hsum_nn : 0 ≤ ∑' n : ℤ, 1 / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => by positivity
  have h1 : ((G + 2 * G * 1) * c ^ 2 / (2 * Real.pi ^ 2)) * (∑' n : ℤ, 1 / (n : ℝ) ^ 2) =
      (3 / (2 * Real.pi ^ 2) * (∑' n : ℤ, 1 / (n : ℝ) ^ 2)) * c ^ 2 * G := by ring
  rw [h1]
  have h2 : 0 ≤ 1 * c ^ 2 * G := by positivity
  linarith

/-- Any continuous `c`-periodic function `q : Plane → ℝ` (`c > 0`) that is bounded by `B` on the
exterior `|w.2| ≥ R` (`R ≥ 0`) is globally bounded on `Plane`. -/
theorem exists_global_bound_of_periodic_and_tail {c R B : ℝ} (hc : 0 < c) (_hR : 0 ≤ R)
    {q : Plane → ℝ} (hq_cont : Continuous q) (hqp : Cyl.IsPeriodic c q)
    (hTail_q : ∀ w : Plane, R ≤ |w.2| → |q w| ≤ B) :
    ∃ M : ℝ, ∀ w : Plane, |q w| ≤ M := by
  let K_box : Set Plane := Icc 0 c ×ˢ Icc (-R) R
  have hK_comp : IsCompact K_box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M_int, hM_int⟩ :=
    hK_comp.bddAbove_image (continuous_abs.comp hq_cont).continuousOn
  refine ⟨max M_int B, fun w => ?_⟩
  rcases le_or_gt R |w.2| with hw | hw
  · exact (hTail_q w hw).trans (le_max_right _ _)
  · let m : ℤ := ⌊w.1 / c⌋
    let x₀ : ℝ := Int.fract (w.1 / c) * c
    have hx₀_mem : x₀ ∈ Icc 0 c := by
      refine ⟨mul_nonneg (Int.fract_nonneg _) hc.le, ?_⟩
      calc Int.fract (w.1 / c) * c
          ≤ 1 * c := mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le hc.le
        _ = c := one_mul c
    have hw2_mem : w.2 ∈ Icc (-R) R := abs_le.1 hw.le
    have hmem : ((x₀, w.2) : Plane) ∈ K_box := ⟨hx₀_mem, hw2_mem⟩
    have hper : Function.Periodic (fun x : ℝ => q (x, w.2)) c := fun x => hqp (x, w.2)
    have hx_eq : x₀ + m • c = w.1 := by
      rw [zsmul_eq_mul]
      dsimp [x₀, m]
      have h1 : Int.fract (w.1 / c) + (⌊w.1 / c⌋ : ℝ) = w.1 / c := Int.fract_add_floor (w.1 / c)
      calc Int.fract (w.1 / c) * c + (⌊w.1 / c⌋ : ℝ) * c
          = (Int.fract (w.1 / c) + (⌊w.1 / c⌋ : ℝ)) * c := by ring
        _ = (w.1 / c) * c := by rw [h1]
        _ = w.1 := div_mul_cancel₀ w.1 hc.ne'
    have hq_eq : q w = q (x₀, w.2) := by
      calc q w = q (w.1, w.2) := rfl
        _ = q (x₀ + m • c, w.2) := by rw [hx_eq]
        _ = q (x₀, w.2) := hper.zsmul m x₀
    rw [hq_eq]
    exact (hM_int (mem_image_of_mem (fun y : Plane => |q y|) hmem)).trans (le_max_left _ _)

/-- Horizontal oscillation operator `vhaOsc c q z = q z - hmean c q z.2` on scalar fields. -/
def vhaOsc (c : ℝ) (q : Plane → ℝ) : Plane → ℝ :=
  fun z => q z - hmean c q z.2

theorem partialX_vhaOsc {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : UnforcedLeray.B0151.IsPeriodicQ c q) :
    UnforcedLeray.GaussianVortex.partialX (vhaOsc c q) =
      vhaOsc c (UnforcedLeray.GaussianVortex.partialX q) := by
  funext z
  have h1 : UnforcedLeray.GaussianVortex.partialX (vhaOsc c q) z =
      UnforcedLeray.GaussianVortex.partialX q z := by
    show deriv (fun x : ℝ => q (x, z.2) - hmean c q z.2) z.1 =
      deriv (fun x : ℝ => q (x, z.2)) z.1
    exact deriv_sub_const (hmean c q z.2)
  have hC2 := Cyl.C2.of_contDiff (hq.of_le (by norm_num))
  have hqp' : Cyl.IsPeriodic c q := fun w => hqp w.1 w.2
  have hint0 : ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0 :=
    cpHL_integral_partialQ_zero hc (hq.differentiable (by simp)) hC2.contQ hqp' z.2
  have hm0 : hmean c (UnforcedLeray.GaussianVortex.partialX q) z.2 = 0 := by
    unfold hmean
    change c⁻¹ • ∫ x in Ioc (-c / 2) (c / 2), Cyl.partialQ q (x, z.2) = 0
    rw [hint0, smul_zero]
  change UnforcedLeray.GaussianVortex.partialX (vhaOsc c q) z =
    UnforcedLeray.GaussianVortex.partialX q z - hmean c (UnforcedLeray.GaussianVortex.partialX q) z.2
  rw [h1, hm0, sub_zero]

theorem partialY_vhaOsc (c : ℝ) {q : Plane → ℝ} (hq : ContDiff ℝ ∞ q) :
    UnforcedLeray.GaussianVortex.partialY (vhaOsc c q) =
      vhaOsc c (UnforcedLeray.GaussianVortex.partialY q) := by
  funext z
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hpath : HasDerivAt (fun y : ℝ => ((z.1, y) : Plane)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd_q : HasDerivAt (fun y : ℝ => q (z.1, y))
      (UnforcedLeray.GaussianVortex.partialY q z) z.2 :=
    ((hqd z).comp z.2 hpath.differentiableAt).hasDerivAt
  have hd_m : HasDerivAt (hmean c q)
      (hmean c (UnforcedLeray.GaussianVortex.partialY q) z.2) z.2 :=
    cpH2_hasDerivAt_hmean (hq.of_le (by norm_num)) z.2
  exact (hd_q.sub hd_m).deriv

/-- Coordinate word derivatives commute with `vhaOsc c` on smooth `c`-periodic fields. -/
theorem derivWord_vhaOsc {c : ℝ} (hc : 0 < c) {q : Plane → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqp : UnforcedLeray.B0151.IsPeriodicQ c q) :
    ∀ w : List Bool,
      UnforcedLeray.B0151.derivWord w (vhaOsc c q) =
        vhaOsc c (UnforcedLeray.B0151.derivWord w q)
  | [] => rfl
  | true :: w => by
    show UnforcedLeray.GaussianVortex.partialX (UnforcedLeray.B0151.derivWord w (vhaOsc c q)) =
      vhaOsc c (UnforcedLeray.GaussianVortex.partialX (UnforcedLeray.B0151.derivWord w q))
    rw [derivWord_vhaOsc hc hq hqp w]
    exact partialX_vhaOsc hc (UnforcedLeray.B0151.contDiff_derivWord hq w)
      (UnforcedLeray.B0151.periodic_derivWord hqp w)
  | false :: w => by
    show UnforcedLeray.GaussianVortex.partialY (UnforcedLeray.B0151.derivWord w (vhaOsc c q)) =
      vhaOsc c (UnforcedLeray.GaussianVortex.partialY (UnforcedLeray.B0151.derivWord w q))
    rw [derivWord_vhaOsc hc hq hqp w]
    exact partialY_vhaOsc c (UnforcedLeray.B0151.contDiff_derivWord hq w)

/-- Pointwise identity `iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) z) k) s = vhaOsc c u_k z`
for `u_k(w) = iteratedDeriv ℓ (fun r => tr.v r w k) s`. -/
theorem iteratedDeriv_hfluct_v_comp_eq {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (k : Fin 2) (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) z) k) s =
      vhaOsc c (fun w => iteratedDeriv ℓ (fun r => tr.v r w k) s) z := by
  have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hvk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hmk_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (fun w => tr.v x.1 w k) x.2.2)
      (Ioi 0 ×ˢ univ) :=
    PartI_T21.contDiffOn_snd_lift (g := fun r η => hmean c (fun w => tr.v r w k) η)
      (hmeanContDiff c hc (fun r w => tr.v r w k) hvk_sm)
  have hev : (fun r => (hfluct c (tr.v r) z) k) =ᶠ[𝓝 s]
      fun r => tr.v r z k - hmean c (fun w => tr.v r w k) z.2 := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have hvc : Continuous (tr.v r) := (bucVel_vslice_contDiff tr hr.le).continuous
    change (tr.v r z - hmean c (tr.v r) z.2) k = _
    rw [PiLp.sub_apply, PartI_T22.hmean_apply_vec' c hvc z.2 k]
  have hsub := iteratedDeriv_sub
    (PartI_T22.contDiffAt_age_slice (F := fun r w => tr.v r w k) hvk_sm hs z ℓ)
    (PartI_T22.contDiffAt_age_slice (F := fun r w => hmean c (fun y => tr.v r y k) w.2) hmk_sm hs z ℓ)
  rw [hev.iteratedDeriv_eq ℓ]
  exact hsub.trans (by rw [PartI_T21.iteratedDeriv_hmean_scalar_eq hc hvk_sm ℓ hs z.2]; rfl)

/-- Pointwise Laplacian bound `|Train.lapS (B0151.derivWord w u_k) z| ≤ ‖ageJet ℓ (j + 1) (Cyl.curl ∘ tr.v) s z‖`
for any coordinate word `w` of length `j` on the velocity age-slice `u_k`. -/
theorem norm_lapS_derivWord_velSlice_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (k : Fin 2) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) {w : List Bool} (hw : w.length = j) (z : Plane) :
    |Train.lapS (UnforcedLeray.B0151.derivWord w (fun y => iteratedDeriv ℓ (fun r => tr.v r y k) s)) z| ≤
      ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s z‖ := by
  let u0 : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => tr.v r y 0) s
  let u1 : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => tr.v r y 1) s
  let vom : Plane → ℝ := fun y => iteratedDeriv ℓ (fun r => Cyl.curl (tr.v r) y) s
  have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hv0_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hv1_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
  have hvom_sm : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) :=
    PartI_T20.smR_curl hv_joint
  have hu0 : ContDiff ℝ ∞ u0 := PartI_T22.contDiff_slice_iteratedDeriv hv0_sm ℓ hs
  have hu1 : ContDiff ℝ ∞ u1 := PartI_T22.contDiff_slice_iteratedDeriv hv1_sm ℓ hs
  have hvoms : ContDiff ℝ ∞ vom := PartI_T22.contDiff_slice_iteratedDeriv hvom_sm ℓ hs
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r y => tr.v r y 1) hv1_sm
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r y => tr.v r y 0) hv0_sm
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => tr.v x.1 y 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r y => tr.v r y 0) hv0_sm
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => tr.v x.1 y 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r y => tr.v r y 1) hv1_sm
  have hvom_eq : vom = fun y => UnforcedLeray.B0151.derivWord [true] u1 y -
      UnforcedLeray.B0151.derivWord [false] u0 y := by
    funext y
    have hsub := iteratedDeriv_sub
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialQ (fun x => tr.v r x 1) w) hQ1 hs y ℓ)
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialEta (fun x => tr.v r x 0) w) hE0 hs y ℓ)
    change iteratedDeriv ℓ (fun r => Cyl.partialQ (fun x => tr.v r x 1) y -
      Cyl.partialEta (fun x => tr.v r x 0) y) s =
      Cyl.partialQ u1 y - Cyl.partialEta u0 y
    exact hsub.trans (by
      rw [PartI_T20.iteratedDeriv_partialQ_eq (F := fun r x => tr.v r x 1) hv1_sm ℓ hs y,
        PartI_T20.iteratedDeriv_partialEta_eq (F := fun r x => tr.v r x 0) hv0_sm ℓ hs y])
  have hdiv : ∀ y, UnforcedLeray.B0151.derivWord [true] u0 y +
      UnforcedLeray.B0151.derivWord [false] u1 y = 0 := by
    intro y
    have hadd := iteratedDeriv_add
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialQ (fun x => tr.v r x 0) w) hQ0 hs y ℓ)
      (PartI_T22.contDiffAt_age_slice (F := fun r w => Cyl.partialEta (fun x => tr.v r x 1) w) hE1 hs y ℓ)
    change Cyl.partialQ u0 y + Cyl.partialEta u1 y = 0
    rw [← PartI_T20.iteratedDeriv_partialQ_eq (F := fun r x => tr.v r x 0) hv0_sm ℓ hs y,
      ← PartI_T20.iteratedDeriv_partialEta_eq (F := fun r x => tr.v r x 1) hv1_sm ℓ hs y,
      ← hadd]
    have hev : ((fun r => Cyl.partialQ (fun x => tr.v r x 0) y) +
        fun r => Cyl.partialEta (fun x => tr.v r x 1) y) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using tr.isTrain.solenoidal r hr.le y
    rw [hev.iteratedDeriv_eq ℓ, iteratedDeriv_const]
    split_ifs <;> rfl
  obtain ⟨hL0, hL1⟩ := vwl_lap_pair u0 u1 vom hu0 hu1 hvom_eq hdiv
  fin_cases k
  · have hcomm : Train.lapS (UnforcedLeray.B0151.derivWord w u0) =
        UnforcedLeray.B0151.derivWord w (Train.lapS u0) :=
      (derivWordLapComm_proof u0 hu0 w).symm
    have hcons : UnforcedLeray.B0151.derivWord (false :: w) vom =
        UnforcedLeray.B0151.derivWord w (UnforcedLeray.B0151.derivWord [false] vom) :=
      vwl_cons_false vom hvoms w
    have hlap_w : Train.lapS (UnforcedLeray.B0151.derivWord w u0) z =
        -UnforcedLeray.B0151.derivWord (false :: w) vom z := by
      rw [hcomm, hL0, vwl_derivWord_neg, hcons]
    change |Train.lapS (UnforcedLeray.B0151.derivWord w u0) z| ≤ ‖iteratedFDeriv ℝ (j + 1) vom z‖
    rw [hlap_w, abs_neg]
    exact (cylJetWord_proof vom hvoms (j + 1) z).1 (false :: w) (by simp [hw])
  · have hcomm : Train.lapS (UnforcedLeray.B0151.derivWord w u1) =
        UnforcedLeray.B0151.derivWord w (Train.lapS u1) :=
      (derivWordLapComm_proof u1 hu1 w).symm
    have hcons : UnforcedLeray.B0151.derivWord (true :: w) vom =
        UnforcedLeray.B0151.derivWord w (UnforcedLeray.B0151.derivWord [true] vom) :=
      vwl_cons_true vom hvoms w
    have hlap_w : Train.lapS (UnforcedLeray.B0151.derivWord w u1) z =
        UnforcedLeray.B0151.derivWord (true :: w) vom z := by
      rw [hcomm, hL1, hcons]
    change |Train.lapS (UnforcedLeray.B0151.derivWord w u1) z| ≤ ‖iteratedFDeriv ℝ (j + 1) vom z‖
    rw [hlap_w]
    exact (cylJetWord_proof vom hvoms (j + 1) z).1 (true :: w) (by simp [hw])

/-- Global bound on `‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖` from a global vorticity jet
bound `G` at `(ℓ, j + 1)` and qualitative exterior boundedness of `ageJet ℓ j tr.v s`. -/
theorem norm_ageJet_hfluct_v_le
    {ν c G R_t B_t : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hRt : 0 ≤ R_t)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hω : ∀ w : Plane, ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤ G)
    (hTail_v : ∀ w : Plane, R_t ≤ |w.2| → ‖ageJet ℓ j tr.v s w‖ ≤ B_t) :
    ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤
      2 * (2 : ℝ) ^ j * vhaOscConst * c ^ 2 * G := by
  have hv_fl_sm : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hv_joint : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hcomp_le : ∀ k : Fin 2,
      ‖ageJet ℓ j (fun r w => (hfluct c (tr.v r) w) k) s z‖ ≤
        (2 : ℝ) ^ j * (vhaOscConst * c ^ 2 * G) := by
    intro k
    let u_k : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => tr.v r w k) s
    let u_fl_k : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => (hfluct c (tr.v r) w) k) s
    have hvk_sm : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_joint
    have hvflk_sm : PartI_T20.SmR (fun x : ℝ × Plane => (hfluct c (tr.v x.1) x.2) k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_fl_sm
    have hu_k : ContDiff ℝ ∞ u_k := PartI_T22.contDiff_slice_iteratedDeriv hvk_sm ℓ hs
    have hu_fl_k : ContDiff ℝ ∞ u_fl_k := PartI_T22.contDiff_slice_iteratedDeriv hvflk_sm ℓ hs
    have hu_k_per : UnforcedLeray.B0151.IsPeriodicQ c u_k := by
      intro q η
      have hev : (fun r => tr.v r (q + c, η) k) =ᶠ[𝓝 s] (fun r => tr.v r (q, η) k) := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact congrArg (fun u : Vec => u k) (tr.isTrain.periodic_v r hr.le (q, η))
      exact hev.iteratedDeriv_eq ℓ
    have hu_fl_eq : u_fl_k = vhaOsc c u_k :=
      funext fun w => iteratedDeriv_hfluct_v_comp_eq hc tr k ℓ hs w
    refine UnforcedLeray.Short.Spine.norm_iteratedFDeriv_le_of_derivWord hu_fl_k j z (fun w hw => ?_)
    rw [hu_fl_eq, derivWord_vhaOsc hc hu_k hu_k_per w]
    let q_w : Plane → ℝ := UnforcedLeray.B0151.derivWord w u_k
    have hq_w_cd : ContDiff ℝ ∞ q_w := UnforcedLeray.B0151.contDiff_derivWord hu_k w
    have hq_w_perQ : UnforcedLeray.B0151.IsPeriodicQ c q_w :=
      UnforcedLeray.B0151.periodic_derivWord hu_k_per w
    have hq_w_per : Cyl.IsPeriodic c q_w := fun y => hq_w_perQ y.1 y.2
    have hLap_w : ∀ y : Plane, |Train.lapS q_w y| ≤ G :=
      fun y => (norm_lapS_derivWord_velSlice_le tr k ℓ j hs hw y).trans (hω y)
    have hTail_qw : ∀ y : Plane, R_t ≤ |y.2| → |q_w y| ≤ B_t := by
      intro y hy
      have h1 : |q_w y| ≤ ‖iteratedFDeriv ℝ j u_k y‖ :=
        (cylJetWord_proof u_k hu_k j y).1 w hw
      have h2 : ‖iteratedFDeriv ℝ j u_k y‖ ≤ ‖ageJet ℓ j tr.v s y‖ :=
        PartI_T20.norm_ageJet_vec_proj_le hv_joint k ℓ j hs y
      exact (h1.trans h2).trans (hTail_v y hy)
    have hBdd_qw : ∃ M : ℝ, ∀ y : Plane, |q_w y| ≤ M :=
      exists_global_bound_of_periodic_and_tail hc hRt hq_w_cd.continuous hq_w_per hTail_qw
    exact cylPoisOscGlobalBound_of_bdd hc hG hq_w_cd hq_w_per z hLap_w hBdd_qw
  have hvec := PartI_T20_1.norm_ageJet_vec_le_add_proj (V := fun r w => hfluct c (tr.v r) w) hv_fl_sm ℓ j hs z
  have h0 := hcomp_le 0
  have h1 := hcomp_le 1
  linarith

/-- Interior-strip velocity jet bounds at all higher age orders `ℓ = m + 1` from `hOv`, `hVort`, and `hTail`. -/
theorem trainInteriorStripVelHigherAgeJetBounds_proof
    (_hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    PartI_T21_2.TrainInteriorStripVelHigherAgeJetBounds := by
  intro ρ hρ m j C' hC'
  let ℓ : ℕ := m + 1
  obtain ⟨C_m, N_m, ν_m, hC_m, hν_m, hMean⟩ :=
    trainInteriorStripMeanVelJetBounds hVort hTail ρ hρ ℓ j C' hC'
  obtain ⟨b₀_ω, C₀_ω, C'_ω, hb₀_ω, hC₀_ω, _hC'_ω, C_ω, N_ω, ν_ω, hC_ω, hν_ω, hW⟩ :=
    hVort ρ hρ ℓ (j + 1)
  obtain ⟨b₀_t, C₀_t, C'_t, _hb₀_t, _hC₀_t, hC'_t, C_t, N_t, ν_t, _hC_t, hν_t, hTj⟩ :=
    hTail ρ hρ ℓ j
  let C_fl : ℝ := 2 * (2 : ℝ) ^ j * vhaOscConst * C_ω
  let N_fl : ℕ := N_ω + 2
  let C_v : ℝ := C_m + C_fl
  let N_v : ℕ := max N_m N_fl
  let ν₀ : ℝ := min ν_m (min ν_ω ν_t)
  have hOsc : 0 < vhaOscConst := vhaOscConst_pos
  have hC_fl : 0 < C_fl := by dsimp [C_fl]; positivity
  have hC_v : 0 < C_v := add_pos hC_m hC_fl
  refine ⟨C_v, N_v, ν₀, hC_v, lt_min hν_m (lt_min hν_ω hν_t), ?_⟩
  intro ν hν hν_le tr htr s hs z hz
  have hν_m_le : ν ≤ ν_m := hν_le.trans (min_le_left _ _)
  have hν_ω_le : ν ≤ ν_ω := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_t_le : ν ≤ ν_t := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hBω_nn : 0 ≤ polyP C_ω N_ω ν c := by unfold polyP; positivity
  have hω_all : ∀ w : Plane, ‖ageJet ℓ (j + 1) (fun r y => Cyl.curl (tr.v r) y) s w‖ ≤
      polyP C_ω N_ω ν c := by
    intro w
    have hw := hW ν hν hν_ω_le tr htr s hs w
    have hexp1 : Real.exp (-(b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : 0 ≤ b₀_ω * (max (|w.2| - C'_ω / ν) 0) ^ 2 / (C₀_ω + ν * s) :=
        div_nonneg (mul_nonneg hb₀_ω.le (sq_nonneg _)) (by positivity)
      linarith
    exact hw.trans (mul_le_of_le_one_right hBω_nn hexp1)
  let R_t : ℝ := C'_t / ν + 2
  have hRt_nn : 0 ≤ R_t := by dsimp [R_t]; positivity
  have hTail_v : ∀ w : Plane, R_t ≤ |w.2| →
      ‖ageJet ℓ j tr.v s w‖ ≤ 2 * polyPS C_t N_t ν c s := by
    intro w hw
    have hw' : C'_t / ν + 2 + 0 ≤ |w.2| := by dsimp [R_t] at hw; linarith
    have hraw := (hTj s hs.le ν hν hν_t_le tr htr 0 le_rfl s hs le_rfl w hw').2.1
    have hexp : Real.exp (-(b₀_t * 0 / c)) + Real.exp (-(b₀_t * 0 ^ 2 / (C₀_t + ν * s))) = 2 := by
      simp; norm_num
    rw [hexp] at hraw
    linarith
  have hfl_raw := norm_ageJet_hfluct_v_le hc hBω_nn hRt_nn tr ℓ j hs z hω_all hTail_v
  have hfl_polyP : 2 * (2 : ℝ) ^ j * vhaOscConst * c ^ 2 * polyP C_ω N_ω ν c ≤
      polyP C_fl N_fl ν c := by
    unfold polyP
    dsimp [C_fl, N_fl]
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
    have hc2 : c ^ 2 ≤ (1 + c + ν⁻¹) ^ 2 := pow_le_pow_left₀ hc.le hcX 2
    calc 2 * (2 : ℝ) ^ j * vhaOscConst * c ^ 2 * (C_ω * (1 + c + ν⁻¹) ^ N_ω)
        = (2 * (2 : ℝ) ^ j * vhaOscConst * C_ω) * (c ^ 2 * (1 + c + ν⁻¹) ^ N_ω) := by ring
      _ ≤ (2 * (2 : ℝ) ^ j * vhaOscConst * C_ω) *
            ((1 + c + ν⁻¹) ^ 2 * (1 + c + ν⁻¹) ^ N_ω) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = (2 * (2 : ℝ) ^ j * vhaOscConst * C_ω) * (1 + c + ν⁻¹) ^ (N_ω + 2) := by
          rw [pow_add]; ring
  have hfl_polyPS : ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ ≤
      polyPS C_fl N_v ν c s := by
    refine (hfl_raw.trans hfl_polyP).trans ?_
    exact (vha_polyP_le_polyPS hC_fl.le hν hc.le hs.le).trans
      (PartI_T21.polyPS_mono hC_fl.le le_rfl (le_max_right _ _) hν hc.le hs.le)
  have hmean_polyPS : ‖ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z‖ ≤
      polyPS C_m N_v ν c s :=
    (hMean ν hν hν_m_le tr htr s hs z hz).trans
      (PartI_T21.polyPS_mono hC_m.le le_rfl (le_max_left _ _) hν hc.le hs.le)
  have hsub := PartI_T21.ageJet_train_v_sub_fluct_eq hc tr hs ℓ j z
  have hadd_eq : ageJet ℓ j tr.v s z =
      ageJet ℓ j (fun r => hfluct c (tr.v r)) s z +
        ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z :=
    eq_add_of_sub_eq' hsub
  rw [hadd_eq]
  calc ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z +
          ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z‖
      ≤ ‖ageJet ℓ j (fun r => hfluct c (tr.v r)) s z‖ +
          ‖ageJet ℓ j (fun r w => hmean c (tr.v r) w.2) s z‖ := norm_add_le _ _
    _ ≤ polyPS C_fl N_v ν c s + polyPS C_m N_v ν c s := add_le_add hfl_polyPS hmean_polyPS
    _ = polyPS C_v N_v ν c s := by
        unfold polyPS
        dsimp [C_v]
        ring

end PartI_T21_2.VelHigherAgeAux

/-- **Target theorem (`PartI:T21/2/1`)**: unweighted `polyPS` bounds for `ageJet ℓ j` of
`(tr.ψ, tr.v, tr.p)` on any interior strip `|z.2| ≤ C' / ν + 2`. -/
theorem trainInteriorStripJetBounds_proof
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    TrainInteriorStripJetBounds :=
  trainInteriorStripJetBounds_of_higherVel
    (PartI_T21_2.VelHigherAgeAux.trainInteriorStripVelHigherAgeJetBounds_proof hOv hVort hTail)
    hOv hVort hTail

end UnforcedLeray.Short.PartI

