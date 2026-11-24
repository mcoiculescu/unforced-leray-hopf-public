import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.RawProfJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainChartBridge
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.FirstJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.D2Jet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSegment
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21.WeightedJetBounds
import UnforcedLeray.Short.PartI.Sub.PartI_T21.TransverseTail
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanCoeff

/-!
# `PartII-b:T20/2`: proof of the coefficient leaf `RawBoxJet`

Source of record: `the November 2 reference manuscript` (SP), lines 2419-2423
(raw coefficients), with the Part I train estimates `sct:transverse` (SP 463-467) and the
weighted jet bounds (SP 518-526), polynomial convention SP 255-258.

On `0 < s ≤ Γ`, `|η| ≤ Γ`, `ν⁻¹ ≤ Γ`:
* the velocity jets `v, ∂_sv, Dv` are `≤ CΓ^N` (weighted sup bounds `m = 0`, polynomial in `s`);
  `TrainChartBridge` turns them into the chart jet of `v`;
* the stream jets with a spatial derivative are velocity jets (`PsiFirstJets`, `PsiD2Jet`);
  `ψ, ∂_sψ, ∂_s²ψ` are bounded at the height `η* = C'/ν + 2` by the transverse tails (with
  `S_* = Γ`) and transported to `η` along a segment of length `≤ (3 + C')Γ` (`PsiEtaSegment`);
* `RaisedChartBridge` and `chartJet_smul_m1` give the chart jet of `He_z`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartI (ageJet wSupNorm polyPS trainPeriod)
open UnforcedLeray.Train (jap)

namespace RemBd

theorem trainOverlap_uncond : UnforcedLeray.Short.PartI.TrainOverlap ∧
    UnforcedLeray.Short.PartI.TrainVorticityGaussianTail := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  exact ⟨hOv, UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv⟩

theorem trainTail_uncond : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTransverseTail :=
  UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_proof
    trainOverlap_uncond.1 trainOverlap_uncond.2

theorem trainWJ_uncond : UnforcedLeray.Short.PartI.TrainWeightedJetBounds :=
  UnforcedLeray.Short.PartI.trainWeightedJetBounds_proof trainOverlap_uncond.1
    trainOverlap_uncond.2 trainTail_uncond

/-- Transport of a BUC train along an equality of periods, keeping `v` and `ψ`. -/
theorem train_transport {ν c c' : ℝ} (h : c = c') (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.v = tr.v ∧ tr'.ψ = tr.ψ := by
  subst h
  exact ⟨tr, hb, rfl, rfl⟩

theorem pt_of_wSupNorm_zero {E : Type*} [NormedAddCommGroup E]
    (f : UnforcedLeray.Cyl.Plane → E) {K : ℝ} (hK : 0 ≤ K) (h : wSupNorm 0 f ≤ ENNReal.ofReal K)
    (z : UnforcedLeray.Cyl.Plane) : ‖f z‖ ≤ K := by
  have h1 := UnforcedLeray.Short.PartIIa.lmc_pt_of_sup 0 f hK h z
  have hj : jap 0 z = 1 := by simp [jap]
  rw [hj, one_mul] at h1
  nlinarith [norm_nonneg (f z)]

theorem polyPS_le_gamma_pow {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {ν s Γ : ℝ}
    (hν : 0 < ν) (hΓ1 : 1 ≤ Γ) (hνi : ν⁻¹ ≤ Γ) (hs0 : 0 ≤ s) (hsΓ : s ≤ Γ) :
    polyPS C N ν (trainPeriod 2 ν) s ≤ (C * 6 ^ N) * Γ ^ (3 * N) := by
  have hc : trainPeriod 2 ν = (ν⁻¹) ^ 2 := by
    rw [velTail_trainPeriod_two hν, inv_pow]
  have hc_le : trainPeriod 2 ν ≤ Γ ^ 2 := by
    rw [hc]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hν.le) hνi 2
  have hνi_le : ν⁻¹ ≤ Γ ^ 2 := by nlinarith
  have hA : 1 + trainPeriod 2 ν + ν⁻¹ ≤ 3 * Γ ^ 2 := by nlinarith
  have hB : 1 + s ≤ 2 * Γ := by linarith
  have hAB : (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s) ≤ 6 * Γ ^ 3 := by
    calc (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s)
        ≤ (3 * Γ ^ 2) * (2 * Γ) :=
          mul_le_mul hA hB (by linarith) (by positivity)
      _ = 6 * Γ ^ 3 := by ring
  have hAB0 : 0 ≤ (1 + trainPeriod 2 ν + ν⁻¹) * (1 + s) := by
    have : 0 ≤ trainPeriod 2 ν := by rw [hc]; positivity
    have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    positivity
  unfold polyPS
  calc C * ((1 + trainPeriod 2 ν + ν⁻¹) * (1 + s)) ^ N
      ≤ C * (6 * Γ ^ 3) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAB0 hAB N) hC
    _ = (C * 6 ^ N) * Γ ^ (3 * N) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- Velocity jets on bounded ages, polynomially in `Γ`. -/
theorem velJet_box (ℓ j : ℕ) : ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ Γ : ℝ, 1 ≤ Γ → p.ν⁻¹ ≤ Γ → ∀ (s : ℝ) (z : ℝ × ℝ), 0 < s → s ≤ Γ →
      ‖ageJet ℓ j p.train.v s z‖ ≤ C * Γ ^ N := by
  obtain ⟨C, N, ν₀, hC, hν₀, hB⟩ := trainWJ_uncond 2 (by norm_num) 0 ℓ j
  refine ⟨C * 6 ^ N, 3 * N, ν₀, by positivity, hν₀, ?_⟩
  intro p d dm dp hbg hν Γ hΓ1 hνi s z hs hsΓ
  have hνpos := p.ν_pos
  have hc_eq : p.c = trainPeriod 2 p.ν := hbg.c_eq.trans (velTail_trainPeriod_two hνpos).symm
  obtain ⟨tr', hb', hv', -⟩ := train_transport hc_eq p.train hbg.train_buc
  have hsup := (hB p.ν hνpos hν tr' hb' s hs).2.2.1.2
  have hK0 : 0 ≤ polyPS C N p.ν (trainPeriod 2 p.ν) s := by
    unfold polyPS
    have : 0 ≤ trainPeriod 2 p.ν := by rw [velTail_trainPeriod_two hνpos]; positivity
    have : 0 ≤ p.ν⁻¹ := inv_nonneg.mpr hνpos.le
    positivity
  have hpt := pt_of_wSupNorm_zero (ageJet ℓ j tr'.v s) hK0 hsup z
  rw [hv'] at hpt
  exact hpt.trans (polyPS_le_gamma_pow hC.le N hνpos hΓ1 hνi hs.le hsΓ)

/-- Stream jets `∂_s^ℓψ` at heights `|η| ≥ C'/ν + 2` on bounded ages (transverse tails, `l = 0`). -/
theorem psiTail_box (ℓ : ℕ) : ∃ C' : ℝ, 0 < C' ∧ ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ Γ : ℝ, 1 ≤ Γ → p.ν⁻¹ ≤ Γ → ∀ (s : ℝ) (z : ℝ × ℝ), 0 < s → s ≤ Γ →
      C' / p.ν + 2 ≤ |z.2| → ‖ageJet ℓ 0 p.train.ψ s z‖ ≤ C * Γ ^ N := by
  obtain ⟨b, C₀, C', _hb, _hC₀, hC', C, N, ν₀, hC, hν₀, hT⟩ := trainTail_uncond 2 (by norm_num) ℓ 0
  refine ⟨C', hC', 2 * (C * 6 ^ N), 3 * N, ν₀, by positivity, hν₀, ?_⟩
  intro p d dm dp hbg hν Γ hΓ1 hνi s z hs hsΓ hz
  have hνpos := p.ν_pos
  have hc_eq : p.c = trainPeriod 2 p.ν := hbg.c_eq.trans (velTail_trainPeriod_two hνpos).symm
  obtain ⟨tr', hb', -, hψ'⟩ := train_transport hc_eq p.train hbg.train_buc
  have hΓ0 : 0 ≤ Γ := by linarith
  have h := (hT Γ hΓ0 p.ν hνpos hν tr' hb' 0 le_rfl s hs hsΓ z (by linarith)).1
  have h1 : ‖ageJet ℓ 0 tr'.ψ s z‖ ≤ polyPS C N p.ν (trainPeriod 2 p.ν) Γ *
      (Real.exp (-(b * 0 / trainPeriod 2 p.ν)) +
        Real.exp (-(b * 0 ^ 2 / (C₀ + p.ν * Γ)))) := h
  have e : Real.exp (-(b * 0 / trainPeriod 2 p.ν)) +
      Real.exp (-(b * 0 ^ 2 / (C₀ + p.ν * Γ))) = 2 := by
    simp; norm_num
  rw [e, hψ'] at h1
  have hp := polyPS_le_gamma_pow hC.le N hνpos hΓ1 hνi hΓ0 le_rfl
  calc ‖ageJet ℓ 0 p.train.ψ s z‖ ≤ polyPS C N p.ν (trainPeriod 2 p.ν) Γ * 2 := h1
    _ ≤ (C * 6 ^ N) * Γ ^ (3 * N) * 2 := by gcongr
    _ = 2 * (C * 6 ^ N) * Γ ^ (3 * N) := by ring

/-- `a ≤ CΓ^N` with `C ≤ C'`, `N ≤ M`, `Γ ≥ 1` gives `a ≤ C'Γ^M`. -/
theorem bound_mono {Γ a C C' : ℝ} {N M : ℕ} (hΓ1 : 1 ≤ Γ) (hC : 0 ≤ C) (hCC : C ≤ C')
    (hNM : N ≤ M) (h : a ≤ C * Γ ^ N) : a ≤ C' * Γ ^ M := by
  have hΓ0 : 0 ≤ Γ := by linarith
  calc a ≤ C * Γ ^ N := h
    _ ≤ C * Γ ^ M := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΓ1 hNM) hC
    _ ≤ C' * Γ ^ M := mul_le_mul_of_nonneg_right hCC (by positivity)

/-- The chart jet of the train velocity on the box from the velocity jets. -/
theorem train_box {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {Γ V : ℝ}
    (hΓ1 : 1 ≤ Γ) (hV0 : 0 ≤ V) {x : Coord} (hx0 : 0 < x.1) (hxΓ : x.1 ≤ Γ)
    (hηΓ : |x.2.2| ≤ Γ)
    (hvx : ‖ageJet 0 0 p.train.v x.1 x.2‖ ≤ V ∧ ‖ageJet 1 0 p.train.v x.1 x.2‖ ≤ V ∧
      ‖ageJet 0 1 p.train.v x.1 x.2‖ ≤ V) :
    chartJet (trainProf p) x ≤ 6 * Γ * V := by
  have hΓ0 : 0 ≤ Γ := by linarith
  obtain ⟨b0, b1, b2, b3⟩ := trainChartBridge_of trainVelSmooth_proof p d dm dp hbg x hx0
  have hk : ‖kAge (trainProf p) x‖ ≤ 2 * x.1 * ‖Axi.dS (trainProf p) x‖ +
      |x.2.2| * ‖Axi.dEta (trainProf p) x‖ := by
    unfold kAge
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x.1)]
  unfold chartJet
  have e1 : ‖Axi.dS (trainProf p) x‖ ≤ V := b1.trans hvx.2.1
  have e2 : ‖Axi.dEta (trainProf p) x‖ ≤ V := b3.trans hvx.2.2
  have e3 : 2 * x.1 * ‖Axi.dS (trainProf p) x‖ ≤ 2 * Γ * V :=
    mul_le_mul (by linarith) e1 (norm_nonneg _) (by positivity)
  have e4 : |x.2.2| * ‖Axi.dEta (trainProf p) x‖ ≤ Γ * V :=
    mul_le_mul hηΓ e2 (norm_nonneg _) hΓ0
  have hV1 : V ≤ Γ * V := le_mul_of_one_le_left hV0 hΓ1
  linarith [b0.trans hvx.1, b2.trans hvx.2.2]

/-- The chart jet of the raised stream on the box from the velocity jets and the stream tails. -/
theorem raised_box {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) {Γ V T D : ℝ}
    (hΓ1 : 1 ≤ Γ) (hνi : p.ν⁻¹ ≤ Γ) (hV0 : 0 ≤ V) (hD0 : 0 ≤ D) {x : Coord} (hx0 : 0 < x.1)
    (hxΓ : x.1 ≤ Γ) (hηΓ : |x.2.2| ≤ Γ)
    (vb : ∀ (s : ℝ) (z : ℝ × ℝ), 0 < s → s ≤ Γ →
      ‖ageJet 0 0 p.train.v s z‖ ≤ V ∧ ‖ageJet 1 0 p.train.v s z‖ ≤ V ∧
      ‖ageJet 0 1 p.train.v s z‖ ≤ V ∧ ‖ageJet 2 0 p.train.v s z‖ ≤ V)
    (hTail : ∀ ℓ : ℕ, ℓ ≤ 2 → ‖ageJet ℓ 0 p.train.ψ x.1 (x.2.1, D / p.ν + 2)‖ ≤ T) :
    chartJet (raisedMerid p) x ≤ 20 * (1 + 2 * Γ) ^ 2 * (3 * (T + V * ((3 + D) * Γ)) + 6 * V) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hνpos := p.ν_pos
  have hpair : IsStreamPair p.train.ψ p.train.v :=
    ⟨hbg.train_stream_smooth,
      p.train.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl),
      fun s hs z => p.train.isTrain.stream s hs.le z⟩
  have hηs0 : 0 < D / p.ν + 2 := by positivity
  have hηsΓ : D / p.ν + 2 ≤ (D + 2) * Γ := by
    have e : D / p.ν = D * p.ν⁻¹ := div_eq_mul_inv _ _
    have h1 : D * p.ν⁻¹ ≤ D * Γ := mul_le_mul_of_nonneg_left hνi hD0
    nlinarith
  have hseg : |x.2.2 - (D / p.ν + 2)| ≤ (3 + D) * Γ := by
    have h1 := abs_sub_le x.2.2 0 (D / p.ν + 2)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_pos hηs0] at h1
    nlinarith
  have hz : x.2 = (x.2.1, x.2.2) := rfl
  have hpsi : ∀ ℓ : ℕ, ℓ ≤ 2 → ‖ageJet ℓ 0 p.train.ψ x.1 x.2‖ ≤ T + V * ((3 + D) * Γ) := by
    intro ℓ hℓ
    have hB : ∀ t ∈ uIcc x.2.2 (D / p.ν + 2), ‖ageJet ℓ 0 p.train.v x.1 (x.2.1, t)‖ ≤ V := by
      intro t _
      have hv := vb x.1 (x.2.1, t) hx0 hxΓ
      interval_cases ℓ
      · exact hv.1
      · exact hv.2.1
      · exact hv.2.2.2
    have hs := psiEtaSegment_proof p.train.ψ p.train.v hpair ℓ x.1 hx0 x.2.1 x.2.2
      (D / p.ν + 2) V hB
    rw [← hz] at hs
    calc ‖ageJet ℓ 0 p.train.ψ x.1 x.2‖
        ≤ ‖ageJet ℓ 0 p.train.ψ x.1 (x.2.1, D / p.ν + 2)‖ + V * |x.2.2 - (D / p.ν + 2)| := hs
      _ ≤ T + V * ((3 + D) * Γ) := by
          gcongr
          exact hTail ℓ hℓ
  have hFJ := psiFirstJets_proof p.train.ψ p.train.v hpair x.1 hx0 x.2
  have hD2 := psiD2Jet_proof p.train.ψ p.train.v hpair x.1 hx0 x.2
  have hvx := vb x.1 x.2 hx0 hxΓ
  have hdiff := trainDiff p d dm dp hbg x hx0
  have e := RawProfJetHelp.chartJet_smul_m1 (h := raisedProf p) x hdiff.2
  have hbr := raisedChartBridge_proof p d dm dp hbg x hx0
  have hrm : raisedMerid p = fun y => raisedProf p y • Axi.m1 := rfl
  rw [hrm, e]
  refine hbr.trans ?_
  have h1 : (1 + |x.2.2| + x.1) ^ 2 ≤ (1 + 2 * Γ) ^ 2 := by
    have : 0 ≤ 1 + |x.2.2| + x.1 := by positivity
    have : 1 + |x.2.2| + x.1 ≤ 1 + 2 * Γ := by linarith
    gcongr
  have hψsum : ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
        ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
        ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖ ≤
      3 * (T + V * ((3 + D) * Γ)) + 6 * V := by
    have a0 := hpsi 0 (by norm_num)
    have a1 := hpsi 1 (by norm_num)
    have a2 := hpsi 2 (by norm_num)
    linarith [hFJ.1, hFJ.2, hD2, hvx.1, hvx.2.1, hvx.2.2.1]
  gcongr

/-- The closing polynomial arithmetic. -/
theorem box_arith {Γ V T CV CT D : ℝ} {NV NT : ℕ} (hΓ1 : 1 ≤ Γ) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (hD0 : 0 ≤ D) (hV0 : 0 ≤ V) (hT0 : 0 ≤ T) (hV : V ≤ CV * Γ ^ NV) (hT : T ≤ CT * Γ ^ NT) :
    6 * Γ * V + 20 * (1 + 2 * Γ) ^ 2 * (3 * (T + V * ((3 + D) * Γ)) + 6 * V) ≤
      (6 * CV + 180 * (3 * CT + 3 * CV * (3 + D) + 6 * CV)) * Γ ^ (NV + NT + 3) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hG1 : 1 ≤ Γ ^ (NV + NT) := one_le_pow₀ hΓ1
  have hVG : V ≤ CV * Γ ^ (NV + NT) :=
    hV.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΓ1 (by omega)) hCV)
  have hTG : T ≤ CT * Γ ^ (NV + NT) :=
    hT.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΓ1 (by omega)) hCT)
  have hpow : Γ ^ (NV + NT + 3) = Γ ^ (NV + NT) * Γ ^ 3 := pow_add _ _ _
  rw [hpow]
  generalize Γ ^ (NV + NT) = G at hG1 hVG hTG ⊢
  have hΓ3 : Γ ≤ Γ ^ 3 := by
    calc Γ = Γ ^ 1 := (pow_one Γ).symm
      _ ≤ Γ ^ 3 := pow_le_pow_right₀ hΓ1 (by norm_num)
  have h12 : (1 + 2 * Γ) ^ 2 ≤ 9 * Γ ^ 2 := by nlinarith
  have hinner : 3 * (T + V * ((3 + D) * Γ)) + 6 * V ≤
      Γ * (3 * CT * G + 3 * CV * G * (3 + D) + 6 * CV * G) := by
    have q1 : T ≤ Γ * (CT * G) := hTG.trans (le_mul_of_one_le_left (by positivity) hΓ1)
    have q2 : V * ((3 + D) * Γ) ≤ Γ * (CV * G * (3 + D)) := by
      have := mul_le_mul_of_nonneg_right hVG (by positivity : (0 : ℝ) ≤ (3 + D) * Γ)
      linarith [this]
    have q3 : V ≤ Γ * (CV * G) := hVG.trans (le_mul_of_one_le_left (by positivity) hΓ1)
    nlinarith
  have hR : 20 * (1 + 2 * Γ) ^ 2 * (3 * (T + V * ((3 + D) * Γ)) + 6 * V) ≤
      180 * (3 * CT + 3 * CV * (3 + D) + 6 * CV) * (G * Γ ^ 3) := by
    have hX0 : 0 ≤ 3 * (T + V * ((3 + D) * Γ)) + 6 * V := by positivity
    calc 20 * (1 + 2 * Γ) ^ 2 * (3 * (T + V * ((3 + D) * Γ)) + 6 * V)
        ≤ 20 * (9 * Γ ^ 2) * (Γ * (3 * CT * G + 3 * CV * G * (3 + D) + 6 * CV * G)) := by
          gcongr
      _ = 180 * (3 * CT + 3 * CV * (3 + D) + 6 * CV) * (G * Γ ^ 3) := by ring
  have hT' : 6 * Γ * V ≤ 6 * CV * (G * Γ ^ 3) := by
    calc 6 * Γ * V ≤ 6 * Γ ^ 3 * (CV * G) := by
          have : 6 * Γ ≤ 6 * Γ ^ 3 := by linarith
          exact mul_le_mul this hVG hV0 (by positivity)
      _ = 6 * CV * (G * Γ ^ 3) := by ring
  linarith

end RemBd

open RemBd in
/-- **`RawBoxJet`** (SP 2015-2018, 2419-2423): unconditional. -/
theorem rawBoxJet_proof : RawBoxJet := by
  obtain ⟨C1, N1, ν1, hC1, hν1, H1⟩ := velJet_box 0 0
  obtain ⟨C2, N2, ν2, hC2, hν2, H2⟩ := velJet_box 1 0
  obtain ⟨C3, N3, ν3, hC3, hν3, H3⟩ := velJet_box 0 1
  obtain ⟨C4, N4, ν4, hC4, hν4, H4⟩ := velJet_box 2 0
  obtain ⟨D0, hD0, T0, M0, μ0, hT0, hμ0, P0⟩ := psiTail_box 0
  obtain ⟨D1, hD1, T1, M1, μ1, hT1, hμ1, P1⟩ := psiTail_box 1
  obtain ⟨D2, hD2, T2, M2, μ2, hT2, hμ2, P2⟩ := psiTail_box 2
  refine ⟨(N1 + N2 + N3 + N4) + (M0 + M1 + M2) + 3,
    6 * (C1 + C2 + C3 + C4) + 180 * (3 * (T0 + T1 + T2) +
      3 * (C1 + C2 + C3 + C4) * (3 + (D0 + D1 + D2)) + 6 * (C1 + C2 + C3 + C4)),
    min (min (min ν1 ν2) (min ν3 ν4)) (min (min μ0 μ1) μ2), by positivity,
    lt_min (lt_min (lt_min hν1 hν2) (lt_min hν3 hν4)) (lt_min (lt_min hμ0 hμ1) hμ2), ?_⟩
  intro p d dm dp hbg hν Γ hΓ1 hνi x hx0 hxΓ hηΓ
  have hνpos := p.ν_pos
  have hν1' : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hν2' : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hν3' : p.ν ≤ ν3 := hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hν4' : p.ν ≤ ν4 := hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hμ0' : p.ν ≤ μ0 := hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hμ1' : p.ν ≤ μ1 := hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hμ2' : p.ν ≤ μ2 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCV : 0 ≤ C1 + C2 + C3 + C4 := by positivity
  have hV0 : 0 ≤ (C1 + C2 + C3 + C4) * Γ ^ (N1 + N2 + N3 + N4) := by positivity
  have vb : ∀ (s : ℝ) (z : ℝ × ℝ), 0 < s → s ≤ Γ →
      ‖ageJet 0 0 p.train.v s z‖ ≤ (C1 + C2 + C3 + C4) * Γ ^ (N1 + N2 + N3 + N4) ∧
      ‖ageJet 1 0 p.train.v s z‖ ≤ (C1 + C2 + C3 + C4) * Γ ^ (N1 + N2 + N3 + N4) ∧
      ‖ageJet 0 1 p.train.v s z‖ ≤ (C1 + C2 + C3 + C4) * Γ ^ (N1 + N2 + N3 + N4) ∧
      ‖ageJet 2 0 p.train.v s z‖ ≤ (C1 + C2 + C3 + C4) * Γ ^ (N1 + N2 + N3 + N4) := by
    intro s z hs hsΓ
    refine ⟨bound_mono hΓ1 hC1.le (by linarith) (by omega)
        (H1 p d dm dp hbg hν1' Γ hΓ1 hνi s z hs hsΓ),
      bound_mono hΓ1 hC2.le (by linarith) (by omega)
        (H2 p d dm dp hbg hν2' Γ hΓ1 hνi s z hs hsΓ),
      bound_mono hΓ1 hC3.le (by linarith) (by omega)
        (H3 p d dm dp hbg hν3' Γ hΓ1 hνi s z hs hsΓ),
      bound_mono hΓ1 hC4.le (by linarith) (by omega)
        (H4 p d dm dp hbg hν4' Γ hΓ1 hνi s z hs hsΓ)⟩
  have hDs : 0 ≤ D0 + D1 + D2 := by positivity
  have hTail : ∀ ℓ : ℕ, ℓ ≤ 2 → ‖ageJet ℓ 0 p.train.ψ x.1 (x.2.1, (D0 + D1 + D2) / p.ν + 2)‖ ≤
      (T0 + T1 + T2) * Γ ^ (M0 + M1 + M2) := by
    intro ℓ hℓ
    have hηs0 : 0 < (D0 + D1 + D2) / p.ν + 2 := by positivity
    have habs : |((x.2.1, (D0 + D1 + D2) / p.ν + 2) : ℝ × ℝ).2| = (D0 + D1 + D2) / p.ν + 2 :=
      abs_of_pos hηs0
    interval_cases ℓ
    · refine bound_mono hΓ1 hT0.le (by linarith) (by omega)
        (P0 p d dm dp hbg hμ0' Γ hΓ1 hνi x.1 _ hx0 hxΓ ?_)
      rw [habs]
      have : D0 / p.ν ≤ (D0 + D1 + D2) / p.ν := div_le_div_of_nonneg_right (by linarith) hνpos.le
      linarith
    · refine bound_mono hΓ1 hT1.le (by linarith) (by omega)
        (P1 p d dm dp hbg hμ1' Γ hΓ1 hνi x.1 _ hx0 hxΓ ?_)
      rw [habs]
      have : D1 / p.ν ≤ (D0 + D1 + D2) / p.ν := div_le_div_of_nonneg_right (by linarith) hνpos.le
      linarith
    · refine bound_mono hΓ1 hT2.le (by linarith) (by omega)
        (P2 p d dm dp hbg hμ2' Γ hΓ1 hνi x.1 _ hx0 hxΓ ?_)
      rw [habs]
      have : D2 / p.ν ≤ (D0 + D1 + D2) / p.ν := div_le_div_of_nonneg_right (by linarith) hνpos.le
      linarith
  have hvx := vb x.1 x.2 hx0 hxΓ
  have hTr := train_box hbg hΓ1 hV0 hx0 hxΓ hηΓ ⟨hvx.1, hvx.2.1, hvx.2.2.1⟩
  have hR := raised_box hbg hΓ1 hνi hV0 hDs hx0 hxΓ hηΓ vb hTail
  have hT0' : 0 ≤ (T0 + T1 + T2) * Γ ^ (M0 + M1 + M2) := by positivity
  have hA := box_arith (CV := C1 + C2 + C3 + C4) (CT := T0 + T1 + T2) hΓ1 hCV (by positivity)
    hDs hV0 hT0' le_rfl le_rfl
  linarith

end UnforcedLeray.Short.IIb

end
