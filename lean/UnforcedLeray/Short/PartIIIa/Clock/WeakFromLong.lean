import UnforcedLeray.Short.PartIIIa.Clock.Stages
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ShortWeakSmoothing
import UnforcedLeray.Short.PartIIIa.T21_2_WeakSmoothing

/-!
# Part III-a full clock: `FullClockWeakForward` from long forward and short smoothing (SP 3085-3094)

Source of record: `the November 2 reference manuscript`, lines 3085-3094 (C7).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem movingWeakStrong_all (m : ℝ) (hm : 8 < m) : MovingWeakStrong m := by
  have hcmp : PartI.TrainComparison := PartI.trainComparison_proof
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hfl : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hme : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hfl hMP
  have hmeq : PartI.TrainMeanEquations := PartI.trainMeanEquations_proof
  have hT : RescaledTrainBounds m := rescaledTrainBounds m hcmp hfl hme hmeq
  have hW : TrainWeightedJetPoly :=
    trainWeightedJetPoly_of (fluctJetWeighted_of hfl)
      (meanJetWeighted_of (meanVecFormula_of hmeq) (meanStreamJetBound_of hme hmeq)) vcWeightedJet
  exact movingWeakStrong_of m adjointEnergyChain
    (adjointEnergyIneqs m hm periodicWeightLogBounds hT (adjointLocalizedBound m hm hT) hW)
    ⟨xNormDuality m, adjointTerminalBound m (by linarith), adjointPairingBound m hm hW⟩
    (adjointExists m hm hW)

/-- `(g(t)/g(s)) exp(γ(θ(t') - θ(s))) = g(t)/g(t')` since `s/(1+νs) = ν⁻¹ - θ(s)`. -/
theorem gainG_mul_exp_theta_eq (γ ν : ℝ) (hν : 0 < ν) {t t' s : ℝ}
    (ht' : 0 ≤ t') (hs : 0 ≤ s) :
    (gainG γ ν t / gainG γ ν s) * Real.exp (γ * (clockTheta ν t' - clockTheta ν s)) =
      gainG γ ν t / gainG γ ν t' := by
  unfold gainG clockTheta clockA
  rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  have h1 : 0 < 1 + ν * t' := by positivity
  have h2 : 0 < 1 + ν * s := by positivity
  have hν' : ν ≠ 0 := hν.ne'
  have h1' : 1 + ν * t' ≠ 0 := h1.ne'
  have h2' : 1 + ν * s ≠ 0 := h2.ne'
  field_simp
  ring

theorem gainG_mul_exp_theta_le (γ ν : ℝ) (hν : 0 < ν) {t t' s : ℝ}
    (ht : 0 ≤ t) (htt' : t ≤ t') (hgap : t' - t ≤ 1) (hs : 0 ≤ s) :
    (gainG γ ν t / gainG γ ν s) * Real.exp (γ * (clockTheta ν t' - clockTheta ν s)) ≤
      Real.exp |γ| := by
  rw [gainG_mul_exp_theta_eq γ ν hν (ht.trans htt') hs]
  exact gainG_ratio_le γ ν hν ht htt' hgap

/-- On `0 ≤ t' ≤ s` with `1 ≤ b ≤ θ(s)` and `0 < ν`, `(θ(t')/θ(s))^{Re κ} ≤ ν^{-|Re κ|}`. -/
theorem theta_ratio_rpow_le (κ : ℝ) {ν b t' s : ℝ} (hν : 0 < ν) (hb1 : 1 ≤ b)
    (ht' : 0 ≤ t') (ht's : t' ≤ s) (hbθ : b ≤ clockTheta ν s) :
    (clockTheta ν t' / clockTheta ν s) ^ κ ≤ ν ^ (-|κ|) := by
  have hs0 : 0 ≤ s := ht'.trans ht's
  have hAt' : 1 ≤ clockA ν t' := by unfold clockA; nlinarith
  have hAs : 1 ≤ clockA ν s := by unfold clockA; nlinarith
  have hAt's : clockA ν t' ≤ clockA ν s := by unfold clockA; nlinarith
  have hθs_pos : 0 < clockTheta ν s := by unfold clockTheta; positivity
  have hθt'_pos : 0 < clockTheta ν t' := by unfold clockTheta; positivity
  have hθ_mono : clockTheta ν s ≤ clockTheta ν t' := by
    unfold clockTheta
    exact inv_anti₀ (mul_pos hν (by linarith)) (mul_le_mul_of_nonneg_left hAt's hν.le)
  have hθt'_le : clockTheta ν t' ≤ ν⁻¹ := by
    unfold clockTheta
    exact inv_anti₀ hν (by nlinarith)
  have hR1 : 1 ≤ clockTheta ν t' / clockTheta ν s := (one_le_div hθs_pos).2 hθ_mono
  have hR_le : clockTheta ν t' / clockTheta ν s ≤ ν⁻¹ := by
    calc clockTheta ν t' / clockTheta ν s ≤ clockTheta ν t' / 1 :=
          div_le_div_of_nonneg_left hθt'_pos.le zero_lt_one (hb1.trans hbθ)
      _ = clockTheta ν t' := div_one _
      _ ≤ ν⁻¹ := hθt'_le
  calc (clockTheta ν t' / clockTheta ν s) ^ κ
      ≤ (clockTheta ν t' / clockTheta ν s) ^ |κ| :=
        Real.rpow_le_rpow_of_exponent_le hR1 (le_abs_self κ)
    _ ≤ (ν⁻¹) ^ |κ| :=
        Real.rpow_le_rpow (by positivity) hR_le (abs_nonneg κ)
    _ = ν ^ (-|κ|) := by
        rw [Real.inv_rpow hν.le, Real.rpow_neg hν.le]

/-- Moving-to-physical scaling product for the intermediate step at `t' = t + 1/2`. -/
theorem long_scale_real {m ν s t t' b C : ℝ} (hm : 0 ≤ m) (hν : 0 < ν) (hb : 1 ≤ b)
    (hkey : b * (ν * clockA ν s) ≤ 1) (hAs : 1 ≤ clockA ν s)
    (hAt'_le : clockA ν t' ≤ clockA ν s) (hAt_le : clockA ν t ≤ clockA ν s)
    (hAt' : 1 ≤ clockA ν t') (hAt : 1 ≤ clockA ν t) (htt' : t' - t = 1 / 2) :
    clockA ν s ^ ((m - 3) / 2) * (|C| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
        clockA ν t ^ (3 / 2 : ℝ) ≤
      |C| * b ^ (-((m + 1) / 2)) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * ν ^ (-((m + 2) / 2)) := by
  have hAs0 : 0 < clockA ν s := by linarith
  have hAt'0 : 0 < clockA ν t' := by linarith
  have hAt0 : 0 < clockA ν t := by linarith
  have hb0 : 0 < b := by linarith
  have hZ : (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ) =
      ν ^ (-1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * clockA ν t' ^ (1 / 2 : ℝ) := by
    rw [htt', Real.div_rpow (by positivity) hAt'0.le, Real.mul_rpow hν.le (by norm_num)]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hAt'0.le, div_inv_eq_mul]
  have hAt's_half : clockA ν t' ^ (1 / 2 : ℝ) ≤ clockA ν s ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hAt'0.le hAt'_le (by norm_num)
  have hAts_3 : clockA ν t ^ (3 / 2 : ℝ) ≤ clockA ν s ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hAt0.le hAt_le (by norm_num)
  have hp : 0 ≤ (m + 1) / 2 := by linarith
  have hY : 0 < ν * b := mul_pos hν hb0
  have hAle : clockA ν s ^ ((m + 1) / 2) ≤ ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2)) := by
    have e : clockA ν s * (ν * b) = b * (ν * clockA ν s) := by ring
    have hA' : clockA ν s ≤ 1 / (ν * b) := (le_div_iff₀ hY).2 (by rw [e]; exact hkey)
    calc clockA ν s ^ ((m + 1) / 2) ≤ (1 / (ν * b)) ^ ((m + 1) / 2) :=
          Real.rpow_le_rpow hAs0.le hA' hp
      _ = ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2)) := by
          rw [one_div, Real.inv_rpow hY.le, Real.mul_rpow hν.le hb0.le, Real.rpow_neg hν.le,
            Real.rpow_neg hb0.le, mul_inv]
  have hAp : clockA ν s ^ ((m - 3) / 2) * clockA ν s ^ (1 / 2 : ℝ) * clockA ν s ^ (3 / 2 : ℝ) =
      clockA ν s ^ ((m + 1) / 2) := by
    rw [← Real.rpow_add hAs0, ← Real.rpow_add hAs0]
    congr 1
    ring
  have hnu : ν ^ (-1 / 2 : ℝ) * ν ^ (-((m + 1) / 2)) = ν ^ (-((m + 2) / 2)) := by
    rw [← Real.rpow_add hν]
    congr 1
    ring
  have h1 : clockA ν t' ^ (1 / 2 : ℝ) * clockA ν t ^ (3 / 2 : ℝ) ≤
      clockA ν s ^ (1 / 2 : ℝ) * clockA ν s ^ (3 / 2 : ℝ) :=
    mul_le_mul hAt's_half hAts_3 (by positivity) (by positivity)
  calc clockA ν s ^ ((m - 3) / 2) * (|C| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
        clockA ν t ^ (3 / 2 : ℝ)
      = (clockA ν s ^ ((m - 3) / 2) * |C| * ν ^ (-1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ)) *
          (clockA ν t' ^ (1 / 2 : ℝ) * clockA ν t ^ (3 / 2 : ℝ)) := by
        rw [hZ]; ring
    _ ≤ (clockA ν s ^ ((m - 3) / 2) * |C| * ν ^ (-1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ)) *
          (clockA ν s ^ (1 / 2 : ℝ) * clockA ν s ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (|C| * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * ν ^ (-1 / 2 : ℝ)) * clockA ν s ^ ((m + 1) / 2) := by
        rw [← hAp]; ring
    _ ≤ (|C| * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * ν ^ (-1 / 2 : ℝ)) *
          (ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2))) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
    _ = |C| * b ^ (-((m + 1) / 2)) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * ν ^ (-((m + 2) / 2)) := by
        rw [← hnu]; ring

theorem ennreal_chain5 (p0 p1 p2 p3 p4 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2) (h3 : 0 ≤ p3) (N : ℝ≥0∞) :
    ENNReal.ofReal p0 * (ENNReal.ofReal p1 * (ENNReal.ofReal p2 *
      (ENNReal.ofReal p3 * (ENNReal.ofReal p4 * N)))) =
      ENNReal.ofReal (p0 * p1 * p2 * p3 * p4) * N := by
  have h01 : 0 ≤ p0 * p1 := mul_nonneg h0 h1
  have h012 : 0 ≤ p0 * p1 * p2 := mul_nonneg h01 h2
  have h0123 : 0 ≤ p0 * p1 * p2 * p3 := mul_nonneg h012 h3
  rw [ENNReal.ofReal_mul h0123, ENNReal.ofReal_mul h012, ENNReal.ofReal_mul h01,
    ENNReal.ofReal_mul h0]
  ring

theorem fullClockWeakForward_of (hLong : FullClockLongForward) (hShort : ShortWeakSmoothing)
    (hZ : ZeroCirculationPreserved) (hS : ScalingBounds) : FullClockWeakForward := by
  intro P hP m hm
  obtain ⟨b₀L, hb₀L⟩ := hLong P hP m hm
  obtain ⟨b₀S, hb₀S⟩ := hShort P hP m hm
  obtain ⟨b₀M, hb₀M⟩ := movingWeakStrong_all m hm
  refine ⟨max (max b₀L b₀S) (max b₀M 1), fun b hb => ?_⟩
  have hbL : b₀L ≤ b := (le_max_left _ _).trans ((le_max_left _ _).trans hb)
  have hbS : b₀S ≤ b := (le_max_right _ _).trans ((le_max_left _ _).trans hb)
  have hbM : b₀M ≤ b := (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hb1 : 1 ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  obtain ⟨CL, ν₀L, hν₀L, hCL⟩ := hb₀L b hbL
  obtain ⟨CS, ν₀S, hν₀S, hCS⟩ := hb₀S b hbS
  obtain ⟨CM, ν₀M, hν₀M, hCM⟩ := hb₀M b hbM
  let C_long := Real.exp |P.eigenvalue.re| * |CL| * |CM| *
    b ^ (-((m + 1) / 2)) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ)
  let C := max |CS| C_long
  refine ⟨C, min (min ν₀L ν₀S) (min ν₀M 1),
    lt_min (lt_min hν₀L hν₀S) (lt_min hν₀M zero_lt_one), ?_⟩
  intro ν hν tr htr t s ht hts hcore f hf hz w u hw
  have hν0 : 0 < ν := hν.1
  have hνL : ν ∈ Ioc 0 ν₀L := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hνS : ν ∈ Ioc 0 ν₀S := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hνM : ν ∈ Ioc 0 ν₀M := ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν1 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdeg_ge : m / 2 + |P.kappa.re| + 2 ≤ (weakDegree m P.kappa : ℝ) :=
    Nat.le_ceil (m / 2 + |P.kappa.re| + 2)
  have hst_pos : 0 < s - t := sub_pos.2 hts
  by_cases hgap : s - t ≤ 1
  · -- Short gap `s - t ≤ 1`: apply `hShort`.
    have h1 := hCS ν hνS tr htr t s ht hts hgap hcore f hf w u hw
    have hexp : -(weakDegree m P.kappa : ℝ) ≤ -((m + 2) / 2) := by
      have : (m + 2) / 2 ≤ m / 2 + |P.kappa.re| + 2 := by
        have := abs_nonneg P.kappa.re
        linarith
      linarith
    have hν_pow : ν ^ (-((m + 2) / 2)) ≤ ν ^ (-(weakDegree m P.kappa : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hν0 hν1 hexp
    have hCS_le : |CS| ≤ C := le_max_left _ _
    have hC0 : 0 ≤ C := (abs_nonneg CS).trans hCS_le
    have h_ineq : CS * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ) ≤
        C * ν ^ (-(weakDegree m P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      calc CS * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ)
          ≤ |CS| * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ) := by
            gcongr; exact le_abs_self CS
        _ ≤ C * ν ^ (-(weakDegree m P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
            gcongr
            linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h_ineq) zero_le)
  · -- Long gap `s - t > 1`: factor at `t' = t + 1/2`.
    push_neg at hgap
    let t' : ℝ := t + 1 / 2
    have htt' : t < t' := by dsimp [t']; linarith
    have ht's : t' < s := by dsimp [t']; linarith
    have ht'_sub : t' - t = 1 / 2 := by dsimp [t']; ring
    have ht'_gap : t' - t ≤ 1 := by linarith
    have ht0 : 0 ≤ t := ht.le
    have ht'0 : 0 ≤ t' := by linarith
    have hs0 : 0 ≤ s := by linarith
    have hb0 : 0 < b := by linarith
    have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
    have hm0 : 0 ≤ m := by linarith
    have hm1 : 1 < m := by linarith
    have hθs : b ≤ clockTheta ν s := theta_ge_of_le_coreEnd hν0 hb0 hs0 hcore
    have hAt : 1 ≤ clockA ν t := by unfold clockA; nlinarith
    have hAt' : 1 ≤ clockA ν t' := by unfold clockA; nlinarith
    have hAs : 1 ≤ clockA ν s := by unfold clockA; nlinarith
    have hAt_s : clockA ν t ≤ clockA ν s := by unfold clockA; nlinarith
    have hAt'_s : clockA ν t' ≤ clockA ν s := by unfold clockA; nlinarith
    have hθt' : b ≤ clockTheta ν t' := by
      refine hθs.trans ?_
      unfold clockTheta
      exact inv_anti₀ (mul_pos hν0 (by linarith)) (mul_le_mul_of_nonneg_left hAt'_s hν0.le)
    have hAs0 : 0 < clockA ν s := by linarith
    have hAt0 : 0 < clockA ν t := by linarith
    have hkey : b * (ν * clockA ν s) ≤ 1 := by
      have hpos : 0 < ν * clockA ν s := mul_pos hν0 hAs0
      have h := mul_le_mul_of_nonneg_right hθs hpos.le
      unfold clockTheta at h
      rwa [inv_mul_cancel₀ hpos.ne'] at h
    have hdS : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := div_pos hc (Real.sqrt_pos.2 hAs0)
    have hdT : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t) := div_pos hc (Real.sqrt_pos.2 hAt0)
    have hdcS : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) * Real.sqrt (clockA ν s) = ν ^ (-2 : ℝ) := by
      unfold cellLen; field_simp [(Real.sqrt_pos.2 hAs0).ne']
    have hdcT : cellLen (ν ^ (-2 : ℝ)) (clockA ν t) * Real.sqrt (clockA ν t) = ν ^ (-2 : ℝ) := by
      unfold cellLen; field_simp [(Real.sqrt_pos.2 hAt0).ne']
    have hw_mem_s : MemLp (w s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.memX s hts.le
    have hw_mem_t' : MemLp (w t') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.memX t' htt'.le
    have hz_t' : HasZeroCirculation (ν ^ (-2 : ℝ)) (w t') :=
      hZ ν (ν ^ (-2 : ℝ)) m hc hm1 tr t f w u hw hz t' htt'.le
    have hw_t' : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t' (w t') w u := hw.restart htt'.le
    -- Four norm steps: scaling at s, long forward t' -> s, moving smoothing t -> t', scaling at t
    have s1 := xNorm_scale_le hS hm0 hAs hdS hdcS hw_mem_s
    have s2_raw := (hCL ν hνL tr htr).2 t' s ht'0 ht's.le hθs (w t') hw_mem_t' hz_t' w u hw_t'
    have s3_raw := hCM ν hνM tr htr t t' ht0 htt' ht'_gap hθt' f hf hz w u hw
    have s4 := negNorm_scale_le hS hm0 hAt hdT hdcT hf
    have hθ_pos : 0 ≤ clockTheta ν t' / clockTheta ν s := by
      unfold clockTheta; positivity
    have hCL_le : CL * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
          (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re ≤
        |CL| * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
          (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re := by
      gcongr; exact le_abs_self CL
    have s2 := s2_raw.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCL_le) zero_le)
    have hZ_pos : 0 ≤ ν * (t' - t) / clockA ν t' := by
      rw [ht'_sub]; positivity
    have hCM_le : CM * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ) ≤
        |CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self CM) (Real.rpow_nonneg hZ_pos _)
    have s3 := s3_raw.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCM_le) zero_le)
    have s34 := s3.trans (mul_le_mul_of_nonneg_left s4 zero_le)
    have s234 := s2.trans (mul_le_mul_of_nonneg_left s34 zero_le)
    have s1234 := s1.trans (mul_le_mul_of_nonneg_left s234 zero_le)
    have step_ennreal := mul_le_mul_of_nonneg_left s1234
      (zero_le (a := ENNReal.ofReal (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s)))
    have hp0 : 0 ≤ gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s := by
      unfold gainG; positivity
    have hp1 : 0 ≤ clockA ν s ^ ((m - 3) / 2) := Real.rpow_nonneg hAs0.le _
    have hp2 : 0 ≤ |CL| * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
        (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re := by positivity
    have hp3 : 0 ≤ |CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ) :=
      mul_nonneg (abs_nonneg CM) (Real.rpow_nonneg hZ_pos _)
    rw [ennreal_chain5 _ _ _ _ _ hp0 hp1 hp2 hp3] at step_ennreal
    -- Bound the combined real prefactor
    have h_gain := gainG_mul_exp_theta_le P.eigenvalue.re ν hν0 ht0 htt'.le ht'_gap hs0
    have h_theta := theta_ratio_rpow_le P.kappa.re hν0 hb1 ht'0 ht's.le hθs
    have h_scale := long_scale_real (C := CM) hm0 hν0 hb1 hkey hAs hAt'_s hAt_s hAt' hAt ht'_sub
    have h_prod :
        (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
          clockA ν s ^ ((m - 3) / 2) *
          (|CL| * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
            (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re) *
          (|CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
          clockA ν t ^ (3 / 2 : ℝ) ≤
        C_long * (ν ^ (-|P.kappa.re|) * ν ^ (-((m + 2) / 2))) := by
      have e1 : (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
          clockA ν s ^ ((m - 3) / 2) *
          (|CL| * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
            (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re) *
          (|CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
          clockA ν t ^ (3 / 2 : ℝ) =
        ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
          Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s))) *
          |CL| *
          (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re *
          (clockA ν s ^ ((m - 3) / 2) * (|CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
            clockA ν t ^ (3 / 2 : ℝ)) := by ring
      have e2 : C_long * (ν ^ (-|P.kappa.re|) * ν ^ (-((m + 2) / 2))) =
          Real.exp |P.eigenvalue.re| * |CL| * ν ^ (-|P.kappa.re|) *
            (|CM| * b ^ (-((m + 1) / 2)) * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) *
              ν ^ (-((m + 2) / 2))) := by
        dsimp [C_long]; ring
      rw [e1, e2]
      have h_g0 : 0 ≤ (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
          Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) := by positivity
      have h_s0 : 0 ≤ clockA ν s ^ ((m - 3) / 2) *
          (|CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
          clockA ν t ^ (3 / 2 : ℝ) := by positivity
      gcongr
    have h_nu_comb : ν ^ (-|P.kappa.re|) * ν ^ (-((m + 2) / 2)) ≤
        ν ^ (-(weakDegree m P.kappa : ℝ)) := by
      rw [← Real.rpow_add hν0]
      have hexp : -(weakDegree m P.kappa : ℝ) ≤ -|P.kappa.re| + -((m + 2) / 2) := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 hexp
    have hC_long_nonneg : 0 ≤ C_long := by dsimp [C_long]; positivity
    have hC_long_le : C_long ≤ C := le_max_right _ _
    have hC0 : 0 ≤ C := hC_long_nonneg.trans hC_long_le
    have h_st_rpow : 0 ≤ (s - t) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hst_pos.le _
    have h_final_real :
        (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
          clockA ν s ^ ((m - 3) / 2) *
          (|CL| * Real.exp (P.eigenvalue.re * (clockTheta ν t' - clockTheta ν s)) *
            (clockTheta ν t' / clockTheta ν s) ^ P.kappa.re) *
          (|CM| * (ν * (t' - t) / clockA ν t') ^ (-1 / 2 : ℝ)) *
          clockA ν t ^ (3 / 2 : ℝ) ≤
        C * ν ^ (-(weakDegree m P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      calc _ ≤ C_long * (ν ^ (-|P.kappa.re|) * ν ^ (-((m + 2) / 2))) := h_prod
        _ ≤ C * ν ^ (-(weakDegree m P.kappa : ℝ)) * 1 := by
          rw [mul_one]
          exact mul_le_mul hC_long_le h_nu_comb (by positivity) hC0
        _ ≤ C * ν ^ (-(weakDegree m P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
          gcongr
          linarith
    exact step_ennreal.trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h_final_real) zero_le)

end UnforcedLeray.Short.IIIa
