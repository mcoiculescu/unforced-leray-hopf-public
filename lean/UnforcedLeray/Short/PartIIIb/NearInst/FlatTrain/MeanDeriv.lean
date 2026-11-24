import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# The transverse derivative of the mean stream (source 447-459, `sct:expansion`, last display)

The last conjunct of `PartI.TrainMeanExpansion` (with `b = 1`, `ℓ = 0`, `p = ∞`) bounds the
weighted sup norm of `∂_η S(s, ·)` by `P (1+s)^{(m-2)/2}`.  The pointwise bound follows from the
sup norm bound and the continuity of `η ↦ η^m ∂_η S(s, η)`, which is `-η^m \bar v₁(s, η)` by
`sct:mean` (`PartI.TrainMeanEquations`, 397-404).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- The horizontal mean of a continuous function of the plane is continuous in the transverse
variable (copy of `PartI.meanEnergy_hmean_continuous`). -/
theorem meanDeriv_hmean_continuous {c : ℝ} {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    Continuous (fun η : ℝ => UnforcedLeray.Short.PartI.hmean c F η) := by
  have hF' : Continuous (fun p : ℝ × ℝ => F (p.2, p.1)) :=
    hF.comp (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun η q : ℝ => F (q, η)) hF' (isCompact_Icc : IsCompact (Icc (-c / 2) (c / 2)))
  have heq : (fun η : ℝ => UnforcedLeray.Short.PartI.hmean c F η)
      = fun η : ℝ => c⁻¹ • ∫ y in Icc (-c / 2) (c / 2), F (y, η) := by
    funext η
    unfold UnforcedLeray.Short.PartI.hmean
    rw [integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h.const_smul c⁻¹

/-- **The transverse derivative of the mean stream** (source 447-459, last display of
`sct:expansion`, `b = 1`, `ℓ = 0`, `p = ∞`; source 2722-2724). -/
theorem meanStreamDerivBound_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : MeanStreamDerivBound := by
  intro m
  obtain ⟨C, M, ν₀, hC, hν₀, h⟩ := hM 2 (by norm_num) 0 m 1 0 ⊤ le_top
  refine ⟨|C| * 3 ^ M, 2 * M, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν c hc
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  subst hc
  intro tr hbuc s hs η
  have hcpos : 0 < (ν ^ 2)⁻¹ := by positivity
  have hh := h ν hν0 hνa
  rw [trainPeriod_two hν0] at hh
  have hL := (hh tr hbuc).2.2.2 s hs.le
  have hE2 := (hE ν (ν ^ 2)⁻¹ hν0 hcpos tr hbuc).2
  have hd : ∀ x : ℝ, deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) x =
      -UnforcedLeray.Short.PartI.hmean (ν ^ 2)⁻¹ (fun z => tr.v s z 0) x := by
    intro x
    rw [(hE2 s hs x).2.1, neg_neg]
  have hF0 : Continuous (fun z : ℝ × ℝ => tr.v s z 0) := by
    have hcont : Continuous (fun z : ℝ × ℝ => tr.v s z) := by
      have h' : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici (0 : ℝ) ×ˢ univ) :=
        tr.isTrain.smooth_v.continuousOn
      have hc' : Continuous (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) :=
        continuous_const.prodMk continuous_id
      exact h'.comp_continuous hc' (fun z => mk_mem_prod (mem_Ici.mpr hs.le) (mem_univ _))
    exact (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
      hcont
  have hcontf : Continuous (fun η : ℝ => η ^ m * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η) := by
    have hfun : (fun η : ℝ => η ^ m * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η)
        = fun η : ℝ => η ^ m * -UnforcedLeray.Short.PartI.hmean (ν ^ 2)⁻¹ (fun z => tr.v s z 0) η :=
      funext fun η => by rw [hd η]
    rw [hfun]
    exact (continuous_pow m).mul (meanDeriv_hmean_continuous hF0).neg
  have hL2 : eLpNorm (fun η : ℝ => η ^ m * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η)
      ⊤ volume ≤ ENNReal.ofReal (UnforcedLeray.Short.PartI.polyP C M ν (ν ^ 2)⁻¹ *
        (1 + s) ^ (((m : ℝ) - 2) / 2)) := by
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at hL
    convert hL using 4
    · norm_num
      ring
  have hP0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν (ν ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.PartI.polyP
    have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν0.le
    have h2 : 0 ≤ (ν ^ 2)⁻¹ := by positivity
    have h3 : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by linarith
    exact mul_nonneg hC.le (pow_nonneg h3 M)
  have hK0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν (ν ^ 2)⁻¹ *
      (1 + s) ^ (((m : ℝ) - 2) / 2) :=
    mul_nonneg hP0 (Real.rpow_nonneg (by linarith) _)
  have key := abs_le_of_eLpNorm_top_le hcontf hK0 hL2 η
  have hPC : UnforcedLeray.Short.PartI.polyP C M ν (ν ^ 2)⁻¹ ≤ |C| * 3 ^ M * ν⁻¹ ^ (2 * M) :=
    polyP_le_of_sq_inv C M hν0 hν1
  calc |η| ^ m * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
      = |η ^ m * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| := by
        rw [abs_mul, abs_pow]
    _ ≤ UnforcedLeray.Short.PartI.polyP C M ν (ν ^ 2)⁻¹ * (1 + s) ^ (((m : ℝ) - 2) / 2) := key
    _ ≤ (|C| * 3 ^ M * ν⁻¹ ^ (2 * M)) * (1 + s) ^ (((m : ℝ) - 2) / 2) :=
        mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg (by linarith) _)

end UnforcedLeray.Short.PartIIIb.NearInst
