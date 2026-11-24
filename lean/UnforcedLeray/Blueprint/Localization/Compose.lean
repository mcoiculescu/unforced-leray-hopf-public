import UnforcedLeray.Blueprint.Localization.Realization
import UnforcedLeray.Blueprint.Top
import UnforcedLeray.Analysis.PeriodicMode
import UnforcedLeray.Analysis.QuadraticContraction

/-!
# Composition of the localization steps

The fourteen step propositions L1–L14 (`Linear.lean`, `Nonlinear.lean`, `Realization.lean`)
imply `LocalizationClaim` (`paper/main.tex` lines 232–260, proof 262–592; blueprint B1035,
restated at the strength of `ViscosityMainClaim` as critic §4 asks). The following pieces of
the manuscript's argument are proved here, not assumed:

* `phase_minimum`: `loc:eq:phase-minimum` (lines 325–329, B1012), from the continuous
  periodic nowhere-zero mode of L4, by the compiled `PeriodicMode`;
* `exists_terminal_time`, `contraction_criterion`: the choice of `τ₀` and the radius
  `ρ = 2C₀(e^{(1/2-β)τ₀} + e^{(2σ-β)τ₀})` (lines 515–524, B1024), and from the same `τ₀` the
  relative error `2ρe^{(β-σ)τ₀} < m_*/2` (lines 581–587);
* the two fixed points, unique in the ball, by the compiled
  `QuadraticContraction.existsUnique_fixedPoint` (the criterion of
  `albritton-brue-colombo2021`, line 514);
* `fixedPoint_invariant`: invariance of the corrections by uniqueness (line 572, B1025);
* `separation_of_remainders`: `loc:eq:separation` with `c = m_*/2` (lines 576–588, B1027);
* the assembly of `ViscosityMainClaim`.

The integrated bound of lines 589–592 is derived in the compiled `MainReduction`.
(The contraction and separation algebra is adapted from `SkeletonDesignC/LocalizationCompose.lean`
and `SkeletonDesignB/LocalizationAssembly.lean`.)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint

open SobolevGraph ViscosityTransport

/-! ## The phase minimum (B1012) -/

/-- `loc:eq:phase-minimum`: `m_* = min_τ ‖b_*(τ)‖₂ > 0`. -/
theorem phase_minimum {D : BackgroundData} (hD : IsUnstableBackground D) {ev : Evolution}
    {bhat : ℝ → Z} (hb : IsRegularMode D ev bhat) :
    ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ ‖Zclass (bhat τ)‖ := by
  let f : ℝ → L2Space := fun τ => Zclass (bhat τ)
  have hcont : Continuous f := (H2.valueCLM.comp Zincl).continuous.comp hb.continuous
  have hper : Function.Periodic f D.period := fun τ => by
    simp only [f, hb.periodic τ]
  exact PeriodicMode.exists_pos_norm_lower_bound hper hD.1.period_pos.ne' hcont
    hb.no_zero_phase

/-! ## The terminal time and the contraction criterion (B1024) -/

theorem tendsto_exp_mul_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (fun τ : ℝ => Real.exp (a * τ)) atBot (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atBot ha)

/-- The contraction radius `ρ = 2C₀(e^{(1/2-β)τ₀} + e^{(2σ-β)τ₀})` of line 519. -/
def contractionRadius (C₀ σ β τ₀ : ℝ) : ℝ :=
  2 * C₀ * (Real.exp ((1 / 2 - β) * τ₀) + Real.exp ((2 * σ - β) * τ₀))

theorem contractionRadius_pos {C₀ σ β τ₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < contractionRadius C₀ σ β τ₀ := by
  unfold contractionRadius
  have := Real.exp_pos ((1 / 2 - β) * τ₀)
  have := Real.exp_pos ((2 * σ - β) * τ₀)
  positivity

/-- For sufficiently negative `τ₀`: the contraction margin and the separation margin. -/
theorem exists_terminal_time {C₀ C σ β m : ℝ} (hσ : 0 < σ) (hσβ : σ < β) (hβ : β < 2 * σ)
    (hσ4 : σ < 1 / 4) (hm : 0 < m) :
    ∃ τ₀ : ℝ, τ₀ ≤ 0 ∧
      2 * contractionRadius C₀ σ β τ₀ * (C * Real.exp (β * τ₀)) +
        C * (Real.exp ((1 / 2) * τ₀) + Real.exp (σ * τ₀)) < 1 / 2 ∧
      2 * contractionRadius C₀ σ β τ₀ * Real.exp ((β - σ) * τ₀) < m / 2 := by
  have h1 : 0 < 1 / 2 - β := by linarith
  have h2 : 0 < 2 * σ - β := by linarith
  have h3 : 0 < β := by linarith
  have h4 : (0 : ℝ) < 1 / 2 := by norm_num
  have h5 : 0 < β - σ := by linarith
  have hR : Tendsto (fun τ => contractionRadius C₀ σ β τ) atBot (𝓝 0) := by
    have := ((tendsto_exp_mul_atBot h1).add (tendsto_exp_mul_atBot h2)).const_mul (2 * C₀)
    simpa [contractionRadius] using this
  have hA : Tendsto (fun τ => 2 * contractionRadius C₀ σ β τ * (C * Real.exp (β * τ)) +
      C * (Real.exp ((1 / 2) * τ) + Real.exp (σ * τ))) atBot (𝓝 0) := by
    have := ((hR.const_mul 2).mul ((tendsto_exp_mul_atBot h3).const_mul C)).add
      (((tendsto_exp_mul_atBot h4).add (tendsto_exp_mul_atBot hσ)).const_mul C)
    simpa using this
  have hB : Tendsto (fun τ => 2 * contractionRadius C₀ σ β τ * Real.exp ((β - σ) * τ))
      atBot (𝓝 0) := by
    have := (hR.const_mul 2).mul (tendsto_exp_mul_atBot h5)
    simpa using this
  obtain ⟨τ₀, hτ, hA', hB'⟩ := ((eventually_le_atBot (0 : ℝ)).and
    ((hA.eventually (gt_mem_nhds h4)).and (hB.eventually (gt_mem_nhds (half_pos hm))))).exists
  exact ⟨τ₀, hτ, hA', hB'⟩

/-- The affine, linear and bilinear bounds give the quadratic criterion
`2ρ‖B‖ + ‖L‖ + ‖G‖/ρ < 1` (line 514) on the ball of radius `ρ`. -/
theorem contraction_criterion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Bq : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E) (G : E) {C₀ C σ β τ₀ : ℝ} (hC₀ : 0 < C₀)
    (hG : ‖G‖ ≤ C₀ * (Real.exp ((1 / 2 - β) * τ₀) + Real.exp ((2 * σ - β) * τ₀)))
    (hL : ‖L‖ ≤ C * (Real.exp ((1 / 2) * τ₀) + Real.exp (σ * τ₀)))
    (hB : ‖Bq‖ ≤ C * Real.exp (β * τ₀))
    (hsmall : 2 * contractionRadius C₀ σ β τ₀ * (C * Real.exp (β * τ₀)) +
        C * (Real.exp ((1 / 2) * τ₀) + Real.exp (σ * τ₀)) < 1 / 2) :
    2 * contractionRadius C₀ σ β τ₀ * ‖Bq‖ + ‖L‖ + ‖G‖ / contractionRadius C₀ σ β τ₀ < 1 := by
  have hρ := contractionRadius_pos (σ := σ) (β := β) (τ₀ := τ₀) hC₀
  have hGρ : ‖G‖ / contractionRadius C₀ σ β τ₀ ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    unfold contractionRadius
    linarith
  have hBρ : 2 * contractionRadius C₀ σ β τ₀ * ‖Bq‖ ≤
      2 * contractionRadius C₀ σ β τ₀ * (C * Real.exp (β * τ₀)) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  linarith

/-! ## Invariance by uniqueness (B1025, line 572) -/

/-- An isometry preserving the quadratic map fixes its unique fixed point in the ball. -/
theorem fixedPoint_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Bq : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E) (G : E) {ρ : ℝ} {w : E}
    (hw : ‖w‖ ≤ ρ ∧ w = Bq w w + L w + G)
    (huniq : ∀ z, ‖z‖ ≤ ρ ∧ z = Bq z z + L z + G → z = w)
    (A : E →L[ℝ] E) (hA : ∀ v, ‖A v‖ = ‖v‖) (hB : ∀ v₁ v₂, Bq (A v₁) (A v₂) = A (Bq v₁ v₂))
    (hL : ∀ v, L (A v) = A (L v)) (hG : A G = G) : A w = w := by
  apply huniq
  refine ⟨by rw [hA]; exact hw.1, ?_⟩
  rw [hB, hL]
  conv_lhs => rw [hw.2]
  rw [map_add, map_add, hG]

/-! ## Separation (B1027, lines 576–588) -/

@[simp] theorem jcoef_zero : jcoef 0 = 0 := by simp [jcoef]
@[simp] theorem jcoef_one : jcoef 1 = 1 := by simp [jcoef]

/-- The `L²` norm of a difference of representatives is the `L²` distance. -/
theorem l2Norm_coe_sub (F G : L2Space) :
    l2Norm ((F : SpatialField) - (G : SpatialField)) = dist F G := by
  rw [dist_eq_norm, Lp.norm_def]
  unfold l2Norm
  congr 1
  exact eLpNorm_congr_ae (Lp.coeFn_sub F G).symm

/-- The similarity scaling multiplies `L²` distances by `t^{1/4}` (line 538). -/
theorem dist_physicalDilation {t : ℝ} (ht : 0 < t) (F G : L2Space) :
    dist (physicalDilation t F) (physicalDilation t G) = t ^ (1 / 4 : ℝ) * dist F G := by
  unfold physicalDilation
  rw [dist_dilationL2 _ (Real.rpow_pos_of_pos ht _)]
  congr 1
  rw [abs_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  norm_num

/-- The common heat remainder cancels in the difference of the two profiles. -/
theorem remainderClass_one_sub_zero (D : BackgroundData) (bhat : ℝ → Z) (β : ℝ) {τ₀ : ℝ}
    (w₀ w₁ : WeightedZ τ₀) (τ : ℝ) :
    remainderClass D bhat β w₁ (jcoef 1) τ - remainderClass D bhat β w₀ (jcoef 0) τ =
      Real.exp (D.σ * τ) • Zclass (bhat τ) +
        (Zclass (unweight β w₁ τ) - Zclass (unweight β w₀ τ)) := by
  simp only [remainderClass, jcoef_one, jcoef_zero, one_mul, zero_mul, zero_smul, add_zero]
  abel

/-- Lines 576–587: `‖e^{στ}b + (e₁ - e₀)‖₂ ≥ m_*e^{στ} - 2ρe^{βτ} ≥ (m_*/2)e^{στ}` for
`τ ≤ τ₀`. -/
theorem profile_lower_bound {σ β m ρ τ τ₀ : ℝ} {b e₀ e₁ : L2Space}
    (hσβ : σ < β) (hτ : τ ≤ τ₀) (hmode : m ≤ ‖b‖)
    (h₀ : ‖e₀‖ ≤ Real.exp (β * τ) * ρ) (h₁ : ‖e₁‖ ≤ Real.exp (β * τ) * ρ)
    (hρ : 0 ≤ ρ) (hsmall : 2 * ρ * Real.exp ((β - σ) * τ₀) < m / 2) :
    m / 2 * Real.exp (σ * τ) ≤ ‖Real.exp (σ * τ) • b + (e₁ - e₀)‖ := by
  have hpos := Real.exp_pos (σ * τ)
  have hsplit : Real.exp (β * τ) = Real.exp ((β - σ) * τ) * Real.exp (σ * τ) := by
    rw [← Real.exp_add]
    ring_nf
  have hmono : Real.exp ((β - σ) * τ) ≤ Real.exp ((β - σ) * τ₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ (by linarith))
  have hlead : ‖Real.exp (σ * τ) • b‖ = Real.exp (σ * τ) * ‖b‖ := by
    rw [norm_smul, Real.norm_of_nonneg hpos.le]
  have htri : ‖Real.exp (σ * τ) • b‖ ≤
      ‖Real.exp (σ * τ) • b + (e₁ - e₀)‖ + ‖e₁‖ + ‖e₀‖ := by
    have e : Real.exp (σ * τ) • b = (Real.exp (σ * τ) • b + (e₁ - e₀)) - e₁ + e₀ := by abel
    calc ‖Real.exp (σ * τ) • b‖ = ‖(Real.exp (σ * τ) • b + (e₁ - e₀)) - e₁ + e₀‖ := by
          rw [← e]
      _ ≤ ‖(Real.exp (σ * τ) • b + (e₁ - e₀)) - e₁‖ + ‖e₀‖ := norm_add_le _ _
      _ ≤ ‖Real.exp (σ * τ) • b + (e₁ - e₀)‖ + ‖e₁‖ + ‖e₀‖ := by
          linarith [norm_sub_le (Real.exp (σ * τ) • b + (e₁ - e₀)) e₁]
  have hm2 : m * Real.exp (σ * τ) ≤ Real.exp (σ * τ) * ‖b‖ := by
    rw [mul_comm m]
    exact mul_le_mul_of_nonneg_left hmode hpos.le
  have herr : 2 * (Real.exp (β * τ) * ρ) ≤ m / 2 * Real.exp (σ * τ) := by
    rw [hsplit]
    have k1 : Real.exp ((β - σ) * τ) * ρ ≤ Real.exp ((β - σ) * τ₀) * ρ :=
      mul_le_mul_of_nonneg_right hmono hρ
    have k2 : 2 * (Real.exp ((β - σ) * τ₀) * ρ) ≤ m / 2 := by linarith
    calc 2 * (Real.exp ((β - σ) * τ) * Real.exp (σ * τ) * ρ)
        = 2 * (Real.exp ((β - σ) * τ) * ρ) * Real.exp (σ * τ) := by ring
      _ ≤ 2 * (Real.exp ((β - σ) * τ₀) * ρ) * Real.exp (σ * τ) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ ≤ m / 2 * Real.exp (σ * τ) := mul_le_mul_of_nonneg_right k2 hpos.le
  linarith

/-- `loc:eq:separation` (line 588) for two velocity fields that agree a.e. with the total
fields of the two remainders, with `c = m_*/2`. -/
theorem separation_of_remainders {D : BackgroundData} {bhat : ℝ → Z} {β m ρ τ₀ h : ℝ}
    {w : Fin 2 → WeightedZ τ₀} {u₀ : SpatialField} {ρs : Fin 2 → ℝ → H2}
    {v : Fin 2 → Velocity}
    (hσβ : D.σ < β) (hw : ∀ j, ‖w j‖ ≤ ρ) (hmode : ∀ τ, m ≤ ‖Zclass (bhat τ)‖)
    (hsmall : 2 * ρ * Real.exp ((β - D.σ) * τ₀) < m / 2)
    (hrep : ∀ j, ∀ t ∈ Ioc (0 : ℝ) (Real.exp τ₀), (ρs j t).value =
      physicalDilation t (remainderClass D bhat β (w j) (jcoef j) (Real.log t)))
    (hag : ∀ j, ∀ t ∈ Icc (0 : ℝ) (Real.exp τ₀),
      v j t =ᵐ[volume] physicalVelocity h u₀ (ρs j) t) :
    ∀ t ∈ Ioc (0 : ℝ) (Real.exp τ₀),
      (m / 2) * Real.rpow t (D.σ + 1 / 4) ≤ l2Norm (v 1 t - v 0 t) := by
  intro t ht
  have htpos : 0 < t := ht.1
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans (hw 0)
  have hτ : Real.log t ≤ τ₀ := by
    have hl := Real.log_le_log htpos ht.2
    rwa [Real.log_exp] at hl
  have hdiff : v 1 t - v 0 t =ᵐ[volume]
      ((ρs 1 t).value : SpatialField) - ((ρs 0 t).value : SpatialField) := by
    filter_upwards [hag 1 t (Ioc_subset_Icc_self ht), hag 0 t (Ioc_subset_Icc_self ht)]
      with x hx₁ hx₀
    simp only [Pi.sub_apply, hx₁, hx₀, physicalVelocity, htpos, ↓reduceIte, Pi.add_apply]
    abel
  have hnorm : l2Norm (v 1 t - v 0 t) = dist (ρs 1 t).value (ρs 0 t).value := by
    rw [← l2Norm_coe_sub]
    unfold l2Norm
    rw [eLpNorm_congr_ae hdiff]
  rw [hnorm, hrep 1 t ht, hrep 0 t ht, dist_physicalDilation htpos, dist_eq_norm,
    remainderClass_one_sub_zero]
  have hj : ∀ j, ‖Zclass (unweight β (w j) (Real.log t))‖ ≤
      Real.exp (β * Real.log t) * ρ := fun j =>
    (norm_Zclass_le _).trans ((norm_unweight_le β (w j) hτ).trans
      (mul_le_mul_of_nonneg_left (hw j) (Real.exp_pos _).le))
  have hlow := profile_lower_bound hσβ hτ (hmode (Real.log t)) (hj 0) (hj 1) hρ hsmall
  have hpow : Real.exp (D.σ * Real.log t) = t ^ D.σ := by
    rw [Real.rpow_def_of_pos htpos]
    ring_nf
  have hpowadd : Real.rpow t (D.σ + 1 / 4) = t ^ (1 / 4 : ℝ) * t ^ D.σ := by
    rw [Real.rpow_eq_pow, Real.rpow_add htpos]
    ring
  rw [hpowadd, ← hpow]
  have h14 : 0 ≤ t ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos htpos _).le
  calc m / 2 * (t ^ (1 / 4 : ℝ) * Real.exp (D.σ * Real.log t)) =
        t ^ (1 / 4 : ℝ) * (m / 2 * Real.exp (D.σ * Real.log t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow h14

/-! ## The conclusion of `thm:localization` for one package -/

/-- `thm:localization` (lines 232–260) for the package `D`, with `h = D.h` and `σ = D.σ`, at
the strength of the Lean solution class. -/
def LocalizationConclusion (D : BackgroundData) : Prop :=
  ∃ (T : ℝ) (u₀ : SpatialField) (u₁ u₂ : Velocity) (p₁ p₂ : Pressure)
      (G₁ G₂ : FirstDerivatives) (H₁ H₂ : SecondDerivatives) (c : ℝ),
    0 < T ∧ IsInitialDatum u₀ ∧
    IsTheoremASolutionViscosity D.h T u₀ u₁ p₁ G₁ H₁ ∧
    IsTheoremASolutionViscosity D.h T u₀ u₂ p₂ G₂ H₂ ∧
    0 < c ∧
    (∀ t ∈ Ioc (0 : ℝ) T, c * Real.rpow t (D.σ + 1 / 4) ≤ l2Norm (u₂ t - u₁ t)) ∧
    IsAxisymmetricNoSwirl u₀ ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₁ t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₂ t))

theorem viscosityMainClaim_of_conclusion {D : BackgroundData} (hD : IsUnstableBackground D)
    (h : LocalizationConclusion D) : ViscosityMainClaim := by
  obtain ⟨T, u₀, u₁, u₂, p₁, p₂, G₁, G₂, H₁, H₂, c, hT, hd, s₁, s₂, hc, hsep, h0, h1, h2⟩ := h
  exact ⟨D.h, T, u₀, u₁, u₂, p₁, p₂, G₁, G₂, H₁, H₂, c, D.σ, hD.1.h_pos, hT, hd, s₁, s₂, hc,
    hD.2.σ_pos, hD.2.σ_lt, hsep, h0, h1, h2⟩

/-- The localization theorem from its fourteen steps, for one package. -/
theorem localizationConclusion_of_steps (h1 : CoefficientStep) (h2 : FreeEvolutionStep)
    (h3 : EvolutionStep) (h4 : ModeRegularityStep) (h5 : EssentialRadiusStep)
    (h6 : SpectralSplittingStep) (h7 : ProjectionStep) (h8 : GreenStep)
    (h9 : CompactDatumStep) (h10 : NonlinearStep) (h11 : AffineBoundStep)
    (h12 : EquivarianceStep) (h13 : PhysicalRemainderStep) (h14 : RealizationStep)
    (D : BackgroundData) (hD : IsUnstableBackground D) : LocalizationConclusion D := by
  obtain ⟨ld, hld⟩ := linearData_of_steps h1 h2 h3 h4 h5 h6 h7 h8 D hD
  obtain ⟨χ, _hχ, hu₀⟩ := h9 D hD
  obtain ⟨nm, hnm⟩ := h10 D hD _ hu₀
  obtain ⟨C₀, C, hC₀, _hC, hmaps⟩ := h11 D hD ld hld _ hu₀ nm hnm
  obtain ⟨m, hm, hmin⟩ := phase_minimum hD hld.mode
  obtain ⟨τ₀, hτ₀, hA, hB⟩ := exists_terminal_time (C₀ := C₀) (C := C) hD.2.σ_pos
    hld.splitting.weight_lower hld.splitting.weight_upper hD.2.σ_lt hm
  obtain ⟨cm, hcm, hG, hL, hBq⟩ := hmaps τ₀ hτ₀
  -- the two fixed points (lines 515–524)
  have hfix : ∀ j : Fin 2, ∃! z : WeightedZ τ₀,
      ‖z‖ ≤ contractionRadius C₀ D.σ ld.sp.β τ₀ ∧ z = cm.Bq z z + cm.L j z + cm.G j :=
    fun j => QuadraticContraction.existsUnique_fixedPoint cm.Bq (cm.L j) (cm.G j)
      (contractionRadius_pos hC₀) (contraction_criterion cm.Bq (cm.L j) (cm.G j) hC₀
        (hG j) (hL j) hBq hA)
  choose w hw huniq using hfix
  -- invariance by uniqueness (line 572)
  have hequiv := h12 D hD ld hld _ hu₀ nm hnm τ₀ hτ₀ cm hcm
  have hwsym : ∀ j (τ : Iic τ₀), IsAxisymmetricNoSwirl (Zval (w j τ)) := by
    intro j τ g hg
    obtain ⟨A, hAiso, hAB, hAL, hAG, hArep⟩ := hequiv g hg
    have hAw : A (w j) = w j := fixedPoint_invariant cm.Bq (cm.L j) (cm.G j) (hw j)
      (huniq j) A hAiso hAB (hAL j) (hAG j)
    have h := hArep (w j) τ
    rw [hAw] at h
    exact h.symm
  -- physical remainders and realization (lines 525–561)
  obtain ⟨pr, hpr⟩ := h13 D hD ld hld _ hu₀ nm hnm τ₀ hτ₀ cm hcm w (fun j => (hw j).2) hwsym
  have hT : 0 < Real.exp τ₀ := Real.exp_pos τ₀
  have hreal := fun j : Fin 2 => h14 D.h (Real.exp τ₀) _ (pr.ρ j) (pr.N j) pr.C hD.1.h_pos hT
    hu₀.datum hu₀.symmetric (hpr j).2
  choose u p G H hag hsol hsym using hreal
  -- separation (lines 576–588)
  have hsep := separation_of_remainders (v := u) hld.splitting.weight_lower (fun j => (hw j).1)
    hmin hB (fun j => (hpr j).1) hag
  exact ⟨Real.exp τ₀, _, u 0, u 1, p 0, p 1, G 0, G 1, H 0, H 1, m / 2, hT, hu₀.datum,
    hsol 0, hsol 1, half_pos hm, hsep, hu₀.symmetric, hsym 0, hsym 1⟩

/-- `thm:localization` from its fourteen steps. -/
theorem localizationClaim_of_steps (h1 : CoefficientStep) (h2 : FreeEvolutionStep)
    (h3 : EvolutionStep) (h4 : ModeRegularityStep) (h5 : EssentialRadiusStep)
    (h6 : SpectralSplittingStep) (h7 : ProjectionStep) (h8 : GreenStep)
    (h9 : CompactDatumStep) (h10 : NonlinearStep) (h11 : AffineBoundStep)
    (h12 : EquivarianceStep) (h13 : PhysicalRemainderStep) (h14 : RealizationStep) :
    LocalizationClaim := fun D hD =>
  viscosityMainClaim_of_conclusion hD
    (localizationConclusion_of_steps h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 D hD)

end UnforcedLeray.Blueprint
