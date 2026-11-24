import UnforcedLeray.Loc.Hyp.ModeIdentification.ModeEq

/-!
# H-ModeId helpers: the time derivative of the mode in the dilated frame (B1009)

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 308–312, blueprint unit B1009: "set `g(x,τ) = b_*(e^{-τ/2}x,τ)` … the
original graph gives `∂_τ g = (𝒯₀b_*)(e^{-τ/2}x,τ) ∈ L²L²`, so `g`, and hence `b_*`, has a
continuous `L²` representative").

The frame is `P_b(τ) = D(-τ)b_*(τ) = e^{-τ/2} b_*(e^{-τ/2}·, τ)`, the manuscript's `g` up to the
factor `e^{-τ/2}`. Testing `driftPairing` (`𝒯₀ b_* = driftB`) with the dilated tests
`Ψ(τ,y) = η(τ)φ(e^{τ/2}y)`, `η = χ e^τ`, the drift `½y·∇` cancels and Fubini gives the weak
time derivative

  `∂_τ P_b = D(-τ)(driftB(τ) - ½ b_*(τ))`   on every bounded interval (`mode_hasWeakDerivTime`).

With `BochnerTime.HasWeakDerivTime.exists_rep` this is the continuous `L²` representative of
B1009.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.BochnerTime
open UnforcedLeray.Loc.L02 (dil norm_dil_apply_le)

/-! ## Joint continuity of the dilation and integrability of dilated paths -/

theorem continuous_dil_joint : Continuous (fun p : ℝ × L2Space => dil p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, F₀⟩
  have h1 : Tendsto (fun p : ℝ × L2Space => dil p.1 F₀) (𝓝 (s₀, F₀)) (𝓝 (dil s₀ F₀)) :=
    ((continuous_dil_apply F₀).comp continuous_fst).tendsto _
  have hexp : Continuous (fun p : ℝ × L2Space => Real.exp (-(p.1 / 4))) := by fun_prop
  have hbd : ∀ᶠ p in 𝓝 (s₀, F₀), Real.exp (-(p.1 / 4)) < Real.exp (-(s₀ / 4)) + 1 :=
    (hexp.tendsto (s₀, F₀)).eventually (gt_mem_nhds (lt_add_one _))
  have hg0 : Tendsto (fun p : ℝ × L2Space => ‖p.2 - F₀‖) (𝓝 (s₀, F₀)) (𝓝 0) := by
    have hc : Continuous (fun p : ℝ × L2Space => ‖p.2 - F₀‖) :=
      (continuous_snd.sub continuous_const).norm
    simpa using hc.tendsto (s₀, F₀)
  have h2 : Tendsto (fun p : ℝ × L2Space => dil p.1 (p.2 - F₀)) (𝓝 (s₀, F₀)) (𝓝 0) := by
    have hlim : Tendsto (fun p : ℝ × L2Space => (Real.exp (-(s₀ / 4)) + 1) * ‖p.2 - F₀‖)
        (𝓝 (s₀, F₀)) (𝓝 0) := by
      simpa using hg0.const_mul (Real.exp (-(s₀ / 4)) + 1)
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbd] with p hp
    calc ‖dil p.1 (p.2 - F₀)‖ ≤ Real.exp (-(p.1 / 4)) * ‖p.2 - F₀‖ := norm_dil_apply_le _ _
      _ ≤ (Real.exp (-(s₀ / 4)) + 1) * ‖p.2 - F₀‖ := by gcongr
  have := h2.add h1
  simp only [zero_add] at this
  refine this.congr (fun p => ?_)
  rw [← map_add, sub_add_cancel]

/-- `τ ↦ D(-τ)g(τ)` is integrable on `(lo,hi)` when `g` is. -/
theorem integrableOn_dil_path {g : ℝ → L2Space} {lo hi : ℝ} (hg : IntegrableOn g (Ioo lo hi)) :
    IntegrableOn (fun τ => dil (-τ) (g τ)) (Ioo lo hi) := by
  have hm0 : AEStronglyMeasurable (fun τ : ℝ => ((-τ : ℝ), g τ)) (volume.restrict (Ioo lo hi)) :=
    continuous_neg.aestronglyMeasurable.prodMk hg.aestronglyMeasurable
  have hm1 := continuous_dil_joint.comp_aestronglyMeasurable hm0
  have hm : AEStronglyMeasurable (fun τ => dil (-τ) (g τ)) (volume.restrict (Ioo lo hi)) := hm1
  refine Integrable.mono' (hg.norm.const_mul (Real.exp (hi / 4))) hm ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall (fun τ hτ => ?_)
  calc ‖dil (-τ) (g τ)‖ ≤ Real.exp (-(-τ / 4)) * ‖g τ‖ := norm_dil_apply_le _ _
    _ ≤ Real.exp (hi / 4) * ‖g τ‖ := by
        gcongr
        linarith [hτ.2]

/-! ## Dilated tests `Ψ(τ,y) = η(τ) φ(e^{τ/2} y)` -/

/-- The dilated test `Ψ(τ,y) = η(τ) φ(e^{τ/2} y)`. -/
def dilTest (η : ℝ → ℝ) (φ : Space → Space) : SpaceTime → Space :=
  fun z => η z.1 • φ (Real.exp (z.1 / 2) • z.2)

variable {η : ℝ → ℝ} {φ : Space → Space}

theorem isSimilarityTest_dilTest (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hφ : IsVectorTest φ) : IsSimilarityTest (dilTest η φ) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun z : SpaceTime => Real.exp (z.1 / 2) • z.2) :=
      (Real.contDiff_exp.comp (contDiff_fst.div_const 2)).smul contDiff_snd
    exact (hη.comp contDiff_fst).smul (hφ.smooth.comp h1)
  · have hK : IsCompact ((fun p : ℝ × Space => (p.1, Real.exp (-(p.1 / 2)) • p.2)) ''
        (tsupport η ×ˢ tsupport φ)) :=
      (hηc.prod hφ.compact).image (by fun_prop)
    apply HasCompactSupport.intro hK
    intro z hz
    by_contra hne
    apply hz
    refine ⟨(z.1, Real.exp (z.1 / 2) • z.2), ⟨?_, ?_⟩, ?_⟩
    · apply subset_tsupport
      intro h0
      apply hne
      simp [dilTest, h0]
    · apply subset_tsupport
      intro h0
      apply hne
      simp [dilTest, h0]
    · simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

theorem timeDerivative_dilTest (hη : ContDiff ℝ ∞ η) (hφ : IsVectorTest φ) (t : ℝ) (y : Space) :
    timeDerivative (dilTest η φ) t y = η t • ((Real.exp (t / 2) * (1 / 2)) •
      fderiv ℝ φ (Real.exp (t / 2) • y) y) + deriv η t • φ (Real.exp (t / 2) • y) := by
  have hg : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • y) ((Real.exp (t / 2) * (1 / 2)) • y) t :=
    (((hasDerivAt_id t).div_const 2).exp).smul_const y
  have hφd : HasDerivAt (fun s : ℝ => φ (Real.exp (s / 2) • y))
      (fderiv ℝ φ (Real.exp (t / 2) • y) ((Real.exp (t / 2) * (1 / 2)) • y)) t :=
    ((hφ.smooth.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t hg
  have hηd : HasDerivAt η (deriv η t) t := (hη.differentiable (by simp) t).hasDerivAt
  have hd := hηd.smul hφd
  show deriv (fun s => η s • φ (Real.exp (s / 2) • y)) t = _
  rw [show (fun s => η s • φ (Real.exp (s / 2) • y)) = η • (fun s => φ (Real.exp (s / 2) • y))
    from rfl, hd.deriv, map_smul]

theorem spatialDerivative_dilTest (hφ : IsVectorTest φ) (t : ℝ) (y v : Space) :
    spatialDerivative (dilTest η φ) t y v =
      η t • (Real.exp (t / 2) • fderiv ℝ φ (Real.exp (t / 2) • y) v) := by
  unfold spatialDerivative dilTest
  have hdiff : Differentiable ℝ (fun y' : Space => Real.exp (t / 2) • y') :=
    differentiable_id.const_smul (Real.exp (t / 2))
  have hd : Differentiable ℝ (fun y' : Space => φ (Real.exp (t / 2) • y')) :=
    (hφ.smooth.differentiable (by simp)).comp hdiff
  rw [fderiv_fun_const_smul (hd y) (η t), smul_apply,
    L13.fderiv_comp_smul (hφ.smooth.differentiable (by simp))]

/-- The drift adjoint against a dilated test: the `½ y·∇` terms cancel. -/
theorem driftAdjointTerm_dilTest (hη : ContDiff ℝ ∞ η) (hφ : IsVectorTest φ)
    (b : ℝ → SpatialField) (z : SpaceTime) :
    driftAdjointTerm b (dilTest η φ) z =
      (-deriv η z.1 + 3 / 2 * η z.1) * inner ℝ (b z.1 z.2) (φ (Real.exp (z.1 / 2) • z.2)) := by
  simp only [driftAdjointTerm, temporalTerm, pairTerm, dilationTerm,
    timeDerivative_dilTest hη hφ, spatialDerivative_dilTest hφ, dilTest, inner_add_right,
    inner_smul_right]
  ring

theorem pairTerm_dilTest (f : ℝ → SpatialField) (z : SpaceTime) :
    pairTerm f (dilTest η φ) z = η z.1 * inner ℝ (f z.1 z.2) (φ (Real.exp (z.1 / 2) • z.2)) := by
  simp only [pairTerm, dilTest, inner_smul_right]

/-- **Fubini with a phase-dependent test.** -/
theorem integral_pair_dep {f : ℝ → SpatialField} {k : ℝ → SpatialField}
    (hk : ∀ τ, MemLp (k τ) 2 volume) (hae : ∀ᵐ τ, MemLp (f τ) 2 volume) {c : ℝ → ℝ}
    (hint : Integrable (fun z : SpaceTime => c z.1 * inner ℝ (f z.1 z.2) (k z.1 z.2))) :
    ∫ z : SpaceTime, c z.1 * inner ℝ (f z.1 z.2) (k z.1 z.2) =
      ∫ τ, c τ * inner ℝ (toL2 (f τ)) (toL2 (k τ)) := by
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hae] with τ hτ
  rw [integral_const_mul, inner_toL2_toL2 hτ (hk τ)]

/-! ## The weak time derivative of the mode in the frame -/

variable {D : BackgroundData}

/-- `⟨φ, D(-τ)X⟩ = e^τ ⟨X, φ(e^{τ/2}·)⟩`. -/
theorem inner_test_dil (hφ : IsVectorTest φ) (τ : ℝ) (X : L2Space) :
    inner ℝ (toL2 φ) (dil (-τ) X) = Real.exp τ * inner ℝ X (L13.testDilation φ τ) := by
  rw [real_inner_comm, L13.dil_neg_inner_toL2 _ _ (L13.isVectorTest_memLp hφ)]
  rfl

/-- **The mode in the frame has a weak time derivative** (B1009): on every bounded interval,
`∂_τ D(-τ)b_*(τ) = D(-τ)(driftB(τ) - ½ b_*(τ))`. -/
theorem mode_hasWeakDerivTime (hD : IsUnstableBackground D) (lo hi : ℝ) :
    HasWeakDerivTime lo hi (fun τ => dil (-τ) (toL2 (D.bstar τ)))
      (fun τ => dil (-τ) (toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ))) := by
  have hT := hD.1.period_pos
  have hg := hD.2.graph
  have hb := integrableOn_dil_path (Y2.integrableOn hT hg.value lo hi)
  have hd := integrableOn_dil_path (Y2.integrableOn hT hg.drift lo hi)
  have i1 : IntegrableOn (fun τ => (1 / 2 : ℝ) • toL2 (D.bstar τ)) (Ioo lo hi) :=
    Integrable.smul (1 / 2 : ℝ) (Y2.integrableOn hT hg.value lo hi)
  have i2 : IntegrableOn (fun τ => toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ))
      (Ioo lo hi) :=
    (Y2.integrableOn hT hg.drift lo hi).sub i1
  have hbd : IntegrableOn (fun τ => dil (-τ) (toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ)))
      (Ioo lo hi) :=
    integrableOn_dil_path i2
  refine hasWeakDerivTime_of_separating
    (Λ := {ℓ | ∃ φ, IsVectorTest φ ∧ ℓ = innerSL ℝ (toL2 φ)}) ?_ hb hbd ?_
  · intro x hx
    apply L13.eq_zero_of_forall_vectorTest
    intro φ hφ
    have := hx _ ⟨φ, hφ, rfl⟩
    rwa [innerSL_apply_apply, real_inner_comm] at this
  rintro ℓ ⟨φ, hφ, rfl⟩
  simp only [innerSL_apply_apply]
  set A : ℝ → ℝ := fun τ => inner ℝ (toL2 φ) (dil (-τ) (toL2 (D.bstar τ))) with hA
  set C : ℝ → ℝ := fun τ => inner ℝ (toL2 φ) (dil (-τ) (toL2 (D.driftB τ))) with hC
  have hAi : IntegrableOn A (Ioo lo hi) := (innerSL ℝ (toL2 φ)).integrable_comp hb
  have hCi : IntegrableOn C (Ioo lo hi) := (innerSL ℝ (toL2 φ)).integrable_comp hd
  have hAC : ∀ τ, inner ℝ (toL2 φ)
      (dil (-τ) (toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ))) = C τ - 1 / 2 * A τ := by
    intro τ
    rw [map_sub, map_smul, inner_sub_right, real_inner_smul_right]
  refine ⟨hAi, (innerSL ℝ (toL2 φ)).integrable_comp hbd, fun χ hχ hχc hχt => ?_⟩
  simp only [hAC]
  -- the test `η = χ e^τ`
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℝ, η = fun τ => χ τ * Real.exp τ := ⟨_, rfl⟩
  have hηs : ContDiff ℝ ∞ η := by
    rw [hη]
    exact hχ.mul Real.contDiff_exp
  have hηc : HasCompactSupport η := by
    rw [hη]
    exact hχc.mul_right
  have hηd : ∀ τ, deriv η τ = (deriv χ τ + χ τ) * Real.exp τ := by
    intro τ
    have h2 : HasDerivAt (fun τ => χ τ * Real.exp τ)
        (deriv χ τ * Real.exp τ + χ τ * Real.exp τ) τ :=
      ((hχ.differentiable (by simp) τ).hasDerivAt).mul (Real.hasDerivAt_exp τ)
    rw [hη, h2.deriv]
    ring
  have hw := hg.drift_weak (dilTest η φ) (isSimilarityTest_dilTest hηs hηc hφ)
  have hkm : ∀ τ, MemLp (fun y => φ (Real.exp (τ / 2) • y)) 2 volume := fun τ =>
    L13.isVectorTest_memLp (L13.isVectorTest_comp_smul hφ (Real.exp_pos _).ne')
  have e1 : driftAdjointTerm D.bstar (dilTest η φ) = fun z =>
      (-deriv η z.1 + 3 / 2 * η z.1) * inner ℝ (D.bstar z.1 z.2) (φ (Real.exp (z.1 / 2) • z.2)) := by
    funext z
    exact driftAdjointTerm_dilTest hηs hφ D.bstar z
  have e2 : pairTerm D.driftB (dilTest η φ) = fun z =>
      η z.1 * inner ℝ (D.driftB z.1 z.2) (φ (Real.exp (z.1 / 2) • z.2)) := by
    funext z
    exact pairTerm_dilTest D.driftB z
  have hi1 := hw.left_integrable
  have hi2 := hw.right_integrable
  rw [e1] at hi1
  rw [e2] at hi2
  have heq := hw.eq
  have p1 := integral_pair_dep (f := D.bstar) (k := fun τ y => φ (Real.exp (τ / 2) • y))
    (c := fun τ => -deriv η τ + 3 / 2 * η τ) hkm (Y2.ae_memLp hT hg.value) hi1
  have p2 := integral_pair_dep (f := D.driftB) (k := fun τ y => φ (Real.exp (τ / 2) • y))
    (c := η) hkm (Y2.ae_memLp hT hg.drift) hi2
  rw [e1, e2, p1, p2] at heq
  -- rewrite in terms of `A` and `C`
  have hAτ : ∀ τ, A τ = Real.exp τ * inner ℝ (toL2 (D.bstar τ)) (L13.testDilation φ τ) :=
    fun τ => inner_test_dil hφ τ _
  have hCτ : ∀ τ, C τ = Real.exp τ * inner ℝ (toL2 (D.driftB τ)) (L13.testDilation φ τ) :=
    fun τ => inner_test_dil hφ τ _
  have l1 : ∀ τ, (-deriv η τ + 3 / 2 * η τ) *
      inner ℝ (toL2 (D.bstar τ)) (toL2 (fun y => φ (Real.exp (τ / 2) • y))) =
        -(deriv χ τ * A τ) + 1 / 2 * (χ τ * A τ) := by
    intro τ
    rw [hAτ, hηd, hη]
    simp only [L13.testDilation]
    ring
  have l2 : ∀ τ, η τ * inner ℝ (toL2 (D.driftB τ)) (toL2 (fun y => φ (Real.exp (τ / 2) • y))) =
      χ τ * C τ := by
    intro τ
    rw [hCτ, hη]
    simp only [L13.testDilation]
    ring
  simp only [l1, l2] at heq
  have j1 : Integrable (fun τ => deriv χ τ * A τ) := integrable_deriv_smul hχ hχc hχt hAi
  have j2 : Integrable (fun τ => χ τ * A τ) := integrable_smul hχ hχc hχt hAi
  have j3 : Integrable (fun τ => χ τ * C τ) := integrable_smul hχ hχc hχt hCi
  have k1 : Integrable (fun τ => -(deriv χ τ * A τ)) := j1.neg
  have k2 : Integrable (fun τ => 1 / 2 * (χ τ * A τ)) := j2.const_mul _
  rw [integral_add k1 k2, integral_neg, integral_const_mul] at heq
  have e3 : ∀ τ, χ τ • (C τ - 1 / 2 * A τ) = χ τ * C τ - 1 / 2 * (χ τ * A τ) := fun τ => by
    rw [smul_eq_mul]
    ring
  simp only [e3, smul_eq_mul]
  rw [integral_sub j3 k2, integral_const_mul]
  linarith

end UnforcedLeray.Blueprint.ModeId
