import UnforcedLeray.Loc.Hyp.ModeIdentification.Dil

/-!
# H-ModeId helpers: the `E`-solution in the dilated frame

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 308–318, blueprint unit B1010: "the mild solution
`E(τ,s)[e^{σs}b_*(s)]` is a solution of `∂_τ w = 𝓛_* w`").

Frame. For a path `R` put `P_R(τ) = D(-τ)R(τ) = e^{-τ/2}R(e^{-τ/2}·, τ)`. The drift `½y·∇` of
`𝓛₀ = hΔ + ½y·∇ + ½` disappears in this frame: a similarity weak solution of
`∂_τR = hΔR + ½R + ½y·∇R + F` has `∂_τ P_R = D(-τ)(hΔR + F)` in `L²`
(`frame_hasDerivAt`; the computation of `L13.physical_weak_of_similarity` without the change of
time `t = e^τ`).

`evolution_frame_hasDerivAt`: conditional on the mild-to-weak theorem `L13.EvolutionWeakForm`

derivative `D(-τ)(hΔE(τ,s₀)f₀ + 𝓑_*(τ)E(τ,s₀)f₀)`. `EvolutionWeakForm` asks for a `Z`-continuous
mild solution on a whole half-line `(-∞, τ₀]`; the solution `E(τ,s₁)x` is cut off smoothly before
`s₁`, `z = χ E(·,s₁)x`, and the cutoff enters as the forcing `χ' E(·,s₁)x`, which vanishes where
`χ ≡ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil)
open UnforcedLeray.Blueprint.L13 (IsSimilarityWeakSolution testDilation radialDeriv
  hasDerivAt_inner_of_weak hasDerivAt_testDilation isVectorTest_comp_smul isVectorTest_memLp
  dil_neg_inner_toL2 hasDerivAt_of_weak)

/-! ## The frame derivative of a similarity weak solution -/

/-- The weak frame derivative: `d/dτ ⟨D(-τ)R(τ), φ⟩ = ⟨D(-τ)(hΔR(τ) + F(τ)), φ⟩`. Adapted from
`L13.physical_weak_of_similarity` (`Loc/L13PhysicalRemainder/WeakStrong.lean`, lines 426–479). -/
theorem frame_weak {h : ℝ} {S : Set ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : ContinuousOn (fun τ => (R τ).value) S) (hw : IsSimilarityWeakSolution h S R F)
    {φ : Space → Space} (hφ : IsVectorTest φ) {τ : ℝ} (hτ : S ∈ 𝓝 τ) :
    HasDerivAt (fun σ => inner ℝ (dil (-σ) (R σ).value) (toL2 φ))
      (inner ℝ (dil (-τ) (h • H2.laplace (R τ) + F τ)) (toL2 φ)) τ := by
  have hτS : τ ∈ S := mem_of_mem_nhds hτ
  have hφτ : IsVectorTest (fun y => φ (Real.exp (τ / 2) • y)) :=
    isVectorTest_comp_smul hφ (Real.exp_pos _).ne'
  set f : ℝ → ℝ := fun σ => Real.exp σ * inner ℝ (R σ).value (testDilation φ σ) with hfdef
  have hpr : HasDerivAt (fun σ => inner ℝ (R σ).value (testDilation φ σ))
      ((inner ℝ (h • H2.laplace (R τ) + F τ) (toL2 (fun y => φ (Real.exp (τ / 2) • y))) -
        inner ℝ (R τ).value (toL2 (fun y => φ (Real.exp (τ / 2) • y))) -
        (1 / 2 : ℝ) * inner ℝ (R τ).value
          (toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y))))) +
        inner ℝ (R τ).value ((1 / 2 : ℝ) •
          toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y))))) τ := by
    apply hasDerivAt_inner_of_weak
    · exact (hR.continuousAt hτ)
    · exact hasDerivAt_testDilation hφ τ
    · exact hw _ hφτ τ hτS
  have hf : HasDerivAt f (Real.exp τ * inner ℝ (h • H2.laplace (R τ) + F τ)
      (toL2 (fun y => φ (Real.exp (τ / 2) • y)))) τ := by
    have h2 := (Real.hasDerivAt_exp τ).mul hpr
    refine h2.congr_deriv ?_
    rw [real_inner_smul_right]
    simp only [testDilation]
    ring
  have hfun : (fun σ => inner ℝ (dil (-σ) (R σ).value) (toL2 φ)) = f := by
    funext σ
    rw [dil_neg_inner_toL2 _ _ (isVectorTest_memLp hφ)]
    rfl
  rw [hfun, dil_neg_inner_toL2 _ _ (isVectorTest_memLp hφ)]
  exact hf

/-- **Frame derivative** (strong form): on an open interval where `R` is `L²`-continuous and
`hΔR + F` is `L²`-continuous, `τ ↦ D(-τ)R(τ)` is differentiable with derivative
`D(-τ)(hΔR(τ) + F(τ))`. -/
theorem frame_hasDerivAt {h a b : ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : ContinuousOn (fun τ => (R τ).value) (Ioo a b))
    (hw : IsSimilarityWeakSolution h (Ioo a b) R F)
    (hG : ContinuousOn (fun τ => h • H2.laplace (R τ) + F τ) (Ioo a b)) :
    ∀ τ ∈ Ioo a b, HasDerivAt (fun σ => dil (-σ) (R σ).value)
      (dil (-τ) (h • H2.laplace (R τ) + F τ)) τ := by
  have hG' : ContinuousOn (fun τ => dil (-τ) (h • H2.laplace (R τ) + F τ)) (Ioo a b) :=
    continuousOn_dil_path (k := fun τ => -τ) continuous_neg hG
  exact hasDerivAt_of_weak hG' (fun φ hφ t ht =>
    frame_weak hR hw hφ (isOpen_Ioo.mem_nhds ht))

/-! ## The `E`-solution -/

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}

theorem continuous_toH2 : Continuous (fun g : Z => g.toH2) := Zincl.continuous

theorem continuous_laplace_toH2 : Continuous (fun g : Z => H2.laplace g.toH2) :=
  H2.laplaceCLM.continuous.comp continuous_toH2

theorem continuous_Lclass : Continuous Lclass := L13.LclassCLM.continuous

theorem continuous_Zclass : Continuous Zclass := by
  have h : Zclass = Xclass ∘ ιZ := by
    funext g
    exact (Xclass_ιZ g).symm
  rw [h]
  exact L04.continuous_Xclass.comp ιZ.continuous

/-- A smooth cutoff vanishing on `(-∞, a]` and equal to `1` on `[a + 2ε... ]`. -/
theorem exists_cutoff {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ (∀ r, r ≤ a → χ r = 0) ∧ (∀ r, b ≤ r → χ r = 1) := by
  refine ⟨fun r => Real.smoothTransition ((r - a) / (b - a)),
    (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop), fun r hr => ?_, fun r hr => ?_⟩
  · exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  · exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem deriv_eq_zero_of_eventuallyEq_const {χ : ℝ → ℝ} {r k : ℝ} (h : χ =ᶠ[𝓝 r] fun _ => k) :
    deriv χ r = 0 := by
  rw [h.deriv_eq]
  simp

/-- The mild formula for the cut-off solution `z = χ E(·,s₁)x` with forcing `χ' E(·,s₁)x`. -/
theorem cutoff_mild (hev : IsEvolution D c S ev) {s₁ a : ℝ} (hs₁a : s₁ < a) (x : X)
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ 1 χ) (hχ0 : ∀ r, r ≤ a → χ r = 0) (z : ℝ → Z) (Fr : ℝ → X)
    (hz : ∀ r, ιZ (z r) = χ r • ev.E r s₁ x) (hFr : ∀ r, Fr r = deriv χ r • ev.E r s₁ x)
    (s σ : ℝ) (hsσ : s ≤ σ) :
    IntegrableOn (fun r => ev.E σ r (Fr r)) (Ioo s σ) ∧
      ιZ (z σ) = ev.E σ s (ιZ (z s)) + ∫ r in Ioo s σ, ev.E σ r (Fr r) := by
  have hχd : Differentiable ℝ χ := hχs.differentiable one_ne_zero
  have hdχc : Continuous (deriv χ) := hχs.continuous_deriv le_rfl
  have hdχ0 : ∀ r, r < a → deriv χ r = 0 := fun r hr =>
    deriv_eq_zero_of_eventuallyEq_const (k := 0) (by
      filter_upwards [Iio_mem_nhds hr] with r' hr'
      exact hχ0 r' (le_of_lt hr'))
  have hEz : ev.E σ s (ιZ (z s)) = χ s • ev.E σ s₁ x := by
    rw [hz, map_smul]
    rcases lt_or_ge s s₁ with hs | hs
    · rw [hχ0 s (by linarith), zero_smul, zero_smul]
    · rw [← L04.E_apply_law hev hs hsσ]
  have heq : EqOn (fun r => ev.E σ r (Fr r)) (fun r => deriv χ r • ev.E σ s₁ x) (Ioo s σ) := by
    intro r hr
    simp only [hFr, map_smul]
    rcases lt_or_ge r s₁ with h1 | h1
    · rw [hdχ0 r (by linarith), zero_smul, zero_smul]
    · rw [← L04.E_apply_law hev h1 (le_of_lt hr.2)]
  have hint : IntegrableOn (fun r => deriv χ r • ev.E σ s₁ x) (Ioo s σ) :=
    ((hdχc.smul continuous_const).integrableOn_Icc (a := s) (b := σ)).mono_set
      Ioo_subset_Icc_self
  refine ⟨hint.congr_fun heq.symm measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_smul_const, hz, hEz]
  have hI : ∫ r in Ioo s σ, deriv χ r = χ σ - χ s := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hsσ]
    exact intervalIntegral.integral_deriv_eq_sub (fun r _ => hχd r)
      (hdχc.intervalIntegrable _ _)
  rw [hI, sub_smul, add_sub_cancel]

/-- The cut-off solution: for `s₁ < a < b` and `g₁ ∈ Z` there are a continuous `z : ℝ → Z` and
a continuous forcing `F : ℝ → X` with the mild formula on every interval, `ι_Z z = E(·,s₁)ι_Z g₁`
on `[b,∞)` and `F = 0` on `(b,∞)`. -/
theorem exists_cutoff_solution (hD : IsUnstableBackground D) (hc : IsCoefficients D c)
    (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev) {s₁ a b : ℝ} (hs₁a : s₁ < a)
    (hab : a < b) (g₁ : Z) :
    ∃ z : ℝ → Z, ∃ Fr : ℝ → X, Continuous z ∧ Continuous Fr ∧
      (∀ r, b ≤ r → ιZ (z r) = ev.E r s₁ (ιZ g₁)) ∧ (∀ r, b < r → Fr r = 0) ∧
      ∀ s σ, s ≤ σ → IntegrableOn (fun r => ev.E σ r (Fr r)) (Ioo s σ) ∧
        ιZ (z σ) = ev.E σ s (ιZ (z s)) + ∫ r in Ioo s σ, ev.E σ r (Fr r) := by
  obtain ⟨χ, hχs, hχ0, hχ1⟩ := exists_cutoff hab
  have hdχc : Continuous (deriv χ) := hχs.continuous_deriv le_rfl
  have hdχ0 : ∀ r, r < a → deriv χ r = 0 := fun r hr =>
    deriv_eq_zero_of_eventuallyEq_const (k := 0) (by
      filter_upwards [Iio_mem_nhds hr] with r' hr'
      exact hχ0 r' (le_of_lt hr'))
  have hdχ1 : ∀ r, b < r → deriv χ r = 0 := fun r hr =>
    deriv_eq_zero_of_eventuallyEq_const (k := 1) (by
      filter_upwards [Ioi_mem_nhds hr] with r' hr'
      exact hχ1 r' (le_of_lt hr'))
  have hZc : ContinuousOn (fun r => ev.EZ r s₁ (ιZ g₁)) (Ioi s₁) :=
    L04.evolutionZContinuity_of hD hc hS hev s₁ g₁
  have hEc : ContinuousOn (fun r => ev.E r s₁ (ιZ g₁)) (Ici s₁) := by
    have hp : Continuous (fun r : ℝ => (r, s₁)) := continuous_id.prodMk continuous_const
    exact (hev.strongly_continuous (ιZ g₁)).comp hp.continuousOn (fun r hr => hr)
  refine ⟨fun r => χ r • ev.EZ r s₁ (ιZ g₁), fun r => deriv χ r • ev.E r s₁ (ιZ g₁),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro r
    rcases lt_or_ge r a with hr | hr
    · have : (fun r => χ r • ev.EZ r s₁ (ιZ g₁)) =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hr] with r' hr'
        rw [hχ0 r' (le_of_lt hr'), zero_smul]
      exact continuousAt_const.congr this.symm
    · have hr' : s₁ < r := by linarith
      exact (hχs.continuous.continuousAt).smul (hZc.continuousAt (Ioi_mem_nhds hr'))
  · rw [continuous_iff_continuousAt]
    intro r
    rcases lt_or_ge r a with hr | hr
    · have : (fun r => deriv χ r • ev.E r s₁ (ιZ g₁)) =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hr] with r' hr'
        rw [hdχ0 r' hr', zero_smul]
      exact continuousAt_const.congr this.symm
    · have hr' : s₁ < r := by linarith
      exact hdχc.continuousAt.smul (hEc.continuousAt (Ici_mem_nhds hr'))
  · intro r hr
    have hr' : s₁ < r := by linarith
    simp only [L04.EZ_apply hev hr', hχ1 r hr, one_smul]
  · intro r hr
    simp only [hdχ1 r hr, zero_smul]
  · intro s σ hsσ
    have hzι : ∀ r, ιZ (χ r • ev.EZ r s₁ (ιZ g₁)) = χ r • ev.E r s₁ (ιZ g₁) := by
      intro r
      rcases le_or_gt r s₁ with hr | hr
      · simp only [hχ0 r (by linarith), zero_smul, map_zero]
      · simp only [map_smul, L04.EZ_apply hev hr]
    exact cutoff_mild hev hs₁a (ιZ g₁) hχs hχ0 (fun r => χ r • ev.EZ r s₁ (ιZ g₁))
      (fun r => deriv χ r • ev.E r s₁ (ιZ g₁)) hzι (fun r => rfl) s σ hsσ

/-- **The `E`-solution in the frame** (B1010, conditional on `L13.EvolutionWeakForm`). For
`f₀ ∈ X` and `τ > s₀`, `σ ↦ D(-σ)E(σ,s₀)f₀` has derivative
`D(-τ)(hΔE_Z(τ,s₀)f₀ + 𝓑_*(τ)E(τ,s₀)f₀)` at `τ`. -/
theorem evolution_frame_hasDerivAt (hW : L13.EvolutionWeakForm) (hD : IsUnstableBackground D)
    (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev)
    (s₀ : ℝ) (f₀ : X) {τ : ℝ} (hτ : s₀ < τ) :
    HasDerivAt (fun σ => dil (-σ) (Xclass (ev.E σ s₀ f₀)))
      (dil (-τ) (D.h • H2.laplace (ev.EZ τ s₀ f₀).toH2 + Lclass (c.B τ (ev.E τ s₀ f₀)))) τ := by
  obtain ⟨s₁, a, b, hs₀₁, hs₁a, hab, hbτ⟩ : ∃ s₁ a b : ℝ, s₀ < s₁ ∧ s₁ < a ∧ a < b ∧ b < τ :=
    ⟨s₀ + (τ - s₀) / 4, s₀ + (τ - s₀) / 2, s₀ + 3 * (τ - s₀) / 4,
      by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨z, Fr, hzc, hFc, hzE, hF0, hmild⟩ :=
    exists_cutoff_solution hD hc hS hev hs₁a hab (ev.EZ s₁ s₀ f₀)
  have hx : ιZ (ev.EZ s₁ s₀ f₀) = ev.E s₁ s₀ f₀ := L04.EZ_apply hev hs₀₁ f₀
  have hweak := hW D c S ev hD hc hS hev (τ + 1) z Fr hzc.continuousOn hFc.continuousOn
    (fun s σ hsσ _ => hmild s σ hsσ)
  have hw' : IsSimilarityWeakSolution D.h (Ioo b (τ + 1)) (fun r => (z r).toH2)
      (fun r => Lclass (c.B r (ιZ (z r))) + Xclass (Fr r)) :=
    hweak.mono (fun r hr => hr.2)
  have hRc : ContinuousOn (fun r => (z r).toH2.value) (Ioo b (τ + 1)) := by
    have : Continuous (fun r => Zclass (z r)) := continuous_Zclass.comp hzc
    exact this.continuousOn
  have h1 : Continuous (fun r => c.B r (ιZ (z r))) :=
    hc.B_continuous.clm_apply (ιZ.continuous.comp hzc)
  have h2 : Continuous (fun r => Lclass (c.B r (ιZ (z r))) + Xclass (Fr r)) :=
    (continuous_Lclass.comp h1).add (L04.continuous_Xclass.comp hFc)
  have h3 : Continuous (fun r => H2.laplace (z r).toH2) := continuous_laplace_toH2.comp hzc
  have hGc : ContinuousOn (fun r => D.h • H2.laplace (z r).toH2 +
      (Lclass (c.B r (ιZ (z r))) + Xclass (Fr r))) (Ioo b (τ + 1)) := by
    have h4 : Continuous (fun r => D.h • H2.laplace (z r).toH2) := h3.const_smul D.h
    exact (h4.add h2).continuousOn
  have hder := frame_hasDerivAt hRc hw' hGc τ ⟨hbτ, by linarith⟩
  have hzE' : ∀ r, b ≤ r → ιZ (z r) = ev.E r s₀ f₀ := by
    intro r hr
    rw [hzE r hr, hx, ← L04.E_apply_law hev hs₀₁.le (by linarith)]
  have hzτ : z τ = ev.EZ τ s₀ f₀ := by
    apply L04.ιZ_injective
    rw [hzE' τ hbτ.le, L04.EZ_apply hev hτ]
  have hval : ∀ σ, b < σ → (z σ).toH2.value = Xclass (ev.E σ s₀ f₀) := by
    intro σ hσ
    rw [← hzE' σ (le_of_lt hσ), Xclass_ιZ]
    rfl
  have hev' : (fun σ => dil (-σ) (z σ).toH2.value) =ᶠ[𝓝 τ]
      (fun σ => dil (-σ) (Xclass (ev.E σ s₀ f₀))) := by
    filter_upwards [Ioi_mem_nhds hbτ] with σ hσ
    rw [hval σ hσ]
  refine (hder.congr_of_eventuallyEq hev'.symm).congr_deriv ?_
  rw [hzτ, L04.EZ_apply hev hτ, hF0 τ hbτ, L04.Xclass_zero, add_zero]

end UnforcedLeray.Blueprint.ModeId
