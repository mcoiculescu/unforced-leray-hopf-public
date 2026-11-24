import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4

/-!
# `PartII-a:N01/9/1/2/4/4` (heat integral): `HeatSliceBounds`

Source `the November 2 reference manuscript`
lines 1684-1689.  For a smooth `c`-periodic force `F` supported in `s ∈ [s₁,s₂]`, `|η| ≤ R`, the
periodized slice satisfies `heatSlice c F σ w = σ⁻¹ • F (σ, w)` (`B0220.periodic_reduceIoc_eq`),
which vanishes for `σ < s₁`, is `C¹` jointly, and has bounded values and `w`-derivatives: the
component `ψ_j(p) = (p.1⁻¹ • F p) j` is `C¹`, `c`-periodic in `q`, vanishes on the open band
complement, and so is bounded together with its derivative on the compact fundamental domain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- A `c`-periodic-in-`q` continuous function vanishing on the band complement is bounded. -/
theorem hsb_bounded_of_periodic_band {c s₁ s₂ R : ℝ} (hc : 0 < c) {E : Type*}
    [NormedAddCommGroup E] {b : Profile → E} (hb : Continuous b)
    (hper : UnforcedLeray.B0220.QPeriodic c b)
    (hz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → b p = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖b p‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
    IsCompact (Icc s₁ s₂ ×ˢ (Icc 0 c ×ˢ Icc (-R) R))).exists_bound_of_continuousOn
      hb.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  obtain ⟨s, q, η⟩ := p
  rw [← UnforcedLeray.B0220.periodic_reduceIoc_eq b hper s q η]
  by_cases hmem : (s, UnforcedLeray.B0220.reduceIoc c q, η) ∈
      (Icc s₁ s₂ ×ˢ (Icc 0 c ×ˢ Icc (-R) R))
  · exact (hC _ hmem).trans (le_max_left _ _)
  · have hr : UnforcedLeray.B0220.reduceIoc c q ∈ Icc 0 c :=
      ⟨(UnforcedLeray.B0220.reduceIoc_mem hc q).1.le, (UnforcedLeray.B0220.reduceIoc_mem hc q).2⟩
    have hband : s < s₁ ∨ s₂ < s ∨ R < |η| := by
      by_contra hcon
      push_neg at hcon
      exact hmem ⟨⟨hcon.1, hcon.2.1⟩, hr, abs_le.1 hcon.2.2⟩
    rw [hz (s, UnforcedLeray.B0220.reduceIoc c q, η) hband]
    simp

/-- The `w`-derivative of a slice is bounded by the full derivative. -/
theorem hsb_norm_fderiv_slice_le {Ψ : Profile → ℂ} (hΨ : Differentiable ℝ Ψ) (σ : ℝ)
    (w : ℝ × ℝ) :
    ‖fderiv ℝ (fun w' : ℝ × ℝ => Ψ (σ, w')) w‖ ≤ ‖fderiv ℝ Ψ (σ, w)‖ := by
  have h1 : HasFDerivAt (fun w' : ℝ × ℝ => (σ, w')) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w :=
    hasFDerivAt_prodMk_right σ w
  have h2 : HasFDerivAt (fun w' : ℝ × ℝ => Ψ (σ, w'))
      ((fderiv ℝ Ψ (σ, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) w :=
    (hΨ (σ, w)).hasFDerivAt.comp w h1
  rw [h2.fderiv]
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp [Prod.norm_def])
  calc ‖(fderiv ℝ Ψ (σ, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖fderiv ℝ Ψ (σ, w)‖ * ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        (fderiv ℝ Ψ (σ, w)).opNorm_comp_le _
    _ ≤ ‖fderiv ℝ Ψ (σ, w)‖ * 1 := mul_le_mul_of_nonneg_left hinr (norm_nonneg _)
    _ = ‖fderiv ℝ Ψ (σ, w)‖ := mul_one _

/-- Bounds for a `C¹`, `c`-periodic-in-`q` complex function vanishing on the band complement:
the function and its derivative are uniformly bounded. -/
theorem hsb_comp_bounds {c s₁ s₂ R : ℝ} (hc : 0 < c) {Ψ : Profile → ℂ}
    (hC : ContDiff ℝ 1 Ψ) (hper : UnforcedLeray.B0220.QPeriodic c Ψ)
    (hz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → Ψ p = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ p, ‖Ψ p‖ ≤ M) ∧ (∀ p, ‖fderiv ℝ Ψ p‖ ≤ M) := by
  have hΨc : Continuous Ψ := hC.continuous
  have hD : Continuous (fderiv ℝ Ψ) := hC.continuous_fderiv (by norm_num)
  have hxa' : ∀ x : Profile, x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) :=
    fun x => by ext <;> simp
  have hpa : ∀ x : Profile, Ψ (x + ((0 : ℝ), c, (0 : ℝ))) = Ψ x := fun x => by
    rw [hxa' x]
    exact hper x
  have hDper : UnforcedLeray.B0220.QPeriodic c (fderiv ℝ Ψ) := by
    intro p
    have hxa : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := hxa' p
    have h1 : fderiv ℝ (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ))))  p =
        fderiv ℝ Ψ (p + ((0 : ℝ), c, (0 : ℝ))) := fderiv_comp_add_right _
    have h2 : (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ)))) = Ψ := funext hpa
    rw [h2] at h1
    rw [← hxa]
    exact h1.symm
  have hU : IsOpen {p : Profile | p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|} :=
    (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hDz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → fderiv ℝ Ψ p = 0 := by
    intro p hp
    have hev : Ψ =ᶠ[𝓝 p] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hp) (fun y hy => hz y hy)
    rw [hev.fderiv_eq]
    simp
  obtain ⟨M1, hM1, hb1⟩ := hsb_bounded_of_periodic_band hc hΨc hper hz
  obtain ⟨M2, hM2, hb2⟩ := hsb_bounded_of_periodic_band hc hD hDper hDz
  exact ⟨max M1 M2, le_max_of_le_left hM1, fun p => (hb1 p).trans (le_max_left _ _),
    fun p => (hb2 p).trans (le_max_right _ _)⟩

theorem heatSliceBounds : UnforcedLeray.Short.PartIIa.N01.HeatSliceBounds := by
  intro c hc F hF
  obtain ⟨hFc, hFper, s₁, s₂, R, hs₁, hz⟩ := hF
  -- the periodized slice is `σ⁻¹ • F (σ, w)`
  have hslice : ∀ σ : ℝ, ∀ w : ℝ × ℝ, heatSlice c F σ w = σ⁻¹ • F (σ, w.1, w.2) := by
    intro σ w
    unfold heatSlice UnforcedLeray.B0220.periodize
    have hq : UnforcedLeray.B0220.QPeriodic c (fun q : Profile => q.1⁻¹ • F q) := by
      intro p
      show p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • F p
      rw [hFper p]
    exact UnforcedLeray.B0220.periodic_reduceIoc_eq _ hq σ w.1 w.2
  have hsl : ∀ (j : Fin 2) (σ : ℝ) (w : ℝ × ℝ),
      heatSlice c F σ w j = (fun p : Profile => (p.1⁻¹ • F p) j) (σ, w) :=
    fun j σ w => congrArg (fun z : MeridC => z j) (hslice σ w)
  -- smoothness of `p ↦ p.1⁻¹ • F p` (it vanishes for `p.1 < s₁`)
  have hgC : ContDiff ℝ 1 (fun p : Profile => p.1⁻¹ • F p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 < s₁
    · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : MeridC))) ?_
      filter_upwards [(isOpen_lt continuous_fst continuous_const :
        IsOpen {p : Profile | p.1 < s₁}).mem_nhds hp] with y hy
      simp [hz y (Or.inl hy)]
    · have hpos : p.1 ≠ 0 := (lt_of_lt_of_le hs₁ (not_lt.1 hp)).ne'
      exact (contDiffAt_fst.inv hpos).smul (hFc.of_le (by simp)).contDiffAt
  have hΨC : ∀ j : Fin 2, ContDiff ℝ 1 (fun p : Profile => (p.1⁻¹ • F p) j) := fun j =>
    ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) j).restrictScalars ℝ).contDiff.comp hgC
  have hΨper : ∀ j : Fin 2, UnforcedLeray.B0220.QPeriodic c (fun p : Profile => (p.1⁻¹ • F p) j) := by
    intro j p
    show (p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2)) j = (p.1⁻¹ • F p) j
    rw [hFper p]
  have hΨz : ∀ j : Fin 2, ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) →
      (p.1⁻¹ • F p) j = 0 := by
    intro j p hp
    simp [hz p hp]
  -- the components are bounded with derivatives
  have key : ∀ j : Fin 2, ∃ M : ℝ, 0 ≤ M ∧ (∀ σ w, ‖heatSlice c F σ w j‖ ≤ M) ∧
      (∀ σ w, ‖fderiv ℝ (fun w' : ℝ × ℝ => heatSlice c F σ w' j) w‖ ≤ M) := by
    intro j
    obtain ⟨M, hM0, hv, hd⟩ := hsb_comp_bounds hc (hΨC j) (hΨper j) (hΨz j)
    refine ⟨M, hM0, fun σ w => ?_, fun σ w => ?_⟩
    · rw [hsl j σ w]
      exact hv _
    · have hfun : (fun w' : ℝ × ℝ => heatSlice c F σ w' j) =
          fun w' : ℝ × ℝ => (fun p : Profile => (p.1⁻¹ • F p) j) (σ, w') :=
        funext fun w' => hsl j σ w'
      rw [hfun]
      exact (hsb_norm_fderiv_slice_le ((hΨC j).differentiable (by norm_num)) σ w).trans (hd _)
  choose M hM0 hv hd using key
  refine ⟨⟨s₁, hs₁, fun σ hσ w => ?_⟩, ?_, ?_⟩
  · rw [hslice, hz (σ, w.1, w.2) (Or.inl hσ), smul_zero]
  · intro j
    have e : (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2 j) =
        fun p : Profile => (p.1⁻¹ • F p) j :=
      funext fun p => hsl j p.1 p.2
    rw [e]
    exact hΨC j
  · exact ⟨∑ k, M k,
      fun j σ w => (hv j σ w).trans (Finset.single_le_sum (fun k _ => hM0 k) (Finset.mem_univ j)),
      fun j σ w => (hd j σ w).trans (Finset.single_le_sum (fun k _ => hM0 k) (Finset.mem_univ j))⟩

end UnforcedLeray.Short.PartIIa.N01
