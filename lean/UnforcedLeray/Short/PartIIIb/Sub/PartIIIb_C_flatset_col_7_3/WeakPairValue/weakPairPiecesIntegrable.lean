import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.ZetaPhiTest
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.FlatIntegrandBound

/-!
# Integrability of the two weak-pair pieces (organizer task `PartIII-b:C/flatset/col/7/3/6/5`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
`ζ_Φ = s^{1/2}Φ` and `(μ - A₀*)ζ_Φ` are continuous, vanish outside the band
`s ∈ [s₁, s₂]`, `|η| ≤ R`, and are bounded on the compact box `K ⊇ fibK1`.
With `g ∈ L²(s^{-3/2} dς)` the weight `s^{-3/2}` is bounded on the band, and the
`fib_key` comparison `L²(ageμ) → L¹` on `fibK1` gives integrability (as in
`weakPairIntegrable`).

The pointwise formula of `(μ - A₀*)ζ_Φ` is not needed: only continuity and the vanishing of
the derivatives on the open complement of the band are used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatLap fibK1 fibK1_mem fibK1_measurable fib_key fib_bound)
open UnforcedLeray.Short.PartIIa (IsMeridTest PepsC T0flat solenoidalHC pdS pdQ pdEta)

/-- A directional derivative of a smooth function is smooth. -/
theorem wp_fderiv_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    (hf : ContDiff ℝ ∞ f) (v : ℝ × ℝ × ℝ) : ContDiff ℝ ∞ (fun p => fderiv ℝ f p v) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

/-- A function vanishing near `p` has vanishing derivatives at `p`. -/
theorem wp_fderiv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    {p : Profile} (h : ∀ᶠ x in 𝓝 p, f x = 0) (v : ℝ × ℝ × ℝ) : fderiv ℝ f p v = 0 := by
  have h' : f =ᶠ[𝓝 p] (fun _ => (0 : E)) := h
  rw [h'.fderiv_eq]
  simp

theorem wp_pdQ_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    {p : Profile} (h : ∀ᶠ x in 𝓝 p, f x = 0) : ∀ᶠ x in 𝓝 p, pdQ f x = 0 :=
  (eventually_eventually_nhds.2 h).mono fun x hx => wp_fderiv_zero hx (0, 1, 0)

theorem wp_pdEta_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    {p : Profile} (h : ∀ᶠ x in 𝓝 p, f x = 0) : ∀ᶠ x in 𝓝 p, pdEta f x = 0 :=
  (eventually_eventually_nhds.2 h).mono fun x hx => wp_fderiv_zero hx (0, 0, 1)

/-- `(μ - A₀*)ζ` vanishes at a point where `ζ` vanishes on a neighbourhood. -/
theorem wp_resolvent_zero {ν μ : ℝ} {ζ : Profile → MeridC} {p : Profile}
    (h : ∀ᶠ x in 𝓝 p, ζ x = 0) : resolventTest ν μ ζ p = 0 := by
  have h1 : pdS ζ p = 0 := wp_fderiv_zero h (1, 0, 0)
  have h2 : pdQ (pdQ ζ) p = 0 := wp_fderiv_zero (wp_pdQ_zero h) (0, 1, 0)
  have h3 : pdEta (pdEta ζ) p = 0 := wp_fderiv_zero (wp_pdEta_zero h) (0, 0, 1)
  have h4 : ζ p = 0 := h.self_of_nhds
  simp [resolventTest, A0adj, h1, h2, h3, h4]

/-- `(μ - A₀*)ζ` is continuous for smooth `ζ`. -/
theorem wp_resolvent_continuous {ν μ : ℝ} {ζ : Profile → MeridC} (hζ : ContDiff ℝ ∞ ζ) :
    Continuous (resolventTest ν μ ζ) := by
  have h1 : ContDiff ℝ ∞ (pdS ζ) := wp_fderiv_contDiff hζ (1, 0, 0)
  have hq : ContDiff ℝ ∞ (pdQ ζ) := wp_fderiv_contDiff hζ (0, 1, 0)
  have hq2 : ContDiff ℝ ∞ (pdQ (pdQ ζ)) := wp_fderiv_contDiff hq (0, 1, 0)
  have he : ContDiff ℝ ∞ (pdEta ζ) := wp_fderiv_contDiff hζ (0, 0, 1)
  have he2 : ContDiff ℝ ∞ (pdEta (pdEta ζ)) := wp_fderiv_contDiff he (0, 0, 1)
  have c0 := hζ.continuous
  have c1 := h1.continuous
  have c2 := hq2.continuous
  have c3 := he2.continuous
  unfold resolventTest A0adj
  fun_prop

theorem wp_norm_merC (b : EuclideanSpace ℝ (Fin 2)) :
    ‖NearInst.merC b‖ = ‖b‖ := by
  unfold NearInst.merC
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem wp_merC_continuous : Continuous (NearInst.merC) := by
  unfold NearInst.merC
  fun_prop

/-- Piece lemma: for a continuous `w` vanishing off the band, `s^{-3/2} ⟪w, g⟫` is integrable on
`Ioi 0 × cell` for `g ∈ H`. -/
theorem wp_piece_integrable {c s1 s2 R : ℝ} (hc : 0 < c) (hs1 : 0 < s1)
    (w : Profile → MeridC) (hwc : Continuous w)
    (hw0 : ∀ p : Profile, (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → w p = 0)
    (g : Hsp c) :
    IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
        inner ℂ (w p) (NearInst.merC (g p))) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  set S : Set Chart := Ioi (0 : ℝ) ×ˢ B0579.cell c with hSdef
  have hSm : MeasurableSet S := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hac : (volume : Measure Chart).restrict S ≪ ageμ c (-3 / 2) :=
    volCyl_ac_ageμ hc (-3 / 2)
  set W : Set Chart := fibK1 c s1 s2 R with hWdef
  have hWm : MeasurableSet W := fibK1_measurable c s1 s2 R
  set K : Set Chart := Icc s1 s2 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hWK : ∀ p, p ∈ W → p ∈ K := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (fibK1_mem).1 hp
    exact ⟨h1, ⟨h2.1, h2.2.le⟩, h3⟩
  obtain ⟨M, hM0, hM⟩ := fib_bound hKc hwc
  -- measurable representative of `g`
  set gm : Chart → EuclideanSpace ℝ (Fin 2) := (Lp.aestronglyMeasurable g).mk ⇑g with hgmdef
  have hgm_meas : Measurable gm := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable
  have hgm_ae : (⇑g) =ᵐ[ageμ c (-3 / 2)] gm := (Lp.aestronglyMeasurable g).ae_eq_mk
  have hgm_S : ∀ᵐ p ∂((volume : Measure Chart).restrict S), g p = gm p := hac.ae_le hgm_ae
  have hfinite : eLpNorm (fun p => ‖gm p‖) 2 (ageμ c (-3 / 2)) < ⊤ := by
    have hcongr : eLpNorm (fun p => ‖gm p‖) 2 (ageμ c (-3 / 2)) =
        eLpNorm (fun p => ‖g p‖) 2 (ageμ c (-3 / 2)) :=
      eLpNorm_congr_ae (by filter_upwards [hgm_ae] with p hp; simp only [hp])
    rw [hcongr]
    exact (Lp.memLp g).norm.eLpNorm_lt_top
  obtain ⟨Cf, hCf_top, hCf⟩ := fib_key (s1 := s1) (s2 := s2) (R := R)
    hc hs1 (-3 / 2) (by norm_num)
  have hWint : Integrable (fun p => ‖gm p‖) ((volume : Measure Chart).restrict W) := by
    refine ⟨hgm_meas.norm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hmain := hCf (fun p => ‖gm p‖) hgm_meas.norm (fun p => norm_nonneg _)
    have hlt : ∫⁻ p in W, ENNReal.ofReal (‖gm p‖) < ⊤ :=
      lt_of_le_of_lt hmain (ENNReal.mul_ne_top hCf_top hfinite.ne).lt_top
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun a => ?_)) hlt
    show ‖‖gm a‖‖ₑ = ENNReal.ofReal (‖gm a‖)
    rw [Real.enorm_eq_ofReal (norm_nonneg _)]
  have hWind : Integrable (W.indicator (fun p => ‖gm p‖)) volume :=
    (integrable_indicator_iff hWm).2 hWint
  have hdom : Integrable (fun p => (s1 ^ (-(3 / 2 : ℝ)) * M) * W.indicator (fun p => ‖gm p‖) p)
      ((volume : Measure Chart).restrict S) :=
    (hWind.const_mul (s1 ^ (-(3 / 2 : ℝ)) * M)).restrict
  have hFm : AEStronglyMeasurable (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
      inner ℂ (w p) (NearInst.merC (gm p))) ((volume : Measure Chart).restrict S) :=
    (Measurable.smul (measurable_fst.pow_const (-(3 / 2 : ℝ)))
      (Measurable.inner hwc.measurable (wp_merC_continuous.measurable.comp hgm_meas))).aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
      inner ℂ (w p) (NearInst.merC (g p))) ((volume : Measure Chart).restrict S) := by
    refine hFm.congr ?_
    filter_upwards [hgm_S] with p hp
    simp only [hp]
  have hpt : ∀ᵐ p ∂((volume : Measure Chart).restrict S),
      ‖(p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (w p) (NearInst.merC (g p))‖ ≤
        (s1 ^ (-(3 / 2 : ℝ)) * M) * W.indicator (fun p => ‖gm p‖) p := by
    filter_upwards [ae_restrict_mem hSm, hgm_S] with p hpS hp
    have hpS' : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c := hpS
    by_cases hpW : p ∈ W
    · have hs : s1 ≤ p.1 := ((fibK1_mem).1 hpW).1.1
      have hp0 : 0 < p.1 := lt_of_lt_of_le hs1 hs
      have hpow : p.1 ^ (-(3 / 2 : ℝ)) ≤ s1 ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs1 hs (by norm_num)
      have hwp : ‖w p‖ ≤ M := hM p (hWK p hpW)
      have hmer : ‖NearInst.merC (g p)‖ = ‖gm p‖ := by rw [hp, wp_norm_merC]
      rw [Set.indicator_of_mem hpW, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hp0.le _)]
      calc p.1 ^ (-(3 / 2 : ℝ)) * ‖inner ℂ (w p) (NearInst.merC (g p))‖
          ≤ s1 ^ (-(3 / 2 : ℝ)) * (‖w p‖ * ‖NearInst.merC (g p)‖) :=
            mul_le_mul hpow (norm_inner_le_norm _ _) (norm_nonneg _)
              (Real.rpow_nonneg hs1.le _)
        _ ≤ s1 ^ (-(3 / 2 : ℝ)) * (M * ‖gm p‖) := by
            rw [hmer]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwp (norm_nonneg _))
              (Real.rpow_nonneg hs1.le _)
        _ = (s1 ^ (-(3 / 2 : ℝ)) * M) * ‖gm p‖ := by ring
    · have hband : p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2| := by
        by_contra hcon
        push_neg at hcon
        apply hpW
        have hq : p.2.1 ∈ Ico (-(c / 2)) (c / 2) :=
          (Set.mem_prod.1 (Set.mem_prod.1 hpS').2).1
        exact fibK1_mem.2 ⟨⟨hcon.1, hcon.2.1⟩, Set.mem_Ico.1 hq, abs_le.1 hcon.2.2⟩
      have h0 : (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (w p) (NearInst.merC (g p)) = 0 := by
        rw [hw0 p hband]
        simp
      rw [h0, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs1.le _) hM0)
        (Set.indicator_nonneg (fun q _ => norm_nonneg _) p)
  exact Integrable.mono' hdom hF hpt

/-- **Integrability of the two weak-pair pieces** (organizer task `PartIII-b:C/flatset/col/7/3/6/5`;
source 1650-1656, 1684-1689). -/
theorem weakPairPiecesIntegrable : WeakPairPiecesIntegrable := by
  intro c ν μ hc Φ hΦ g
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  have hΨ : ContDiff ℝ ∞ (zetaPhi Φ) := (zetaPhiMeridTest c hc Φ hΦ).smooth
  have hΨ0 : ∀ p : Profile, (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → zetaPhi Φ p = 0 := by
    intro p hp
    ext i
    simp [zetaPhi, hsupp p.1 p.2 i hp]
  have hU : IsOpen {x : Profile | x.1 < s1 ∨ s2 < x.1 ∨ R < |x.2.2|} := by
    rw [setOf_or, setOf_or]
    exact (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hΘ0 : ∀ p : Profile, (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) →
      resolventTest ν μ (zetaPhi Φ) p = 0 := by
    intro p hp
    apply wp_resolvent_zero
    exact Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx => hΨ0 x hx)
  refine ⟨?_, ?_⟩
  · exact wp_piece_integrable hc hs1 _ (wp_resolvent_continuous hΨ) hΘ0 g
  · exact wp_piece_integrable hc hs1 _ hΨ.continuous hΨ0 g

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
