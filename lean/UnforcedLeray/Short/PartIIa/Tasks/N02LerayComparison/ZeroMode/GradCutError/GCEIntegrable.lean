import UnforcedLeray.Short.PartIIa.Sub.N02_3_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.Cutoff

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Each function is either continuous (`errG`, `etaFz`) or the indicator of a closed `η`-window of
the norm of a continuous function (`winP`). All of them vanish outside the compact box
`A = [s₀,s₁] × [0,c] × [-R,R]` on the cell (`R = max (2L) L₀`), and `measureH c A ≠ ⊤`.
So each is in `L²(measureH c)` by `memLp_outside`.
Vanishing outside the `s`-band: `Φ = zPrimC f_z` vanishes for `s` outside the band, hence so do
`∂_s`, `∂_η`, `∂_q` of `Ψ = zCut L Φ`. Vanishing for `|η| > 2L`: `χ(η/L) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open ZeroGradCutErrorAux

namespace GCEIntegrableAux

theorem continuous_fst_P : Continuous fun p : Profile => p.1 := continuous_fst

theorem continuous_snd2_P : Continuous fun p : Profile => p.2.2 := continuous_snd.snd

/-! ### An `L²` criterion for bounded functions supported in a compact set of finite measure -/

theorem memLp_outside {μ : Measure Profile} {F : Profile → ℝ} (hF : Measurable F)
    {A : Set Profile} (hA : IsCompact A) (hμA : μ A ≠ ⊤) {C : ℝ}
    (hC : ∀ p ∈ A, ‖F p‖ ≤ C) (h0 : ∀ᵐ p ∂μ, p ∉ A → F p = 0) : MemLp F 2 μ := by
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hμA
  have h1 : MemLp (A.indicator F) 2 μ := by
    rw [memLp_indicator_iff_restrict hAm]
    refine MemLp.of_bound hF.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hAm] with p hp
    exact hC p hp
  refine MemLp.ae_eq ?_ h1
  filter_upwards [h0] with p hp
  by_cases hpA : p ∈ A
  · simp [hpA]
  · simp [hpA, hp hpA]

/-- The window integrand `1_{|η| ≤ 2L} N` of a continuous `N` vanishing for `s` outside the band. -/
theorem memLp_winP {s0 s1 c L R : ℝ} (hs0 : 0 < s0) (hR : 2 * L ≤ R) {N : Profile → ℝ}
    (hN : Continuous N) (hNz : ∀ p : Profile, p.1 ∉ Icc s0 s1 → N p = 0) :
    MemLp ({p : Profile | |p.2.2| ≤ 2 * L}.indicator N) 2 (measureH c) := by
  have hAc : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hμA : measureH c (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) ≠ ⊤ :=
    measureH_band_ne_top c hs0 s1 R
  have hS : MeasurableSet {p : Profile | |p.2.2| ≤ 2 * L} :=
    measurableSet_le (continuous_snd2_P.abs.measurable) measurable_const
  obtain ⟨C, hC⟩ := hAc.exists_bound_of_continuousOn hN.continuousOn
  refine memLp_outside (hN.measurable.indicator hS) hAc hμA (C := max C 0) ?_ ?_
  · intro p hp
    by_cases h : |p.2.2| ≤ 2 * L
    · rw [Set.indicator_of_mem (show p ∈ {p : Profile | |p.2.2| ≤ 2 * L} from h)]
      exact (hC p hp).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem (show p ∉ {p : Profile | |p.2.2| ≤ 2 * L} from h), norm_zero]
      exact le_max_right _ _
  · filter_upwards [ae_cell_measureH c] with p hp
    intro hpA
    by_cases h1 : p.1 ∈ Icc s0 s1
    · have hS' : p ∉ {p : Profile | |p.2.2| ≤ 2 * L} := fun hS' =>
        hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 ((show |p.2.2| ≤ 2 * L from hS').trans hR)⟩
      rw [Set.indicator_of_notMem hS']
    · have hS0 : N p = 0 := hNz p h1
      by_cases hS' : p ∈ {p : Profile | |p.2.2| ≤ 2 * L}
      · rw [Set.indicator_of_mem hS', hS0]
      · rw [Set.indicator_of_notMem hS']

/-! ### Coordinate derivatives -/

theorem hasDerivAt_q {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun q : ℝ => F (p.1, q, p.2.2)) (fderiv ℝ F p (0, 1, 0)) p.2.1 := by
  have hl : HasDerivAt (fun q : ℝ => ((p.1, q, p.2.2) : Profile)) ((0 : ℝ), (1 : ℝ), (0 : ℝ))
      p.2.1 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.1 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun q : ℝ => q) (1 : ℝ) p.2.1 := hasDerivAt_id' _
    have h3 : HasDerivAt (fun _ : ℝ => p.2.2) (0 : ℝ) p.2.1 := by apply hasDerivAt_const
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.2.1 hl

theorem hasDerivAt_s {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun σ : ℝ => F (σ, p.2.1, p.2.2)) (fderiv ℝ F p (1, 0, 0)) p.1 := by
  have hl : HasDerivAt (fun σ : ℝ => ((σ, p.2.1, p.2.2) : Profile)) ((1 : ℝ), (0 : ℝ), (0 : ℝ))
      p.1 := by
    have h1 : HasDerivAt (fun σ : ℝ => σ) (1 : ℝ) p.1 := hasDerivAt_id' _
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.1 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun _ : ℝ => p.2.2) (0 : ℝ) p.1 := by apply hasDerivAt_const
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.1 hl

theorem hasDerivAt_eta {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun η : ℝ => F (p.1, p.2.1, η)) (fderiv ℝ F p (0, 0, 1)) p.2.2 := by
  have hl : HasDerivAt (fun η : ℝ => ((p.1, p.2.1, η) : Profile)) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
      p.2.2 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun η : ℝ => η) (1 : ℝ) p.2.2 := hasDerivAt_id' _
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.2.2 hl

theorem pdS_zero_of {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile)
    (h : ∀ᶠ σ in 𝓝 p.1, F (σ, p.2.1, p.2.2) = 0) : pdS F p = 0 := by
  have h1 := hasDerivAt_s hF p
  have h2 : HasDerivAt (fun σ : ℝ => F (σ, p.2.1, p.2.2)) 0 p.1 :=
    (hasDerivAt_const p.1 (0 : ℂ)).congr_of_eventuallyEq h
  exact h1.unique h2

theorem pdEta_zero_of {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile)
    (h : ∀ᶠ η in 𝓝 p.2.2, F (p.1, p.2.1, η) = 0) : pdEta F p = 0 := by
  have h1 := hasDerivAt_eta hF p
  have h2 : HasDerivAt (fun η : ℝ => F (p.1, p.2.1, η)) 0 p.2.2 :=
    (hasDerivAt_const p.2.2 (0 : ℂ)).congr_of_eventuallyEq h
  exact h1.unique h2

theorem pdQ_zero_of_inv {F : Profile → ℂ} (hF : Differentiable ℝ F)
    (hI : ∀ s q q' η : ℝ, F (s, q, η) = F (s, q', η)) (p : Profile) : pdQ F p = 0 := by
  have hl := hasDerivAt_q hF p
  have hc : HasDerivAt (fun q : ℝ => F (p.1, q, p.2.2)) 0 p.2.1 := by
    have hfun : (fun q : ℝ => F (p.1, q, p.2.2)) = fun _ => F p := by
      funext q
      exact hI p.1 q p.2.1 p.2.2
    rw [hfun]
    exact hasDerivAt_const _ _
  exact hl.unique hc

/-! ### The cutoff primitive `Ψ = zCut L Φ` -/

theorem zCutProd_contDiff {L : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) := by
  have h1 : ContDiff ℝ ∞ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ZeroCutoffAux.zChi_contDiff.comp
      (show ContDiff ℝ ∞ (fun r : Profile => r.2.2 / L) from by fun_prop))
  exact h1.mul hΦ

theorem pdQ_zCut {L : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hQ : ∀ s q q' η : ℝ, Φ (s, q, η) = Φ (s, q', η)) (p : Profile) :
    pdQ (zCut L Φ) p = 0 := by
  refine pdQ_zero_of_inv ((zCutProd_contDiff hΦ).differentiable (by simp)) ?_ p
  intro s q q' η
  show ((zChi (η / L) : ℝ) : ℂ) * Φ (s, q, η) = ((zChi (η / L) : ℝ) : ℂ) * Φ (s, q', η)
  rw [hQ s q q' η]

theorem zPrimC_inv {c : ℝ} {f : Profile → MeridC} (hQ : QInvariant c f) (s q q' η : ℝ) :
    zPrimC (fun r => f r 1) (s, q, η) = zPrimC (fun r => f r 1) (s, q', η) := by
  show (∫ t in (0 : ℝ)..η, f (s, q, t) 1) = ∫ t in (0 : ℝ)..η, f (s, q', t) 1
  congr 1
  funext t
  rw [hQ s q q' t]

theorem pdX_continuous {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) (v : Profile) :
    Continuous (fun p => fderiv ℝ F p v) :=
  (hF.continuous_fderiv (by simp)).clm_apply continuous_const

theorem opS_continuous {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (opS F) :=
  continuous_fst_P.smul (pdX_continuous hF (1, 0, 0))

theorem opK_continuous {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (opK F) := by
  have h1 := pdX_continuous hF (1, 0, 0)
  have h2 := pdX_continuous hF (0, 0, 1)
  have e : opK F = fun p => (2 : ℝ) • (p.1 • fderiv ℝ F p (1, 0, 0))
      + p.2.2 • fderiv ℝ F p (0, 0, 1) := rfl
  rw [e]
  exact ((continuous_const (y := (2 : ℝ))).smul (continuous_fst_P.smul h1)).add (continuous_snd2_P.smul h2)

theorem vec2_continuous {x y : Profile → ℂ} (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun p => (!₂[x p, y p] : MeridC)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
    (Continuous.matrixVecCons hx (Continuous.matrixVecCons hy continuous_const))

theorem errG_continuous {ε L : ℝ} {f : Profile → MeridC}
    (hΦ : ContDiff ℝ ∞ (zPrimC (fun r => f r 1))) (hf : Continuous f) :
    Continuous (errG ε L f) := by
  have hΨ : ContDiff ℝ ∞ (zCut L (zPrimC (fun r => f r 1))) := zCutProd_contDiff hΦ
  have hcg : Continuous (cgradC ε (zCut L (zPrimC (fun r => f r 1)))) := by
    unfold cgradC
    exact vec2_continuous
      ((pdX_continuous hΨ (0, 1, 0)).sub (continuous_const.mul (opK_continuous hΨ)))
      (pdX_continuous hΨ (0, 0, 1))
  have hfc : Continuous (fun p : Profile => f p 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).continuous.comp hf
  have h0 : Continuous (fun p : Profile => (!₂[(0 : ℂ), f p 1] : MeridC)) :=
    vec2_continuous continuous_const hfc
  unfold errG
  exact h0.sub hcg

/-- If `f p 1 = 0` and the three derivatives of `Ψ` at `p` vanish, then `errG = 0` at `p`. -/
theorem errG_zero_of_derivs {ε L : ℝ} {f : Profile → MeridC} {p : Profile}
    (hf1 : f p 1 = 0) (hQ0 : pdQ (zCut L (zPrimC (fun r => f r 1))) p = 0)
    (hS0 : pdS (zCut L (zPrimC (fun r => f r 1))) p = 0)
    (hE0 : pdEta (zCut L (zPrimC (fun r => f r 1))) p = 0) :
    errG ε L f p = 0 := by
  have hopK0 : opK (zCut L (zPrimC (fun r => f r 1))) p = 0 := by
    unfold opK opS
    simp [hS0, hE0]
  have hz1 : (!₂[0, f p 1] : MeridC) = 0 := by
    ext i
    fin_cases i <;> simp [hf1]
  have hz2 : cgradC ε (zCut L (zPrimC (fun r => f r 1))) p = 0 := by
    unfold cgradC
    ext i
    fin_cases i <;> simp [hQ0, hopK0, hE0]
  unfold errG
  rw [hz1, hz2, sub_zero]

/-! ### The main theorem -/

open GCEIntegrableAux in
/-- **Square integrability of the four terms** (`GCEIntegrable`). -/
theorem gCEIntegrable : UnforcedLeray.Short.PartIIa.ZeroGradCutErrorAux.GCEIntegrable := by
  unfold ZeroGradCutErrorAux.GCEIntegrable
  intro hS hK c ε L f hε hL hc hf hQ
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hgS : ContDiff ℝ ∞ (fun r => f r 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hgb : ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ q : Profile, (fun r => f r 1) q ≠ 0 → q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L :=
    ⟨s0, s1, L0, hs0, fun q hq => hb q (fun h => hq (by simp [h]))⟩
  obtain ⟨hΦS, hΦE⟩ := hS (fun r => f r 1) hgS hgb
  have hcomm := hK (fun r => f r 1) hgS hgb
  have hΦd : Differentiable ℝ (zPrimC (fun r => f r 1)) := hΦS.differentiable (by simp)
  have hΦinv : ∀ s q q' η : ℝ, zPrimC (fun r => f r 1) (s, q, η)
      = zPrimC (fun r => f r 1) (s, q', η) := fun s q q' η => zPrimC_inv hQ s q q' η
  have hΨd : Differentiable ℝ (zCut L (zPrimC (fun r => f r 1))) :=
    (zCutProd_contDiff hΦS).differentiable (by simp)
  -- vanishing of `f` and of `Φ` outside the band
  have hfs : ∀ p : Profile, p.1 ∉ Icc s0 s1 → f p = 0 := fun p h => by
    by_contra hne
    exact h (hb p hne).1
  have hfη : ∀ p : Profile, L0 < |p.2.2| → f p = 0 := fun p h => by
    by_contra hne
    exact absurd (hb p hne).2 (not_le.2 h)
  have hΦs : ∀ σ q η : ℝ, σ ∉ Icc s0 s1 → zPrimC (fun r => f r 1) (σ, q, η) = 0 := by
    intro σ q η hσ
    have h0 : ∀ t : ℝ, f (σ, q, t) 1 = 0 := fun t => by
      rw [hfs (σ, q, t) hσ]
      simp
    unfold zPrimC
    simp [h0]
  have hΦs' : ∀ p : Profile, p.1 ∉ Icc s0 s1 → zPrimC (fun r => f r 1) p = 0 :=
    fun p h => hΦs p.1 p.2.1 p.2.2 h
  -- the constants
  have hR2 : 2 * L ≤ max (2 * L) L0 := le_max_left _ _
  have hRL0 : L0 ≤ max (2 * L) L0 := le_max_right _ _
  have hAc : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(max (2 * L) L0)) (max (2 * L) L0))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hμA : measureH c (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(max (2 * L) L0)) (max (2 * L) L0))) ≠ ⊤ :=
    measureH_band_ne_top c hs0 s1 (max (2 * L) L0)
  -- vanishing of `errG`
  have errS : ∀ p : Profile, p.1 ∉ Icc s0 s1 → errG ε L f p = 0 := by
    intro p h1
    refine errG_zero_of_derivs ?_ (pdQ_zCut hΦS hΦinv p) ?_ ?_
    · rw [hfs p h1]
      simp
    · refine pdS_zero_of hΨd p ?_
      have hopen : (Icc s0 s1)ᶜ ∈ 𝓝 p.1 := isClosed_Icc.isOpen_compl.mem_nhds h1
      filter_upwards [hopen] with σ hσ
      show ((zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (fun r => f r 1) (σ, p.2.1, p.2.2) = 0
      rw [hΦs σ p.2.1 p.2.2 hσ, mul_zero]
    · refine pdEta_zero_of hΨd p (Filter.Eventually.of_forall fun η => ?_)
      show ((zChi (η / L) : ℝ) : ℂ) * zPrimC (fun r => f r 1) (p.1, p.2.1, η) = 0
      rw [hΦs p.1 p.2.1 η h1, mul_zero]
  have errE : ∀ p : Profile, max (2 * L) L0 < |p.2.2| → errG ε L f p = 0 := by
    intro p hp
    have hz : ∀ σ q η : ℝ, 2 * L < |η| → zCut L (zPrimC (fun r => f r 1)) (σ, q, η) = 0 := by
      intro σ q η h
      have h2 : 2 ≤ |η / L| := by
        rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]
        linarith
      show ((zChi (η / L) : ℝ) : ℂ) * zPrimC (fun r => f r 1) (σ, q, η) = 0
      rw [ZeroCutoffAux.zChi_eq_zero h2]
      simp
    have hη2 : 2 * L < |p.2.2| := lt_of_le_of_lt hR2 hp
    refine errG_zero_of_derivs ?_ (pdQ_zCut hΦS hΦinv p) ?_ ?_
    · rw [hfη p (lt_of_le_of_lt hRL0 hp)]
      simp
    · refine pdS_zero_of hΨd p (Filter.Eventually.of_forall fun σ => ?_)
      exact hz σ p.2.1 p.2.2 hη2
    · refine pdEta_zero_of hΨd p ?_
      have hopen : {x : ℝ | 2 * L < |x|} ∈ 𝓝 p.2.2 :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hη2
      filter_upwards [hopen] with η' hη'
      exact hz p.1 p.2.1 η' hη'
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `‖errG‖`
    have hcont : Continuous (fun p => ‖errG ε L f p‖) :=
      (errG_continuous hΦS hf.smooth.continuous).norm
    obtain ⟨C1, hC1⟩ := hAc.exists_bound_of_continuousOn hcont.continuousOn
    refine memLp_outside hcont.measurable hAc hμA hC1 ?_
    filter_upwards [ae_cell_measureH c] with p hp
    intro hpA
    by_cases h1 : p.1 ∈ Icc s0 s1
    · have hη : max (2 * L) L0 < |p.2.2| := by
        by_contra hcon
        push_neg at hcon
        exact hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 hcon⟩
      rw [errE p hη, norm_zero]
    · rw [errS p h1, norm_zero]
  · -- the window `winP L (f_z)`
    have hwb : winP L (fun r => f r 1)
        = {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC (fun r => f r 1) p‖) := rfl
    rw [hwb]
    refine memLp_winP (s1 := s1) hs0 hR2 (N := fun p => ‖zPrimC (fun r => f r 1) p‖)
      hΦS.continuous.norm ?_
    intro p h1
    simp [hΦs' p h1]
  · -- the window `winP L (opS f_z)`
    have hwc : winP L (fun r => (opS (fun r' => f r' 1)) r)
        = {p : Profile | |p.2.2| ≤ 2 * L}.indicator
            (fun p => ‖opS (zPrimC (fun r => f r 1)) p‖) := by
      funext p
      unfold winP
      rw [hcomm]
    rw [hwc]
    refine memLp_winP (s1 := s1) hs0 hR2 (N := fun p => ‖opS (zPrimC (fun r => f r 1)) p‖)
      (opS_continuous hΦS).norm ?_
    intro p h1
    have hp0 : pdS (zPrimC (fun r => f r 1)) p = 0 := by
      refine pdS_zero_of hΦd p ?_
      have hopen : (Icc s0 s1)ᶜ ∈ 𝓝 p.1 := isClosed_Icc.isOpen_compl.mem_nhds h1
      filter_upwards [hopen] with σ hσ
      exact hΦs σ p.2.1 p.2.2 hσ
    show ‖p.1 • pdS (zPrimC (fun r => f r 1)) p‖ = 0
    rw [hp0, smul_zero, norm_zero]
  · -- the tail `etaFz f`
    have hcont : Continuous (etaFz f) := by
      unfold etaFz
      exact (continuous_snd2_P.abs).mul hgS.continuous.norm
    obtain ⟨C4, hC4⟩ := hAc.exists_bound_of_continuousOn hcont.continuousOn
    refine memLp_outside hcont.measurable hAc hμA hC4 ?_
    filter_upwards [ae_cell_measureH c] with p hp
    intro hpA
    have hz : f p 1 = 0 := by
      by_cases h1 : p.1 ∈ Icc s0 s1
      · have hη : max (2 * L) L0 < |p.2.2| := by
          by_contra hcon
          push_neg at hcon
          exact hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 hcon⟩
        rw [hfη p (lt_of_le_of_lt hRL0 hη)]
        simp
      · rw [hfs p h1]
        simp
    unfold etaFz
    rw [hz, norm_zero, mul_zero]

end GCEIntegrableAux

end UnforcedLeray.Short.PartIIa
