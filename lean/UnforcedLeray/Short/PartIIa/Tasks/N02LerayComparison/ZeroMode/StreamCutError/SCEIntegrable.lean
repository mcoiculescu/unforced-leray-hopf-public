import UnforcedLeray.Short.PartIIa.Sub.N02_3_8
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Twin of the `GCEIntegrable` step with index `0` (`f_r`) in place of `1` (`f_z`).

For a smooth band test `f`, with `Φ = zPrimC f_r` and `ψ = zCut L (-Φ)`, the error
`errS ε L f = (f_r, 0) - streamC ε ψ` is continuous and vanishes outside the closed box
`{s ∈ [s0,s1], |η| ≤ max (2L) L0}`: off the `s`-band `Φ` and `ψ` vanish, and for `|η| > 2L` the
cutoff `ψ` vanishes on the open set `{|η| > 2L}` (`zChi = 0` for `|t| ≥ 2`), so `streamC ε ψ`
vanishes there. The window terms are dominated by a constant times the indicator of a compact box
of finite `measureH c` mass. The term `|η| ‖f_r‖` is continuous and band supported.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

open ZeroGradCutErrorAux ZeroStreamCutErrorAux

namespace SCEIntAux

theorem zChi_contDiff : ContDiff ℝ ∞ zChi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem zChi_zero_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : zChi t = 0 := by
  unfold zChi
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [sq_abs t, abs_nonneg t]

theorem zPrimC_zero_off {g : Profile → ℂ} {s0 s1 L0 : ℝ}
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0) (q : Profile)
    (hq : q.1 ∉ Icc s0 s1) : zPrimC g q = 0 := by
  have h0 : ∀ t : ℝ, g (q.1, q.2.1, t) = 0 := fun t => by
    by_contra h
    exact hq (hb _ h).1
  unfold zPrimC
  simp [h0]

/-- A function vanishing outside a closed band has zero derivative outside the band. -/
theorem fderiv_eq_zero_of_notBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Profile → E) (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (p : Profile)
    (hp : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) : fderiv ℝ F p = 0 := by
  have hU : IsOpen ({q : Profile | q.1 < s0} ∪ {q : Profile | s1 < q.1} ∪
      {q : Profile | L < |q.2.2|}) := by
    have h1 : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
    have h2 : IsOpen {q : Profile | s1 < q.1} := isOpen_lt continuous_const continuous_fst
    have h3 : IsOpen {q : Profile | L < |q.2.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))
    exact (h1.union h2).union h3
  have h3 : p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2| := by
    by_contra h'
    push_neg at h'
    exact hp ⟨⟨h'.1, h'.2.1⟩, h'.2.2⟩
  have hpU : p ∈ ({q : Profile | q.1 < s0} ∪ {q : Profile | s1 < q.1} ∪
      {q : Profile | L < |q.2.2|}) := by
    rcases h3 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hev : F =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    by_contra hne
    obtain ⟨h1, h2⟩ := hb q hne
    rcases hq with (hq | hq) | hq
    · exact absurd h1.1 (not_le.2 hq)
    · exact absurd h1.2 (not_le.2 hq)
    · exact absurd h2 (not_le.2 hq)
  rw [hev.fderiv_eq (𝕜 := ℝ)]
  simp

theorem bandOpS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Profile → E) (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∀ p : Profile, opS F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  intro p hp
  by_contra hq
  apply hp
  unfold opS pdS
  rw [fderiv_eq_zero_of_notBand F s0 s1 L hb p hq]
  simp

theorem contDiffOpS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Profile → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (opS F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ F p (1, 0, 0)) :=
    h1.clm_apply contDiff_const
  exact contDiff_fst.smul h2

theorem cont_pdEta {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (pdEta F) := by
  have h1 : Continuous fun p => fderiv ℝ F p := hF.continuous_fderiv (by simp)
  unfold pdEta
  exact h1.clm_apply continuous_const

theorem cont_pdQ {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (pdQ F) := by
  have h1 : Continuous fun p => fderiv ℝ F p := hF.continuous_fderiv (by simp)
  unfold pdQ
  exact h1.clm_apply continuous_const

theorem cont_opK {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (opK F) := by
  have h1 : Continuous fun p => fderiv ℝ F p := hF.continuous_fderiv (by simp)
  have hS : Continuous (opS F) := by
    unfold opS pdS
    exact continuous_fst.smul (h1.clm_apply continuous_const)
  unfold opK
  exact (continuous_const.smul hS).add ((continuous_snd.comp continuous_snd).smul (cont_pdEta hF))

theorem continuous_mk' {a b : Profile → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun p : Profile => (!₂[a p, b p] : MeridC) := by
  have h : Continuous fun p : Profile => (![a p, b p] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
  exact (PiLp.continuous_toLp 2 _).comp h

theorem streamC_cont {ε : ℝ} {ψ : Profile → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (streamC ε ψ) := by
  unfold streamC
  exact continuous_mk' (cont_pdEta hψ).neg
    (((cont_pdQ hψ).sub (continuous_const.mul (cont_opK hψ))).add
      (continuous_const.mul hψ.continuous))

theorem streamC_zero_of {ε : ℝ} {ψ : Profile → ℂ} {s0 s1 L : ℝ}
    (hψb : ∀ q : Profile, ψ q ≠ 0 → q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L) (p : Profile)
    (hp : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) : streamC ε ψ p = 0 := by
  have hd := fderiv_eq_zero_of_notBand ψ s0 s1 L hψb p hp
  have hψp : ψ p = 0 := by
    by_contra h
    exact hp (hψb p h)
  have hpE : pdEta ψ p = 0 := by
    unfold pdEta
    rw [hd]
    simp
  have hpQ : pdQ ψ p = 0 := by
    unfold pdQ
    rw [hd]
    simp
  have hK : opK ψ p = 0 := by
    unfold opK opS pdS pdEta
    rw [hd]
    simp
  unfold streamC
  rw [hpE, hpQ, hK, hψp]
  ext i
  fin_cases i <;> simp

theorem psi_contDiff {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (L : ℝ) :
    ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-Φ p)) := by
  have h1 : ContDiff ℝ ∞ (fun p : Profile => zChi (p.2.2 / L)) :=
    zChi_contDiff.comp ((contDiff_snd.comp contDiff_snd).div_const L)
  have h2 : ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact h2.mul hΦ.neg

theorem psi_band {g : Profile → ℂ} {s0 s1 L0 L : ℝ} (hL : 0 < L)
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0) (q : Profile) :
    ((zChi (q.2.2 / L) : ℝ) : ℂ) * (-zPrimC g q) ≠ 0 → q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ 2 * L := by
  intro hq
  have hz : zChi (q.2.2 / L) ≠ 0 := by
    intro h
    apply hq
    simp [h]
  have hs : q.1 ∈ Icc s0 s1 := by
    by_contra h
    apply hq
    simp [zPrimC_zero_off hb q h]
  have hη : |q.2.2| ≤ 2 * L := by
    by_contra h
    push_neg at h
    apply hz
    apply zChi_zero_of_two_le
    rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]
    linarith
  exact ⟨hs, hη⟩

/-- A continuous function supported in the band `s0 ≤ s ≤ s1`, `|η| ≤ L` is in `L²(measureH c)`
(copy of `NearGradMemberAux.memLp_of_band`). -/
theorem memLp_band {c s0 s1 L : ℝ} {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopologyEither Profile E] {F : Profile → E} (hF : Continuous F)
    (hs0 : 0 < s0) (hz : ∀ p : Profile, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → F p = 0) :
    MemLp F 2 (measureH c) := by
  refine memLp_of_continuous_of_ae_vanish hF
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (measureH_band_ne_top c hs0 s1 L) ?_ 2
  filter_upwards [ae_cell_measureH c] with p hp hpA
  apply hz p
  intro hb
  exact hpA ⟨hb.1, Ioc_subset_Icc_self hp.2.1, abs_le.1 hb.2⟩

/-- `L²` membership of a window term `winP L h`, for `zPrimC h` continuous and vanishing off the
`s`-band. -/
theorem winP_memLp (c : ℝ) {s0 s1 L : ℝ} (hs0 : 0 < s0) {h : Profile → ℂ}
    (hcont : Continuous (zPrimC h)) (hz : ∀ q : Profile, q.1 ∉ Icc s0 s1 → zPrimC h q = 0) :
    MemLp (winP L h) 2 (measureH c) := by
  have hA : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hAm : MeasurableSet (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))) :=
    hA.isClosed.measurableSet
  have hAne : measureH c (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))) ≠ (⊤ : ℝ≥0∞) :=
    measureH_band_ne_top c hs0 s1 (2 * L)
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hcont.continuousOn
  have hmeas : Measurable (winP L h) := by
    unfold winP
    exact hcont.norm.measurable.indicator
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
        continuous_const).measurableSet
  refine MemLp.of_le
    (memLp_indicator_const 2 hAm (max C 0) (Or.inr hAne)) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_cell_measureH c] with p hp
  have hq : p.2.1 ∈ Icc 0 c := Ioc_subset_Icc_self hp.2.1
  have key : winP L h p ≤
      (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))).indicator (fun _ => max C 0) p := by
    by_cases hpA : p ∈ Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))
    · rw [Set.indicator_of_mem hpA]
      unfold winP
      by_cases hη : |p.2.2| ≤ 2 * L
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hη, if_true]
        exact (hC p hpA).trans (le_max_left _ _)
      · simp [Set.indicator_apply, hη]
    · have hz0 : winP L h p = 0 := by
        by_cases hs : p.1 ∈ Icc s0 s1
        · have hη : ¬ (|p.2.2| ≤ 2 * L) := fun hη => hpA ⟨hs, hq, abs_le.1 hη⟩
          unfold winP
          simp [Set.indicator_apply, hη]
        · unfold winP
          simp [hz p hs]
      rw [hz0]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) p
  have hI : 0 ≤ (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-(2 * L)) (2 * L))).indicator
      (fun _ => max C 0) p := Set.indicator_nonneg (fun _ _ => le_max_right _ _) p
  rw [Real.norm_of_nonneg (winP_nonneg L h p), Real.norm_of_nonneg hI]
  exact key

end SCEIntAux

open SCEIntAux in
/-- **Target `PartII-a:N02/3/8/2`**: square-integrability of the error and of the three terms. -/
theorem sCEIntegrable : UnforcedLeray.Short.PartIIa.ZeroStreamCutErrorAux.SCEIntegrable := by
  unfold ZeroStreamCutErrorAux.SCEIntegrable
  intro hS _hK c ε L f _hε hL _hc hf _hq
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hg0S : ContDiff ℝ ∞ (fun r => f r 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hg0c : Continuous (fun r => f r 0) := hg0S.continuous
  have hb0 : ∀ p : Profile, (fun r => f r 0) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    fun p hp => hb p (fun h => hp (by simp [h]))
  obtain ⟨hΦS, -⟩ := hS (fun r => f r 0) hg0S ⟨s0, s1, L0, hs0, hb0⟩
  have hΦc : Continuous (zPrimC (fun r => f r 0)) := hΦS.continuous
  have hΦz : ∀ q : Profile, q.1 ∉ Icc s0 s1 → zPrimC (fun r => f r 0) q = 0 :=
    fun q hq' => zPrimC_zero_off hb0 q hq'
  have hψS : ContDiff ℝ ∞ (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) := by
    unfold zCut
    exact psi_contDiff hΦS L
  have hψb : ∀ q : Profile, zCut L (fun r => -zPrimC (fun r' => f r' 0) r) q ≠ 0 →
      q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ 2 * L :=
    fun q hq' => psi_band hL hb0 q hq'
  have hErr : Continuous (errS ε L f) := by
    unfold errS
    exact (continuous_mk' hg0c continuous_const).sub (streamC_cont hψS)
  have part1 : MemLp (fun p => ‖errS ε L f p‖) 2 (measureH c) := by
    refine memLp_band (c := c) (s0 := s0) (s1 := s1) (L := max (2 * L) L0) hErr.norm hs0 ?_
    intro p hp
    have hnot : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ 2 * L) := fun h =>
      hp ⟨h.1, h.2.trans (le_max_left _ _)⟩
    have hfp : f p = 0 := by
      by_contra h
      obtain ⟨h1, h2⟩ := hb p h
      exact hp ⟨h1, h2.trans (le_max_right _ _)⟩
    have hst := streamC_zero_of (ε := ε) hψb p hnot
    have hz0 : (!₂[f p 0, 0] : MeridC) = 0 := by
      ext i
      fin_cases i <;> simp [hfp]
    show ‖errS ε L f p‖ = 0
    unfold errS
    rw [hst, sub_zero, hz0, norm_zero]
  have part2 : MemLp (winP L (fun r => f r 0)) 2 (measureH c) :=
    winP_memLp c hs0 hΦc hΦz
  have part3 : MemLp (winP L (fun r => (opS (fun r' => f r' 0)) r)) 2 (measureH c) := by
    have hgO : ContDiff ℝ ∞ (opS (fun r' => f r' 0)) := contDiffOpS hg0S
    have hgOb : ∀ p : Profile, opS (fun r' => f r' 0) p ≠ 0 →
        p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
      bandOpS (fun r' => f r' 0) s0 s1 L0 hb0
    obtain ⟨hPS, -⟩ := hS (opS (fun r' => f r' 0)) hgO ⟨s0, s1, L0, hs0, hgOb⟩
    exact winP_memLp c hs0 hPS.continuous (fun q hq' => zPrimC_zero_off hgOb q hq')
  have part4 : MemLp (etaFr f) 2 (measureH c) := by
    have hEta : Continuous (etaFr f) := by
      unfold etaFr
      exact (continuous_abs.comp (continuous_snd.comp continuous_snd)).mul hg0c.norm
    refine memLp_band (c := c) (s0 := s0) (s1 := s1) (L := L0) hEta hs0 ?_
    intro p hp
    have hfp : f p = 0 := by
      by_contra h
      obtain ⟨h1, h2⟩ := hb p h
      exact hp ⟨h1, h2⟩
    unfold etaFr
    simp [hfp]
  exact ⟨part1, part2, part3, part4⟩

end UnforcedLeray.Short.PartIIa
