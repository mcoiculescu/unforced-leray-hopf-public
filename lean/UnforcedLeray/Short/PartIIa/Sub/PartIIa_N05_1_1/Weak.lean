import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Deriv

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1P

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)

/-- Measurable, band-supported (`s ∈ [s0, s1]`, `|η| ≤ L`, `s0 > 0`) and bounded on the cell. -/
def Nice (c : ℝ) (ψ : Profile → MeridC) : Prop :=
  Measurable ψ ∧ ∃ s0 s1 L C : ℝ, 0 < s0 ∧
    (∀ p, ψ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) ∧ ∀ p ∈ cell c, ‖ψ p‖ ≤ C

theorem integrable_inner_periodize {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC)
    {ψ : Profile → MeridC} (hψ : Nice c ψ) :
    Integrable (fun p => inner ℂ (periodize c (W : Profile → MeridC) p) (ψ p))
      (cellMeasure c) := by
  obtain ⟨hm, s0, s1, L, C, hs0, hband, hC⟩ := hψ
  have hC0 : 0 ≤ C :=
    (norm_nonneg _).trans (hC ((1 : ℝ), c, (0 : ℝ)) ⟨show (0:ℝ) < 1 from one_pos, ⟨hc, le_refl c⟩, Set.mem_univ _⟩)
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKm : MeasurableSet K := hK.measurableSet
  let g : Profile → ℝ := K.indicator 1
  have hgm : Measurable g := measurable_const.indicator hKm
  have hgB : ∀ p, |g p| ≤ 1 := fun p => by
    by_cases h : p ∈ K <;> simp [g, h]
  have hgs : ∀ p, g p ≠ 0 → s0 ≤ p.1 ∧ p.1 ≤ max s1 s0 := fun p hp => by
    have : p ∈ K := by by_contra h; exact hp (by simp [g, h])
    exact ⟨this.1.1, this.1.2.trans (le_max_left _ _)⟩
  have hmem := memLp_cutRep hc hs0 (le_max_right s1 s0) hgs hgB hgm W
  have hfin : cellMeasure c K < ⊤ := by
    unfold cellMeasure
    rw [Measure.restrict_apply hKm]
    exact (measure_mono inter_subset_left).trans_lt hK.measure_lt_top
  have : IsFiniteMeasure ((cellMeasure c).restrict K) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hfin⟩
  have hintK : IntegrableOn (fun p => ‖cutRep c g W p‖) K (cellMeasure c) :=
    (hmem.norm.restrict K).integrable one_le_two
  have hint : Integrable (fun p => ‖cutRep c g W p‖) (cellMeasure c) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hintK
    intro p hp
    by_contra h
    exact hp (by simp [cutRep, g, h])
  refine Integrable.mono' (hint.const_mul C) ?_ ?_
  · exact (((Lp.stronglyMeasurable W).measurable.comp
      (measurable_fst.prodMk (((measurable_reduceIoc c).comp
        (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))).aestronglyMeasurable).inner hm.aestronglyMeasurable
  · unfold cellMeasure
    refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun p hp => ?_)
    by_cases h0 : ψ p = 0
    · simp only [h0, inner_zero_right, norm_zero]
      positivity
    · have hpK : p ∈ K := by
        obtain ⟨h1, h2⟩ := hband p h0
        exact ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩
      calc ‖inner ℂ (periodize c (W : Profile → MeridC) p) (ψ p)‖
          ≤ ‖periodize c (W : Profile → MeridC) p‖ * ‖ψ p‖ := norm_inner_le_norm _ _
        _ ≤ ‖periodize c (W : Profile → MeridC) p‖ * C :=
            mul_le_mul_of_nonneg_left (hC p hp) (norm_nonneg _)
        _ = C * ‖cutRep c g W p‖ := by
            simp [cutRep, g, hpK, mul_comm]

/-! ### Coordinate derivatives and product rules -/

theorem fderiv_fst_apply (p v : Profile) : fderiv ℝ (fun p : Profile => p.1) p v = v.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ) (p := p)).fderiv]; rfl

theorem fderiv_eta_apply (p v : Profile) : fderiv ℝ (fun p : Profile => p.2.2) p v = v.2.2 := by
  have h : HasFDerivAt (fun p : Profile => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd (𝕜 := ℝ)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  rw [h.fderiv]; rfl

theorem fderiv_smul_apply {g : Profile → ℝ} {f : Profile → MeridC} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (p v : Profile) :
    fderiv ℝ (fun p => g p • f p) p v = g p • fderiv ℝ f p v + (fderiv ℝ g p v) • f p := by
  rw [fderiv_fun_smul (hg.differentiable (by simp) p) (hf.differentiable (by simp) p)]
  simp

theorem pdS_smul {g : Profile → ℝ} {f : Profile → MeridC} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (p : Profile) :
    pdS (fun p => g p • f p) p = g p • pdS f p + pdS g p • f p := fderiv_smul_apply hg hf p _

theorem pdQ_smul {g : Profile → ℝ} {f : Profile → MeridC} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (p : Profile) :
    pdQ (fun p => g p • f p) p = g p • pdQ f p + pdQ g p • f p := fderiv_smul_apply hg hf p _

theorem pdEta_smul {g : Profile → ℝ} {f : Profile → MeridC} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (p : Profile) :
    pdEta (fun p => g p • f p) p = g p • pdEta f p + pdEta g p • f p := fderiv_smul_apply hg hf p _

theorem pdS_fst (p : Profile) : pdS (fun p : Profile => p.1) p = 1 := by simp [pdS, fderiv_fst_apply]
theorem pdQ_fst (p : Profile) : pdQ (fun p : Profile => p.1) p = 0 := by simp [pdQ, fderiv_fst_apply]
theorem pdEta_fst (p : Profile) : pdEta (fun p : Profile => p.1) p = 0 := by
  simp [pdEta, fderiv_fst_apply]
theorem pdS_eta (p : Profile) : pdS (fun p : Profile => p.2.2) p = 0 := by
  simp [pdS, fderiv_eta_apply]
theorem pdQ_eta (p : Profile) : pdQ (fun p : Profile => p.2.2) p = 0 := by
  simp [pdQ, fderiv_eta_apply]
theorem pdEta_eta (p : Profile) : pdEta (fun p : Profile => p.2.2) p = 1 := by
  simp [pdEta, fderiv_eta_apply]

/-! ### Closure of the test class -/

/-- Smooth `q`-periodic real multipliers. -/
def SP (c : ℝ) (g : Profile → ℝ) : Prop := ContDiff ℝ ∞ g ∧ QPeriodic c g

theorem SP.pd {c : ℝ} {g : Profile → ℝ} (hg : SP c g) (v : Profile) :
    SP c (fun p => fderiv ℝ g p v) :=
  ⟨(hg.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, fun p => by
    show fderiv ℝ g _ v = fderiv ℝ g p v
    rw [qPeriodic_fderiv hg.2 p]⟩

theorem SP.fst (c : ℝ) : SP c (fun p : Profile => p.1) := ⟨contDiff_fst, fun _ => rfl⟩
theorem SP.eta (c : ℝ) : SP c (fun p : Profile => p.2.2) :=
  ⟨contDiff_snd.comp contDiff_snd, fun _ => rfl⟩
theorem SP.const (c r : ℝ) : SP c (fun _ : Profile => r) := ⟨contDiff_const, fun _ => rfl⟩
theorem SP.mul {c : ℝ} {g h : Profile → ℝ} (hg : SP c g) (hh : SP c h) :
    SP c (fun p => g p * h p) :=
  ⟨hg.1.mul hh.1, fun p => by
    show g _ * h _ = g p * h p
    rw [hg.2 p, hh.2 p]⟩
theorem SP.add {c : ℝ} {g h : Profile → ℝ} (hg : SP c g) (hh : SP c h) :
    SP c (fun p => g p + h p) :=
  ⟨hg.1.add hh.1, fun p => by
    show g _ + h _ = g p + h p
    rw [hg.2 p, hh.2 p]⟩
theorem SP.sub {c : ℝ} {g h : Profile → ℝ} (hg : SP c g) (hh : SP c h) :
    SP c (fun p => g p - h p) :=
  ⟨hg.1.sub hh.1, fun p => by
    show g _ - h _ = g p - h p
    rw [hg.2 p, hh.2 p]⟩
theorem SP.of_cutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) :
    SP c χ := ⟨hχ.smooth, hχ.periodic⟩

theorem fderiv_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    {s0 s1 L : ℝ} (hb : ∀ p, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) {p : Profile}
    (h : fderiv ℝ f p ≠ 0) : p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  have hcl : IsClosed {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hts : tsupport f ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    closure_minimal (fun p hp => hb p hp) hcl
  exact hts (support_fderiv_subset ℝ h)

theorem mt_add {c : ℝ} {f g : Profile → MeridC} (hf : IsMeridTest c f) (hg : IsMeridTest c g) :
    IsMeridTest c (fun p => f p + g p) := by
  refine ⟨hf.smooth.add hg.smooth, fun p => ?_, ?_⟩
  · show f _ + g _ = f p + g p
    rw [hf.periodic p, hg.periodic p]
  · obtain ⟨a0, a1, aL, ha0, ha⟩ := hf.band
    obtain ⟨b0, b1, bL, hb0, hb⟩ := hg.band
    refine ⟨min a0 b0, max a1 b1, max aL bL, lt_min ha0 hb0, fun p hp => ?_⟩
    by_cases h1 : f p = 0
    · have h2 : g p ≠ 0 := fun h2 => hp (by simp [h1, h2])
      obtain ⟨u, v⟩ := hb p h2
      exact ⟨⟨(min_le_right _ _).trans u.1, u.2.trans (le_max_right _ _)⟩,
        v.trans (le_max_right _ _)⟩
    · obtain ⟨u, v⟩ := ha p h1
      exact ⟨⟨(min_le_left _ _).trans u.1, u.2.trans (le_max_left _ _)⟩,
        v.trans (le_max_left _ _)⟩

theorem mt_sub {c : ℝ} {f g : Profile → MeridC} (hf : IsMeridTest c f) (hg : IsMeridTest c g) :
    IsMeridTest c (fun p => f p - g p) := by
  refine ⟨hf.smooth.sub hg.smooth, fun p => ?_, ?_⟩
  · show f _ - g _ = f p - g p
    rw [hf.periodic p, hg.periodic p]
  · obtain ⟨a0, a1, aL, ha0, ha⟩ := hf.band
    obtain ⟨b0, b1, bL, hb0, hb⟩ := hg.band
    refine ⟨min a0 b0, max a1 b1, max aL bL, lt_min ha0 hb0, fun p hp => ?_⟩
    by_cases h1 : f p = 0
    · have h2 : g p ≠ 0 := fun h2 => hp (by simp [h1, h2])
      obtain ⟨u, v⟩ := hb p h2
      exact ⟨⟨(min_le_right _ _).trans u.1, u.2.trans (le_max_right _ _)⟩,
        v.trans (le_max_right _ _)⟩
    · obtain ⟨u, v⟩ := ha p h1
      exact ⟨⟨(min_le_left _ _).trans u.1, u.2.trans (le_max_left _ _)⟩,
        v.trans (le_max_left _ _)⟩

theorem mt_smul {c : ℝ} {g : Profile → ℝ} {f : Profile → MeridC} (hg : SP c g)
    (hf : IsMeridTest c f) : IsMeridTest c (fun p => g p • f p) := by
  refine ⟨hg.1.smul hf.smooth, fun p => ?_, ?_⟩
  · show g _ • f _ = g p • f p
    rw [hg.2 p, hf.periodic p]
  · obtain ⟨a0, a1, aL, ha0, ha⟩ := hf.band
    exact ⟨a0, a1, aL, ha0, fun p hp => ha p (fun h0 => hp (by simp [h0]))⟩

theorem mt_fderiv {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) (v : Profile) :
    IsMeridTest c (fun p => fderiv ℝ f p v) := by
  refine ⟨(hf.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, fun p => ?_, ?_⟩
  · show fderiv ℝ f _ v = fderiv ℝ f p v
    rw [qPeriodic_fderiv hf.periodic p]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
    refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
    have hne : fderiv ℝ f p ≠ 0 := fun h0 => hp (by simp [h0])
    exact fderiv_band hb hne

theorem mt_pdS {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) : IsMeridTest c (pdS f) :=
  mt_fderiv hf (1, 0, 0)
theorem mt_pdQ {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) : IsMeridTest c (pdQ f) :=
  mt_fderiv hf (0, 1, 0)
theorem mt_pdEta {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) :
    IsMeridTest c (pdEta f) := mt_fderiv hf (0, 0, 1)

theorem mt_opK {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) : IsMeridTest c (opK f) :=
  mt_add (mt_smul (SP.const c 2) (mt_smul (SP.fst c) (mt_pdS hf)))
    (mt_smul (SP.eta c) (mt_pdEta hf))

theorem SP.pdS {c : ℝ} {g : Profile → ℝ} (hg : SP c g) : SP c (pdS g) := hg.pd (1, 0, 0)
theorem SP.pdQ {c : ℝ} {g : Profile → ℝ} (hg : SP c g) : SP c (pdQ g) := hg.pd (0, 1, 0)
theorem SP.pdEta {c : ℝ} {g : Profile → ℝ} (hg : SP c g) : SP c (pdEta g) := hg.pd (0, 0, 1)

/-! ### The functional `Lam` -/

theorem nice_of_mt {c : ℝ} (hc : 0 < c) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Nice c φ := by
  refine ⟨hφ.smooth.continuous.measurable, ?_⟩
  obtain ⟨s0, s1, L, hs0, hb⟩ := hφ.band
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hφ.smooth.continuous.continuousOn
  refine ⟨s0, s1, L, max C0 0, hs0, hb, fun p hp => ?_⟩
  by_cases h0 : φ p = 0
  · simp [h0]
  · obtain ⟨h1, h2⟩ := hb p h0
    exact (hC0 p ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩).trans (le_max_left _ _)

theorem nice_C_nonneg {c : ℝ} (hc : 0 < c) {ψ : Profile → MeridC} {C : ℝ}
    (hC : ∀ p ∈ cell c, ‖ψ p‖ ≤ C) : 0 ≤ C :=
  (norm_nonneg _).trans (hC ((1 : ℝ), c, (0 : ℝ))
    ⟨show (0 : ℝ) < 1 from one_pos, ⟨hc, le_refl c⟩, Set.mem_univ _⟩)

theorem nice_sinv {c : ℝ} (hc : 0 < c) {ψ : Profile → MeridC} (hψ : Nice c ψ) :
    Nice c (fun p => p.1⁻¹ • ψ p) := by
  obtain ⟨hm, s0, s1, L, C, hs0, hb, hC⟩ := hψ
  have hC0 := nice_C_nonneg hc hC
  refine ⟨measurable_fst.inv.smul hm, s0, s1, L, s0⁻¹ * C, hs0,
    fun p hp => hb p (fun h0 => hp (by simp [h0])), fun p hp => ?_⟩
  by_cases h0 : ψ p = 0
  · simp only [h0, smul_zero, norm_zero]; positivity
  · have h1 := (hb p h0).1
    have hp0 : 0 < p.1 := lt_of_lt_of_le hs0 h1.1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp0.le)]
    exact mul_le_mul (inv_anti₀ hs0 h1.1) (hC p hp) (norm_nonneg _) (by positivity)

/-- `Λ_W(ψ) = ∫ ⟨periodize W, ψ⟩` over the cell. -/
def Lam (c : ℝ) (W : HSpace c MeridC) (ψ : Profile → MeridC) : ℂ :=
  ∫ p, inner ℂ (periodize c (W : Profile → MeridC) p) (ψ p) ∂(cellMeasure c)

theorem Lam_add {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) {f g : Profile → MeridC}
    (hf : Nice c f) (hg : Nice c g) :
    Lam c W (fun p => f p + g p) = Lam c W f + Lam c W g := by
  unfold Lam
  simp only [inner_add_right]
  exact integral_add (integrable_inner_periodize hc W hf) (integrable_inner_periodize hc W hg)

theorem Lam_sub {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) {f g : Profile → MeridC}
    (hf : Nice c f) (hg : Nice c g) :
    Lam c W (fun p => f p - g p) = Lam c W f - Lam c W g := by
  unfold Lam
  simp only [inner_sub_right]
  exact integral_sub (integrable_inner_periodize hc W hf) (integrable_inner_periodize hc W hg)

theorem Lam_smul {c : ℝ} (W : HSpace c MeridC) (r : ℝ) (f : Profile → MeridC) :
    Lam c W (fun p => r • f p) = (r : ℂ) * Lam c W f := by
  unfold Lam
  have h : (fun p => inner ℂ (periodize c (W : Profile → MeridC) p) (r • f p)) =
      fun p => (r : ℂ) * inner ℂ (periodize c (W : Profile → MeridC) p) (f p) := by
    funext p; simp
  rw [h]
  exact integral_const_mul _ _

theorem Lam_congr {c : ℝ} (W : HSpace c MeridC) {f g : Profile → MeridC}
    (h : ∀ p ∈ cell c, f p = g p) : Lam c W f = Lam c W g := by
  unfold Lam cellMeasure
  exact setIntegral_congr_fun (measurableSet_cell c) (fun p hp => by rw [h p hp])

theorem weakS_lam {c : ℝ} {w Sw : HSpace c MeridC} (h : N05_1_1Org.WeakS c w Sw)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Lam c Sw (fun p => p.1⁻¹ • φ p) = -Lam c w (pdS φ) := by
  have := h φ hφ
  unfold Lam
  rw [← this]
  congr 1
  funext p
  simp [dsFromS]

theorem weakE_lam {c : ℝ} {w Ew : HSpace c MeridC} (h : N05_1_1Org.WeakEta c w Ew)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Lam c Ew φ = -Lam c w (pdEta φ) := h φ hφ

theorem weakQ_lam {c ε : ℝ} {w Qw : HSpace c MeridC} (h : N05_1_1Org.WeakQ c ε w Qw)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Lam c Qw φ = -Lam c w (fun p => pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)) := h φ hφ

end N05_1_1P

end UnforcedLeray.Short.PartIIa
