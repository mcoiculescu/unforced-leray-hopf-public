import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.ChartLiftPairing
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LocalIntegrable
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_4
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness

/-!
# Cross-exponent uniqueness of the physical response (`PartII-b:T18/1` helper)

Source of record: `the November 2 reference manuscript`, lines 1912-1938, 1992-2004.

Proves that if `F₁ ∈ H_{r₁}` and `F₂ ∈ H_{r₂}` agree `dm c`-a.e., then their physical responses
`b₁ ∈ H_{r₁}` and `b₂ ∈ H_{r₂}` agree Lebesgue-a.e. on `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.HrOpHelp

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- If `F₁, F₂` agree a.e. on `{s > 0}` and are `q`-periodic and measurable, their ring lifts
`NvC ε⁻¹ F₁` and `NvC ε⁻¹ F₂` agree a.e. on `ℝ × Space`. -/
theorem nvC_ae_eq_of_ae_pos {c ε r₁ r₂ : ℝ} (hc : 0 < c) (hε : 0 < ε) {F₁ F₂ : CProf}
    (hF₁ : InHr c r₁ F₁) (hF₂ : InHr c r₂ F₂)
    (h12 : ∀ᵐ x : Coord, 0 < x.1 → F₁ x = F₂ x) :
    NvC ε⁻¹ F₁ =ᵐ[volume] NvC ε⁻¹ F₂ := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  obtain ⟨F₁', M₁, -, -, hM₁m, hM₁0, hM₁per, hFF₁⟩ :=
    periodicRepresentative c r₁ hc F₁ hF₁.periodic hF₁.meas
  obtain ⟨F₂', M₂, -, -, hM₂m, hM₂0, hM₂per, hFF₂⟩ :=
    periodicRepresentative c r₂ hc F₂ hF₂.periodic hF₂.meas
  obtain ⟨M₀, hZM₀, hM₀m, hM₀0⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 h12)
  have hM₀per_null : ∀ k : ℤ, volume ((fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) ⁻¹' M₀) = 0 := by
    intro k
    have hmp : MeasurePreserving (fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) volume volume :=
      (MeasurePreserving.id volume).prod
        ((measurePreserving_add_right volume ((k : ℝ) * c)).prod (MeasurePreserving.id volume))
    exact hmp.quasiMeasurePreserving.preimage_null hM₀0
  set M₃ : Set Coord := ⋃ k : ℤ, (fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) ⁻¹' M₀
  have hM₃m : MeasurableSet M₃ := MeasurableSet.iUnion fun k =>
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).add_const _ |>.prodMk
      (measurable_snd.comp measurable_snd))) hM₀m
  have hM₃0 : volume M₃ = 0 := measure_iUnion_null hM₀per_null
  have hM₃per : ∀ s q η, (s, (q + c, η)) ∈ M₃ ↔ (s, (q, η)) ∈ M₃ := by
    intro s q η
    simp only [M₃, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      push_cast
      convert hk using 2
      ext <;> simp; ring
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      push_cast
      convert hk using 2
      ext <;> simp; ring
  have hNull₁ := NvCInYrHelp.chart_null_all (P := 2 * ε * c) hR hc hP M₁ hM₁m hM₁0 hM₁per
  have hNull₂ := NvCInYrHelp.chart_null_all (P := 2 * ε * c) hR hc hP M₂ hM₂m hM₂0 hM₂per
  have hNull₃ := NvCInYrHelp.chart_null_all (P := 2 * ε * c) hR hc hP M₃ hM₃m hM₃0 hM₃per
  have hax : ∀ᵐ x : ℝ × Space, x.2 ∉ Axi.axis :=
    (Measure.quasiMeasurePreserving_snd).ae Axi.ae_not_mem_axis
  filter_upwards [hNull₁, hNull₂, hNull₃, hax] with x hx₁ hx₂ hx₃ hxax
  have hpos : 0 < (Axi.chart ε⁻¹ x.1 x.2).1 := Axi.age_pos hR0 hxax
  have hx₀ : Axi.chart ε⁻¹ x.1 x.2 ∉ M₀ := by
    intro hm
    apply hx₃
    refine mem_iUnion.2 ⟨0, ?_⟩
    simpa using hm
  have h12x : F₁ (Axi.chart ε⁻¹ x.1 x.2) = F₂ (Axi.chart ε⁻¹ x.1 x.2) := by
    by_contra hne
    exact hx₀ (hZM₀ fun h => hne (h hpos))
  simp only [NvC, Axi.Nv, h12x]

/-- Consistency of `phasePair` against `lerayY` across two exponents `q₁, q₂` for a common
pointwise representative `f`. -/
theorem phasePair_lerayY_consistent {P : ℝ} [Fact (0 < P)] {q₁ q₂ : ℝ≥0∞}
    [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] (h1₁ : 1 < q₁) (hq₁ : q₁ ≠ ⊤) (h1₂ : 1 < q₂) (hq₂ : q₂ ≠ ⊤)
    {f : ℝ × Space → CVec3} {Ff₁ : Yq P q₁} {Ff₂ : Yq P q₂}
    (hF₁ : HasRepY Ff₁ f) (hF₂ : HasRepY Ff₂ f) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q₁ Φ (lerayY P q₁ h1₁ hq₁ Ff₁) = phasePair P q₂ Φ (lerayY P q₂ h1₂ hq₂ Ff₂) := by
  rw [phasePair_eq_periodIntegral hΦ, phasePair_eq_periodIntegral hΦ]
  congr 1
  have hP0 : (0 : ℝ) < P := Fact.out
  have hτ₁ : ∀ᵐ τ ∂(volume : Measure (AddCircle P)),
      lerayY P q₁ h1₁ hq₁ Ff₁ τ = lerayC q₁ h1₁ hq₁ (Ff₁ τ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 hP0).ne']
    exact coeFn_lerayY h1₁ hq₁ Ff₁
  have hτ₂ : ∀ᵐ τ ∂(volume : Measure (AddCircle P)),
      lerayY P q₂ h1₂ hq₂ Ff₂ τ = lerayC q₂ h1₂ hq₂ (Ff₂ τ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 hP0).ne']
    exact coeFn_lerayY h1₂ hq₂ Ff₂
  have hae₁ := (AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae
    (p := fun τ : AddCircle P => lerayY P q₁ h1₁ hq₁ Ff₁ τ = lerayC q₁ h1₁ hq₁ (Ff₁ τ)) hτ₁
  have hae₂ := (AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae
    (p := fun τ : AddCircle P => lerayY P q₂ h1₂ hq₂ Ff₂ τ = lerayC q₂ h1₂ hq₂ (Ff₂ τ)) hτ₂
  apply integral_congr_ae
  filter_upwards [hae₁, hae₂, ae_restrict_of_ae hF₁.slice, ae_restrict_of_ae hF₂.slice]
    with t ht₁ ht₂ hs₁ hs₂
  rw [ht₁, ht₂]
  have hmp₁ : MemLp (fun y => f (t, y)) q₁ volume :=
    (Lp.memLp (Ff₁ (t : AddCircle P))).ae_eq hs₁.symm
  have hmp₂ : MemLp (fun y => f (t, y)) q₂ volume :=
    (Lp.memLp (Ff₂ (t : AddCircle P))).ae_eq hs₂.symm
  have hto₁ : hmp₁.toLp (fun y => f (t, y)) = Ff₁ (t : AddCircle P) := by
    apply Lp.ext
    exact hmp₁.coeFn_toLp.trans hs₁
  have hto₂ : hmp₂.toLp (fun y => f (t, y)) = Ff₂ (t : AddCircle P) := by
    apply Lp.ext
    exact hmp₂.coeFn_toLp.trans hs₂
  have hcons := lerayC_consistent h1₁ hq₁ h1₂ hq₂ hmp₁ hmp₂
  rw [hto₁, hto₂] at hcons
  refine integral_congr_ae ?_
  filter_upwards [hcons] with y hy
  rw [hy]

/-- Cross-exponent uniqueness of free responses to a common datum `f ∈ Y_{r₁} ∩ Y_{r₂}` on phase tests. -/
theorem freeResponse_pairF_unique_cross {ν : ℝ} {μ : ℂ} {r₁ r₂ P : ℝ}
    {f w₁ w₂ : ℝ × Space → CVec3} (hP : 0 < P) (hν : 0 < ν)
    (hr₁1 : 1 < r₁) (hr₁3 : r₁ < 3) (hr₂1 : 1 < r₂) (hr₂3 : r₂ < 3)
    (hμ₁ : 0 < μ.re + (3 / r₁ - 1) / 2) (hμ₂ : 0 < μ.re + (3 / r₂ - 1) / 2)
    (hf₁ : IsInYr P r₁ f) (hf₂ : IsInYr P r₂ f)
    (hw₁ : IsFreeResponse ν μ r₁ P f w₁) (hw₂ : IsFreeResponse ν μ r₂ P f w₂)
    {Φ₀ : ℝ × Space → CVec3} (hΦ₀ : IsPhaseTest P Φ₀) :
    pairF P Φ₀ w₁ = pairF P Φ₀ w₂ := by
  have : Fact (0 < P) := ⟨hP⟩
  have hr₁0 : 0 < r₁ := by linarith
  have hr₂0 : 0 < r₂ := by linarith
  set q₁ := ENNReal.ofReal r₁
  set q₂ := ENNReal.ofReal r₂
  have h1₁' : 1 < q₁ := ENNReal.one_lt_ofReal.2 hr₁1
  have h1₂' : 1 < q₂ := ENNReal.one_lt_ofReal.2 hr₂1
  have hq₁ : q₁ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq₂ : q₂ ≠ ⊤ := ENNReal.ofReal_ne_top
  have : Fact (1 ≤ q₁) := ⟨h1₁'.le⟩
  have : Fact (1 ≤ q₂) := ⟨h1₂'.le⟩
  have h3₁' : q₁ < 3 := ofReal_lt_three hr₁3
  have h3₂' : q₂ < 3 := ofReal_lt_three hr₂3
  have hμ₁' : 0 < μ.re + gammaR q₁ := by rw [gammaR_ofReal hr₁0.le]; exact hμ₁
  have hμ₂' : 0 < μ.re + gammaR q₂ := by rw [gammaR_ofReal hr₂0.le]; exact hμ₂
  obtain ⟨Ff₁, hF₁, -⟩ := exists_hasRepY P r₁ hr₁0 f hf₁
  obtain ⟨Ff₂, hF₂, -⟩ := exists_hasRepY P r₂ hr₂0 f hf₂
  obtain ⟨W₁, hW₁, -⟩ := exists_hasRepY P r₁ hr₁0 w₁ hw₁.mem_w
  obtain ⟨W₂, hW₂, -⟩ := exists_hasRepY P r₂ hr₂0 w₂ hw₂.mem_w
  obtain ⟨-, D₁, -, b₁⟩ := (isFreeResponse_iff hr₁0 lerayPairSol solSeparation hr₁1 hF₁ hW₁).1 hw₁
  obtain ⟨-, D₂, -, b₂⟩ := (isFreeResponse_iff hr₂0 lerayPairSol solSeparation hr₂1 hF₂ hW₂).1 hw₂
  have hop₁ : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) W₁ (lerayY P q₁ h1₁' hq₁ Ff₁) := by
    intro Φ hΦ
    dsimp only
    have := phasePair_bodyOp μ ⟨W₁, D₁⟩ hΦ
    rw [b₁] at this
    have heq : (fun x => L0T ν Φ x + μ • Φ x) = (μ • Φ + L0T ν Φ) := by
      funext x; simp [Pi.add_apply, add_comm]
    rw [← heq]
    exact this.symm
  have hop₂ : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) W₂ (lerayY P q₂ h1₂' hq₂ Ff₂) := by
    intro Φ hΦ
    dsimp only
    have := phasePair_bodyOp μ ⟨W₂, D₂⟩ hΦ
    rw [b₂] at this
    have heq : (fun x => L0T ν Φ x + μ • Φ x) = (μ • Φ + L0T ν Φ) := by
      funext x; simp [Pi.add_apply, add_comm]
    rw [← heq]
    exact this.symm
  obtain ⟨Ψ, hsm, hper, heq, C, hC⟩ :=
    adjResolventSolution P ν hν μ (re_add_one_pos h1₁' hq₁ hμ₁') Φ₀ hΦ₀
  have hΨ_of : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ → 0 < μ.re + gammaR q →
      IsPhaseSchwartz P (conjExp q) Ψ := by
    intro q _ h1q hqt hμq
    have hs := decay_exponent h1q hqt hμq
    have hqc : conjExp q ≠ ⊤ := conjExp_ne_top h1q
    have hS := fun G (hG : Continuous G) (hb : ∀ (τ : ℝ) (y : Space),
        ‖G (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 * (μ.re + 1)))) =>
      sliceContOfDecay (conjExp q) hqc (2 * (μ.re + 1)) C hs G hG hb
    have hΨc : SliceCont (conjExp q) Ψ := hS Ψ hsm.continuous fun τ y => (hC τ y).1
    have hdy : ∀ j, SliceCont (conjExp q) (dy j Ψ) := fun j =>
      hS _ (contDiff_dy hsm j).continuous fun τ y => (hC τ y).2.1 j
    have hlap : SliceCont (conjExp q) (lapT Ψ) :=
      hS _ (continuous_finsetSum _ fun j _ => (contDiff_dy (contDiff_dy hsm j) j).continuous)
        fun τ y => (hC τ y).2.2
    have hdrift : driftT Ψ = Φ₀ + (-μ + (1 / 2 : ℂ)) • Ψ + (ν : ℂ) • lapT Ψ := by
      funext p
      have := heq p
      simp only [L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [← this]
      have h1' : ((ν : ℂ)) • lapT Ψ p = ν • lapT Ψ p := Complex.coe_smul _ _
      have h2' : ((1 / 2 : ℂ)) • Ψ p = (1 / 2 : ℝ) • Ψ p := by
        rw [← Complex.coe_smul]; norm_num
      rw [h1', add_smul, neg_smul, h2']
      abel
    refine ⟨hsm, hper, hΨc, hdy, hlap, ?_⟩
    rw [hdrift]
    exact ((hΦ₀.sliceCont (conjExp q)).add (hΨc.const_smul _)).add (hlap.const_smul _)
  have hΨ₁ : IsPhaseSchwartz P (conjExp q₁) Ψ := hΨ_of q₁ h1₁' hq₁ hμ₁'
  have hΨ₂ : IsPhaseSchwartz P (conjExp q₂) Ψ := hΨ_of q₂ h1₂' hq₂ hμ₂'
  have hext₁ := hasPhaseOp_body_extend h1₁' μ ν hop₁ hΨ₁
  have hext₂ := hasPhaseOp_body_extend h1₂' μ ν hop₂ hΨ₂
  have heq' : μ • Ψ + L0T ν Ψ = Φ₀ := funext heq
  rw [heq', phasePair_eq_pairF_of_hasRepY W₁ w₁ hW₁ hΦ₀] at hext₁
  rw [heq', phasePair_eq_pairF_of_hasRepY W₂ w₂ hW₂ hΦ₀] at hext₂
  rw [hext₁, hext₂]
  have c₁ : Tendsto (fun n => phasePair P q₁ (mulT (cutχ n) Ψ) (lerayY P q₁ h1₁' hq₁ Ff₁)) atTop
      (𝓝 (phasePair P q₁ Ψ (lerayY P q₁ h1₁' hq₁ Ff₁))) :=
    (((phasePairing P q₁).flip (lerayY P q₁ h1₁' hq₁ Ff₁)).continuous.tendsto _).comp
      (tendsto_cut (conjExp_ne_top h1₁') hΨ₁)
  have c₂ : Tendsto (fun n => phasePair P q₂ (mulT (cutχ n) Ψ) (lerayY P q₂ h1₂' hq₂ Ff₂)) atTop
      (𝓝 (phasePair P q₂ Ψ (lerayY P q₂ h1₂' hq₂ Ff₂))) :=
    (((phasePairing P q₂).flip (lerayY P q₂ h1₂' hq₂ Ff₂)).continuous.tendsto _).comp
      (tendsto_cut (conjExp_ne_top h1₂') hΨ₂)
  have hseq : (fun n => phasePair P q₁ (mulT (cutχ n) Ψ) (lerayY P q₁ h1₁' hq₁ Ff₁)) =
      fun n => phasePair P q₂ (mulT (cutχ n) Ψ) (lerayY P q₂ h1₂' hq₂ Ff₂) :=
    funext fun n =>
      phasePair_lerayY_consistent h1₁' hq₁ h1₂' hq₂ hF₁ hF₂ (hΨ₁.isPhaseTest_cut n)
  rw [hseq] at c₁
  exact tendsto_nhds_unique c₁ c₂

/-- Cross-exponent uniqueness of the physical response profile on `{s > 0}`. -/
theorem physResponse_unique_cross {c ε ν r₁ r₂ : ℝ} {μ : ℂ} {F₁ F₂ b₁ b₂ : CProf}
    (hc : 0 < c) (hε : 0 < ε) (hν : 0 < ν)
    (hr₁1 : 1 < r₁) (hr₁3 : r₁ < 3) (hr₂1 : 1 < r₂) (hr₂3 : r₂ < 3)
    (hμ₁ : 0 < μ.re + (3 / r₁ - 1) / 2) (hμ₂ : 0 < μ.re + (3 / r₂ - 1) / 2)
    (hF₁ : InHr c r₁ F₁) (hF₂ : InHr c r₂ F₂) (hFF : F₁ =ᵐ[dm c] F₂)
    (hb₁ : InHr c r₁ b₁) (hresp₁ : IsResponse ν c ε μ r₁ F₁ b₁)
    (hb₂ : InHr c r₂ b₂) (hresp₂ : IsResponse ν c ε μ r₂ F₂ b₂) :
    ∀ᵐ x : Coord, 0 < x.1 → b₁ x = b₂ x := by
  have hP : 0 < 2 * ε * c := by positivity
  have hr₁0 : 0 < r₁ := by linarith
  have hr₂0 : 0 < r₂ := by linarith
  have hFF_pos : ∀ᵐ x : Coord, 0 < x.1 → F₁ x = F₂ x :=
    CongrHelp.ae_volume_of_ageμ hc hF₁.periodic hF₂.periodic hFF
  have hNvF : NvC ε⁻¹ F₁ =ᵐ[volume] NvC ε⁻¹ F₂ :=
    nvC_ae_eq_of_ae_pos hc hε hF₁ hF₂ hFF_pos
  have hf₁ : IsInYr (2 * ε * c) r₁ (NvC ε⁻¹ F₁) := nvCInYr_proof c ε r₁ F₁ hc hε hr₁0 hF₁
  have hf₂' : IsInYr (2 * ε * c) r₂ (NvC ε⁻¹ F₂) := nvCInYr_proof c ε r₂ F₂ hc hε hr₂0 hF₂
  have hf₂ : IsInYr (2 * ε * c) r₂ (NvC ε⁻¹ F₁) := FreeRespCongrHelp.isInYr_congr hNvF.symm hf₂'
  have hresp₂' : IsFreeResponse ν μ r₂ (2 * ε * c) (NvC ε⁻¹ F₁) (NvC ε⁻¹ b₂) :=
    freeResponseCongr_proof ν μ r₂ (2 * ε * c) (NvC ε⁻¹ F₂) (NvC ε⁻¹ F₁)
      (NvC ε⁻¹ b₂) (NvC ε⁻¹ b₂) hP hNvF.symm (EventuallyEq.refl _ _) hresp₂
  have hcomp : ∀ i : Fin 2, ∀ᵐ x : Coord, 0 < x.1 → b₁ x i = b₂ x i := by
    intro i
    have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
    have hloc₁ : LocallyIntegrableOn (fun x => b₁ x i) DriftWeakSHelp.Upos volume :=
      DriftWeakSHelp.locInt_of_tests (fun x => b₁ x i)
        (fun φ hφ => hrLocalIntegrable_proof c r₁ b₁ φ i hc hr₁1 hb₁ hφ)
    have hloc₂ : LocallyIntegrableOn (fun x => b₂ x i) DriftWeakSHelp.Upos volume :=
      DriftWeakSHelp.locInt_of_tests (fun x => b₂ x i)
        (fun φ hφ => hrLocalIntegrable_proof c r₂ b₂ φ i hc hr₂1 hb₂ hφ)
    have hloc : LocallyIntegrableOn (fun x => b₁ x i - b₂ x i) DriftWeakSHelp.Upos volume :=
      hloc₁.sub hloc₂
    have htest : ∀ φ : Coord → ℝ, IsCoordTest φ →
        ∫ x, (b₁ x i - b₂ x i) * (φ x : ℂ) = 0 := by
      intro φ hφ
      have hA : Integrable (fun x => b₁ x i * (φ x : ℂ)) :=
        hrLocalIntegrable_proof c r₁ b₁ φ i hc hr₁1 hb₁ hφ
      have hB : Integrable (fun x => b₂ x i * (φ x : ℂ)) :=
        hrLocalIntegrable_proof c r₂ b₂ φ i hc hr₂1 hb₂ hφ
      have hsub : ∫ x, (b₁ x i - b₂ x i) * (φ x : ℂ) =
          (∫ x, b₁ x i * (φ x : ℂ)) - ∫ x, b₂ x i * (φ x : ℂ) := by
        rw [← integral_sub hA hB]
        congr 1; funext x; ring
      have hΦ : IsPhaseTest (2 * ε * c) (ChartLift.liftTest c ε φ i) :=
        ChartLift.liftTest_isPhaseTest ChartLift.liftNice_proof φ i hc hε hφ
      have hp₁ := liftPairing_proof c ε r₁ φ i hc hε hr₁1 hφ b₁ hb₁
      have hp₂ := liftPairing_proof c ε r₂ φ i hc hε hr₂1 hφ b₂ hb₂
      have heq := freeResponse_pairF_unique_cross hP hν hr₁1 hr₁3 hr₂1 hr₂3 hμ₁ hμ₂
        hf₁ hf₂ hresp₁ hresp₂' hΦ
      rw [hsub, ← hp₁, ← hp₂, heq, sub_self]
    have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
      intro χ hχs hχc hχU
      have hχt : IsCoordTest χ := ⟨hχs, hχc, hχU⟩
      have hχ := htest χ hχt
      simp only [Complex.real_smul]
      convert hχ using 2
      funext x; ring)
    filter_upwards [hae] with x hx hpos
    exact sub_eq_zero.1 (hx (DriftWeakSHelp.mem_Upos.2 hpos))
  filter_upwards [hcomp 0, hcomp 1] with x hx0 hx1 hpos
  ext i
  fin_cases i
  · exact hx0 hpos
  · exact hx1 hpos

end UnforcedLeray.Short.IIb.HrOpHelp

end
