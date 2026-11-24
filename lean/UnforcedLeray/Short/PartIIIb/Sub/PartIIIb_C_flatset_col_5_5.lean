import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5

/-!
# Decomposition of `FcvFubini` (source 4610)

`FcvFubini` is the Fubini exchange on the triangle `{0 < t < ρ ≤ s}` for
`f(t,ρ) = t^μ ℓ_ρ(𝒰(ρ,t) g_B(t))` (source `shorter-proof-2026-11-02.tex` 4610, with `ξ_B` from
4605-4612).  It follows from four analytic inputs:

* `FcvEllCLM` : for `r > 0` the functional `ℓ_r` is a bounded real-linear functional of `X_{m,c}`
  (source 2819-2836: `flowIntegrand` is real-linear in `(ω, u)`, `kcC` real-linear and bounded);
* `FcvBochnerInt` : `t ↦ t^μ 𝒰(ρ,t) g_B(t)` is Bochner integrable on `(0, ρ]` in `X_{m,c}`
  (`xiD_apply`, `locBdd`, local boundedness of `gBD`);
* `FcvTriMeas` : the joint function is a.e.-strongly measurable on the triangle;
* `FcvTriBound` : it is bounded there (the constant of `ℓ_ρ`, `locBdd`, bound of `gBD`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **`ℓ_r` is a bounded real-linear functional** (source 2819-2836): for a cylinder test `φ`
and `r > 0`, `ω ↦ ℓ_r(ω)` is given by a continuous `ℝ`-linear map `X_{m,c} → ℂ`.  Route: linearity
of `flowIntegrand` in `(ω,u)`, real linearity of `xFn`, `kcC`, integrability (`CellPairBound`,
`IIIa.flowIntegrand` bounds) and the cell `L¹` bound of `xFn`; see task `col/5/4` (`ellFn_le`). -/
def FcvEllCLM : Prop :=
  ∀ (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (tr : UnforcedLeray.B0140.TrainSol ν c)
    (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ r : ℝ, 0 < r →
      ∃ Λ : Xmc c m →L[ℝ] ℂ, ∀ w : Xmc c m, ellFn tr φ r w = Λ w

/-- **Bochner integrability of the Duhamel integrand** (source 4610): for `ρ > 0` the map
`t ↦ t^μ 𝒰(ρ,t) g_B(t)` is integrable on `(0, ρ]` (it is strongly measurable by `jointCont` and the
continuity of `gBD` on `(0,∞)`, and bounded by `locBdd`, `t^μ ≤ ρ^μ`, and the local bound of
`gBD`: `B` is `O(t^{3/2})`, `bmatBound`, as in `FcvGInt`). -/
def FcvBochnerInt : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) • D.ev.U ρ t (gBD D (Bmat ν μ χf A) t))
        (Ioc 0 ρ)

/-- **Joint measurability on the triangle** (source 4610): `(t,ρ) ↦ t^μ ℓ_ρ(𝒰(ρ,t) g_B(t))` is
a.e.-strongly measurable on `{0 < t < ρ ≤ s}`.  Route: Carathéodory-type argument; continuity in
`ρ` of `ℓ_ρ` (the train is smooth, `φ` compactly supported), measurability of `t ↦ g_B(t)`
(continuous on `(0,∞)`), `TrainEvolution.jointCont`, `locBdd` (equicontinuity), and the uniform
bound of `FcvEllCLM`; or realise it as a limit of a jointly continuous sequence. -/
def FcvTriMeas : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => ((p.1 : ℂ) ^ (μ : ℂ)) *
          ellFn tr φ p.2 (D.ev.U p.2 p.1 (gBD D (Bmat ν μ χf A) p.1)))
        (volume.restrict {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ s})

/-- **Boundedness on the triangle** (source 4610): `‖ℓ_ρ(𝒰(ρ,t) g_B(t))‖ ≤ C` for
`0 < t < ρ ≤ s`.  Route: `‖ℓ_ρ ω‖ ≤ C_s ‖ω‖` uniformly for `ρ ∈ (0,s]` (`ellFn_le`, task
`col/5/4`), `‖𝒰(ρ,t)‖ ≤ C` (`locBdd`), `‖gBD D (Bmat ..) t‖ ≤ C` on `(0,s]` (`FcvGInt` proof,
`bmatBound`). -/
def FcvTriBound : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν c m : ℝ) [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (D : FlatInstData κ ν c m tr) (μ as : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3), 0 < ν → 0 < μ → IsSourceCutoffC χf → IsAffElem as A →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, ∀ t ρ : ℝ, 0 < t → t < ρ → ρ ≤ s →
        ‖ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t))‖ ≤ C

/-- Pulling a bounded real-linear functional through the weighted Bochner integral. -/
theorem slice_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Λ : E →L[ℝ] ℂ) (v : ℝ → E) (μ ρ : ℝ) (hρ : 0 < ρ)
    (hint : IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) • v t) (Ioc 0 ρ)) :
    ∫ t in Ioc 0 ρ, ((t : ℂ) ^ (μ : ℂ)) * Λ (v t) =
      ((ρ : ℂ) ^ (μ : ℂ)) *
        Λ (((ρ : ℂ) ^ (-(μ : ℂ))) • ∫ t in Ioc 0 ρ, ((t : ℂ) ^ (μ : ℂ)) • v t) := by
  have hreal : ∀ x : ℝ, 0 < x → ∀ y : ℝ, ∀ w : E, (((x : ℂ) ^ (y : ℂ)) • w : E) = (x ^ y) • w := by
    intro x hx y w
    rw [← Complex.ofReal_cpow hx.le y, Complex.coe_smul]
  have h1 : ∫ t in Ioc 0 ρ, ((t : ℂ) ^ (μ : ℂ)) * Λ (v t) =
      ∫ t in Ioc 0 ρ, Λ (((t : ℂ) ^ (μ : ℂ)) • v t) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hreal t ht.1 μ, map_smul, ← Complex.ofReal_cpow ht.1.le μ]
    simp [Complex.real_smul]
  rw [h1, ContinuousLinearMap.integral_comp_comm Λ hint]
  have h2 : ((ρ : ℂ) ^ (-(μ : ℂ))) = (((ρ ^ (-μ) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cpow hρ.le]; push_cast; rfl
  have h3 : ((ρ : ℂ) ^ (μ : ℂ)) = (((ρ ^ μ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cpow hρ.le]
  rw [h2, h3, Complex.coe_smul, map_smul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add hρ]
  simp

theorem fcvFubini_of (h1 : FcvEllCLM) (h2 : FcvBochnerInt) (h3 : FcvTriMeas)
    (h4 : FcvTriBound) : FcvFubini := by
  intro κ ν c m _ _ tr D μ as χf A hν hμ hχ hA φ hφ s hs
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ s} with hT
  set f : ℝ → ℝ → ℂ := fun t ρ => ((t : ℂ) ^ (μ : ℂ)) *
    ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) with hf
  have hTm : MeasurableSet T := by
    have a1 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
    have a2 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have a3 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ s} := measurableSet_le measurable_snd measurable_const
    exact a1.inter (a2.inter a3)
  have hTsub : T ⊆ Icc 0 s ×ˢ Icc 0 s := by
    intro p hp
    exact ⟨⟨hp.1.le, (hp.2.1.trans_le hp.2.2).le⟩, ⟨(hp.1.trans hp.2.1).le, hp.2.2⟩⟩
  have hTfin : volume T ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hTsub) ?_)
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [ENNReal.mul_lt_top]
  obtain ⟨C, hC⟩ := h4 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) T := by
    haveI : IsFiniteMeasure (volume.restrict T) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hTfin⟩
    refine Integrable.mono' (integrable_const (s ^ μ * |C|))
      (h3 κ ν c m tr D μ as χf A hν hμ hχ hA φ hφ s hs) ?_
    refine ae_restrict_of_forall_mem hTm fun p hp => ?_
    obtain ⟨hp1, hp2, hp3⟩ := hp
    simp only [hf, norm_mul]
    have e1 : ‖((p.1 : ℂ) ^ (μ : ℂ))‖ ≤ s ^ μ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp1]
      simp only [Complex.ofReal_re]
      exact Real.rpow_le_rpow hp1.le (hp2.le.trans hp3) hμ.le
    have e2 := (hC p.1 p.2 hp1 hp2 hp3).trans (le_abs_self C)
    exact mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
  have hF : Integrable (T.indicator fun p : ℝ × ℝ => f p.1 p.2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hTm).2 hint
  -- the slices
  have hslice1 : ∀ t : ℝ, ∫ ρ, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) =
      (Ioc 0 s).indicator (fun t => ∫ ρ in Ioc t s, f t ρ) t := by
    intro t
    by_cases ht0 : 0 < t
    · have : ∀ ρ, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) =
          (Ioc t s).indicator (f t) ρ := by
        intro ρ
        by_cases hρ : ρ ∈ Ioc t s
        · have hm : (t, ρ) ∈ T := ⟨ht0, hρ.1, hρ.2⟩
          rw [indicator_of_mem hρ, indicator_of_mem hm]
        · rw [indicator_of_notMem hρ, indicator_of_notMem]
          intro h; exact hρ ⟨h.2.1, h.2.2⟩
      simp_rw [this]
      rw [integral_indicator measurableSet_Ioc]
      by_cases hts : t ≤ s
      · rw [indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht0, hts⟩)]
      · rw [indicator_of_notMem (show t ∉ Ioc 0 s from fun h => hts h.2), Ioc_eq_empty (not_lt.2 (not_le.1 hts).le)]
        simp
    · rw [indicator_of_notMem (show t ∉ Ioc 0 s from fun h => ht0 h.1)]
      have : ∀ ρ, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) = 0 := by
        intro ρ; exact indicator_of_notMem (fun h => ht0 h.1) _
      simp [this]
  have hslice2 : ∀ ρ : ℝ, ∫ t, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) =
      (Ioc 0 s).indicator (fun ρ => ((ρ : ℂ) ^ (μ : ℂ)) *
        ellFn tr φ ρ (xiD D (μ : ℂ) (Bmat ν μ χf A) ρ)) ρ := by
    intro ρ
    by_cases hρ : ρ ∈ Ioc 0 s
    · have : ∀ t, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) =
          (Ioo 0 ρ).indicator (fun t => f t ρ) t := by
        intro t
        by_cases ht : t ∈ Ioo 0 ρ
        · have hm : (t, ρ) ∈ T := ⟨ht.1, ht.2, hρ.2⟩
          rw [indicator_of_mem ht, indicator_of_mem hm]
        · rw [indicator_of_notMem ht, indicator_of_notMem]
          intro h; exact ht ⟨h.1, h.2.1⟩
      simp_rw [this]
      rw [integral_indicator measurableSet_Ioo, indicator_of_mem hρ, ← integral_Ioc_eq_integral_Ioo]
      obtain ⟨Λ, hΛ⟩ := h1 ν c m tr φ hφ ρ hρ.1
      have := slice_commute Λ (fun t => D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) μ ρ hρ.1
        (h2 κ ν c m tr D μ as χf A hν hμ hχ hA ρ hρ.1)
      simp only [hf, hΛ]
      refine this.trans ?_
      rfl
    · rw [indicator_of_notMem hρ]
      have : ∀ t, T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ) = 0 := by
        intro t
        refine indicator_of_notMem (fun h => hρ ⟨h.1.trans h.2.1, h.2.2⟩) _
      simp [this]
  have hG : Integrable (Ioc 0 s |>.indicator fun t => ∫ ρ in Ioc t s, f t ρ) := by
    have := hF.integral_prod_left
    simpa only [hslice1] using this
  have hmain := integral_integral_swap (f := fun t ρ => T.indicator (fun p : ℝ × ℝ => f p.1 p.2) (t, ρ))
    (by rw [Measure.volume_eq_prod] at *; exact hF)
  simp only [hslice1, hslice2] at hmain
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc] at hmain
  have hinner : ∀ t : ℝ, ((t : ℂ) ^ (μ : ℂ)) *
      ∫ ρ in Ioc t s, ellFn tr φ ρ (D.ev.U ρ t (gBD D (Bmat ν μ χf A) t)) = ∫ ρ in Ioc t s, f t ρ := by
    intro t; simp only [hf]; rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hinner]
    exact (integrable_indicator_iff measurableSet_Ioc).1 hG
  · simp_rw [hinner]
    exact hmain

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
