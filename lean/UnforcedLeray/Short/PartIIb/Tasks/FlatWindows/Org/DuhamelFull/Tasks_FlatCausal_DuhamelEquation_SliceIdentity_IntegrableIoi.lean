import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.IntegrableIoi
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Slice_Support

/-!
# Part II-b, task `PartII-b:T12/7/6/2` (`dfe_deqPairIntegrableIoi`)

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`flatTranspose ν μ Ψ` vanishes off a box `[σ,H] × [-R,R]²` with `σ > 0` (`dfe_deqAbsSupport`), so
`deqPair ν μ g Ψ t s = 0` unless `s ∈ [σ,H]`; for `s ∈ [σ,H]`, `s > t`, the box bound of the heat
flow uniform in the age (`flatHeatBoxBound_of`) gives a bound independent of `s`; `s ↦ deqPair`
is measurable by joint measurability of the heat flow of a strongly measurable representative.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dfe_deqPair_aesm_aux (ν : ℝ) (μ : ℂ) (t : ℝ) (g : ℝ × ℝ → CMerid)
    (hg : AEStronglyMeasurable g volume) (Ψ : Coord → Fin 2 → ℝ) (hΨ : IsPlanarTestDfe Ψ) :
    AEStronglyMeasurable (fun s : ℝ => deqPair ν μ g Ψ t s) volume := by
  have hg0s : StronglyMeasurable (hg.mk g) := hg.stronglyMeasurable_mk
  have hG's : StronglyMeasurable (fun p : Coord => hg.mk g p.2) :=
    hg0s.comp_measurable measurable_snd
  have hH := (deqam_flatHeat_stronglyMeasurable ν hG's).measurable
  have hH2 : Measurable (fun x : Coord => flatHeat (ν * (x.1 - t)) g x.2) := by
    have h1 := hH.comp (measurable_const.prodMk measurable_id :
      Measurable (fun x : Coord => ((t, x) : ℝ × Coord)))
    have e : (fun x : Coord => flatHeat (ν * (x.1 - t)) g x.2) =
        fun x : Coord => flatHeat (ν * (x.1 - t)) (hg.mk g) x.2 := by
      funext x; rw [flatHeat_eq_mk_aux _ g hg]
    rw [e]; exact h1
  have hcomp : ∀ i : Fin 2, Measurable (fun x : Coord => flatHeat (ν * (x.1 - t)) g x.2 i) :=
    fun i => ((EuclideanSpace.proj i).continuous.measurable).comp hH2
  have hT : ∀ i : Fin 2, Measurable (fun x : Coord => flatTranspose ν μ Ψ x i) :=
    fun i => (dfe_deqTransposeTest ν μ hΨ i).1.measurable
  have hf : Measurable (fun x : Coord =>
      ∑ i : Fin 2, flatHeat (ν * (x.1 - t)) g x.2 i * flatTranspose ν μ Ψ x i) :=
    Finset.measurable_sum _ (fun i _ => (hcomp i).mul (hT i))
  have := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))).aestronglyMeasurable
    (μ := (volume : Measure ℝ))
  exact this

theorem dfe_deqPairIntegrableIoi : UnforcedLeray.Short.IIb.dfe_DeqPairIntegrableIoi := by
  intro ν μ c r t hν ht hc hr g hg Ψ hΨ
  obtain ⟨σ, H, R, K, hσ, hK, hKb⟩ := dfe_deqAbsSupport ν μ Ψ hΨ
  obtain ⟨C, hC⟩ := flatHeatBoxBound_of periodicBoxBound flatHeatAEMeas r c R hr.le hc
  set N := eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) with hN
  have hNt : N ≠ ⊤ := hg.2.2.ne
  set E : ℝ≥0∞ := ENNReal.ofReal K * (ENNReal.ofReal C * N) with hE
  have hEt : E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNt)
  have hbd : ∀ s : ℝ, t < s → ‖deqPair ν μ g Ψ t s‖ ≤ E.toReal := by
    intro s hs
    have h1 := deqPair_bound_aux ν μ c r t hν hc hr g hg Ψ σ H R K hK hKb C
      (fun θ g' hθ hp hm => hC θ g' hθ hp hm) s hs
    have h2 : ‖deqPair ν μ g Ψ t s‖ₑ ≤ E := by
      refine h1.trans ?_
      split_ifs
      · exact le_rfl
      · exact zero_le
    have := ENNReal.toReal_mono hEt h2
    rwa [toReal_enorm] at this
  -- power factor bound on `[σ, H]`
  have hcontp : ContinuousOn (fun s : ℝ => s ^ (-μ.re)) (Icc σ H) :=
    fun s hs => (Real.continuousAt_rpow_const _ _ (Or.inl (hσ.trans_le hs.1).ne')).continuousWithinAt
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontp
  set M : ℝ := max M1 0 * E.toReal with hM
  have hmeas : AEStronglyMeasurable (fun s : ℝ => ((s : ℂ) ^ (-μ)) * deqPair ν μ g Ψ t s)
      (volume.restrict (Ioi t)) := by
    have h1 : Measurable (fun s : ℝ => ((s : ℂ) ^ (-μ))) :=
      Complex.measurable_ofReal.pow_const (-μ)
    exact (h1.aestronglyMeasurable).mul
      ((dfe_deqPair_aesm_aux ν μ t g hg.2.1 Ψ hΨ).restrict)
  have hdom : Integrable (fun s : ℝ => (Icc σ H).indicator (fun _ => M) s) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine Integrable.mono' hdom.integrableOn hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hst : t < s := hs
  by_cases hsm : s ∈ Icc σ H
  · rw [Set.indicator_of_mem hsm, norm_mul]
    have hs0 : 0 < s := hσ.trans_le hsm.1
    have hp : ‖(s : ℂ) ^ (-μ)‖ ≤ max M1 0 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0]
      have := hM1 s hsm
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs0 _)] at this
      simpa using this.trans (le_max_left _ _)
    exact mul_le_mul hp (hbd s hst) (norm_nonneg _) (le_max_right _ _)
  · rw [Set.indicator_of_notMem hsm]
    have h1 := deqPair_bound_aux ν μ c r t hν hc hr g hg Ψ σ H R K hK hKb C
      (fun θ g' hθ hp hm => hC θ g' hθ hp hm) s hst
    rw [if_neg hsm] at h1
    have : deqPair ν μ g Ψ t s = 0 := enorm_eq_zero.1 (le_antisymm h1 zero_le)
    simp [this]

end UnforcedLeray.Short.IIb
