import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_6
import UnforcedLeray.Short.PartIIb.Sub.T12_6_2
import UnforcedLeray.Short.PartIIb.Sub.T12_7_7_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Slice.Support
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Meas.Core
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.PeriodicBoxBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.FlatHeatAEMeas

/-!
# Part II-b, task `PartII-b:T12/7/6/2` (`deqPairIntegrableIoi`)

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`flatTranspose ν μ Ψ` vanishes off a box `[σ,H] × [-R,R]²` with `σ > 0` (`deqAbsSupport`), so
`deqPair ν μ g Ψ t s = 0` unless `s ∈ [σ,H]`; for `s ∈ [σ,H]`, `s > t`, the box bound of the heat
flow uniform in the age (`flatHeatBoxBound_of`) gives a bound independent of `s`; `s ↦ deqPair`
is measurable by joint measurability of the heat flow of a strongly measurable representative.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem flatHeat_eq_mk_aux (θ : ℝ) (g : ℝ × ℝ → CMerid) (hg : AEStronglyMeasurable g volume) :
    flatHeat θ g = flatHeat θ (hg.mk g) := by
  funext z
  unfold flatHeat
  apply integral_congr_ae
  have hqm := ((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving
  filter_upwards [hqm.ae hg.ae_eq_mk] with w hw
  rw [hw]

theorem deqPair_aesm_aux (ν : ℝ) (μ : ℂ) (t : ℝ) (g : ℝ × ℝ → CMerid)
    (hg : AEStronglyMeasurable g volume) (Ψ : Coord → Fin 2 → ℝ) (hΨ : IsPlanarSolTest Ψ) :
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
    fun i => (deqTransposeTest ν μ hΨ i).1.measurable
  have hf : Measurable (fun x : Coord =>
      ∑ i : Fin 2, flatHeat (ν * (x.1 - t)) g x.2 i * flatTranspose ν μ Ψ x i) :=
    Finset.measurable_sum _ (fun i _ => (hcomp i).mul (hT i))
  have := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))).aestronglyMeasurable
    (μ := (volume : Measure ℝ))
  exact this

theorem deqPair_bound_aux (ν : ℝ) (μ : ℂ) (c r t : ℝ) (hν : 0 < ν) (hc : 0 < c) (hr : 1 < r)
    (g : ℝ × ℝ → CMerid) (hg : DeqSliceGood c r g) (Ψ : Coord → Fin 2 → ℝ)
    (σ H R K : ℝ) (hK : 0 ≤ K)
    (hKb : ∀ x : Coord, ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ ≤ K ∧
        (x ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) →
          ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ = 0))
    (C : ℝ) (hC : ∀ (θ : ℝ) (g : ℝ × ℝ → CMerid), 0 < θ →
        (∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) → AEStronglyMeasurable g volume →
          ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖flatHeat θ g z‖ₑ ≤
            ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    (s : ℝ) (hs : t < s) :
    ‖deqPair ν μ g Ψ t s‖ₑ ≤
      (if s ∈ Icc σ H then
        ENNReal.ofReal K * (ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
      else 0) := by
  have hzero : ∀ z : ℝ × ℝ, (s, z) ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) →
      ∀ i : Fin 2, flatTranspose ν μ Ψ (s, z) i = 0 := by
    intro z hz i
    have h0 := (hKb (s, z)).2 hz
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg _)).1 h0 i (Finset.mem_univ i)
    exact norm_eq_zero.1 this
  split_ifs with hsm
  · set h := flatHeat (ν * (s - t)) g with hh
    set f : ℝ × ℝ → ℂ := fun z => ∑ i : Fin 2, h z i * flatTranspose ν μ Ψ (s, z) i with hf
    have hpt : ∀ z : ℝ × ℝ, ‖f z‖ ≤ ‖h z‖ * K := by
      intro z
      calc ‖f z‖ ≤ ∑ i : Fin 2, ‖h z i * flatTranspose ν μ Ψ (s, z) i‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 2, ‖h z‖ * ‖flatTranspose ν μ Ψ (s, z) i‖ := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (h z) i) (norm_nonneg _)
        _ = ‖h z‖ * ∑ i : Fin 2, ‖flatTranspose ν μ Ψ (s, z) i‖ := by rw [Finset.mul_sum]
        _ ≤ ‖h z‖ * K := mul_le_mul_of_nonneg_left (hKb (s, z)).1 (norm_nonneg _)
    have hoff : ∀ z : ℝ × ℝ, z ∉ Icc (-R) R ×ˢ Icc (-R) R → f z = 0 := by
      intro z hz
      have : (s, z) ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) := fun hh' => hz hh'.2
      simp [hf, hzero z this]
    have hdp : deqPair ν μ g Ψ t s = ∫ z, f z := rfl
    rw [hdp]
    refine (enorm_integral_le_lintegral_enorm f).trans ?_
    have hpt' : ∀ z : ℝ × ℝ, ‖f z‖ₑ ≤ (Icc (-R) R ×ˢ Icc (-R) R).indicator
        (fun z => ENNReal.ofReal K * ‖h z‖ₑ) z := by
      intro z
      by_cases hz : z ∈ Icc (-R) R ×ˢ Icc (-R) R
      · rw [Set.indicator_of_mem hz, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
          ← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (by rw [mul_comm K]; exact hpt z)
      · rw [Set.indicator_of_notMem hz, hoff z hz]; simp
    calc ∫⁻ z, ‖f z‖ₑ ≤ ∫⁻ z, (Icc (-R) R ×ˢ Icc (-R) R).indicator
          (fun z => ENNReal.ofReal K * ‖h z‖ₑ) z := lintegral_mono hpt'
      _ = ENNReal.ofReal K * ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖h z‖ₑ := by
          rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact hC (ν * (s - t)) g (mul_pos hν (sub_pos.2 hs)) hg.1 hg.2.1
  · have hdp : deqPair ν μ g Ψ t s = 0 := by
      unfold deqPair
      have : ∀ z : ℝ × ℝ, ∑ i : Fin 2, flatHeat (ν * (s - t)) g z i *
          flatTranspose ν μ Ψ (s, z) i = 0 := by
        intro z
        have hz : (s, z) ∉ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) := fun hh' => hsm hh'.1
        simp [hzero z hz]
      simp [this]
    rw [hdp]; simp

theorem deqPairIntegrableIoi : UnforcedLeray.Short.IIb.DeqPairIntegrableIoi := by
  intro ν μ c r t hν ht hc hr g hg Ψ hΨ
  obtain ⟨σ, H, R, K, hσ, hK, hKb⟩ := deqAbsSupport ν μ Ψ hΨ
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
      ((deqPair_aesm_aux ν μ t g hg.2.1 Ψ hΨ).restrict)
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
