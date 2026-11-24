import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_3.NormEq

/-!
# `selCompleteL1`: completeness of `Y_2` on one period

Source `the November 2 reference manuscript` lines 1341-1344.
`selNormEq` turns `phaseLpNorm P 2` into `c * eLpNorm _ 2 μ` with `μ` the restriction of `volume`
to `Ioc 0 P ×ˢ univ` and `c = (ofReal P⁻¹)^(1/2)`.  So a `Y_2`-Cauchy sequence is Cauchy in
`Lp CVec3 2 μ`; its limit is represented by a measurable `F0`, and the norm identity transfers
the convergence back to `phaseLpNorm`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selCompleteL1 : SelCompleteL1 := by
  intro P hP f hf hC
  -- the measure on one period and the normalising constant
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (ℝ × Space),
      μ = volume.restrict (Ioc (0 : ℝ) P ×ˢ (Set.univ : Set Space)) := ⟨_, rfl⟩
  have hrel : ∀ g : ℝ × Space → CVec3, AEStronglyMeasurable g volume →
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 g
        = ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) * eLpNorm g 2 μ := by
    intro g hg
    rw [hμ]
    exact selNormEq P hP g hg
  have hpos : 0 < ENNReal.ofReal P⁻¹ := ENNReal.ofReal_pos.2 (inv_pos.2 hP)
  have hc0 : ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos hpos ENNReal.ofReal_ne_top).ne'
  have hctop : ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, c = ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hc] at hrel hc0 hctop
  -- eLpNorm in terms of phaseLpNorm
  have hE : ∀ g : ℝ × Space → CVec3, AEStronglyMeasurable g volume →
      eLpNorm g 2 μ = UnforcedLeray.Short.IIb.phaseLpNorm P 2 g * c⁻¹ := by
    intro g hg
    rw [hrel g hg, mul_comm c, mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one]
  -- each member lies in L^2(μ)
  have hmeasμ : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    rw [hμ]
    exact (hf n).meas.restrict
  have hmem : ∀ n, MemLp (f n) 2 μ := by
    intro n
    refine ⟨hmeasμ n, ?_⟩
    rw [hE (f n) (hf n).meas]
    exact ENNReal.mul_lt_top (hf n).finite (ENNReal.inv_ne_top.2 hc0).lt_top
  obtain ⟨u, hu⟩ : ∃ u : ℕ → Lp CVec3 2 μ, ∀ n, u n = (hmem n).toLp (f n) :=
    ⟨fun n => (hmem n).toLp (f n), fun n => rfl⟩
  have hue : ∀ n, (⇑(u n)) =ᵐ[μ] f n := by
    intro n
    rw [hu n]
    exact (hmem n).coeFn_toLp
  -- edist in Lp is the eLpNorm of the difference
  have hedist : ∀ m n, edist (u m) (u n) = eLpNorm (fun x => f m x - f n x) 2 μ := by
    intro m n
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    filter_upwards [hue m, hue n] with x h1 h2
    simp [h1, h2]
  -- Cauchy in Lp
  have hcau : CauchySeq u := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < c * ε := ENNReal.mul_pos hc0 hε.ne'
    obtain ⟨N, hN⟩ := hC (c * ε) hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [hedist m n, hE (fun x => f m x - f n x) ((hf m).meas.sub (hf n).meas)]
    have h2 := hN m n hm hn
    calc UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => f m x - f n x) * c⁻¹
        < (c * ε) * c⁻¹ :=
          ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0) h2
      _ = ε := by rw [mul_comm c ε, mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one]
  -- limit in Lp
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  -- a measurable representative of the limit
  have hLm : AEStronglyMeasurable (⇑L) μ := Lp.aestronglyMeasurable L
  obtain ⟨F0, hF0m, hF0eq⟩ : ∃ F0 : ℝ × Space → CVec3, Measurable F0 ∧ (⇑L) =ᵐ[μ] F0 :=
    ⟨hLm.mk _, hLm.stronglyMeasurable_mk.measurable, hLm.ae_eq_mk⟩
  refine ⟨F0, hF0m, ?_, ?_⟩
  · -- finiteness of the norm
    have hfinF : eLpNorm F0 2 μ < ⊤ := by
      rw [eLpNorm_congr_ae hF0eq.symm]
      exact Lp.eLpNorm_lt_top L
    rw [hrel F0 hF0m.aestronglyMeasurable]
    exact ENNReal.mul_lt_top hctop.lt_top hfinF
  · -- convergence in Y_2
    unfold YConv
    have hkey : ∀ n, UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => f n x - F0 x)
        = c * edist (u n) L := by
      intro n
      rw [hrel (fun x => f n x - F0 x) ((hf n).meas.sub hF0m.aestronglyMeasurable), Lp.edist_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [hue n, hF0eq] with x h1 h2
      simp [h1, h2]
    have ht : Tendsto (fun n => edist (u n) L) atTop (𝓝 0) :=
      tendsto_iff_edist_tendsto_0.1 hL
    have ht2 := ENNReal.Tendsto.const_mul ht (Or.inr hctop)
    rw [mul_zero] at ht2
    exact ht2.congr (fun n => (hkey n).symm)

end UnforcedLeray.Short.PartIIIb.Concrete
