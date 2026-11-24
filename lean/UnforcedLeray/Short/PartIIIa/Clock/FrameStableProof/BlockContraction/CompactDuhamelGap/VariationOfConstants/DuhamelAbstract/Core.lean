import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract.Continuity
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract.Measurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Leaf A: inhomogeneous variation of constants for a Duhamel evolution (pure functional analysis)

Task `PartIII-a:T21/c3/2/1/2/1` (`DuhamelVoCAbstract`, SP 2962-2982).

Let `U` be the `B0104.IsDuhamelEvolution` of `(F, A)` on one block, with `F` strongly continuous on
the block triangle and `A` strongly measurable and bounded on `[0, B]`. If `Y` is a bounded
measurable mild solution `Y(τ) = F(τ,0) Y(0) + ∫₀^τ F(τ,σ) (A(σ) Y(σ) + G(σ)) dσ` with integrable
forcing `G`, then `Y(B) = U(B,0) Y(0) + ∫₀^B U(B,σ) G(σ) dσ`.

Proof: `Z(τ) = U(τ,0) Y(0) + ∫₀^τ U(τ,σ) G(σ) dσ` satisfies the same mild equation (Duhamel
identity for `U(·,σ)` and Fubini on the triangle, using the joint strong continuity of `U` from
`Continuity.lean` and the Carathéodory composition of `Measurability.lean`), so `D = Y - Z` solves
`D(τ) = ∫₀^τ F(τ,r) A(r) D(r) dr` and vanishes by Gronwall.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.DuhamelAbstractSub

/-- **Variation of constants** (core form of `DuhamelVoCAbstract`). -/
theorem duhamelVoC_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (B : ℝ) (F : ℝ → ℝ → H →L[ℂ] H) (A : ℝ → H →L[ℂ] H) (U : ℝ → ℝ → H →L[ℂ] H)
    (hB : 0 < B)
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hFc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (tri B))
    (hAm : ∀ x : H, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) B)))
    (hAb : ∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A r‖ ≤ K_A)
    (Y G : ℝ → H)
    (hYm : AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)))
    (hYb : ∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C)
    (hGi : IntegrableOn G (Icc (0 : ℝ) B))
    (hY : ∀ τ ∈ Icc (0 : ℝ) B,
      Y τ = F τ 0 (Y 0) + ∫ σ in (0 : ℝ)..τ, F τ σ (A σ (Y σ) + G σ)) :
    Y B = U B 0 (Y 0) + ∫ σ in (0 : ℝ)..B, U B σ (G σ) := by
  obtain ⟨M, hM, hF⟩ := exists_opNorm_bound hFc
  obtain ⟨K₀, hK₀⟩ := hAb
  have hK : 0 ≤ max K₀ 0 := le_max_right _ _
  have hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ max K₀ 0 := fun r h0 h1 =>
    (hK₀ r ⟨h0, h1⟩).trans (le_max_left _ _)
  generalize max K₀ 0 = K at hK hA
  obtain ⟨CY, hCY⟩ := hYb
  have hCY0 : 0 ≤ CY := (norm_nonneg _).trans (hCY 0 ⟨le_rfl, hB.le⟩)
  have hCU := norm_U_le hU hM hF hK hA
  generalize 2 * M * Real.exp ((2 * (M * K) + 1) * B) = CU at hCU
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0 le_rfl le_rfl hB.le)
  have hUc := continuousOn_U_min hU hM hF hK hA hCU hFc
  have hIoc : ∀ τ ≤ B, Ioc (0 : ℝ) τ ⊆ Icc 0 B := fun τ hτ r hr => ⟨hr.1.le, hr.2.trans hτ⟩
  have hGτ : ∀ τ ≤ B, IntegrableOn G (Ioc 0 τ) := fun τ hτ => hGi.mono_set (hIoc τ hτ)
  have hFσ : ∀ τ ∈ Icc (0 : ℝ) B, ∀ y : H,
      ContinuousOn (fun σ => F τ (min σ τ) y) (Icc 0 B) :=
    fun τ hτ y => (hFc y).comp
      (continuous_const.prodMk (continuous_id.min continuous_const)).continuousOn
      (fun σ hσ => ⟨le_min hσ.1 hτ.1, min_le_right _ _, hτ.2⟩)
  have hUσ : ∀ τ ∈ Icc (0 : ℝ) B, ∀ y : H,
      ContinuousOn (fun σ => U τ (min σ τ) y) (Icc 0 B) :=
    fun τ hτ y => (hUc y).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun σ hσ => ⟨hτ, hσ⟩)
  have hmF : ∀ τ ∈ Icc (0 : ℝ) B, ∀ y : H,
      AEStronglyMeasurable (fun σ => F τ (min σ τ) y) (volume.restrict (Ioc 0 τ)) :=
    fun τ hτ y => ((hFσ τ hτ y).aestronglyMeasurable measurableSet_Icc).mono_set (hIoc τ hτ.2)
  have hmU : ∀ τ ∈ Icc (0 : ℝ) B, ∀ y : H,
      AEStronglyMeasurable (fun σ => U τ (min σ τ) y) (volume.restrict (Ioc 0 τ)) :=
    fun τ hτ y => ((hUσ τ hτ y).aestronglyMeasurable measurableSet_Icc).mono_set (hIoc τ hτ.2)
  have hmA : ∀ τ ≤ B, ∀ y : H,
      AEStronglyMeasurable (fun r => A r y) (volume.restrict (Ioc 0 τ)) :=
    fun τ hτ y => (hAm y).mono_set (hIoc τ hτ)
  -- integrability of the three one-variable integrands
  have hUG : ∀ τ ∈ Icc (0 : ℝ) B, IntegrableOn (fun σ => U τ σ (G σ)) (Ioc 0 τ) := by
    intro τ hτ
    have hm : AEStronglyMeasurable (fun σ => U τ σ (G σ)) (volume.restrict (Ioc 0 τ)) := by
      refine (aestronglyMeasurable_clm_apply (hmU τ hτ) (hGτ τ hτ.2).aestronglyMeasurable).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      rw [min_eq_left hσ.2]
    refine Integrable.mono' ((hGτ τ hτ.2).norm.const_mul CU) hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    exact ((U τ σ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hCU τ σ hσ.1.le hσ.2 hτ.2) (norm_nonneg _))
  have hFG : ∀ τ ∈ Icc (0 : ℝ) B, IntegrableOn (fun σ => F τ σ (G σ)) (Ioc 0 τ) := by
    intro τ hτ
    have hm : AEStronglyMeasurable (fun σ => F τ σ (G σ)) (volume.restrict (Ioc 0 τ)) := by
      refine (aestronglyMeasurable_clm_apply (hmF τ hτ) (hGτ τ hτ.2).aestronglyMeasurable).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      rw [min_eq_left hσ.2]
    refine Integrable.mono' ((hGτ τ hτ.2).norm.const_mul M) hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    exact ((F τ σ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF τ σ hσ.1.le hσ.2 hτ.2) (norm_nonneg _))
  have hFAY : ∀ τ ∈ Icc (0 : ℝ) B, IntegrableOn (fun σ => F τ σ (A σ (Y σ))) (Ioc 0 τ) := by
    intro τ hτ
    have hm : AEStronglyMeasurable (fun σ => F τ σ (A σ (Y σ))) (volume.restrict (Ioc 0 τ)) := by
      refine (aestronglyMeasurable_clm_apply (hmF τ hτ) (aestronglyMeasurable_clm_apply
        (hmA τ hτ.2) (hYm.mono_set (hIoc τ hτ.2)))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      rw [min_eq_left hσ.2]
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) τ)) :=
      isFiniteMeasure_restrict.2 (by simp)
    refine Integrable.mono' (integrable_const (M * K * CY)) hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    calc ‖F τ σ (A σ (Y σ))‖ ≤ M * K * ‖Y σ‖ :=
          UnforcedLeray.B0104.norm_apply_apply_le (hF τ σ hσ.1.le hσ.2 hτ.2)
            (hA σ hσ.1.le (hσ.2.trans hτ.2)) _
      _ ≤ M * K * CY := mul_le_mul_of_nonneg_left (hCY σ (hIoc τ hτ.2 hσ)) (mul_nonneg hM hK)
  have hEb : ∀ r ∈ Icc (0 : ℝ) B,
      ‖∫ σ in Ioc 0 r, U r σ (G σ)‖ ≤ CU * ∫ σ in Icc 0 B, ‖G σ‖ := by
    intro r hr
    calc ‖∫ σ in Ioc 0 r, U r σ (G σ)‖ ≤ ∫ σ in Ioc 0 r, CU * ‖G σ‖ := by
          refine norm_integral_le_of_norm_le ((hGτ r hr.2).norm.const_mul CU) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
          exact ((U r σ).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hCU r σ hσ.1.le hσ.2 hr.2) (norm_nonneg _))
      _ = CU * ∫ σ in Ioc 0 r, ‖G σ‖ := integral_const_mul _ _
      _ ≤ CU * ∫ σ in Icc 0 B, ‖G σ‖ :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hGi.norm
            (ae_of_all _ fun _ => norm_nonneg _) (hIoc r hr.2).eventuallyLE) hCU0
  -- Fubini on the triangle
  have hFub : ∀ τ ∈ Icc (0 : ℝ) B,
      IntegrableOn (fun r => F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ)))) (Ioc 0 τ) ∧
      ∫ σ in Ioc 0 τ, U τ σ (G σ) = (∫ σ in Ioc 0 τ, F τ σ (G σ)) +
        ∫ r in Ioc 0 τ, F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) := by
    intro τ hτ
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) τ)) :=
      isFiniteMeasure_restrict.2 (by simp)
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ × ℝ → H, Φ = {p : ℝ × ℝ | p.2 < p.1}.indicator
        (fun p => F τ (min p.1 τ) (A p.1 (U p.1 (min p.2 p.1) (G p.2)))) := ⟨_, rfl⟩
    have hbox : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) τ)).prod (volume.restrict (Ioc (0 : ℝ) τ))),
        p ∈ Ioc (0 : ℝ) τ ×ˢ Ioc (0 : ℝ) τ := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    have hΦm : AEStronglyMeasurable Φ
        ((volume.restrict (Ioc (0 : ℝ) τ)).prod (volume.restrict (Ioc (0 : ℝ) τ))) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => U p.1 (min p.2 p.1) (G p.2))
          ((volume.restrict (Ioc (0 : ℝ) τ)).prod (volume.restrict (Ioc (0 : ℝ) τ))) := by
        refine aestronglyMeasurable_clm_apply (T := fun p : ℝ × ℝ => U p.1 (min p.2 p.1))
          (fun y => ?_) (hGτ τ hτ.2).aestronglyMeasurable.comp_snd
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact ((hUc y).aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc)).mono_set
          (Set.prod_mono (hIoc τ hτ.2) (hIoc τ hτ.2))
      have h2 := aestronglyMeasurable_clm_apply (T := fun p : ℝ × ℝ => A p.1)
        (fun y => (hmA τ hτ.2 y).comp_fst) h1
      have h3 := aestronglyMeasurable_clm_apply (T := fun p : ℝ × ℝ => F τ (min p.1 τ))
        (fun y => (hmF τ hτ y).comp_fst) h2
      rw [hΦ]
      exact h3.indicator (measurableSet_lt measurable_snd measurable_fst)
    have hΦi : Integrable Φ
        ((volume.restrict (Ioc (0 : ℝ) τ)).prod (volume.restrict (Ioc (0 : ℝ) τ))) := by
      refine Integrable.mono' (((integrable_const (1 : ℝ)).mul_prod
        (hGτ τ hτ.2).norm).const_mul (M * K * CU)) hΦm ?_
      filter_upwards [hbox] with p hp
      simp only [one_mul]
      rw [hΦ]
      by_cases hlt : p.2 < p.1
      · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 < p.1} from hlt)]
        exact norm_FAU_le (hF τ _ (le_min hp.1.1.le hτ.1) (min_le_right _ _) hτ.2)
          (hA p.1 hp.1.1.le (hp.1.2.trans hτ.2))
          (hCU p.1 _ (le_min hp.2.1.le hp.1.1.le) (min_le_right _ _) (hp.1.2.trans hτ.2))
          hM hK _
      · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 < p.1} from hlt), norm_zero]
        positivity
    have hσslice : ∀ σ ∈ Ioc (0 : ℝ) τ,
        ∫ r in Ioc 0 τ, Φ (r, σ) = U τ σ (G σ) - F τ σ (G σ) := by
      intro σ hσ
      have hd := hU.duhamel () σ τ hσ.2 (by linarith [hτ.2, hσ.1]) (G σ)
      calc ∫ r in Ioc 0 τ, Φ (r, σ)
          = ∫ r in Ioc 0 τ, (Ioi σ).indicator (fun r => F τ r (A r (U r σ (G σ)))) r := by
            refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
            rw [hΦ]
            by_cases h : σ < r
            · rw [Set.indicator_of_mem (show (r, σ) ∈ {p : ℝ × ℝ | p.2 < p.1} from h),
                Set.indicator_of_mem (show r ∈ Ioi σ from h), min_eq_left hr.2,
                min_eq_left h.le]
            · rw [Set.indicator_of_notMem (show (r, σ) ∉ {p : ℝ × ℝ | p.2 < p.1} from h),
                Set.indicator_of_notMem (show r ∉ Ioi σ from h)]
        _ = ∫ r in Ioc σ τ, F τ r (A r (U r σ (G σ))) := by
            rw [setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi,
              sup_eq_right.2 hσ.1.le]
        _ = U τ σ (G σ) - F τ σ (G σ) := by
            rw [← intervalIntegral.integral_of_le hσ.2, hd]
            abel
    have hrslice : ∀ r ∈ Ioc (0 : ℝ) τ,
        ∫ σ in Ioc 0 τ, Φ (r, σ) = F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) := by
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) B := ⟨hr.1.le, hr.2.trans hτ.2⟩
      have hset : Ioc (0 : ℝ) τ ∩ Iio r = Ioo 0 r := by
        ext σ
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3.le.trans hr.2⟩, h3⟩
      calc ∫ σ in Ioc 0 τ, Φ (r, σ)
          = ∫ σ in Ioc 0 τ, (Iio r).indicator (fun σ => F τ r (A r (U r σ (G σ)))) σ := by
            refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
            rw [hΦ]
            by_cases h : σ < r
            · rw [Set.indicator_of_mem (show (r, σ) ∈ {p : ℝ × ℝ | p.2 < p.1} from h),
                Set.indicator_of_mem (show σ ∈ Iio r from h), min_eq_left hr.2,
                min_eq_left h.le]
            · rw [Set.indicator_of_notMem (show (r, σ) ∉ {p : ℝ × ℝ | p.2 < p.1} from h),
                Set.indicator_of_notMem (show σ ∉ Iio r from h)]
        _ = ∫ σ in Ioc 0 r, F τ r (A r (U r σ (G σ))) := by
            rw [setIntegral_indicator measurableSet_Iio, hset, integral_Ioc_eq_integral_Ioo]
        _ = F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) := by
            have h := ((F τ r).comp (A r)).integral_comp_comm (hUG r hr')
            simpa using h
    have hswap := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) τ))
      (ν := volume.restrict (Ioc (0 : ℝ) τ)) (f := fun r σ => Φ (r, σ)) hΦi
    have hL : ∫ r in Ioc 0 τ, ∫ σ in Ioc 0 τ, Φ (r, σ) =
        ∫ r in Ioc 0 τ, F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) :=
      setIntegral_congr_fun measurableSet_Ioc hrslice
    have hR : ∫ σ in Ioc 0 τ, ∫ r in Ioc 0 τ, Φ (r, σ) =
        (∫ σ in Ioc 0 τ, U τ σ (G σ)) - ∫ σ in Ioc 0 τ, F τ σ (G σ) := by
      rw [setIntegral_congr_fun measurableSet_Ioc hσslice]
      exact integral_sub (hUG τ hτ) (hFG τ hτ)
    refine ⟨?_, ?_⟩
    · refine hΦi.integral_prod_left.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hrslice r hr
    · rw [hL, hR] at hswap
      rw [hswap]
      abel
  -- the mild equation for `Y`, split
  have hYsplit : ∀ τ ∈ Icc (0 : ℝ) B, Y τ = F τ 0 (Y 0) +
      ((∫ r in Ioc 0 τ, F τ r (A r (Y r))) + ∫ σ in Ioc 0 τ, F τ σ (G σ)) := by
    intro τ hτ
    rw [← integral_add (hFAY τ hτ) (hFG τ hτ), ← intervalIntegral.integral_of_le hτ.1]
    simp only [← map_add]
    exact hY τ hτ
  have hU0 : ∀ τ ∈ Icc (0 : ℝ) B,
      U τ 0 (Y 0) = F τ 0 (Y 0) + ∫ r in Ioc 0 τ, F τ r (A r (U r 0 (Y 0))) := by
    intro τ hτ
    rw [hU.duhamel () 0 τ hτ.1 (by linarith [hτ.2]) (Y 0), intervalIntegral.integral_of_le hτ.1]
  have hU0i : ∀ τ ∈ Icc (0 : ℝ) B,
      IntegrableOn (fun r => F τ r (A r (U r 0 (Y 0)))) (Ioc 0 τ) :=
    fun τ hτ => (hU.integrable () 0 τ hτ.1 (by linarith [hτ.2]) (Y 0)).1
  -- the difference `D = Y - Z` solves the homogeneous Volterra equation
  have hD : ∀ τ ∈ Icc (0 : ℝ) B,
      Y τ - (U τ 0 (Y 0) + ∫ σ in Ioc 0 τ, U τ σ (G σ)) =
        ∫ r in Ioc 0 τ, F τ r (A r (Y r - (U r 0 (Y 0) + ∫ σ in Ioc 0 r, U r σ (G σ)))) := by
    intro τ hτ
    obtain ⟨hint, hEq⟩ := hFub τ hτ
    have h1 : ∫ r in Ioc 0 τ, (F τ r (A r (Y r)) - F τ r (A r (U r 0 (Y 0)))) =
        (∫ r in Ioc 0 τ, F τ r (A r (Y r))) - ∫ r in Ioc 0 τ, F τ r (A r (U r 0 (Y 0))) :=
      integral_sub (hFAY τ hτ) (hU0i τ hτ)
    have h2 : ∫ r in Ioc 0 τ, (F τ r (A r (Y r)) - F τ r (A r (U r 0 (Y 0))) -
          F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ)))) =
        (∫ r in Ioc 0 τ, (F τ r (A r (Y r)) - F τ r (A r (U r 0 (Y 0))))) -
          ∫ r in Ioc 0 τ, F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) :=
      integral_sub ((hFAY τ hτ).sub (hU0i τ hτ)) hint
    have h3 : ∀ r, F τ r (A r (Y r - (U r 0 (Y 0) + ∫ σ in Ioc 0 r, U r σ (G σ)))) =
        F τ r (A r (Y r)) - F τ r (A r (U r 0 (Y 0))) -
          F τ r (A r (∫ σ in Ioc 0 r, U r σ (G σ))) := by
      intro r
      simp only [map_sub, map_add]
      abel
    simp only [h3]
    rw [h2, h1]
    conv_lhs => rw [hYsplit τ hτ, hU0 τ hτ, hEq]
    abel
  have hDb : ∀ t, 0 ≤ t → t ≤ 0 + B →
      ‖Y t - (U t 0 (Y 0) + ∫ σ in Ioc 0 t, U t σ (G σ))‖ ≤
        CY + CU * CY + CU * ∫ σ in Icc 0 B, ‖G σ‖ := by
    intro t h0 h1
    have ht : t ∈ Icc (0 : ℝ) B := ⟨h0, by linarith⟩
    calc ‖Y t - (U t 0 (Y 0) + ∫ σ in Ioc 0 t, U t σ (G σ))‖
        ≤ ‖Y t‖ + (‖U t 0 (Y 0)‖ + ‖∫ σ in Ioc 0 t, U t σ (G σ)‖) :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ CY + (CU * CY + CU * ∫ σ in Icc 0 B, ‖G σ‖) := by
          gcongr
          · exact hCY t ht
          · exact ((U t 0).le_opNorm _).trans (mul_le_mul (hCU t 0 le_rfl h0 ht.2)
              (hCY 0 ⟨le_rfl, hB.le⟩) (norm_nonneg _) hCU0)
          · exact hEb t ht
      _ = CY + CU * CY + CU * ∫ σ in Icc 0 B, ‖G σ‖ := by ring
  have Gr := UnforcedLeray.B0104.gronwall_family (I := Unit)
    (fun _ t => ‖Y t - (U t 0 (Y 0) + ∫ σ in Ioc 0 t, U t σ (G σ))‖) (s := 0) (B := B)
    (a := 0) (L := M * K) (C := CY + CU * CY + CU * ∫ σ in Icc 0 B, ‖G σ‖) le_rfl
    (mul_nonneg hM hK) (fun _ t h0 h1 => hDb t h0 h1)
    (fun g hg t h0 h1 _ hφ _ => by
      have ht : t ∈ Icc (0 : ℝ) B := ⟨h0, by linarith⟩
      rw [hD t ht, zero_add, ← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le h0]
      refine norm_integral_le_of_norm_le (continuous_const.mul hg).integrableOn_Ioc ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      calc ‖F t r (A r (Y r - (U r 0 (Y 0) + ∫ σ in Ioc 0 r, U r σ (G σ))))‖
          ≤ M * K * ‖Y r - (U r 0 (Y 0) + ∫ σ in Ioc 0 r, U r σ (G σ))‖ :=
            UnforcedLeray.B0104.norm_apply_apply_le (hF t r hr.1.le hr.2 ht.2)
              (hA r hr.1.le (hr.2.trans ht.2)) _
        _ ≤ M * K * g r := mul_le_mul_of_nonneg_left (hφ () r hr.1.le hr.2)
            (mul_nonneg hM hK))
    () B hB.le (by linarith)
  have hzero : ‖Y B - (U B 0 (Y 0) + ∫ σ in Ioc 0 B, U B σ (G σ))‖ ≤ 0 :=
    Gr.trans (by simp)
  rw [intervalIntegral.integral_of_le hB.le]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hzero)

end UnforcedLeray.Short.IIIa.DuhamelAbstractSub
