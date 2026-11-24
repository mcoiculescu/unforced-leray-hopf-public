import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# `PartII-a:N01/9/1/4/1`: completeness of the tensor `L²` (`energyGradLimit`)

Source `the November 2 reference manuscript` lines 3426-3430. A Cauchy sequence of
measurable tensor fields in `L²(ageμ c (-1/2))` has a measurable `L²` limit. Route: the entries
are Cauchy scalar `L²` sequences; each is shifted to start at index `N` so that it lies in `L²`,
is put into `Lp ℂ 2 μ` (complete), and the limit is recovered as a measurable representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.EnergyGradLimitAux

variable {X : Type*} [MeasurableSpace X]

lemma enorm_rpow_two_eq (x : ℂ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg x), ofReal_norm x]

lemma eLpNorm_two_rpow_eq (μ : Measure X) (g : X → ℂ) :
    eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := g) (p := 2) (by norm_num)
  simpa using h

lemma lt_of_rpow_two_lt {a b : ℝ≥0∞} (h : a ^ (2 : ℝ) < b ^ (2 : ℝ)) : a < b :=
  (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 h

/-- Scalar `L²(μ)` completeness for a sequence with Cauchy differences. -/
lemma scalar_L2_complete (μ : Measure X) (f : ℕ → X → ℂ) (hf : ∀ k, Measurable (f k))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ k, M ≤ k → ∀ l, M ≤ l →
      ∫⁻ x, ‖f k x - f l x‖ₑ ^ (2 : ℝ) ∂μ < ENNReal.ofReal (δ ^ 2)) :
    ∃ g : X → ℂ, Measurable g ∧
      Tendsto (fun k => ∫⁻ x, ‖f k x - g x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := hC 1 one_pos
  have hfin : ∀ n : ℕ, eLpNorm (fun x => f (n + N) x - f N x) 2 μ < ⊤ := by
    intro n
    have h1 := hN (n + N) (by omega) N le_rfl
    have h2 : eLpNorm (fun x => f (n + N) x - f N x) 2 μ ^ (2 : ℝ) < ⊤ := by
      rw [eLpNorm_two_rpow_eq]
      exact lt_trans h1 ENNReal.ofReal_lt_top
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h2
    exact lt_irrefl _ h2
  have hmem : ∀ n : ℕ, MemLp (fun x => f (n + N) x - f N x) 2 μ := fun n =>
    ⟨((hf _).sub (hf _)).aestronglyMeasurable, hfin n⟩
  set u : ℕ → Lp ℂ 2 μ := fun n => (hmem n).toLp _ with hu
  have hcau : CauchySeq u := by
    rw [MeasureTheory.Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    rcases eq_or_ne ε ⊤ with rfl | hεt
    · exact Eventually.of_forall fun _ => le_top
    have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    obtain ⟨M, hM⟩ := hC ε.toReal hδ
    refine Filter.eventually_atTop.2 ⟨(M, M), fun p hp => ?_⟩
    have h1 : M ≤ p.1 := hp.1
    have h2 : M ≤ p.2 := hp.2
    have hae : (⇑(u p.1) - ⇑(u p.2)) =ᵐ[μ] (fun x => f (p.1 + N) x - f (p.2 + N) x) := by
      filter_upwards [(hmem p.1).coeFn_toLp, (hmem p.2).coeFn_toLp] with x hx1 hx2
      simp only [Pi.sub_apply, hu]
      rw [hx1, hx2]
      ring
    rw [eLpNorm_congr_ae hae]
    have hlt := hM (p.1 + N) (by omega) (p.2 + N) (by omega)
    have hlt' : eLpNorm (fun x => f (p.1 + N) x - f (p.2 + N) x) 2 μ ^ (2 : ℝ)
        < (ENNReal.ofReal ε.toReal) ^ (2 : ℝ) := by
      rw [eLpNorm_two_rpow_eq, ENNReal.rpow_two, ← ENNReal.ofReal_pow hδ.le]
      simpa using hlt
    rw [ENNReal.ofReal_toReal hεt] at hlt'
    exact (lt_of_rpow_two_lt hlt').le
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hcau
  have hlim := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm' u H).1 hH
  obtain ⟨g0, hg0m, hg0ae⟩ : ∃ g0 : X → ℂ, Measurable g0 ∧ ⇑H =ᵐ[μ] g0 :=
    ⟨_, (MeasureTheory.Lp.aestronglyMeasurable H).stronglyMeasurable_mk.measurable,
      (MeasureTheory.Lp.aestronglyMeasurable H).ae_eq_mk⟩
  refine ⟨fun x => f N x + g0 x, (hf N).add hg0m, ?_⟩
  have hshift : Tendsto (fun n => eLpNorm (fun x => f (n + N) x - (f N x + g0 x)) 2 μ)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hlim
    apply eLpNorm_congr_ae
    filter_upwards [(hmem n).coeFn_toLp, hg0ae] with x hx1 hx2
    simp only [Pi.sub_apply] at hx1 hx2 ⊢
    rw [hx1, hx2]
    ring
  have hfinal := (Filter.tendsto_add_atTop_iff_nat (f := fun k => eLpNorm
    (fun x => f k x - (f N x + g0 x)) 2 μ) N).1 hshift
  have hpow := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hfinal
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at hpow
  refine Tendsto.congr (fun k => ?_) hpow
  simp only [Function.comp_apply]
  rw [eLpNorm_two_rpow_eq]

lemma tnorm2_sq_eq (T : Fin 2 → Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
  unfold UnforcedLeray.Short.IIIa.tnorm2
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma norm_sq_le_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    ‖T i j‖ ^ 2 ≤ UnforcedLeray.Short.IIIa.tnorm2 T ^ 2 := by
  rw [tnorm2_sq_eq]
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b : Fin 2, ‖T a b‖ ^ 2)
    (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun b => ‖T i b‖ ^ 2)
    (fun b _ => sq_nonneg _) (Finset.mem_univ j)

end UnforcedLeray.Short.PartIIa.N01.EnergyGradLimitAux

open UnforcedLeray.Short.PartIIa.N01.EnergyGradLimitAux in
theorem energyGradLimit : UnforcedLeray.Short.PartIIa.N01.EnergyGradLimit := by
  intro c hc Gk hmeas hcauchy
  have hentry : ∀ i j : Fin 2, ∃ g : _ → ℂ, Measurable g ∧
      Tendsto (fun k => ∫⁻ p, ‖Gk k p i j - g p‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)))
        atTop (𝓝 0) := by
    intro i j
    refine scalar_L2_complete _ (fun k p => Gk k p i j) (fun k => hmeas k i j) ?_
    intro δ hδ
    obtain ⟨M, hM⟩ := hcauchy (δ ^ 2) (by positivity)
    refine ⟨M, fun k hk l hl => ?_⟩
    calc ∫⁻ p, ‖Gk k p i j - Gk l p i j‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2))
        ≤ ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tnorm2
            (fun a b => Gk k p a b - Gk l p a b) ^ 2) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) := by
          refine lintegral_mono fun p => ?_
          rw [enorm_rpow_two_eq]
          exact ENNReal.ofReal_le_ofReal (norm_sq_le_tnorm2_sq (fun a b => Gk k p a b - Gk l p a b) i j)
      _ < ENNReal.ofReal (δ ^ 2) := hM k hk l hl
  choose g hgm hgl using hentry
  refine ⟨fun p i j => g i j p, fun i j => hgm i j, ?_⟩
  have hsum : Tendsto (fun k => ∑ i : Fin 2, ∑ j : Fin 2,
      ∫⁻ p, ‖Gk k p i j - g i j p‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 2))
      (fun i _ => tendsto_finsetSum (Finset.univ : Finset (Fin 2)) (fun j _ => hgl i j))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun k => zero_le) (fun k => ?_)
  calc ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tnorm2
          (fun i j => Gk k p i j - g i j p) ^ 2) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2))
      ≤ ∫⁻ p, ∑ i : Fin 2, ∑ j : Fin 2, ‖Gk k p i j - g i j p‖ₑ ^ (2 : ℝ)
          ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) := by
        refine lintegral_mono fun p => ?_
        rw [tnorm2_sq_eq, ENNReal.ofReal_sum_of_nonneg
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
        refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
        rw [enorm_rpow_two_eq]
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
          ∫⁻ p, ‖Gk k p i j - g i j p‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_finsetSum]
          intro j _
          exact ((hmeas k i j).sub (hgm i j)).enorm.pow_const _
        · intro i _
          exact Finset.measurable_sum _ fun j _ => ((hmeas k i j).sub (hgm i j)).enorm.pow_const _
