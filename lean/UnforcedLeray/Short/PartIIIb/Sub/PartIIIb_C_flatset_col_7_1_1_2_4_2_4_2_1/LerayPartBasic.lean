import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.MeridTestBounded
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayModeCont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayModeSupp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayModeBound

/-!
# `LerayPartBasic` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/16`)

Source of record `the November 2 reference manuscript`
lines 1676, 1713-1737. The flat Leray part is `(f̄_r, 0)` plus the stream tail
`Σ_n e_n (-∂_η ψ_n, i k_n ψ_n)`; the zero-frequency term inherits regularity, periodicity, boundedness
and the age band from `avgQ`, and the tail is a uniformly summable series of continuous, periodic,
band-supported terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem lpb_eN_norm (c : ℝ) (n : ℤ) (q : ℝ) : ‖eN c n q‖ = 1 := by
  have h : eN c n q = Complex.exp (((2 * Real.pi * n * q / c : ℝ) : ℂ) * Complex.I) := by
    unfold eN
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem lpb_eN_periodic (c : ℝ) (hc : 0 < c) (n : ℤ) (q : ℝ) :
    eN c n (q + c) = eN c n q := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((q + c : ℝ) : ℂ) / (c : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)
        + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  unfold eN
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem lpb_summable_bound (C : ℝ) : Summable (fun n : ℤ => C / (1 + (n : ℝ) ^ 2)) := by
  have h1 : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.2 (by norm_num)
  have h2 : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
    refine Summable.of_norm_bounded_eventually h1 ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ 2 := by positivity
    show ‖1 / (1 + (n : ℝ) ^ 2)‖ ≤ 1 / (n : ℝ) ^ 2
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hpos (by linarith)
  exact (h2.mul_left C).congr (fun n => by ring)

theorem lerayPartBasic : LerayPartBasic := by
  intro c hc f hf
  obtain ⟨C, hC⟩ := lerayModeBound c hc f hf
  have hbound : ∀ (n : ℤ) (p : Profile),
      ‖eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)‖ ≤ C / (1 + (n : ℝ) ^ 2) := by
    intro n p
    rw [norm_smul, lpb_eN_norm, one_mul]
    exact hC n (p.1, p.2.2)
  have hTc : ∀ n : ℤ, Continuous (fun p : Profile => eN c n p.2.1 • lerayMode c f n (p.1, p.2.2)) := by
    intro n
    have hq : Continuous (fun p : Profile => eN c n p.2.1) := by
      unfold eN
      fun_prop
    have hl : Continuous (fun p : Profile => lerayMode c f n (p.1, p.2.2)) :=
      (lerayModeCont c hc f hf n).comp (continuous_fst.prodMk continuous_snd.snd)
    exact hq.smul hl
  have hTail : Continuous (lerayTail c f) :=
    continuous_tsum (fun n => hTc n) (lpb_summable_bound C) (fun n p => hbound n p)
  have hA : IsMeridTest c (avgQ c f) := (fOsc_isMeridTest hc hf).1
  have hAc : Continuous (avgQ c f) := hA.smooth.continuous
  have hHc : Continuous (fun p : Profile => (!₂[avgQ c f p 0, 0] : MeridC)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℂ)).comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).comp hAc
    · exact continuous_const
  have hBasicCont : Continuous (lerayPart c f) := by
    unfold lerayPart
    exact hHc.add hTail
  have hA' : ∀ σ q η, avgQ c f (σ, (q + c, η)) = avgQ c f (σ, (q, η)) :=
    fun σ q η => qInvariant_avgQ c f σ (q + c) q η
  have hPer : ∀ σ q η, lerayPart c f (σ, (q + c, η)) = lerayPart c f (σ, (q, η)) := by
    intro σ q η
    have hT : lerayTail c f (σ, (q + c, η)) = lerayTail c f (σ, (q, η)) := by
      unfold lerayTail
      refine tsum_congr (fun n => ?_)
      show eN c n (q + c) • lerayMode c f n (σ, η) = eN c n q • lerayMode c f n (σ, η)
      rw [lpb_eN_periodic c hc n q]
    unfold lerayPart
    rw [hT, hA' σ q η]
  obtain ⟨M0, hM0⟩ := meridTestBounded c hc (avgQ c f) hA
  have hAbd : ∀ p : Profile, ‖(!₂[avgQ c f p 0, 0] : MeridC)‖ ≤ M0 := by
    intro p
    refine le_trans (lmb_norm_two _ _) ?_
    rw [norm_zero, add_zero]
    exact le_trans (PiLp.norm_apply_le (avgQ c f p) 0) (hM0 p)
  have hTbd : ∀ p : Profile, ‖lerayTail c f p‖ ≤ ∑' n : ℤ, C / (1 + (n : ℝ) ^ 2) := fun p =>
    tsum_of_norm_bounded (lpb_summable_bound C).hasSum (fun n => hbound n p)
  obtain ⟨s0A, s1A, LA, hs0A, hbA⟩ := hf.band
  have hAz : ∀ p : Profile, p.1 < s0A → avgQ c f p = 0 := by
    intro p hp
    by_contra hne
    exact absurd (avgQ_band hbA p hne).1.1 (not_le.2 hp)
  obtain ⟨s0L, hs0L, hL⟩ := lerayModeSupp c hc f hf
  have hTz : ∀ p : Profile, p.1 < s0L → lerayTail c f p = 0 := by
    intro p hp
    have hz : ∀ n : ℤ, eN c n p.2.1 • lerayMode c f n (p.1, p.2.2) = 0 := fun n => by
      rw [hL n (p.1, p.2.2) hp, smul_zero]
    unfold lerayTail
    simp only [hz, tsum_zero]
  refine ⟨hBasicCont, hPer, ⟨M0 + ∑' n : ℤ, C / (1 + (n : ℝ) ^ 2), fun p => ?_⟩, ?_⟩
  · unfold lerayPart
    exact (norm_add_le _ _).trans (add_le_add (hAbd p) (hTbd p))
  · refine ⟨min s0A s0L, lt_min hs0A hs0L, fun p hp => ?_⟩
    have h1 : p.1 < s0A := lt_of_lt_of_le hp (min_le_left _ _)
    have h2 : p.1 < s0L := lt_of_lt_of_le hp (min_le_right _ _)
    unfold lerayPart
    rw [hAz p h1, hTz p h2, add_zero]
    ext i
    fin_cases i <;> simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
