import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Pt

/-!
# Part II-a, task `PartII-a:N02/4/3` helper: the exponential envelope in `L²(measureH c)`

For `0 < s0`, `0 < κ` the envelope `nzfmE s0 s1 κ p = 1_{[s0,s1]}(s) e^{-κ|η|}` is square integrable
for `measureH c`. The weight `s^{-3/2}` is at most `s0^{-3/2}` on the band, the `q`-cell has finite
length, and `e^{-κ|η|}` is integrable on `ℝ` (`nzfm_exp_abs_integrable`). The majorant
`nzfmMaj` is a product of three one-variable integrable functions, so `Integrable.mul_prod` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- `x ↦ e^{-κ|x|}` is integrable on `ℝ`: it is dominated by `H(x) + H(-x)` with
`H = 1_{[0,∞)} e^{-κ·}` integrable (`exp_neg_integrableOn_Ioi`). -/
lemma nzfm_exp_abs_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => Real.exp (-κ * |x|)) := by
  have hHint : Integrable (fun x : ℝ => (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) x) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    refine (integrableOn_Ici_iff_integrableOn_Ioi (f := fun y : ℝ => Real.exp (-κ * y))
      (μ := volume) (b := (0:ℝ)) ?_).2 (exp_neg_integrableOn_Ioi 0 hκ)
    simp
  have key : ∀ x : ℝ, Real.exp (-κ * |x|) ≤
      (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) x +
        (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) (-x) := by
    intro x
    rcases le_total 0 x with hx | hx
    · have h1 : (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) x = Real.exp (-κ * x) :=
        indicator_of_mem (mem_Ici.2 hx) _
      have h2 : 0 ≤ (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) (-x) :=
        indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
      rw [h1, abs_of_nonneg hx]
      linarith
    · have h1 : (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) (-x) = Real.exp (-κ * -x) :=
        indicator_of_mem (mem_Ici.2 (by linarith)) _
      have h2 : 0 ≤ (Ici (0:ℝ)).indicator (fun y : ℝ => Real.exp (-κ * y)) x :=
        indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
      rw [h1, abs_of_nonpos hx]
      linarith
  refine Integrable.mono' (hHint.add hHint.comp_neg)
    (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact key x

/-- The envelope `1_{[s0,s1]}(s) e^{-κ|η|}` on the profile space. -/
def nzfmE (s0 s1 κ : ℝ) : Profile → ℝ :=
  ((fun p : Profile => p.1) ⁻¹' Icc s0 s1).indicator (fun p : Profile => Real.exp (-κ * |p.2.2|))

lemma nzfmE_of_mem {s0 s1 κ : ℝ} {p : Profile} (h : p.1 ∈ Icc s0 s1) :
    nzfmE s0 s1 κ p = Real.exp (-κ * |p.2.2|) :=
  indicator_of_mem (show p ∈ (fun p : Profile => p.1) ⁻¹' Icc s0 s1 from h) _

lemma nzfmE_of_not_mem {s0 s1 κ : ℝ} {p : Profile} (h : p.1 ∉ Icc s0 s1) :
    nzfmE s0 s1 κ p = 0 :=
  indicator_of_notMem (show p ∉ (fun p : Profile => p.1) ⁻¹' Icc s0 s1 from h) _

lemma nzfmE_nonneg (s0 s1 κ : ℝ) (p : Profile) : 0 ≤ nzfmE s0 s1 κ p :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) p

lemma nzfmE_le_one {s0 s1 κ : ℝ} (hκ : 0 ≤ κ) (p : Profile) : nzfmE s0 s1 κ p ≤ 1 := by
  by_cases h : p.1 ∈ Icc s0 s1
  · rw [nzfmE_of_mem h]
    refine Real.exp_le_one_iff.2 ?_
    rw [neg_mul]
    exact neg_nonpos.2 (mul_nonneg hκ (abs_nonneg _))
  · rw [nzfmE_of_not_mem h]
    norm_num

lemma nzfmE_measurable (s0 s1 κ : ℝ) : Measurable (nzfmE s0 s1 κ) :=
  Measurable.indicator (by fun_prop) (measurableSet_Icc.preimage measurable_fst)

/-- The majorant `s0^{-3/2} 1_{[s0,s1]}(s) 1_{(0,c]}(q) e^{-κ|η|}` of `nzfmE · weightH` on the cell. -/
def nzfmMaj (s0 s1 c κ : ℝ) (p : Profile) : ℝ :=
  (Icc s0 s1).indicator (fun _ : ℝ => s0 ^ (-(3 / 2 : ℝ))) p.1 *
    ((Ioc 0 c).indicator (fun _ : ℝ => (1 : ℝ)) p.2.1 * Real.exp (-κ * |p.2.2|))

lemma nzfmMaj_integrable (s0 s1 c κ : ℝ) (hκ : 0 < κ) :
    Integrable (nzfmMaj s0 s1 c κ) := by
  have h1 : Integrable (fun s : ℝ => (Icc s0 s1).indicator (fun _ : ℝ => s0 ^ (-(3 / 2 : ℝ))) s) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := s0 ^ (-(3 / 2 : ℝ))) measure_Icc_lt_top.ne enorm_ne_top)
  have h2 : Integrable (fun q : ℝ => (Ioc 0 c).indicator (fun _ : ℝ => (1 : ℝ)) q) :=
    (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne enorm_ne_top)
  have h3 : Integrable (fun η : ℝ => Real.exp (-κ * |η|)) := nzfm_exp_abs_integrable hκ
  have h23 : Integrable (fun z : ℝ × ℝ => (Ioc 0 c).indicator (fun _ : ℝ => (1 : ℝ)) z.1 *
      Real.exp (-κ * |z.2|)) := Integrable.mul_prod h2 h3
  exact Integrable.mul_prod h1 h23

/-- The envelope is integrable against the weight `s^{-3/2}` on the cell. -/
lemma nzfmE_integrable_measureH (s0 s1 c κ : ℝ) (hκ : 0 < κ) (hs0 : 0 < s0) :
    Integrable (nzfmE s0 s1 κ) (measureH c) := by
  unfold measureH
  rw [integrable_withDensity_iff measurable_weightH (ae_of_all _ fun p => ENNReal.ofReal_lt_top)]
  refine Integrable.mono' ((nzfmMaj_integrable s0 s1 c κ hκ).restrict (s := cell c))
    ((nzfmE_measurable s0 s1 κ).mul ?_).aestronglyMeasurable ?_
  · exact (measurable_weightH.ennreal_toReal)
  · filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
    have hs : 0 < p.1 := hp.1
    have hq : p.2.1 ∈ Ioc 0 c := hp.2.1
    have hw : (weightH p).toReal = p.1 ^ (-(3 / 2 : ℝ)) := by
      rw [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hs.le _)]
    have hnn : 0 ≤ nzfmE s0 s1 κ p * (weightH p).toReal :=
      mul_nonneg (nzfmE_nonneg _ _ _ _) ENNReal.toReal_nonneg
    rw [Real.norm_of_nonneg hnn, hw]
    by_cases h : p.1 ∈ Icc s0 s1
    · rw [nzfmE_of_mem h]
      have h1 : p.1 ^ (-(3 / 2 : ℝ)) ≤ s0 ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs0 h.1 (by norm_num)
      have h2 : (Icc s0 s1).indicator (fun _ : ℝ => s0 ^ (-(3 / 2 : ℝ))) p.1 =
          s0 ^ (-(3 / 2 : ℝ)) := indicator_of_mem h _
      have h3 : (Ioc 0 c).indicator (fun _ : ℝ => (1 : ℝ)) p.2.1 = 1 := indicator_of_mem hq _
      unfold nzfmMaj
      rw [h2, h3, one_mul]
      have h4 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-κ * |p.2.2|)).le
      linarith [mul_comm (Real.exp (-κ * |p.2.2|)) (s0 ^ (-(3 / 2 : ℝ))),
        mul_comm (Real.exp (-κ * |p.2.2|)) (p.1 ^ (-(3 / 2 : ℝ)))]
    · rw [nzfmE_of_not_mem h]
      have h0 : (Icc s0 s1).indicator (fun _ : ℝ => s0 ^ (-(3 / 2 : ℝ))) p.1 = 0 :=
        indicator_of_notMem h _
      unfold nzfmMaj
      rw [h0]
      simp

/-- The envelope is in `L²(measureH c)`. -/
lemma nzfmE_memLp (s0 s1 c κ : ℝ) (hκ : 0 < κ) (hs0 : 0 < s0) :
    MemLp (nzfmE s0 s1 κ) 2 (measureH c) := by
  have hint := nzfmE_integrable_measureH s0 s1 c κ hκ hs0
  have hm : AEStronglyMeasurable (nzfmE s0 s1 κ) (measureH c) :=
    (nzfmE_measurable s0 s1 κ).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine Integrable.mono' hint (hm.pow 2) (ae_of_all _ fun p => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_of_le_one (nzfmE_nonneg _ _ _ _) (nzfmE_le_one hκ.le p) two_ne_zero

/-- Dominated by a constant multiple of the envelope and continuous: in `L²(measureH c)`. -/
lemma nzfm_memLp_of_env {c : ℝ} {F : Profile → MeridC} (hF : Continuous F) {s0 s1 κ K : ℝ}
    (hκ : 0 < κ) (hs0 : 0 < s0) (hK : 0 ≤ K) (hb : ∀ p, ‖F p‖ ≤ K * nzfmE s0 s1 κ p) :
    MemLp F 2 (measureH c) := by
  refine MemLp.of_le ((nzfmE_memLp s0 s1 c κ hκ hs0).const_mul K) hF.aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  show ‖F p‖ ≤ ‖K * nzfmE s0 s1 κ p‖
  rw [Real.norm_of_nonneg (mul_nonneg hK (nzfmE_nonneg _ _ _ _))]
  exact hb p

end UnforcedLeray.Short.PartIIa
