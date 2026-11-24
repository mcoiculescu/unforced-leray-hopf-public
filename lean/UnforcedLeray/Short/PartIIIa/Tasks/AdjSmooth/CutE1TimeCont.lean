import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutTimeAux

lemma ladCut_continuous (R : ℝ) : Continuous (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp (by fun_prop)

lemma ladCut_nonneg (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma ladCut_eq_one_of {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ^ 2 ≤ R ^ 2) :
    ladCut R x = 1 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.1 x hx

lemma ladCut_eq_zero_of {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x hx

lemma integrableOn_cell_of_vanish {c R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 → g x = 0) :
    IntegrableOn g (B0579.cell c) := by
  refine B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (2 * R)) ?_
  intro x hx hxK
  apply h0
  by_contra hcon
  push Not at hcon
  apply hxK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

/-- The cut energy integrand is continuous in the age along the strip, at each age of `[t, s)`. -/
lemma cutInt_continuousWithinAt {c m R t s : ℝ} (hR : 0 < R) (L : ℝ → ℝ × ℝ → ℂ)
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2) (Ico t s ×ˢ (univ : Set (ℝ × ℝ))))
    {r₀ : ℝ} (hr₀ : r₀ ∈ Ico t s) :
    ContinuousWithinAt (fun r => ∫ x in B0579.cell c,
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖L r x‖ ^ 2)) (Ico t s) r₀ := by
  obtain ⟨b, hb1, hb2⟩ := exists_between hr₀.2
  have htb : t ≤ b := le_trans hr₀.1 hb1.le
  have hS : Icc t b ⊆ Ico t s := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hb2⟩
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : Icc t b ×ˢ K ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := prod_mono hS (subset_univ _)
  have hc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m) * ‖L p.1 p.2‖ ^ 2)
      (Icc t b ×ˢ K) := by
    have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ‖L p.1 p.2‖ ^ 2) (Icc t b ×ˢ K) :=
      ((hL.mono hsub).norm).pow 2
    have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m)) (Icc t b ×ˢ K) :=
      ((B0579.continuous_jb_rpow (-m)).comp continuous_snd).continuousOn
    exact h2.mul h1
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  set C₀ : ℝ := max C 0 with hC₀
  have hC₀nn : 0 ≤ C₀ := le_max_right _ _
  have hbound_int : IntegrableOn (fun x => C₀ * ladCut (2 * R) x) (B0579.cell c) := by
    refine integrableOn_cell_of_vanish (c := c) (R := 2 * R) (by linarith)
      (continuous_const.mul (ladCut_continuous _)) (fun x hx => ?_)
    simp [ladCut_eq_zero_of (R := 2 * R) (by linarith) hx]
  have hIio : Iio b ∈ 𝓝[Ico t s] r₀ := nhdsWithin_le_nhds (Iio_mem_nhds hb1)
  have hLx : ∀ r ∈ Ico t s, Continuous (fun x => L r x) := fun r hr =>
    hL.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => (⟨hr, mem_univ x⟩ : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ))))
  have hLim : ∀ x : ℝ × ℝ, ContinuousWithinAt (fun r => L r x) (Ico t s) r₀ := fun x => by
    have hcx : Continuous fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)) := continuous_id.prodMk continuous_const
    have h := hL.continuousWithinAt (x := ((r₀, x) : ℝ × (ℝ × ℝ))) ⟨hr₀, mem_univ x⟩
    have h2 : ContinuousWithinAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) (Ico t s) r₀ :=
      hcx.continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)))
      (g := fun p : ℝ × (ℝ × ℝ) => L p.1 p.2) h h2 (fun r hr => ⟨hr, mem_univ x⟩)
  unfold ContinuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C₀ * ladCut (2 * R) x) ?_ ?_
    hbound_int ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (Continuous.mul ((ladCut_continuous R).pow 2)
      (Continuous.mul (B0579.continuous_jb_rpow (-m)) ((hLx r hr).norm.pow 2))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hIio] with r hr1 hr2
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (ae_of_all _ fun x hx => ?_)
    show ‖ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖L r x‖ ^ 2)‖ ≤ C₀ * ladCut (2 * R) x
    have hQnn : 0 ≤ B0579.jb x ^ (-m) * ‖L r x‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
    have hF0 : 0 ≤ ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖L r x‖ ^ 2) :=
      mul_nonneg (sq_nonneg _) hQnn
    by_cases hx2 : 2 * R ^ 2 ≤ x.2 ^ 2
    · rw [ladCut_eq_zero_of hR hx2, zero_pow two_ne_zero, zero_mul, norm_zero]
      exact mul_nonneg hC₀nn (ladCut_nonneg _ _)
    · push Not at hx2
      have habs : |x.2| ≤ 2 * R := by nlinarith [sq_abs x.2, abs_nonneg x.2]
      have hl1 : ladCut (2 * R) x = 1 :=
        ladCut_eq_one_of (R := 2 * R) (by linarith) (by nlinarith [sq_abs x.2, abs_nonneg x.2])
      have hxK : x ∈ K := ⟨Ico_subset_Icc_self hx.1, abs_le.1 habs⟩
      have hmem : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Icc t b ×ˢ K :=
        ⟨⟨hr1.1, (Set.mem_Iio.1 hr2).le⟩, hxK⟩
      have hQC : ‖B0579.jb x ^ (-m) * ‖L r x‖ ^ 2‖ ≤ C := hC (r, x) hmem
      rw [Real.norm_of_nonneg hQnn] at hQC
      have hQle : B0579.jb x ^ (-m) * ‖L r x‖ ^ 2 ≤ C₀ := le_trans hQC (le_max_left _ _)
      rw [Real.norm_of_nonneg hF0, hl1, mul_one]
      exact le_trans (mul_le_of_le_one_left hQnn (pow_le_one₀ (n := 2) (ladCut_nonneg R x)
        (ladCut_le_one R x))) hQle
  · refine ae_of_all _ fun x => ?_
    exact continuousWithinAt_const.mul (continuousWithinAt_const.mul ((hLim x).norm.pow 2))

end CutTimeAux

open CutTimeAux in
theorem cutE1TimeCont : UnforcedLeray.Short.IIIa.CutE1TimeCont := by
  intro c m R t s ψ hc hR hj
  refine ⟨?_, ?_⟩
  · intro r₀ hr₀
    show Tendsto (fun r => cutE1 c m R (ψ r)) (𝓝[Ico t s] r₀) (𝓝 (cutE1 c m R (ψ r₀)))
    unfold cutE1
    refine tendsto_finsetSum _ fun k _ => ?_
    exact cutInt_continuousWithinAt hR (fun r x => pdCx k (ψ r) x)
      ((jointSmooth_pdCx hj k).continuousOn) hr₀
  · intro r₀ hr₀
    show Tendsto (fun r => cutLap c m R (ψ r)) (𝓝[Ico t s] r₀) (𝓝 (cutLap c m R (ψ r₀)))
    unfold cutLap
    exact cutInt_continuousWithinAt hR (fun r x => ladLapCx (ψ r) x)
      ((jointSmooth_ladLapCx hj).continuousOn) hr₀
