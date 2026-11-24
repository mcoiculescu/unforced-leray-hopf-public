import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

/-!
# `PartIII-a:T21/2/7/2/2/1/2`: continuity of the cutoff energy, rate and gradient energy on `[t, s)`

Proves `AdjCutE0Cont m` (leaf (b) of `AdjCutRate`, SP 3060-3067).

* `ladDt φ ρ x = fderivWithin` of the joint map on the half-open strip `Ico t s ×ˢ univ`, for
  `ρ ∈ Ico t s` (the right derivative at `ρ = t` is the one-sided derivative inside the strip);
* `(ρ, x) ↦ ladDt φ ρ x` is continuous on the strip;
* the cutoff integrals `ρ ↦ ∫_{cell} χ_R² H(ρ, x)` are continuous within `Ico t s` whenever
  `H` is continuous on the strip (dominated convergence on the compact band).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace AdjCutE0ContAux

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

/-- Continuity within `Ico t s` in the age of a cutoff integral `∫_{cell c} χ_R² H ρ x`, for a real
density `H` jointly continuous on the strip `Ico t s × ℝ²`. -/
lemma cutInt_cws (c : ℝ) {R t s : ℝ} (hR : 0 < R) (H : ℝ → ℝ × ℝ → ℝ)
    (hH : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) (Ico t s ×ˢ (univ : Set (ℝ × ℝ))))
    {r₀ : ℝ} (hr₀ : r₀ ∈ Ico t s) :
    ContinuousWithinAt (fun r => ∫ x in B0579.cell c, ladCut R x ^ 2 * H r x) (Ico t s) r₀ := by
  obtain ⟨b, hb1, hb2⟩ := exists_between hr₀.2
  have htb : t ≤ b := le_trans hr₀.1 hb1.le
  have hS : Icc t b ⊆ Ico t s := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hb2⟩
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : Icc t b ×ˢ K ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := prod_mono hS (subset_univ _)
  have hc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) (Icc t b ×ˢ K) := hH.mono hsub
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  set C₀ : ℝ := max C 0 with hC₀
  have hC₀nn : 0 ≤ C₀ := le_max_right _ _
  have hbound_int : IntegrableOn (fun x => C₀ * ladCut (2 * R) x) (B0579.cell c) := by
    refine integrableOn_cell_of_vanish (c := c) (R := 2 * R) (by linarith)
      (continuous_const.mul (ladCut_continuous _)) (fun x hx => ?_)
    simp [ladCut_eq_zero_of (R := 2 * R) (by linarith) hx]
  have hIio : Iio b ∈ 𝓝[Ico t s] r₀ := nhdsWithin_le_nhds (Iio_mem_nhds hb1)
  have hLx : ∀ r ∈ Ico t s, Continuous (fun x : ℝ × ℝ => H r x) := fun r hr =>
    hH.comp_continuous
      (continuous_const.prodMk continuous_id : Continuous fun x : ℝ × ℝ => ((r, x) : ℝ × (ℝ × ℝ)))
      (fun x => (⟨hr, mem_univ x⟩ : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ))))
  have hLim : ∀ x : ℝ × ℝ, ContinuousWithinAt (fun r => H r x) (Ico t s) r₀ := fun x => by
    have hcx : Continuous fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)) :=
      continuous_id.prodMk continuous_const
    have h := hH.continuousWithinAt (x := ((r₀, x) : ℝ × (ℝ × ℝ))) ⟨hr₀, mem_univ x⟩
    have h2 : ContinuousWithinAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) (Ico t s) r₀ :=
      hcx.continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)))
      (g := fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) h h2 (fun r hr => ⟨hr, mem_univ x⟩)
  unfold ContinuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C₀ * ladCut (2 * R) x) ?_ ?_
    hbound_int ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (((ladCut_continuous R).pow 2).mul (hLx r hr)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hIio] with r hr1 hr2
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (ae_of_all _ fun x hx => ?_)
    show ‖ladCut R x ^ 2 * H r x‖ ≤ C₀ * ladCut (2 * R) x
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
      have hHC : ‖H r x‖ ≤ C := hC (r, x) hmem
      have hHC' : ‖H r x‖ ≤ C₀ := le_trans hHC (le_max_left _ _)
      have hsq : ladCut R x ^ 2 ≤ 1 := pow_le_one₀ (ladCut_nonneg R x) (ladCut_le_one R x)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg (ladCut R x)), hl1, mul_one]
      calc ladCut R x ^ 2 * ‖H r x‖ ≤ 1 * C₀ := mul_le_mul hsq hHC' (norm_nonneg _) zero_le_one
        _ = C₀ := one_mul _
  · exact ae_of_all _ fun x => continuousWithinAt_const.mul (hLim x)

/-- Pointwise identity: for `ρ ∈ [t, s)` the right derivative `ladDt` equals the `fderivWithin` of
the joint map on the half-open strip. -/
lemma ladDt_eq_fderivWithin_Ico {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) {ρ : ℝ}
    (hρ : ρ ∈ Ico t s) (x : ℝ × ℝ) :
    ladDt φ ρ x =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)
        ((1 : ℝ), (0 : ℝ × ℝ)) := by
  have hmem : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hρ, mem_univ _⟩
  have hd : DifferentiableWithinAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) ((ρ, x) : ℝ × (ℝ × ℝ)) :=
    (hj _ hmem).differentiableWithinAt (by simp)
  have hline : HasDerivWithinAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ))
      (Ico t s) ρ :=
    ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) (Ico t s)
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
    fun r hr => ⟨hr, mem_univ x⟩
  have h1 : HasDerivWithinAt (fun r => φ r x)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)
        ((1 : ℝ), (0 : ℝ × ℝ)))
      (Ico t s) ρ :=
    HasFDerivWithinAt.comp_hasDerivWithinAt (f := fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ρ
      hd.hasFDerivWithinAt hline hmaps
  have hnhds : Ico t s ∈ 𝓝[Ici ρ] ρ := by
    have hsub : Ici ρ ∩ Iio s ⊆ Ico t s := fun r hr => ⟨le_trans hρ.1 hr.1, hr.2⟩
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ici ρ) (Iio_mem_nhds hρ.2)) hsub
  have h2 : HasDerivWithinAt (fun r => φ r x)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)
        ((1 : ℝ), (0 : ℝ × ℝ)))
      (Ici ρ) ρ :=
    h1.mono_of_mem_nhdsWithin hnhds
  unfold ladDt
  exact h2.derivWithin (uniqueDiffWithinAt_Ici ρ)

/-- The right time derivative is jointly continuous on the half-open strip. -/
lemma continuousOn_ladDt_strip {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2) (Ico t s ×ˢ univ) := by
  have hA : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.continuousOn_fderivWithin (adjStrip_uniqueDiff t s) (by simp)).clm_apply continuousOn_const
  exact hA.congr fun p hp => ladDt_eq_fderivWithin_Ico hj hp.1 p.2

end AdjCutE0ContAux

open AdjCutE0ContAux in
/-- **(b) Continuity in `ρ` on `[t, s)`** of `E_R`, `D_R` and `G_k^R` (SP 3060-3067). -/
theorem adjCutE0Cont (m : ℝ) : AdjCutE0Cont m := by
  intro ν tr t s G φ hctx R hR
  have hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) :=
    hctx.2.2.2.2.2.2.2
  have hF : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) :=
    hφ.continuousOn
  have hJ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m)) (Ico t s ×ˢ univ) :=
    ((B0579.continuous_jb_rpow (-m)).comp continuous_snd).continuousOn
  have hLD := continuousOn_ladDt_strip hφ
  have hE0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m) * ‖φ p.1 p.2‖ ^ 2)
      (Ico t s ×ˢ univ) :=
    hJ.mul (hF.norm.pow 2)
  have hRate : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m) *
      ((starRingEnd ℂ) (φ p.1 p.2) * ladDt φ p.1 p.2).re) (Ico t s ×ˢ univ) :=
    hJ.mul (Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn hF).mul hLD))
  have hGk : ∀ k : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      B0579.jb p.2 ^ (-m) * ‖pdCx k (φ p.1) p.2‖ ^ 2) (Ico t s ×ˢ univ) := fun k =>
    hJ.mul ((jointSmooth_pdCx hφ k).continuousOn.norm.pow 2)
  refine ⟨?_, ?_, ?_⟩
  · intro r₀ hr₀
    unfold cutE0
    exact cutInt_cws (ν ^ (-2 : ℝ)) hR (fun r x => B0579.jb x ^ (-m) * ‖φ r x‖ ^ 2) hE0 hr₀
  · intro r₀ hr₀
    unfold cutE0Rate
    exact continuousWithinAt_const.mul
      (cutInt_cws (ν ^ (-2 : ℝ)) hR
        (fun r x => B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ r x) * ladDt φ r x).re) hRate hr₀)
  · intro k r₀ hr₀
    unfold cutGReal
    exact cutInt_cws (ν ^ (-2 : ℝ)) hR
      (fun r x => B0579.jb x ^ (-m) * ‖pdCx k (φ r) x‖ ^ 2) (hGk k) hr₀

end UnforcedLeray.Short.IIIa
