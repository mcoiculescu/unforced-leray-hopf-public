import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjDtDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Test
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Deriv

/-!
# Classical free adjoint equation on `(t, s)`

Source `the November 2 reference manuscript` (SP) lines 2937-2958, 3060.

For a regular backward free adjoint flow `φ` (`IsFreeAdjointFlow`) on `[t, s]` (`0 ≤ t < s`),
`ladChi tr φ ρ = ∂_ρφ + νΔφ + v·∇φ` vanishes on `B0579.cell c` for every `ρ ∈ (t, s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux

/-- Continuity in `r ∈ (t, s)` of the tested right-hand side `∫_{C_c} freeAdjIntegrand`. -/
lemma freeAdj_rhs_continuousOn {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (ht : 0 ≤ t) (hφ : IsFreeAdjointFlow ν c m tr t s g φ)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ContinuousOn (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) (Ioo t s) := by
  intro r₀ hr₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R₀, hR₀⟩ := hψ.band
  obtain ⟨R₁, hR₁⟩ := (hψ.pd 0).band
  obtain ⟨R₂, hR₂⟩ := (hψ.pd 1).band
  obtain ⟨R₃, hR₃⟩ := ((hψ.pd 0).pd 0).band
  obtain ⟨R₄, hR₄⟩ := ((hψ.pd 1).pd 1).band
  set R : ℝ := max 1 (max (max R₀ R₁) (max R₂ (max R₃ R₄))) with hRdef
  have hvan : ∀ r : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → freeAdjIntegrand tr (φ r) r ψ x = 0 := by
    intro r x hx
    have h1 : R₁ < |x.2| := lt_of_le_of_lt
      ((le_max_right R₀ R₁).trans ((le_max_left _ _).trans (le_max_right _ _))) hx
    have h2 : R₂ < |x.2| := lt_of_le_of_lt
      ((le_max_left R₂ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hx
    have h3 : R₃ < |x.2| := lt_of_le_of_lt
      ((le_max_left R₃ R₄).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))) hx
    have h4 : R₄ < |x.2| := lt_of_le_of_lt
      ((le_max_right R₃ R₄).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))) hx
    unfold freeAdjIntegrand UnforcedLeray.Short.IIb.lapP
    rw [hR₁ x h1, hR₂ x h2, hR₃ x h3, hR₄ x h4]
    simp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hr₀.1 hr₀.2)
  have hIcc : ∀ r ∈ Icc (r₀ - ε / 2) (r₀ + ε / 2), r ∈ Ioo t s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hball2 : ∀ r ∈ Metric.ball r₀ (ε / 2), r ∈ Icc (r₀ - ε / 2) (r₀ + ε / 2) := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  -- joint continuity of `freeAdjIntegrand` on `Ioo t s ×ˢ univ`
  have hφC : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ univ) :=
    hφ.jointSmooth.continuousOn.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have hvC : ∀ j : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j)
      (Ioo t s ×ˢ univ) := by
    intro j
    have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hsub : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici 0 ×ˢ univ :=
      prod_mono (fun r hr => ht.trans hr.1.le) subset_rfl
    exact ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn
      (hv0.mono hsub)
  have hlapC : Continuous (UnforcedLeray.Short.IIb.lapP ψ) :=
    (((hψ.pd 0).pd 0).continuous).add (((hψ.pd 1).pd 1).continuous)
  have hjoint : ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) => freeAdjIntegrand tr (φ p.1) p.1 ψ p.2) (Ioo t s ×ˢ univ) := by
    unfold freeAdjIntegrand
    have hreal : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
        ν * UnforcedLeray.Short.IIb.lapP ψ p.2 -
          (tr.v p.1 p.2 0 * B0579.pd 0 ψ p.2 + tr.v p.1 p.2 1 * B0579.pd 1 ψ p.2))
        (Ioo t s ×ˢ univ) := by
      refine ((continuous_const.mul (hlapC.comp continuous_snd)).continuousOn).sub ?_
      exact ((hvC 0).mul (((hψ.pd 0).continuous.comp continuous_snd).continuousOn)).add
        ((hvC 1).mul (((hψ.pd 1).continuous.comp continuous_snd).continuousOn))
    exact hφC.mul (Complex.continuous_ofReal.comp_continuousOn hreal)
  have hKc : IsCompact (Icc (r₀ - ε / 2) (r₀ + ε / 2) ×ˢ B0579.box c R) :=
    isCompact_Icc.prod (B0579.isCompact_box c R)
  have hKsub : Icc (r₀ - ε / 2) (r₀ + ε / 2) ×ˢ B0579.box c R ⊆ Ioo t s ×ˢ univ :=
    fun p hp => ⟨hIcc p.1 hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hjoint.mono hKsub)
  set C0 : ℝ := max M 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  set bound : ℝ × ℝ → ℝ := (B0579.box c R).indicator (fun _ => C0)
  have hbox_meas : MeasurableSet (B0579.box c R) := (B0579.isCompact_box c R).measurableSet
  have hbox_fin : (volume.restrict (B0579.cell c)) (B0579.box c R) < ⊤ :=
    (Measure.restrict_apply_le _ _).trans_lt (B0579.isCompact_box c R).measure_lt_top
  have hbound_int : Integrable bound (volume.restrict (B0579.cell c)) :=
    (integrable_indicator_iff hbox_meas).2 (integrableOn_const hbox_fin.ne)
  refine MeasureTheory.continuousAt_of_dominated (bound := bound) ?_ ?_ hbound_int ?_
  · filter_upwards [Ioo_mem_nhds hr₀.1 hr₀.2] with r hr
    have hslice : Continuous (fun x : ℝ × ℝ => freeAdjIntegrand tr (φ r) r ψ x) :=
      continuousOn_univ.1 (hjoint.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨hr, mem_univ x⟩))
    exact hslice.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds r₀ (half_pos hε)] with r hr
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    by_cases hxK : x ∈ B0579.box c R
    · simp only [bound, Set.indicator_of_mem hxK]
      exact (hM (r, x) ⟨hball2 r hr, hxK⟩).trans (le_max_left _ _)
    · have hgt : R < |x.2| := by
        by_contra hle
        exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 hle))
      simp [bound, Set.indicator_of_notMem hxK, hvan r x hgt]
  · refine ae_of_all _ fun x => ?_
    have hopen : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r₀, x) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr₀, mem_univ x⟩
    have hc1 : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => freeAdjIntegrand tr (φ p.1) p.1 ψ p.2)
        (r₀, x) := hjoint.continuousAt hopen
    have hc2 : ContinuousAt (fun r : ℝ => (r, x)) r₀ :=
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousAt
    exact ContinuousAt.comp (g := fun p : ℝ × (ℝ × ℝ) => freeAdjIntegrand tr (φ p.1) p.1 ψ p.2)
      (f := fun r : ℝ => (r, x)) hc1 hc2

/-- Differentiation under the cell integral of `r ↦ ∫_{C_c} φ(r) ψ` at `ρ ∈ (t, s)`. -/
lemma freeAdj_dtDeriv {c : ℝ} {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ))
      (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) ρ := by
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
  have hs0nhds : Metric.ball ρ (ε / 2) ∈ 𝓝 ρ := Metric.ball_mem_nhds ρ (by linarith)
  have hIcc : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r ∈ Ioo t s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hball2 : ∀ r ∈ Metric.ball ρ (ε / 2), r ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hJc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  have hKc : IsCompact (Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) ⊆
      Ico t s ×ˢ univ :=
    fun p hp => ⟨Ioo_subset_Ico_self (hIcc p.1 hp.1), mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hJc.mono hKsub)
  have hLD : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), ∀ x : ℝ × ℝ, x.1 ∈ Icc (-(c / 2)) (c / 2) →
      x.2 ∈ Icc (-R) R → ‖ladDt φ r x‖ ≤ M := by
    intro r hr x hx1 hx2
    rw [ladDt_eq_fderivWithin hj (hIcc r hr) x]
    exact hM (r, x) ⟨hr, hx1, hx2⟩
  have hcellsub : ∀ x : ℝ × ℝ, x ∈ B0579.cell c → x.1 ∈ Icc (-(c / 2)) (c / 2) := by
    intro x hx
    have hx' := Set.mem_prod.1 hx
    exact ⟨hx'.1.1, hx'.1.2.le⟩
  have hcont : ∀ r ∈ Ioo t s, Continuous (fun x : ℝ × ℝ => φ r x * ((ψ x : ℝ) : ℂ)) := fun r hr =>
    (adjContDiff_slice hj (Ioo_subset_Ico_self hr)).continuous.mul
      (Complex.continuous_ofReal.comp hψ.continuous)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hvan : UnforcedLeray.Cyl.VanishesOutside R (fun x => φ ρ x * ((ψ x : ℝ) : ℂ)) :=
    fun x hx => by simp [hR x hx]
  have hF_int : Integrable (fun x => φ ρ x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := by
    rw [← IntegrableOn, hcell]
    exact hvan.integrableOn_cell (hcont ρ hρ) c
  have hF'_meas : AEStronglyMeasurable (fun x => ladDt φ ρ x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    ((continuous_ladDt hj hρ).mul (Complex.continuous_ofReal.comp hψ.continuous)).aestronglyMeasurable
  have hbound_int : Integrable (fun x => M * ‖ψ x‖) (volume.restrict (B0579.cell c)) :=
    Integrable.const_mul (Integrable.norm hψ.integrableOn) M
  have h_bound : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      ‖ladDt φ r a * ((ψ a : ℝ) : ℂ)‖ ≤ M * ‖ψ a‖ := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (Filter.Eventually.of_forall fun a ha r hr => ?_)
    by_cases hA2 : |a.2| ≤ R
    · have h1 := hLD r (hball2 r hr) a (hcellsub a ha) (abs_le.1 hA2)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · have h0 : ψ a = 0 := hR a (not_le.1 hA2)
      simp [h0]
  have h_diff : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      HasDerivAt (fun r => φ r a * ((ψ a : ℝ) : ℂ)) (ladDt φ r a * ((ψ a : ℝ) : ℂ)) r :=
    Filter.Eventually.of_forall fun a r hr =>
      (ladDt_hasDerivAt hj (hIcc r (hball2 r hr)) a).mul_const _
  have hF_meas : ∀ᶠ r in 𝓝 ρ, AEStronglyMeasurable (fun x => φ r x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r hr => (hcont r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs0nhds hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff).2

/-- Cell integration by parts for the free adjoint integrand (`div v = 0`). -/
lemma freeAdj_ibp {ν c : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {φ : ℝ → ℝ × ℝ → ℂ} (hc : 0 < c) (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hper_all : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x)
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, freeAdjIntegrand tr (φ ρ) ρ ψ x =
      ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hφs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hper : ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x :=
    fun x => hper_all ρ (Ioo_subset_Ico_self hρ) x
  have hφd : Differentiable ℝ (φ ρ) := hφs.differentiable (by simp)
  have hvC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v ρ x) :=
    tr.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨hρ0.le, mem_univ _⟩)
  have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 2) => v j) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
  have hvr : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => tr.v ρ x j) := fun j =>
    ((hcoord j).comp hvC).differentiable (by simp)
  have hvj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp ((hcoord j).comp hvC)
  have hvd : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => (hvj j).differentiable (by simp)
  have hvper : ∀ x : ℝ × ℝ, tr.v ρ (x.1 + c, x.2) = tr.v ρ x :=
    fun x => tr.isTrain.periodic_v ρ hρ0.le x
  have hdiv : ∀ x : ℝ × ℝ, pdCx 0 (fun y => ((tr.v ρ y 0 : ℝ) : ℂ)) x +
      pdCx 1 (fun y => ((tr.v ρ y 1 : ℝ) : ℂ)) x = 0 := by
    intro x
    rw [ibpPdCx_ofReal _ (hvr 0) 0 x, ibpPdCx_ofReal _ (hvr 1) 1 x, ← Complex.ofReal_add]
    have hd := tr.isTrain.solenoidal ρ hρ0.le x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hvr 0) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv (hvr 1) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v ρ y 0) x + B0579.pd 1 (fun y => tr.v ρ y 1) x = 0 := hd
    rw [hd', Complex.ofReal_zero]
  have hΦs : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ)) :=
    fun j => hφs.mul (hvj j)
  have hΦper : ∀ j : Fin 2, ∀ x : ℝ × ℝ,
      φ ρ (x.1 + c, x.2) * ((tr.v ρ (x.1 + c, x.2) j : ℝ) : ℂ) =
        φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) :=
    fun j x => by rw [hper x, hvper x]
  have hP : ∀ j : Fin 2,
      IntegrableOn (fun x => φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ))
        (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ))
        (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * ((tr.v ρ x j : ℝ) : ℂ) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, pdCx j (fun y => φ ρ y * ((tr.v ρ y j : ℝ) : ℂ)) x * (ψ x : ℂ) :=
    fun j => mpWeakCore c hc _ (hΦs j) (hΦper j) j ψ hψ
  have hLap : ∀ k : Fin 2,
      IntegrableOn (fun x => φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ ρ x * (B0579.pd k (B0579.pd k ψ) x : ℂ) =
        ∫ x in B0579.cell c, pdCx k (pdCx k (φ ρ)) x * (ψ x : ℂ) := by
    intro k
    obtain ⟨i1, _, e1⟩ := mpWeakCore c hc (φ ρ) hφs hper k (B0579.pd k ψ) (hψ.pd k)
    obtain ⟨_, i2, e2⟩ := mpWeakCore c hc (pdCx k (φ ρ)) (ibpPdCx_smooth hφs k)
      (ibpPdCx_periodic k (φ ρ) hper) k ψ hψ
    refine ⟨i1, i2, ?_⟩
    rw [e1, e2, neg_neg]
  have hTpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => φ ρ y * ((tr.v ρ y 0 : ℝ) : ℂ)) x * (ψ x : ℂ) +
        pdCx 1 (fun y => φ ρ y * ((tr.v ρ y 1 : ℝ) : ℂ)) x * (ψ x : ℂ) =
        ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    intro x
    rw [ibpPdCx_mul hφd (hvd 0) 0 x, ibpPdCx_mul hφd (hvd 1) 1 x]
    have hdx := hdiv x
    simp only [ladTransport]
    linear_combination (φ ρ x * (ψ x : ℂ)) * hdx
  have hTint : IntegrableOn (fun x => ladTransport tr ρ (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) :=
    ((hP 0).2.1.add (hP 1).2.1).congr_fun (fun x _ => by
      simp only [Pi.add_apply]; exact hTpt x) (B0579.measurableSet_cell c)
  have hA1 : ∫ x in B0579.cell c, φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ) =
      ∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
          φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x; simp only [UnforcedLeray.Short.IIb.lapP]; push_cast; ring
    rw [hsplit, integral_add (hLap 0).1 (hLap 1).1, (hLap 0).2.2, (hLap 1).2.2,
      ← integral_add (hLap 0).2.1 (hLap 1).2.1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladLapCx]; ring
  have hB1 : ∫ x in B0579.cell c, φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hsplit : (fun x => φ ρ x *
        ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) =
        fun x => φ ρ x * ((tr.v ρ x 0 : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ) +
          φ ρ x * ((tr.v ρ x 1 : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ) := by
      funext x; push_cast; ring
    rw [hsplit, integral_add (hP 0).1 (hP 1).1, (hP 0).2.2, (hP 1).2.2, ← neg_add,
      ← integral_add (hP 0).2.1 (hP 1).2.1]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hTpt)
  have hI1 : IntegrableOn (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ))
      (B0579.cell c) := by
    have hfun : (fun x => φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) = fun x =>
        φ ρ x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
          φ ρ x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ) := by
      funext x; simp only [UnforcedLeray.Short.IIb.lapP]; push_cast; ring
    rw [hfun]; exact (hLap 0).1.add (hLap 1).1
  have hI2 : IntegrableOn (fun x => φ ρ x *
      ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) (B0579.cell c) := by
    refine ((hP 0).1.add (hP 1).1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.add_apply]; push_cast; ring
  have hLHS : ∫ x in B0579.cell c, freeAdjIntegrand tr (φ ρ) ρ ψ x =
      (ν : ℂ) * (∫ x in B0579.cell c, φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
        ∫ x in B0579.cell c, φ ρ x *
          ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
    have hpt : freeAdjIntegrand tr (φ ρ) ρ ψ = fun x =>
        (ν : ℂ) * (φ ρ x * (UnforcedLeray.Short.IIb.lapP ψ x : ℂ)) -
          φ ρ x * ((tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x : ℝ) : ℂ) := by
      funext x; unfold freeAdjIntegrand; push_cast; ring
    rw [hpt, integral_sub (Integrable.const_mul hI1 (ν : ℂ)) hI2, integral_const_mul]
  have hRHS : ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) =
      (ν : ℂ) * (∫ x in B0579.cell c, ladLapCx (φ ρ) x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c, ladTransport tr ρ (φ ρ) x * (ψ x : ℂ) := by
    have hL : IntegrableOn (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) (B0579.cell c) := by
      have hfun : (fun x => ladLapCx (φ ρ) x * (ψ x : ℂ)) = fun x =>
          pdCx 0 (pdCx 0 (φ ρ)) x * (ψ x : ℂ) + pdCx 1 (pdCx 1 (φ ρ)) x * (ψ x : ℂ) := by
        funext x; simp only [ladLapCx]; ring
      rw [hfun]; exact (hLap 0).2.1.add (hLap 1).2.1
    rw [← integral_const_mul, ← integral_add (Integrable.const_mul hL (ν : ℂ)) hTint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ladChi, ladTransport, ladLapCx]; ring
  rw [hLHS, hRHS, hA1, hB1]
  ring

/-- Tested against any cylinder test `ψ`, `ladChi tr φ ρ` integrates to `0` on `B0579.cell c`. -/
lemma freeAdj_test_chi_zero {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hc : 0 < c) (ht : 0 ≤ t) (hφ : IsFreeAdjointFlow ν c m tr t s g φ)
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) = 0 := by
  have hts : t < s := hρ.1.trans hρ.2
  set Af : ℝ → ℂ := fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x
  have hcont := freeAdj_rhs_continuousOn ht hφ hψ
  have hint : IntervalIntegrable Af volume t s := hφ.timeIntegrable ψ hψ
  have hint' : IntervalIntegrable Af volume ρ s :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hts.le, Set.uIcc_of_le hρ.2.le]
      exact Icc_subset_Icc hρ.1.le le_rfl)
  have hmeas : StronglyMeasurableAtFilter Af (𝓝 ρ) :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioo ρ hρ
  have hcA : ContinuousAt Af ρ := hcont.continuousAt (Ioo_mem_nhds hρ.1 hρ.2)
  have hder1 : HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ)) (-Af ρ) ρ := by
    have h0 : HasDerivAt (fun r => (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ r' in r..s, Af r')
        (-Af ρ) ρ := by
      have := intervalIntegral.integral_hasDerivAt_left hint' hmeas hcA
      simpa using this.const_add (∫ x in B0579.cell c, g x * (ψ x : ℂ))
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hρ.1 hρ.2] with r hr
    exact hφ.weak ψ hψ r hr
  have hder2 := freeAdj_dtDeriv hφ.jointSmooth hρ hψ
  have heq : (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) = -Af ρ := hder2.unique hder1
  have hibp := freeAdj_ibp (tr := tr) hc ht hφ.jointSmooth hφ.periodic hρ hψ
  -- integrability of `ladDt * ψ` and `ladChi * ψ` via compact `η`-support of `ψ`
  obtain ⟨R, hR⟩ := hψ.band
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have hI1 : IntegrableOn (fun x => ladDt φ ρ x * (ψ x : ℂ)) (B0579.cell c) := by
    have hvan : UnforcedLeray.Cyl.VanishesOutside R (fun x => ladDt φ ρ x * (ψ x : ℂ)) :=
      fun x hx => by simp [hR x hx]
    rw [hcell]
    exact hvan.integrableOn_cell
      ((continuous_ladDt hφ.jointSmooth hρ).mul (Complex.continuous_ofReal.comp hψ.continuous)) c
  have hI2 : IntegrableOn (fun x => ladChi tr φ ρ x * (ψ x : ℂ)) (B0579.cell c) := by
    have hvan : UnforcedLeray.Cyl.VanishesOutside R (fun x => ladChi tr φ ρ x * (ψ x : ℂ)) :=
      fun x hx => by simp [hR x hx]
    rw [hcell]
    exact hvan.integrableOn_cell
      ((continuous_ladChi tr ht hφ.jointSmooth hρ).mul
        (Complex.continuous_ofReal.comp hψ.continuous)) c
  have hI3 : IntegrableOn (fun x => (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ))
      (B0579.cell c) := by
    refine (hI2.sub hI1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.sub_apply]; ring
  have hsplit : (∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ)) =
      (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) := by
    rw [← integral_add hI1 hI3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; ring)
  rw [hsplit, heq, ← hibp]
  ring

/-- Pointwise vanishing of `ladChi tr φ ρ` on `B0579.cell c` for `ρ ∈ (t, s)`. -/
theorem freeAdj_chi_eq_zero {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hc : 0 < c) (ht : 0 ≤ t) (hφ : IsFreeAdjointFlow ν c m tr t s g φ)
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ B0579.cell c) :
    ladChi tr φ ρ x₀ = 0 := by
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  -- smoothness and `c`-periodicity of `ladChi tr φ ρ`
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hΦU : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ univ) :=
    hφ.jointSmooth.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)) (Ioo t s ×ˢ univ) :=
    hΦU.fderiv_of_isOpen hU (by simp)
  have hdt_smooth : ContDiff ℝ ∞ (ladDt φ ρ) := by
    have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (ρ, x) (1, 0)) :=
      (hfd.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x => ⟨hρ, mem_univ x⟩)).clm_apply contDiff_const
    have heq : ladDt φ ρ = fun x : ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (ρ, x) (1, 0) :=
      funext fun x => LadPRDerivAux.ladDt_eq_fderiv hφ.jointSmooth hρ x
    rw [heq]; exact h1
  have hdt_per : ∀ x : ℝ × ℝ, ladDt φ ρ (x.1 + c, x.2) = ladDt φ ρ x := by
    intro x
    have d1 := ladDt_hasDerivAt hφ.jointSmooth hρ (x.1 + c, x.2)
    have d2 := ladDt_hasDerivAt hφ.jointSmooth hρ x
    have d1' : HasDerivAt (fun r => φ r x) (ladDt φ ρ (x.1 + c, x.2)) ρ :=
      d1.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2)
        fun r hr => (hφ.periodic r (Ioo_subset_Ico_self hr) x).symm)
    exact d1'.unique d2
  have hφs : ContDiff ℝ ∞ (φ ρ) := hφ.smooth ρ (Ioo_subset_Ico_self hρ)
  have hφp : ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x :=
    hφ.periodic ρ (Ioo_subset_Ico_self hρ)
  have hlap_s : ContDiff ℝ ∞ (ladLapCx (φ ρ)) :=
    (ibpPdCx_smooth (ibpPdCx_smooth hφs 0) 0).add (ibpPdCx_smooth (ibpPdCx_smooth hφs 1) 1)
  have hlap_p : ∀ x : ℝ × ℝ, ladLapCx (φ ρ) (x.1 + c, x.2) = ladLapCx (φ ρ) x := fun x => by
    unfold ladLapCx
    rw [ibpPdCx_periodic 0 _ (ibpPdCx_periodic 0 _ hφp) x,
      ibpPdCx_periodic 1 _ (ibpPdCx_periodic 1 _ hφp) x]
  have hv_s : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => ((tr.v ρ x j : ℝ) : ℂ)) := fun j =>
    RateSplitAux.contDiff_ofReal (RateSplitAux.continuous_v tr hρ0 j)
  have hv_p : ∀ j : Fin 2, ∀ x : ℝ × ℝ, tr.v ρ (x.1 + c, x.2) j = tr.v ρ x j := fun j x =>
    congrArg (fun v => v j) (tr.isTrain.periodic_v ρ hρ0 x)
  have hchi_s : ContDiff ℝ ∞ (ladChi tr φ ρ) := by
    unfold ladChi ladTransport
    exact (hdt_smooth.add (contDiff_const.mul hlap_s)).add
      (((hv_s 0).mul (ibpPdCx_smooth hφs 0)).add ((hv_s 1).mul (ibpPdCx_smooth hφs 1)))
  have hchi_p : ∀ x : ℝ × ℝ, ladChi tr φ ρ (x.1 + c, x.2) = ladChi tr φ ρ x := fun x => by
    unfold ladChi ladTransport
    rw [hdt_per x, hlap_p x, hv_p 0 x, hv_p 1 x,
      ibpPdCx_periodic 0 _ hφp x, ibpPdCx_periodic 1 _ hφp x]
  -- test against `χ_R · conj(ladChi)` with `R = |x₀.2| + 1`
  set R : ℝ := |x₀.2| + 1
  have hR : 0 < R := by positivity
  obtain ⟨_, _, hCut⟩ := ladCutProps
  have hCutR := (hCut R hR).1 c
  set F : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * (starRingEnd ℂ) (ladChi tr φ ρ x)
  have hFs : ContDiff ℝ ∞ F :=
    (RateSplitAux.contDiff_ofReal hCutR.smooth).mul (Complex.conjCLE.contDiff.comp hchi_s)
  have hFp : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x := fun x => by
    simp only [F, hCutR.periodic x, hchi_p x]
  have hFb : ∀ x : ℝ × ℝ, 2 * R < |x.2| → F x = 0 := fun x hx => by
    simp [F, RateSplitAux.cut_zero hR hx]
  obtain ⟨hre, him⟩ := LadPRTestAux.isCylTest_re_im hFs hFp (2 * R) hFb
  have hz_re := freeAdj_test_chi_zero hc ht hφ hρ hre
  have hz_im := freeAdj_test_chi_zero hc ht hφ hρ him
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have hint_re : IntegrableOn (fun x => ladChi tr φ ρ x * (((F x).re : ℝ) : ℂ))
      (B0579.cell c) := by
    obtain ⟨Rb, hRb⟩ := hre.band
    have hvan : UnforcedLeray.Cyl.VanishesOutside Rb
        (fun x => ladChi tr φ ρ x * (((F x).re : ℝ) : ℂ)) :=
      fun x hx => by simp [hRb x hx]
    rw [hcell]
    exact hvan.integrableOn_cell
      (hchi_s.continuous.mul (Complex.continuous_ofReal.comp hre.continuous)) c
  have hint_im : IntegrableOn (fun x => ladChi tr φ ρ x * (((F x).im : ℝ) : ℂ))
      (B0579.cell c) := by
    obtain ⟨Rb, hRb⟩ := him.band
    have hvan : UnforcedLeray.Cyl.VanishesOutside Rb
        (fun x => ladChi tr φ ρ x * (((F x).im : ℝ) : ℂ)) :=
      fun x hx => by simp [hRb x hx]
    rw [hcell]
    exact hvan.integrableOn_cell
      (hchi_s.continuous.mul (Complex.continuous_ofReal.comp him.continuous)) c
  have hzF : ∫ x in B0579.cell c, ladChi tr φ ρ x * F x = 0 := by
    have hpt : (fun x => ladChi tr φ ρ x * F x) = fun x =>
        ladChi tr φ ρ x * (((F x).re : ℝ) : ℂ) +
          (ladChi tr φ ρ x * (((F x).im : ℝ) : ℂ)) * Complex.I := by
      funext x
      have hF_split : F x = (((F x).re : ℝ) : ℂ) + (((F x).im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im (F x)).symm
      conv_lhs => rw [hF_split]
      ring
    rw [hpt, integral_add hint_re (hint_im.mul_const Complex.I), integral_mul_const,
      hz_re, hz_im]
    simp
  set G : ℝ × ℝ → ℝ := fun x => ladCut R x * Complex.normSq (ladChi tr φ ρ x)
  have hGF : (fun x => ladChi tr φ ρ x * F x) = fun x => ((G x : ℝ) : ℂ) := by
    funext x
    simp only [F, G]
    calc ladChi tr φ ρ x * ((ladCut R x : ℂ) * (starRingEnd ℂ) (ladChi tr φ ρ x))
        = (ladCut R x : ℂ) * (ladChi tr φ ρ x * (starRingEnd ℂ) (ladChi tr φ ρ x)) := by ring
      _ = (ladCut R x : ℂ) * (Complex.normSq (ladChi tr φ ρ x) : ℂ) := by rw [Complex.mul_conj]
      _ = ((ladCut R x * Complex.normSq (ladChi tr φ ρ x) : ℝ) : ℂ) := by push_cast; rfl
  have hzG : ∫ x in B0579.cell c, G x = 0 := by
    rw [hGF, integral_complex_ofReal] at hzF
    exact Complex.ofReal_eq_zero.1 hzF
  -- conclude `ladChi tr φ ρ x₀ = 0` via a small square inside `B0579.cell c`
  by_contra hne
  have hGc : Continuous G :=
    (CutLimitAux.continuous_cut R).mul (Complex.continuous_normSq.comp hchi_s.continuous)
  have hG0 : ∀ x : ℝ × ℝ, 0 ≤ G x :=
    fun x => mul_nonneg (CutLimitAux.nonneg R x) (Complex.normSq_nonneg _)
  have hGint : IntegrableOn G (B0579.cell c) := by
    have hvan : UnforcedLeray.Cyl.VanishesOutside (2 * R) G :=
      fun x hx => by simp [G, RateSplitAux.cut_zero hR hx]
    rw [hcell]
    exact hvan.integrableOn_cell hGc c
  have hGx₀ : 0 < G x₀ := by
    simp only [G]
    rw [CutLimitAux.eq_one (le_rfl : |x₀.2| + 1 ≤ R), one_mul]
    exact Complex.normSq_pos.2 hne
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hGc.continuousAt (G x₀ / 2) (half_pos hGx₀)
  have hx₀1 : x₀.1 ∈ Ico (-(c / 2)) (c / 2) := hx₀.1
  set r₀ : ℝ := min (δ / 2) ((c / 2 - x₀.1) / 2)
  have hr₀ : 0 < r₀ := lt_min (half_pos hδ) (by linarith [hx₀1.2])
  set Q : Set (ℝ × ℝ) := Icc x₀.1 (x₀.1 + r₀) ×ˢ Icc x₀.2 (x₀.2 + r₀)
  have hQsub : Q ⊆ B0579.cell c := by
    intro x hx
    refine ⟨⟨by linarith [hx₀1.1, hx.1.1], ?_⟩, mem_univ _⟩
    have hr2 : r₀ ≤ (c / 2 - x₀.1) / 2 := min_le_right _ _
    linarith [hx.1.2, hx₀1.2]
  have hQlow : ∀ x ∈ Q, G x₀ / 2 ≤ G x := by
    intro x hx
    have hr1 : r₀ ≤ δ / 2 := min_le_left _ _
    have hd1 : dist x.1 x₀.1 < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1.1, hx.1.2, hr1, hδ]
    have hd2 : dist x.2 x₀.2 < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.2.1, hx.2.2, hr1, hδ]
    have hd : dist x x₀ < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨hd1, hd2⟩
    have hlt := hδG hd
    rw [Real.dist_eq, abs_lt] at hlt
    linarith [hlt.1]
  have hQmeas : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hQfin : volume Q < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hle1 : ∫ x in Q, G x ≤ ∫ x in B0579.cell c, G x :=
    setIntegral_mono_set hGint (Eventually.of_forall hG0) hQsub.eventuallyLE
  have hle2 : ∫ _ in Q, (G x₀ / 2) ≤ ∫ x in Q, G x :=
    setIntegral_mono_on (integrableOn_const hQfin.ne) (hGint.mono_set hQsub) hQmeas hQlow
  have hvol : volume Q = ENNReal.ofReal r₀ * ENNReal.ofReal r₀ := by
    simp only [Q]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    have e1 : x₀.1 + r₀ - x₀.1 = r₀ := by ring
    have e2 : x₀.2 + r₀ - x₀.2 = r₀ := by ring
    rw [e1, e2]
  have hconst : ∫ _ in Q, (G x₀ / 2) = (r₀ * r₀) * (G x₀ / 2) := by
    rw [setIntegral_const, smul_eq_mul]
    congr 1
    simp only [Measure.real, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr₀.le]
  have hpos : 0 < (r₀ * r₀) * (G x₀ / 2) := by positivity
  linarith [hle1, hle2, hzG, hconst, hpos]

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux
