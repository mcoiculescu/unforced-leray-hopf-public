import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1.PhysCol
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjDtDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.Loc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Test
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.PairCont

/-!
# Cutoff physical-column pairing: continuity and interior derivative

Helper for `PartIII-a:T21/c3/3/1/1/2/2/3/c/1` (`FramePairingFTC`, SP 2905-2925, 2937-2958).
Puts the transverse cutoff `ladCut R` on the jointly smooth physical frame column `physFrameE`,
proves continuity of the cutoff pairing `cutPair` on the closed interval `Icc t₁ s` (using only
`φ ∈ C([t₁, s]; X_{-m,c})`), differentiates `IsFreeAdjointFlow.weak` at interior ages `q ∈ (t₁, s)`,
and establishes `HasDerivAt (cutPair ...) (cutRate ...) q` together with continuity of `cutRate`
on `(t₁, s)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.FramePairing1Aux

/-! ## 1. Definitions and closed-interval continuity of `cutPair` -/

/-- Transverse-cutoff physical frame column `χ_R(x) physFrameE(q, x)`. -/
def cutCol (κ : PlanarFrameKernels) (ν R q : ℝ) (j : Fin 2) (x : ℝ × ℝ) : ℂ :=
  ladCutPhi (fun q' x' => physFrameE κ ν q' j x') R q x

/-- Cutoff physical pairing `∫_{C_{ν⁻²}} χ_R(x) physFrameE(q, x) φ(q, x) dx`. -/
def cutPair (κ : PlanarFrameKernels) (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (R : ℝ) (j : Fin 2)
    (q : ℝ) : ℂ :=
  ∫ x in B0579.cell (ν ^ (-2 : ℝ)), cutCol κ ν R q j x * φ q x

/-- Classical time derivative of `cutPair` on `(t₁, s)`. -/
def cutRate (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (φ : ℝ → ℝ × ℝ → ℂ) (R : ℝ)
    (j : Fin 2) (q : ℝ) : ℂ :=
  ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
    ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x -
      (ν : ℂ) * ladLapCx (cutCol κ ν R q j) x +
      ladTransport tr q (cutCol κ ν R q j) x) * φ q x

/-- `cutPair` is continuous on the entire closed interval `Icc t₁ s` (including `s`). -/
theorem continuousOn_cutPair {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m t₁ s R : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hR : 0 < R)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {g : ℝ × ℝ → ℂ}
    {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ)
    (j : Fin 2) :
    ContinuousOn (cutPair κ ν φ R j) (Icc t₁ s) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameE κ ν p.1 j p.2)
      (Ico t₁ (s + 1) ×ˢ univ) :=
    contDiffOn_physFrameE hκ hν ht₁ j
  intro q hq
  have hwm : ∀ r' ∈ Icc t₁ s, MemLp (φ r') 2 (B0579.cellMeasure c (-m)) := hφ.memX
  have hψm : ∀ r' ∈ Icc t₁ s, MemLp (cutCol κ ν R r' j) 2 (B0579.cellMeasure c (-(-m))) :=
    fun r' hr' => LadPRPairAux.memLp_cutPhi hR hsm ⟨hr'.1, by linarith [hr'.2]⟩ (-(-m))
  have ha : Tendsto (fun r' => (eLpNorm (φ r' - φ q) 2 (B0579.cellMeasure c (-m))).toReal)
      (𝓝[Icc t₁ s] q) (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hφ.strongCont q hq)
    simpa only [Function.comp_def, xNorm, ENNReal.toReal_zero] using h1
  have hb := LadPRPairAux.tendsto_cutDiff (c := c) (m := -(-m)) (t := t₁) (s := s + 1) (r := s)
    (φ := fun q' x' => physFrameE κ ν q' j x') hR (by linarith) hsm hq
  have hcw := LadPRPairAux.pairCW (c := c) (m := -m) (S := Icc t₁ s) hq φ
    (fun r' => cutCol κ ν R r' j) hwm hψm ha hb
  refine hcw.congr (fun r' _ => ?_) ?_
  · unfold cutPair
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  · unfold cutPair
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ## 2. General band-supported cell integral continuity and differentiation -/

/-- Joint continuity of `ladDt ψ` on `Ioo t s ×ˢ univ` for `ψ` jointly smooth on `Ico t s ×ˢ univ`. -/
lemma continuousOn_ladDt_strip {t s : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDt ψ p.1 p.2) (Ioo t s ×ˢ univ) := by
  have hJc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  refine (hJc.mono (prod_mono Ioo_subset_Ico_self subset_rfl)).congr fun p hp => ?_
  exact ladDt_eq_fderivWithin hj hp.1 p.2

/-- Continuity on `Ioo t s` of a cell integral whose integrand is jointly continuous and vanishes
outside a fixed band `|x.2| ≤ B`. -/
lemma continuousOn_cell_band {c t s B : ℝ} (_hB : 0 ≤ B) {H : ℝ → ℝ × ℝ → ℂ}
    (hH_cont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) (Ioo t s ×ˢ univ))
    (hH_van : ∀ r' ∈ Ioo t s, ∀ x : ℝ × ℝ, B < |x.2| → H r' x = 0) :
    ContinuousOn (fun r' => ∫ x in B0579.cell c, H r' x) (Ioo t s) := by
  intro ρ hρ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
  have hIcc : ∀ r' ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r' ∈ Ioo t s := by
    intro r' hr'
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  have hball2 : ∀ r' ∈ Metric.ball ρ (ε / 2), r' ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
    intro r' hr'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr'
    exact ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  set Kx : Set (ℝ × ℝ) := Icc (-(|c| / 2)) (|c| / 2) ×ˢ Icc (-B) B
  have hKxc : IsCompact Kx := isCompact_Icc.prod isCompact_Icc
  set Kc : Set (ℝ × (ℝ × ℝ)) := Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ Kx
  have hKc : IsCompact Kc := isCompact_Icc.prod hKxc
  have hKsub : Kc ⊆ Ioo t s ×ˢ univ := fun p hp => ⟨hIcc p.1 hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hH_cont.mono hKsub)
  set M' : ℝ := max 0 M
  have hbound_int : Integrable (Kx.indicator fun _ => M') (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hKxc.isClosed.measurableSet]
    apply integrableOn_const <;>
      first
      | exact enorm_ne_top
      | exact ne_top_of_le_ne_top hKxc.measure_lt_top.ne (Measure.restrict_apply_le _ _)
  have hF_meas : ∀ᶠ r' in 𝓝 ρ, AEStronglyMeasurable (H r') (volume.restrict (B0579.cell c)) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r' hr' => ?_
    have hc_r : Continuous (H r') :=
      hH_cont.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hr', mem_univ _⟩)
    exact hc_r.aestronglyMeasurable
  have h_bound : ∀ᶠ r' in 𝓝 ρ, ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖H r' x‖ ≤ Kx.indicator (fun _ => M') x := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds ρ (half_pos hε)) fun r' hr' => ?_
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    by_cases hxK : x ∈ Kx
    · rw [Set.indicator_of_mem hxK]
      exact (hM (r', x) ⟨hball2 r' hr', hxK⟩).trans (le_max_right 0 M)
    · rw [Set.indicator_of_notMem hxK]
      have hx1 : x.1 ∈ Icc (-(|c| / 2)) (|c| / 2) := by
        have hx' := (Set.mem_prod.1 hx).1
        have hc_le : c ≤ |c| := le_abs_self c
        exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
      have hB_lt : B < |x.2| := by
        by_contra hcon
        exact hxK ⟨hx1, abs_le.1 (not_lt.1 hcon)⟩
      rw [hH_van r' (hIcc r' (hball2 r' hr')) x hB_lt, norm_zero]
  have h_cont : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ContinuousAt (fun r' => H r' x) ρ := by
    refine Eventually.of_forall fun x => ?_
    have hnhds : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((ρ, x) : ℝ × (ℝ × ℝ)) :=
      prod_mem_nhds (Ioo_mem_nhds hρ.1 hρ.2) univ_mem
    exact (hH_cont.continuousAt hnhds).comp (f := fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ)))
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_of_dominated hF_meas h_bound hbound_int h_cont).continuousWithinAt

/-- Differentiation under the cell integral on `(t, s)` for a jointly smooth band-supported `H`. -/
lemma hasDerivAt_cell_band {c t s B : ℝ} (_hB : 0 ≤ B) {H : ℝ → ℝ × ℝ → ℂ}
    (hH_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) (Ico t s ×ˢ univ))
    (hH_van : ∀ r' ∈ Ioo t s, ∀ x : ℝ × ℝ, B < |x.2| → H r' x = 0)
    {q : ℝ} (hq : q ∈ Ioo t s) :
    IntegrableOn (ladDt H q) (B0579.cell c) ∧
      HasDerivAt (fun r' => ∫ x in B0579.cell c, H r' x)
        (∫ x in B0579.cell c, ladDt H q x) q := by
  have hdt_van : ∀ r' ∈ Ioo t s, ∀ x : ℝ × ℝ, B < |x.2| → ladDt H r' x = 0 := by
    intro r' hr' x hx
    have hev : (fun r'' => H r'' x) =ᶠ[𝓝 r'] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds hr'.1 hr'.2] with r'' hr''
      exact hH_van r'' hr'' x hx
    exact ladDt_eq_of_hasDerivAt ((hasDerivAt_const r' (0 : ℂ)).congr_of_eventuallyEq hev)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have hcont_H : ∀ r' ∈ Ioo t s, Continuous (H r') := fun r' hr' =>
    (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hr') hH_sm).continuous
  have hF_int : Integrable (H q) (volume.restrict (B0579.cell c)) := by
    rw [← IntegrableOn, hcell]
    have hv : UnforcedLeray.Cyl.VanishesOutside B (H q) := hH_van q hq
    exact hv.integrableOn_cell (hcont_H q hq) c
  have hdt_int : IntegrableOn (ladDt H q) (B0579.cell c) := by
    rw [hcell]
    have hv : UnforcedLeray.Cyl.VanishesOutside B (ladDt H q) := hdt_van q hq
    exact hv.integrableOn_cell (continuous_ladDt hH_sm hq) c
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hq.1 hq.2)
  have hs0nhds : Metric.ball q (ε / 2) ∈ 𝓝 q := Metric.ball_mem_nhds q (half_pos hε)
  have hIcc : ∀ r' ∈ Icc (q - ε / 2) (q + ε / 2), r' ∈ Ioo t s := by
    intro r' hr'
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  have hball2 : ∀ r' ∈ Metric.ball q (ε / 2), r' ∈ Icc (q - ε / 2) (q + ε / 2) := by
    intro r' hr'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr'
    exact ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  set Kx : Set (ℝ × ℝ) := Icc (-(|c| / 2)) (|c| / 2) ×ˢ Icc (-B) B
  have hKxc : IsCompact Kx := isCompact_Icc.prod isCompact_Icc
  set Kc : Set (ℝ × (ℝ × ℝ)) := Icc (q - ε / 2) (q + ε / 2) ×ˢ Kx
  have hKc : IsCompact Kc := isCompact_Icc.prod hKxc
  have hKsub : Kc ⊆ Ioo t s ×ˢ univ := fun p hp => ⟨hIcc p.1 hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((continuousOn_ladDt_strip hH_sm).mono hKsub)
  set M' : ℝ := max 0 M
  have hbound_int : Integrable (Kx.indicator fun _ => M') (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hKxc.isClosed.measurableSet]
    apply integrableOn_const <;>
      first
      | exact enorm_ne_top
      | exact ne_top_of_le_ne_top hKxc.measure_lt_top.ne (Measure.restrict_apply_le _ _)
  have h_bound : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ r' ∈ Metric.ball q (ε / 2),
      ‖ladDt H r' x‖ ≤ Kx.indicator (fun _ => M') x := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (Eventually.of_forall fun x hx r' hr' => ?_)
    by_cases hxK : x ∈ Kx
    · rw [Set.indicator_of_mem hxK]
      exact (hM (r', x) ⟨hball2 r' hr', hxK⟩).trans (le_max_right 0 M)
    · rw [Set.indicator_of_notMem hxK]
      have hx1 : x.1 ∈ Icc (-(|c| / 2)) (|c| / 2) := by
        have hx' := (Set.mem_prod.1 hx).1
        have hc_le : c ≤ |c| := le_abs_self c
        exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
      have hB_lt : B < |x.2| := by
        by_contra hcon
        exact hxK ⟨hx1, abs_le.1 (not_lt.1 hcon)⟩
      rw [hdt_van r' (hIcc r' (hball2 r' hr')) x hB_lt, norm_zero]
  have h_diff : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ r' ∈ Metric.ball q (ε / 2),
      HasDerivAt (fun r'' => H r'' x) (ladDt H r' x) r' :=
    Eventually.of_forall fun x r' hr' => ladDt_hasDerivAt hH_sm (hIcc r' (hball2 r' hr')) x
  have hF_meas : ∀ᶠ r' in 𝓝 q, AEStronglyMeasurable (H r') (volume.restrict (B0579.cell c)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hq.1 hq.2) fun r' hr' =>
      (hcont_H r' hr').aestronglyMeasurable
  exact ⟨hdt_int, (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs0nhds hF_meas hF_int
    hdt_int.aestronglyMeasurable h_bound hbound_int h_diff).2⟩

/-! ## 3. Classical interior pairing of `IsFreeAdjointFlow` -/

/-- Differentiating `IsFreeAdjointFlow.weak` at an interior age `q ∈ (t₁, s)`. -/
theorem freeAdj_dt_pairing {ν c m t₁ s : ℝ} (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointFlow ν c m tr t₁ s g φ) {q : ℝ} (hq : q ∈ Ioo t₁ s)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => ladDt φ q x * (ψ x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, ladDt φ q x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, freeAdjIntegrand tr (φ q) q ψ x := by
  obtain ⟨R₀, hR₀⟩ := hψ.band
  set B : ℝ := max 0 R₀
  have hB0 : 0 ≤ B := le_max_left 0 R₀
  have hψ_van : ∀ x : ℝ × ℝ, B < |x.2| → ψ x = 0 :=
    fun x hx => hR₀ x ((le_max_right 0 R₀).trans_lt hx)
  have hpdz : ∀ j : Fin 2, ∀ x : ℝ × ℝ, B < |x.2| → B0579.pd j ψ x = 0 := by
    intro j x hx
    show fderiv ℝ ψ x (B0579.dir j) = 0
    exact mpVanishFderiv hψ_van (B0579.dir j) x hx
  have hlapz : ∀ x : ℝ × ℝ, B < |x.2| → UnforcedLeray.Short.IIb.lapP ψ x = 0 := by
    intro x hx
    unfold UnforcedLeray.Short.IIb.lapP
    have h1 : B0579.pd 0 (B0579.pd 0 ψ) x = 0 :=
      mpVanishFderiv (hpdz 0) (B0579.dir 0) x hx
    have h2 : B0579.pd 1 (B0579.pd 1 ψ) x = 0 :=
      mpVanishFderiv (hpdz 1) (B0579.dir 1) x hx
    rw [h1, h2, add_zero]
  -- Continuity of `Af r' = ∫ freeAdjIntegrand` on `Ioo t₁ s`
  set Af : ℝ → ℂ := fun r' => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r') r' ψ x
  have hAf_cont : ContinuousOn Af (Ioo t₁ s) := by
    refine continuousOn_cell_band hB0 ?_ ?_
    · have hjc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t₁ s ×ˢ univ) :=
        hφ.jointSmooth.continuousOn.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
      have hsub0 : Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici 0 ×ˢ univ :=
        fun p hp => ⟨ht₁.trans hp.1.1.le, mem_univ _⟩
      have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ioo t₁ s ×ˢ univ) :=
        tr.isTrain.smooth_v.continuousOn.mono hsub0
      have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (Ioo t₁ s ×ˢ univ) :=
        ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn hvS
      have hv1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (Ioo t₁ s ×ˢ univ) :=
        ((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn hvS
      have hlapC : Continuous (UnforcedLeray.Short.IIb.lapP ψ) := by
        unfold UnforcedLeray.Short.IIb.lapP
        exact ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
      have hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.IIb.lapP ψ p.2)
          (Ioo t₁ s ×ˢ univ) := hlapC.comp_continuousOn continuousOn_snd
      have hD0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 0 ψ p.2) (Ioo t₁ s ×ˢ univ) :=
        (hψ.pd 0).continuous.comp_continuousOn continuousOn_snd
      have hD1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 ψ p.2) (Ioo t₁ s ×ˢ univ) :=
        (hψ.pd 1).continuous.comp_continuousOn continuousOn_snd
      have hreal : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
          ν * UnforcedLeray.Short.IIb.lapP ψ p.2 -
            (tr.v p.1 p.2 0 * B0579.pd 0 ψ p.2 + tr.v p.1 p.2 1 * B0579.pd 1 ψ p.2))
          (Ioo t₁ s ×ˢ univ) :=
        (continuousOn_const.mul hL).sub ((hv0.mul hD0).add (hv1.mul hD1))
      exact hjc.mul (Complex.continuous_ofReal.comp_continuousOn hreal)
    · intro r' _ x hx
      unfold freeAdjIntegrand
      simp [hlapz x hx, hpdz 0 x hx, hpdz 1 x hx]
  -- Derivative from `IsFreeAdjointFlow.weak`
  have hts : t₁ < s := hq.1.trans hq.2
  have hint : IntervalIntegrable Af volume q s :=
    (hφ.timeIntegrable ψ hψ).mono_set (by
      rw [Set.uIcc_of_le hts.le, Set.uIcc_of_le hq.2.le]
      exact Icc_subset_Icc hq.1.le le_rfl)
  have hmeas : StronglyMeasurableAtFilter Af (𝓝 q) :=
    hAf_cont.stronglyMeasurableAtFilter isOpen_Ioo q hq
  have hcA : ContinuousAt Af q := hAf_cont.continuousAt (Ioo_mem_nhds hq.1 hq.2)
  have hder1 : HasDerivAt (fun r' => ∫ x in B0579.cell c, φ r' x * (ψ x : ℂ)) (-Af q) q := by
    have h0 : HasDerivAt (fun r' => (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ ρ in r'..s, Af ρ)
        (-Af q) q := by
      simpa using (intervalIntegral.integral_hasDerivAt_left hint hmeas hcA).const_add
        (∫ x in B0579.cell c, g x * (ψ x : ℂ))
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hq.1 hq.2] with r' hr'
    exact hφ.weak ψ hψ r' hr'
  -- Derivative under the integral on the compact band
  have hψ_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (ψ p.2 : ℂ)) (Ico t₁ s ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hψ.smooth.comp contDiff_snd)).contDiffOn
  obtain ⟨hdt_int0, hder2_0⟩ := hasDerivAt_cell_band (c := c) (H := fun r' x => φ r' x * (ψ x : ℂ))
    hB0 (show ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2 * (ψ p.2 : ℂ)) (Ico t₁ s ×ˢ univ)
      from hφ.jointSmooth.mul hψ_sm)
    (fun _ _ x hx => by rw [hψ_van x hx]; simp) hq
  have hdt_eq : ladDt (fun r' x => φ r' x * (ψ x : ℂ)) q = fun x => ladDt φ q x * (ψ x : ℂ) := by
    funext x
    exact ladDt_eq_of_hasDerivAt ((ladDt_hasDerivAt hφ.jointSmooth hq x).mul_const (ψ x : ℂ))
  rw [hdt_eq] at hdt_int0 hder2_0
  exact ⟨hdt_int0, hder2_0.unique hder1⟩

/-! ## 4. Derivative of `cutPair` and continuity of `cutRate` on `(t₁, s)` -/

/-- Decomposition of `pdCx k F` into real and imaginary parts for smooth `F`. -/
lemma pdCx_re_im {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k F x =
      (B0579.pd k (fun y => (F y).re) x : ℂ) +
        Complex.I * (B0579.pd k (fun y => (F y).im) x : ℂ) := by
  have hre : ContDiff ℝ ∞ (fun y => (F y).re) := Complex.reCLM.contDiff.comp hF
  have him : ContDiff ℝ ∞ (fun y => (F y).im) := Complex.imCLM.contDiff.comp hF
  have hFeq : F = fun y => (((F y).re : ℝ) : ℂ) + Complex.I * (((F y).im : ℝ) : ℂ) := by
    funext y
    have hri := (Complex.re_add_im (F y)).symm
    linear_combination hri
  have hd_re : DifferentiableAt ℝ (fun y => (((F y).re : ℝ) : ℂ)) x :=
    ((RateSplitAux.contDiff_ofReal hre).differentiable (by simp)) x
  have hd_im : DifferentiableAt ℝ (fun y => (((F y).im : ℝ) : ℂ)) x :=
    ((RateSplitAux.contDiff_ofReal him).differentiable (by simp)) x
  have hd_Iim : DifferentiableAt ℝ (fun y => Complex.I * (((F y).im : ℝ) : ℂ)) x :=
    (differentiableAt_const Complex.I).mul hd_im
  conv_lhs => rw [hFeq]
  rw [RateSplitAux.pdCx_add k hd_re hd_Iim,
    RateSplitAux.pdCx_ofReal k ((hre.differentiable (by simp)) x),
    RateSplitAux.pdCx_mul k (differentiableAt_const Complex.I) hd_im,
    RateSplitAux.pdCx_ofReal k ((him.differentiable (by simp)) x)]
  have hc0 : pdCx k (fun _ : ℝ × ℝ => Complex.I) x = 0 := by unfold pdCx; simp
  rw [hc0, zero_mul, zero_add]

/-- Decomposition of `ladLapCx F` into real and imaginary parts for smooth `F`. -/
lemma ladLapCx_re_im {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ × ℝ) :
    ladLapCx F x =
      (UnforcedLeray.Short.IIb.lapP (fun y => (F y).re) x : ℂ) +
        Complex.I * (UnforcedLeray.Short.IIb.lapP (fun y => (F y).im) x : ℂ) := by
  have h2 : ∀ k : Fin 2, pdCx k (pdCx k F) x =
      (B0579.pd k (B0579.pd k (fun y => (F y).re)) x : ℂ) +
        Complex.I * (B0579.pd k (B0579.pd k (fun y => (F y).im)) x : ℂ) := by
    intro k
    have hre1 : ContDiff ℝ ∞ (B0579.pd k (fun y => (F y).re)) :=
      ForceMemXAux.contDiff_pd (Complex.reCLM.contDiff.comp hF) k
    have him1 : ContDiff ℝ ∞ (B0579.pd k (fun y => (F y).im)) :=
      ForceMemXAux.contDiff_pd (Complex.imCLM.contDiff.comp hF) k
    have h1 : pdCx k F = fun y =>
        (B0579.pd k (fun z => (F z).re) y : ℂ) +
          Complex.I * (B0579.pd k (fun z => (F z).im) y : ℂ) :=
      funext (pdCx_re_im hF k)
    rw [h1]
    have hd_re : DifferentiableAt ℝ (fun y => (B0579.pd k (fun z => (F z).re) y : ℂ)) x :=
      ((RateSplitAux.contDiff_ofReal hre1).differentiable (by simp)) x
    have hd_im : DifferentiableAt ℝ (fun y => (B0579.pd k (fun z => (F z).im) y : ℂ)) x :=
      ((RateSplitAux.contDiff_ofReal him1).differentiable (by simp)) x
    have hd_Iim : DifferentiableAt ℝ
        (fun y => Complex.I * (B0579.pd k (fun z => (F z).im) y : ℂ)) x :=
      (differentiableAt_const Complex.I).mul hd_im
    rw [RateSplitAux.pdCx_add k hd_re hd_Iim,
      RateSplitAux.pdCx_ofReal k ((hre1.differentiable (by simp)) x),
      RateSplitAux.pdCx_mul k (differentiableAt_const Complex.I) hd_im,
      RateSplitAux.pdCx_ofReal k ((him1.differentiable (by simp)) x)]
    have hc0 : pdCx k (fun _ : ℝ × ℝ => Complex.I) x = 0 := by unfold pdCx; simp
    rw [hc0, zero_mul, zero_add]
  unfold ladLapCx UnforcedLeray.Short.IIb.lapP
  rw [h2 0, h2 1]
  push_cast
  ring

/-- Joint `C^∞` smoothness of `cutCol` on `Ico t₁ S ×ˢ univ` for `R > 0`. -/
lemma contDiffOn_cutCol {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν t₁ S R : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hR : 0 < R) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cutCol κ ν R p.1 j p.2) (Ico t₁ S ×ˢ univ) := by
  obtain ⟨_, _, hK⟩ := ladCutProps
  have hcut : ContDiff ℝ ∞ (ladCut R) := ((hK R hR).1 (ν ^ (-2 : ℝ))).smooth
  have hcut_p : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (ladCut R p.2 : ℂ)) (Ico t₁ S ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hcut.comp contDiff_snd)).contDiffOn
  exact hcut_p.mul (contDiffOn_physFrameE hκ hν ht₁ j)

/-- Interior derivative `HasDerivAt (cutPair κ ν φ R j) (cutRate κ tr φ R j q) q` on `(t₁, s)`. -/
theorem hasDerivAt_cutPair {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m t₁ s R : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hR : 0 < R)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {g : ℝ × ℝ → ℂ}
    {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ)
    (j : Fin 2) {q : ℝ} (hq : q ∈ Ioo t₁ s) :
    HasDerivAt (cutPair κ ν φ R j) (cutRate κ tr φ R j q) q := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hB0 : (0 : ℝ) ≤ 2 * R := by linarith
  have hcut_van : ∀ r' : ℝ, ∀ x : ℝ × ℝ, 2 * R < |x.2| → cutCol κ ν R r' j x = 0 := by
    intro r' x hx
    unfold cutCol ladCutPhi
    rw [LadPRPairAux.cut_zero hR hx, Complex.ofReal_zero, zero_mul]
  have hsm_col : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cutCol κ ν R p.1 j p.2)
      (Ico t₁ s ×ˢ univ) := contDiffOn_cutCol hκ hν ht₁ hR j
  have hsm_E : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameE κ ν p.1 j p.2)
      (Ico t₁ s ×ˢ univ) := contDiffOn_physFrameE hκ hν ht₁ j
  -- Differentiate `r' ↦ ∫ cutCol * φ` under the integral
  obtain ⟨_, hder_prod⟩ := hasDerivAt_cell_band (c := c)
    (H := fun r' y => cutCol κ ν R r' j y * φ r' y) hB0
    (show ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cutCol κ ν R p.1 j p.2 * φ p.1 p.2)
      (Ico t₁ s ×ˢ univ) from hsm_col.mul hφ.jointSmooth)
    (fun r' _ x hx => by rw [hcut_van r' x hx, zero_mul]) hq
  -- Pointwise product rule for `ladDt (cutCol * φ)`
  have hdt_prod : ∀ x : ℝ × ℝ,
      ladDt (fun r' y => cutCol κ ν R r' j y * φ r' y) q x =
        ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x) * φ q x +
          cutCol κ ν R q j x * ladDt φ q x := by
    intro x
    have hd1 : HasDerivAt (fun r' => cutCol κ ν R r' j x)
        ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x) q := by
      unfold cutCol ladCutPhi
      exact (ladDt_hasDerivAt hsm_E hq x).const_mul (ladCut R x : ℂ)
    have hd2 : HasDerivAt (fun r' => φ r' x) (ladDt φ q x) q :=
      ladDt_hasDerivAt hφ.jointSmooth hq x
    exact ladDt_eq_of_hasDerivAt (hd1.mul hd2)
  -- Integrability of the two summands on `cell c`
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have hint1 : IntegrableOn
      (fun x => ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x) * φ q x)
      (B0579.cell c) := by
    rw [hcell]
    have hv : UnforcedLeray.Cyl.VanishesOutside (2 * R)
        (fun x => ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x) * φ q x) :=
      fun x hx => by simp [LadPRPairAux.cut_zero hR hx]
    have hc1 : Continuous
        (fun x => ((ladCut R x : ℂ) * ladDt (fun q' x' => physFrameE κ ν q' j x') q x) * φ q x) :=
      ((Complex.continuous_ofReal.comp (LadPRPairAux.cut_continuous R)).mul
        (continuous_ladDt hsm_E hq)).mul (hφ.smooth q (Ioo_subset_Ico_self hq)).continuous
    exact hv.integrableOn_cell hc1 c
  -- Cylinder test properties of `Re (cutCol)` and `Im (cutCol)`
  have hcol_slice : ContDiff ℝ ∞ (cutCol κ ν R q j) :=
    RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hq) hsm_col
  obtain ⟨_, _, hK⟩ := ladCutProps
  have hcol_per : ∀ x : ℝ × ℝ, cutCol κ ν R q j (x.1 + c, x.2) = cutCol κ ν R q j x := by
    intro x
    unfold cutCol ladCutPhi
    dsimp only
    rw [((hK R hR).1 c).periodic x, physFrameE_periodic κ ν q j x]
  obtain ⟨hψ_re, hψ_im⟩ :=
    LadPRTestAux.isCylTest_re_im hcol_slice hcol_per (2 * R) (hcut_van q)
  obtain ⟨hint_re, hpair_re⟩ := freeAdj_dt_pairing ht₁ hφ hq hψ_re
  obtain ⟨hint_im, hpair_im⟩ := freeAdj_dt_pairing ht₁ hφ hq hψ_im
  have hint2 : IntegrableOn (fun x => cutCol κ ν R q j x * ladDt φ q x) (B0579.cell c) := by
    have heq2 : (fun x => cutCol κ ν R q j x * ladDt φ q x) = fun x =>
        ladDt φ q x * ((cutCol κ ν R q j x).re : ℂ) +
          Complex.I * (ladDt φ q x * ((cutCol κ ν R q j x).im : ℂ)) := by
      funext x
      have hri := (Complex.re_add_im (cutCol κ ν R q j x)).symm
      calc cutCol κ ν R q j x * ladDt φ q x
          = (((cutCol κ ν R q j x).re : ℂ) + ((cutCol κ ν R q j x).im : ℂ) * Complex.I) *
              ladDt φ q x := by rw [← hri]
        _ = ladDt φ q x * ((cutCol κ ν R q j x).re : ℂ) +
              Complex.I * (ladDt φ q x * ((cutCol κ ν R q j x).im : ℂ)) := by ring
    rw [heq2]
    exact hint_re.add (hint_im.const_mul Complex.I)
  -- Evaluate `∫ cutCol * ladDt φ` via `freeAdj_dt_pairing`
  have hpair_col : ∫ x in B0579.cell c, cutCol κ ν R q j x * ladDt φ q x =
      ∫ x in B0579.cell c,
        (-(ν : ℂ) * ladLapCx (cutCol κ ν R q j) x +
          ladTransport tr q (cutCol κ ν R q j) x) * φ q x := by
    have heq2 : ∀ x : ℝ × ℝ, cutCol κ ν R q j x * ladDt φ q x =
        ladDt φ q x * ((cutCol κ ν R q j x).re : ℂ) +
          Complex.I * (ladDt φ q x * ((cutCol κ ν R q j x).im : ℂ)) := by
      intro x
      have hri := (Complex.re_add_im (cutCol κ ν R q j x)).symm
      calc cutCol κ ν R q j x * ladDt φ q x
          = (((cutCol κ ν R q j x).re : ℂ) + ((cutCol κ ν R q j x).im : ℂ) * Complex.I) *
              ladDt φ q x := by rw [← hri]
        _ = ladDt φ q x * ((cutCol κ ν R q j x).re : ℂ) +
              Complex.I * (ladDt φ q x * ((cutCol κ ν R q j x).im : ℂ)) := by ring
    have hf_re := hφ.integrable _ hψ_re q (Ioo_subset_Icc_self hq)
    have hf_im := hφ.integrable _ hψ_im q (Ioo_subset_Icc_self hq)
    rw [integral_congr_ae (Eventually.of_forall heq2),
      integral_add hint_re (hint_im.const_mul Complex.I), integral_const_mul,
      hpair_re, hpair_im]
    have hcomb : -(∫ x in B0579.cell c, freeAdjIntegrand tr (φ q) q
          (fun y => (cutCol κ ν R q j y).re) x) +
        Complex.I * -(∫ x in B0579.cell c, freeAdjIntegrand tr (φ q) q
          (fun y => (cutCol κ ν R q j y).im) x) =
        ∫ x in B0579.cell c,
          (-freeAdjIntegrand tr (φ q) q (fun y => (cutCol κ ν R q j y).re) x -
            Complex.I * freeAdjIntegrand tr (φ q) q (fun y => (cutCol κ ν R q j y).im) x) := by
      have hsub := integral_sub hf_re.neg (hf_im.const_mul Complex.I)
      dsimp only [Pi.neg_apply, c] at hsub ⊢
      rw [hsub, integral_neg, integral_const_mul]
      ring
    rw [hcomb]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    unfold freeAdjIntegrand ladTransport
    rw [ladLapCx_re_im hcol_slice x, pdCx_re_im hcol_slice 0 x, pdCx_re_im hcol_slice 1 x]
    push_cast
    ring
  -- Combine with `hint1` to form `cutRate`
  have hint_rhs : IntegrableOn
      (fun x => (-(ν : ℂ) * ladLapCx (cutCol κ ν R q j) x +
        ladTransport tr q (cutCol κ ν R q j) x) * φ q x)
      (B0579.cell c) := by
    have hf_re := hφ.integrable _ hψ_re q (Ioo_subset_Icc_self hq)
    have hf_im := hφ.integrable _ hψ_im q (Ioo_subset_Icc_self hq)
    refine (hf_re.neg.sub (hf_im.const_mul Complex.I)).congr_fun (fun x _ => ?_)
      (B0579.measurableSet_cell c)
    simp only [Pi.sub_apply, Pi.neg_apply, freeAdjIntegrand, ladTransport]
    rw [ladLapCx_re_im hcol_slice x, pdCx_re_im hcol_slice 0 x, pdCx_re_im hcol_slice 1 x]
    push_cast
    ring
  refine hder_prod.congr_deriv ?_
  rw [integral_congr_ae (Eventually.of_forall hdt_prod), integral_add hint1 hint2, hpair_col,
    ← integral_add hint1 hint_rhs]
  unfold cutRate
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

/-- `cutRate` is continuous on the open interval `Ioo t₁ s` for `R > 0`. -/
theorem continuousOn_cutRate {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν m t₁ s R : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hR : 0 < R)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {g : ℝ × ℝ → ℂ}
    {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ)
    (j : Fin 2) :
    ContinuousOn (cutRate κ tr φ R j) (Ioo t₁ s) := by
  have hB0 : (0 : ℝ) ≤ 2 * R := by linarith
  have hsm_col : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cutCol κ ν R p.1 j p.2)
      (Ico t₁ s ×ˢ univ) := contDiffOn_cutCol hκ hν ht₁ hR j
  have hsm_E : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameE κ ν p.1 j p.2)
      (Ico t₁ s ×ˢ univ) := contDiffOn_physFrameE hκ hν ht₁ j
  refine continuousOn_cell_band hB0 ?_ ?_
  · have hsub : Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t₁ s ×ˢ univ :=
      prod_mono Ioo_subset_Ico_self subset_rfl
    have hsub0 : Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici 0 ×ˢ univ :=
      fun p hp => ⟨ht₁.trans hp.1.1.le, mem_univ _⟩
    have hc_cut : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => (ladCut R p.2 : ℂ)) (Ioo t₁ s ×ˢ univ) :=
      (Complex.continuous_ofReal.comp ((LadPRPairAux.cut_continuous R).comp continuous_snd)).continuousOn
    have hc_dt : ContinuousOn
        (fun p : ℝ × (ℝ × ℝ) => ladDt (fun q' x' => physFrameE κ ν q' j x') p.1 p.2)
        (Ioo t₁ s ×ˢ univ) :=
      continuousOn_ladDt_strip hsm_E
    have hc_lap : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladLapCx (cutCol κ ν R p.1 j) p.2)
        (Ioo t₁ s ×ˢ univ) :=
      (jointSmooth_ladLapCx hsm_col).continuousOn.mono hsub
    have hc_pd0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx 0 (cutCol κ ν R p.1 j) p.2)
        (Ioo t₁ s ×ˢ univ) :=
      (jointSmooth_pdCx hsm_col 0).continuousOn.mono hsub
    have hc_pd1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx 1 (cutCol κ ν R p.1 j) p.2)
        (Ioo t₁ s ×ˢ univ) :=
      (jointSmooth_pdCx hsm_col 1).continuousOn.mono hsub
    have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ioo t₁ s ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn.mono hsub0
    have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ((tr.v p.1 p.2 0 : ℝ) : ℂ))
        (Ioo t₁ s ×ˢ univ) :=
      Complex.continuous_ofReal.comp_continuousOn
        (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn hvS)
    have hv1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ((tr.v p.1 p.2 1 : ℝ) : ℂ))
        (Ioo t₁ s ×ˢ univ) :=
      Complex.continuous_ofReal.comp_continuousOn
        (((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn hvS)
    have hc_tr : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladTransport tr p.1 (cutCol κ ν R p.1 j) p.2)
        (Ioo t₁ s ×ˢ univ) :=
      (hv0.mul hc_pd0).add (hv1.mul hc_pd1)
    have hc_φ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t₁ s ×ˢ univ) :=
      hφ.jointSmooth.continuousOn.mono hsub
    exact (((hc_cut.mul hc_dt).sub (continuousOn_const.mul hc_lap)).add hc_tr).mul hc_φ
  · intro r' _ x hx
    have hvan : ∀ y : ℝ × ℝ, 2 * R < |y.2| → cutCol κ ν R r' j y = 0 := by
      intro y hy
      unfold cutCol ladCutPhi
      rw [LadPRPairAux.cut_zero hR hy, Complex.ofReal_zero, zero_mul]
    have hopen : IsOpen {w : ℝ × ℝ | 2 * R < |w.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev0 : cutCol κ ν R r' j =ᶠ[𝓝 x] (0 : ℝ × ℝ → ℂ) := by
      filter_upwards [hopen.mem_nhds hx] with w hw
      exact hvan w hw
    have hpd0 : ∀ k : Fin 2, ∀ y : ℝ × ℝ, 2 * R < |y.2| → pdCx k (cutCol κ ν R r' j) y = 0 := by
      intro k y hy
      unfold pdCx
      have hevy : cutCol κ ν R r' j =ᶠ[𝓝 y] (0 : ℝ × ℝ → ℂ) := by
        filter_upwards [hopen.mem_nhds hy] with w hw
        exact hvan w hw
      rw [hevy.fderiv_eq]; simp
    have hlap0 : ladLapCx (cutCol κ ν R r' j) x = 0 := by
      unfold ladLapCx
      have h0 : pdCx 0 (pdCx 0 (cutCol κ ν R r' j)) x = 0 := by
        change fderiv ℝ (pdCx 0 (cutCol κ ν R r' j)) x (B0579.dir 0) = 0
        have hev : pdCx 0 (cutCol κ ν R r' j) =ᶠ[𝓝 x] (0 : ℝ × ℝ → ℂ) := by
          filter_upwards [hopen.mem_nhds hx] with w hw
          exact hpd0 0 w hw
        rw [hev.fderiv_eq]; simp
      have h1 : pdCx 1 (pdCx 1 (cutCol κ ν R r' j)) x = 0 := by
        change fderiv ℝ (pdCx 1 (cutCol κ ν R r' j)) x (B0579.dir 1) = 0
        have hev : pdCx 1 (cutCol κ ν R r' j) =ᶠ[𝓝 x] (0 : ℝ × ℝ → ℂ) := by
          filter_upwards [hopen.mem_nhds hx] with w hw
          exact hpd0 1 w hw
        rw [hev.fderiv_eq]; simp
      rw [h0, h1, add_zero]
    unfold ladTransport
    rw [LadPRPairAux.cut_zero hR hx, hlap0, hpd0 0 x hx, hpd0 1 x hx]
    simp

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.FramePairing1Aux
