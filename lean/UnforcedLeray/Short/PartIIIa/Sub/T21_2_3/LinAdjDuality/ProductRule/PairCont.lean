import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont

/-!
# Continuity of the cut pairing (`LadPRPair`, SP 3074-3075)

The cut pairing `P_R(ρ) = ∫_{C_c} w(ρ) χ_R φ(ρ)` is continuous on `[t, r]`: the weighted
Cauchy-Schwarz bound (`PairContAux.holder`) splits the increment as in `ladPairCont`, and the
cut test `χ_R φ(ρ)` is continuous in `ρ` in `X_{-m,c}` because it is supported in the compact
box `|η| ≤ 2R` and jointly continuous there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadPRPairAux

lemma cut_nonneg (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x := Real.smoothTransition.nonneg _

lemma cut_le_one (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 := Real.smoothTransition.le_one _

lemma cut_zero {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) : ladCut R x = 0 := by
  unfold ladCut
  apply Real.smoothTransition.zero_of_nonpos
  have hp : 0 < (|x.2| - 2 * R) * (|x.2| + 2 * R) :=
    mul_pos (sub_pos.2 hx) (by linarith [abs_nonneg x.2])
  have hsq := sq_abs x.2
  have h2 : 2 * R ^ 2 ≤ x.2 ^ 2 := by nlinarith
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  linarith

lemma cut_continuous (R : ℝ) : Continuous (fun x : ℝ × ℝ => ladCut R x) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp (by fun_prop)

lemma not_mem_box_gt {c R : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hxK : x ∉ B0579.box c (2 * R)) : 2 * R < |x.2| := by
  by_contra h
  exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h))

lemma cellMeasure_lt_top {c m : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    B0579.cellMeasure c m K < ⊤ := by
  have hcont : ContinuousOn (fun x : ℝ × ℝ => B0579.jb x ^ m) K :=
    (B0579.continuous_jb_rpow m).continuousOn
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hcont).bddAbove
  rw [B0579.cellMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, (B0579.density m x : ℝ≥0∞) ∂(volume.restrict (B0579.cell c))
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂(volume.restrict (B0579.cell c)) := by
        refine setLIntegral_mono' hK.measurableSet (fun x hx => ?_)
        show ENNReal.ofReal (B0579.jb x ^ m) ≤ ENNReal.ofReal C
        exact ENNReal.ofReal_le_ofReal (hC (Set.mem_image_of_mem _ hx))
    _ = ENNReal.ofReal C * (volume.restrict (B0579.cell c)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

/-- A function vanishing on the cell off a compact `K` with `‖F‖ ≤ ε` on `K` has
`X_{m,c}`-norm at most `ε · μ(K)^{1/2}`. -/
lemma eLpNorm_le_of_bdd {c m : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) {F : ℝ × ℝ → ℂ}
    {ε : ℝ} (hε : 0 ≤ ε) (hF : ∀ x ∈ B0579.cell c, x ∉ K → F x = 0)
    (hb : ∀ x ∈ K, ‖F x‖ ≤ ε) :
    eLpNorm F 2 (B0579.cellMeasure c m) ≤
      ENNReal.ofReal ε * (B0579.cellMeasure c m K) ^ (2⁻¹ : ℝ) := by
  have hcell : ∀ᵐ x ∂(B0579.cellMeasure c m), x ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  have hmono : eLpNorm F 2 (B0579.cellMeasure c m) ≤
      eLpNorm (K.indicator fun _ => ε) 2 (B0579.cellMeasure c m) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hcell] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, Real.norm_of_nonneg hε]
      exact hb x hxK
    · rw [Set.indicator_of_notMem hxK, hF x hx hxK, norm_zero, norm_zero]
  refine hmono.trans ?_
  rw [eLpNorm_indicator_const hK.measurableSet (by norm_num) (by norm_num),
    Real.enorm_of_nonneg hε]
  norm_num

/-- The slice `ρ ↦ φ ρ` is continuous on `ℝ²` for `ρ ∈ [t, s)`. -/
lemma phi_slice_cont {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ico t s) : Continuous (φ ρ) := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => φ ρ x) univ :=
    hφs.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hρ, mem_univ x⟩)
  exact continuousOn_univ.1 h1

lemma memLp_cutPhi {c t s R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ico t s) (n : ℝ) :
    MemLp (ladCutPhi φ R ρ) 2 (B0579.cellMeasure c n) := by
  have hcc : Continuous (ladCutPhi φ R ρ) := by
    unfold ladCutPhi
    exact (Complex.continuous_ofReal.comp (cut_continuous R)).mul (phi_slice_cont hφs hρ)
  have hK : IsCompact (B0579.box c (2 * R)) := B0579.isCompact_box c (2 * R)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcc.continuousOn
  refine ⟨hcc.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (eLpNorm_le_of_bdd (m := n) hK (abs_nonneg C) ?_ ?_) ?_
  · intro x hx hxK
    unfold ladCutPhi
    rw [cut_zero hR (not_mem_box_gt hx hxK)]
    simp
  · intro x hx
    exact (hC x hx).trans (le_abs_self C)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (cellMeasure_lt_top hK).ne))

/-- Continuity in `ρ` of the cut test in `X_{-m,c}`. -/
lemma tendsto_cutDiff {c m t s r R : ℝ} (hR : 0 < R) (hr : r < s) {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Icc t r) :
    Tendsto (fun ρ' => (eLpNorm (ladCutPhi φ R ρ' - ladCutPhi φ R ρ) 2
      (B0579.cellMeasure c m)).toReal) (𝓝[Icc t r] ρ) (𝓝 0) := by
  have hK : IsCompact (B0579.box c (2 * R)) := B0579.isCompact_box c (2 * R)
  have hS : IsCompact (Icc t r ×ˢ B0579.box c (2 * R)) := isCompact_Icc.prod hK
  have hsub : Icc t r ×ˢ B0579.box c (2 * R) ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr⟩) (subset_univ _)
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (Icc t r ×ˢ B0579.box c (2 * R)) :=
    hφs.continuousOn.mono hsub
  have hunif := hS.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  set a : ℝ := ((B0579.cellMeasure c m (B0579.box c (2 * R))).toReal) ^ (2⁻¹ : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hunif (ε / (a + 1)) (by positivity)
  have h1 : ∀ᶠ ρ' in 𝓝 ρ, dist ρ' ρ < δ := Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hy⟩
  have h2 : ∀ᶠ ρ' in 𝓝[Icc t r] ρ, dist ρ' ρ < δ := nhdsWithin_le_nhds h1
  filter_upwards [eventually_mem_nhdsWithin, h2] with ρ' hρ' hd
  have hε' : 0 ≤ ε / (a + 1) := by positivity
  have hbd := eLpNorm_le_of_bdd (c := c) (m := m) hK hε'
    (F := ladCutPhi φ R ρ' - ladCutPhi φ R ρ) ?_ ?_
  · have hne : ENNReal.ofReal (ε / (a + 1)) * (B0579.cellMeasure c m (B0579.box c (2 * R))) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (cellMeasure_lt_top hK).ne)
    have hreal := ENNReal.toReal_mono hne hbd
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε', ← ENNReal.toReal_rpow] at hreal
    have key : ε / (a + 1) * a < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    exact lt_of_le_of_lt hreal key
  · intro x hx hxK
    rw [Pi.sub_apply]
    unfold ladCutPhi
    rw [cut_zero hR (not_mem_box_gt hx hxK)]
    simp
  · intro x hxK
    rw [Pi.sub_apply]
    have hF : ladCutPhi φ R ρ' x - ladCutPhi φ R ρ x =
        (ladCut R x : ℂ) * (φ ρ' x - φ ρ x) := by
      unfold ladCutPhi; ring
    rw [hF, norm_mul]
    have hc : ‖(ladCut R x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (cut_nonneg R x)]
      exact cut_le_one R x
    have hdist := hδ' (ρ', x) ⟨hρ', hxK⟩ (ρ, x) ⟨hρ, hxK⟩
      (by
        rw [Prod.dist_eq, dist_self, max_lt_iff]
        exact ⟨hd, hδ⟩)
    rw [← dist_eq_norm]
    calc ‖(ladCut R x : ℂ)‖ * dist (φ ρ' x) (φ ρ x) ≤ 1 * dist (φ ρ' x) (φ ρ x) :=
          mul_le_mul_of_nonneg_right hc dist_nonneg
      _ ≤ ε / (a + 1) := by rw [one_mul]; exact hdist.le

/-- Abstract continuity of a weighted pairing `ρ ↦ ∫ w(ρ) ψ(ρ)` within a set `S`, from the
`X_m`-continuity of `w` and the `X_{-m}`-continuity of `ψ` (weighted Cauchy-Schwarz,
`PairContAux.holder`; the splitting of `ladPairCont`). -/
lemma pairCW {c m : ℝ} {S : Set ℝ} {ρ : ℝ} (hρ : ρ ∈ S) (w ψ : ℝ → ℝ × ℝ → ℂ)
    (hwm : ∀ r' ∈ S, MemLp (w r') 2 (B0579.cellMeasure c m))
    (hψm : ∀ r' ∈ S, MemLp (ψ r') 2 (B0579.cellMeasure c (-m)))
    (ha : Tendsto (fun r' => (eLpNorm (w r' - w ρ) 2 (B0579.cellMeasure c m)).toReal)
      (𝓝[S] ρ) (𝓝 0))
    (hb : Tendsto (fun r' => (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal)
      (𝓝[S] ρ) (𝓝 0)) :
    ContinuousWithinAt (fun r' => ∫ x in B0579.cell c, w r' x * ψ r' x) S ρ := by
  have hwρ := hwm ρ hρ
  have hψρ := hψm ρ hρ
  set Nψ := (eLpNorm (ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal with hNψ
  set Nw := (eLpNorm (w ρ) 2 (B0579.cellMeasure c m)).toReal with hNw
  have hbound : ∀ r' ∈ S, ‖(∫ x in B0579.cell c, w r' x * ψ r' x) -
      ∫ x in B0579.cell c, w ρ x * ψ ρ x‖ ≤
      (eLpNorm (w r' - w ρ) 2 (B0579.cellMeasure c m)).toReal *
          (Nψ + (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal) +
        Nw * (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal := by
    intro r' hr'
    have hd1 : MemLp (w r' - w ρ) 2 (B0579.cellMeasure c m) := (hwm r' hr').sub hwρ
    have hd2 : MemLp (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m)) := (hψm r' hr').sub hψρ
    obtain ⟨i1, n1⟩ := PairContAux.holder hd1 (hψm r' hr')
    obtain ⟨i2, n2⟩ := PairContAux.holder hwρ hd2
    obtain ⟨i3, -⟩ := PairContAux.holder (hwm r' hr') (hψm r' hr')
    obtain ⟨i4, -⟩ := PairContAux.holder hwρ hψρ
    have hsplit : (∫ x in B0579.cell c, w r' x * ψ r' x) -
        ∫ x in B0579.cell c, w ρ x * ψ ρ x =
        (∫ x in B0579.cell c, (w r' - w ρ) x * ψ r' x) +
          ∫ x in B0579.cell c, w ρ x * (ψ r' - ψ ρ) x := by
      rw [← integral_sub i3 i4, ← integral_add i1 i2]
      congr 1; funext x; simp only [Pi.sub_apply]; ring
    have hψn : (eLpNorm (ψ r') 2 (B0579.cellMeasure c (-m))).toReal ≤
        Nψ + (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal := by
      have hle : eLpNorm (ψ r') 2 (B0579.cellMeasure c (-m)) ≤
          eLpNorm (ψ ρ) 2 (B0579.cellMeasure c (-m)) +
            eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m)) := by
        have hsum : ψ r' = ψ ρ + (ψ r' - ψ ρ) := by abel
        calc eLpNorm (ψ r') 2 (B0579.cellMeasure c (-m))
            = eLpNorm (ψ ρ + (ψ r' - ψ ρ)) 2 (B0579.cellMeasure c (-m)) := by rw [← hsum]
          _ ≤ _ := eLpNorm_add_le hψρ.1 hd2.1 (by norm_num)
      have hfin : eLpNorm (ψ ρ) 2 (B0579.cellMeasure c (-m)) +
          eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m)) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hψρ.2.ne, hd2.2.ne⟩
      have := ENNReal.toReal_mono hfin hle
      rwa [ENNReal.toReal_add hψρ.2.ne hd2.2.ne] at this
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact n1.trans (mul_le_mul_of_nonneg_left hψn ENNReal.toReal_nonneg)
    · exact n2
  have hlim : Tendsto (fun r' => (eLpNorm (w r' - w ρ) 2 (B0579.cellMeasure c m)).toReal *
      (Nψ + (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal) +
        Nw * (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal)
      (𝓝[S] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r' => Nψ + (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal)
        (𝓝[S] ρ) (𝓝 (Nψ + 0)) := (tendsto_const_nhds (x := Nψ)).add hb
    have h2 : Tendsto (fun r' => Nw * (eLpNorm (ψ r' - ψ ρ) 2 (B0579.cellMeasure c (-m))).toReal)
        (𝓝[S] ρ) (𝓝 (Nw * 0)) := (tendsto_const_nhds (x := Nw)).mul hb
    have := (ha.mul h1).add h2
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

end LadPRPairAux

open LadPRPairAux in
/-- **Leaf 5** (`LadPRPair`): the cut pairing is continuous on `[t, r]`. -/
theorem ladPRPair : LadPRPair := by
  intro ν c m tr t s f w u φ hS R hR r hr ρ hρ
  have hρs : ρ ∈ Ico t s := ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
  have hwm : ∀ r' ∈ Icc t r, MemLp (w r') 2 (B0579.cellMeasure c m) :=
    fun r' h => hS.flow.memX r' h.1
  have hψm : ∀ r' ∈ Icc t r, MemLp (ladCutPhi φ R r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => memLp_cutPhi hR hS.smooth ⟨h.1, lt_of_le_of_lt h.2 hr.2⟩ (-m)
  have ha : Tendsto (fun r' => (eLpNorm (w r' - w ρ) 2 (B0579.cellMeasure c m)).toReal)
      (𝓝[Icc t r] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (w r' - w ρ)) (𝓝[Icc t r] ρ) (𝓝 0) :=
      (hS.flow.strongCont ρ hρ.1).mono_left (nhdsWithin_mono _ (fun x hx => hx.1))
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, xNorm] using this
  have hb := LadPRPairAux.tendsto_cutDiff (c := c) (m := -m) hR hr.2 hS.smooth hρ
  unfold ladCutPair
  exact LadPRPairAux.pairCW (S := Icc t r) hρ w (fun r' => ladCutPhi φ R r') hwm hψm ha hb

end UnforcedLeray.Short.IIIa
