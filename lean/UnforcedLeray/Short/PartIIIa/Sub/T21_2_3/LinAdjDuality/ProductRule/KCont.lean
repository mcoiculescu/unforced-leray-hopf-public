import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Deriv

/-!
# Continuity of the derivative pairing `ρ ↦ ∫ w(ρ) χ_R ∂_ρφ(ρ)` (`LadPRK`, SP 3074-3075)

`ladDt` is the right derivative. On the open strip `(t, s)` it agrees with the two-sided
`fderivWithin` on `Ico t s × ℝ²` in the direction `(1, 0)` (`ladDW`), and `ladDW` is jointly
continuous on `Ico t s × ℝ²` (`ContDiffOn.continuousOn_fderivWithin`). So the pairing
`Φ(ρ) = ∫ w(ρ) χ_R ladDW(ρ)` is continuous on `Icc t p` for every `p < s` (`pairCW`, using
the `X_m`-continuity of `w` and the uniform continuity of `ladDW` on compact boxes). Continuity
of `ladK` on `Ioc t r` and the right limit at `t` both follow from `Φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadPRKAux

open LadPRPairAux LadPRDerivAux

/-- The two-sided `x`-slice derivative in `ρ` on `Ico t s × ℝ²`, direction `(1, 0)`. -/
def ladDW (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℂ :=
  fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ (univ : Set (ℝ × ℝ)))
    (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ))

lemma uniqueDiffOn_strip (t s : ℝ) :
    UniqueDiffOn ℝ (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
  (uniqueDiffOn_Ico t s).prod uniqueDiffOn_univ

lemma ladDt_eq_ladDW {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {τ : ℝ} (hτ : τ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladDt φ τ x = ladDW t s φ τ x := by
  have hmem : (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) ∈ 𝓝 (τ, x) := by
    apply mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hτ, mem_univ x⟩)
    exact prod_mono Ioo_subset_Ico_self (subset_refl _)
  unfold ladDW
  rw [fderivWithin_of_mem_nhds hmem]
  exact ladDt_eq_fderiv hφs hτ x

lemma ladDW_continuousOn {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDW t s φ p.1 p.2) (Ico t s ×ˢ univ) := by
  have hfd := hφs.continuousOn_fderivWithin (uniqueDiffOn_strip t s) (by simp)
  have hev := (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).continuous.comp_continuousOn
    hfd
  exact hev

lemma ladDW_slice {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hJ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDW t s φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ico t s) : Continuous (ladDW t s φ ρ) := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => ladDW t s φ ρ x) univ :=
    hJ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hρ, mem_univ x⟩)
  exact continuousOn_univ.1 h1

lemma memLp_cutDW {c t s R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ × ℝ → ℂ}
    (hJ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDW t s φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ico t s) (n : ℝ) :
    MemLp (ladCutPhi (ladDW t s φ) R ρ) 2 (B0579.cellMeasure c n) := by
  have hcc : Continuous (ladCutPhi (ladDW t s φ) R ρ) := by
    unfold ladCutPhi
    exact (Complex.continuous_ofReal.comp (cut_continuous R)).mul (ladDW_slice hJ hρ)
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

/-- Continuity in `ρ ∈ Icc t p` of the cut `ladDW`-test in `X_{n,c}`. -/
lemma tendsto_cutDW {c m t s p R : ℝ} (hR : 0 < R) (hp : p < s) {φ : ℝ → ℝ × ℝ → ℂ}
    (hJ : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => ladDW t s φ q.1 q.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Icc t p) :
    Tendsto (fun ρ' => (eLpNorm (ladCutPhi (ladDW t s φ) R ρ' - ladCutPhi (ladDW t s φ) R ρ) 2
      (B0579.cellMeasure c m)).toReal) (𝓝[Icc t p] ρ) (𝓝 0) := by
  have hK : IsCompact (B0579.box c (2 * R)) := B0579.isCompact_box c (2 * R)
  have hS : IsCompact (Icc t p ×ˢ B0579.box c (2 * R)) := isCompact_Icc.prod hK
  have hsub : Icc t p ×ˢ B0579.box c (2 * R) ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hp⟩) (subset_univ _)
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => ladDW t s φ q.1 q.2)
      (Icc t p ×ˢ B0579.box c (2 * R)) :=
    hJ.mono hsub
  have hunif := hS.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  set a : ℝ := ((B0579.cellMeasure c m (B0579.box c (2 * R))).toReal) ^ (2⁻¹ : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hunif (ε / (a + 1)) (by positivity)
  have h1 : ∀ᶠ ρ' in 𝓝 ρ, dist ρ' ρ < δ := Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hy⟩
  have h2 : ∀ᶠ ρ' in 𝓝[Icc t p] ρ, dist ρ' ρ < δ := nhdsWithin_le_nhds h1
  filter_upwards [eventually_mem_nhdsWithin, h2] with ρ' hρ' hd
  have hε' : 0 ≤ ε / (a + 1) := by positivity
  have hbd := eLpNorm_le_of_bdd (c := c) (m := m) hK hε'
    (F := ladCutPhi (ladDW t s φ) R ρ' - ladCutPhi (ladDW t s φ) R ρ) ?_ ?_
  · have hne : ENNReal.ofReal (ε / (a + 1)) *
        (B0579.cellMeasure c m (B0579.box c (2 * R))) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
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
    have hF : ladCutPhi (ladDW t s φ) R ρ' x - ladCutPhi (ladDW t s φ) R ρ x =
        (ladCut R x : ℂ) * (ladDW t s φ ρ' x - ladDW t s φ ρ x) := by
      unfold ladCutPhi; ring
    rw [hF, norm_mul]
    have hc : ‖(ladCut R x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (cut_nonneg R x)]
      exact cut_le_one R x
    have hdist : dist (ladDW t s φ ρ' x) (ladDW t s φ ρ x) < ε / (a + 1) :=
      hδ' (ρ', x) ⟨hρ', hxK⟩ (ρ, x) ⟨hρ, hxK⟩
        (by
          rw [Prod.dist_eq, dist_self, max_lt_iff]
          exact ⟨hd, hδ⟩)
    rw [← dist_eq_norm]
    calc ‖(ladCut R x : ℂ)‖ * dist (ladDW t s φ ρ' x) (ladDW t s φ ρ x)
        ≤ 1 * dist (ladDW t s φ ρ' x) (ladDW t s φ ρ x) :=
          mul_le_mul_of_nonneg_right hc dist_nonneg
      _ ≤ ε / (a + 1) := by rw [one_mul]; exact hdist.le

/-- Continuity of the `ladDW`-cut pairing within `Icc t p`, `p < s`. -/
lemma fp_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    {φ : ℝ → ℝ × ℝ → ℂ} (hS : LadPRSetup ν c m tr t s f w u φ) {R : ℝ} (hR : 0 < R)
    {p : ℝ} (hp : p < s) {ρ : ℝ} (hρ : ρ ∈ Icc t p) :
    ContinuousWithinAt (fun r' => ∫ x in B0579.cell c, w r' x * ladCutPhi (ladDW t s φ) R r' x)
      (Icc t p) ρ := by
  have hJ := ladDW_continuousOn hS.smooth
  have hwm : ∀ r' ∈ Icc t p, MemLp (w r') 2 (B0579.cellMeasure c m) :=
    fun r' h => hS.flow.memX r' h.1
  have hψm : ∀ r' ∈ Icc t p,
      MemLp (ladCutPhi (ladDW t s φ) R r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => memLp_cutDW hR hJ ⟨h.1, lt_of_le_of_lt h.2 hp⟩ (-m)
  have ha : Tendsto (fun r' => (eLpNorm (w r' - w ρ) 2 (B0579.cellMeasure c m)).toReal)
      (𝓝[Icc t p] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (w r' - w ρ)) (𝓝[Icc t p] ρ) (𝓝 0) :=
      (hS.flow.strongCont ρ hρ.1).mono_left (nhdsWithin_mono _ (fun x hx => hx.1))
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, xNorm] using this
  have hb := tendsto_cutDW (c := c) (m := -m) hR hp hJ hρ
  exact pairCW (S := Icc t p) hρ w (fun r' => ladCutPhi (ladDW t s φ) R r') hwm hψm ha hb

/-- On `(t, s)`, `ladK` is the `ladDW`-cut pairing. -/
lemma ladK_eq_pair {c t s R : ℝ} {w : ℝ → ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) :
    ladK c w φ R ρ = ∫ x in B0579.cell c, w ρ x * ladCutPhi (ladDW t s φ) R ρ x := by
  unfold ladK ladCutPhi
  congr 1
  funext x
  rw [ladDt_eq_ladDW hφs hρ x]

end LadPRKAux

open LadPRKAux in
/-- **Leaf 4** (`LadPRK`): `ladK` is continuous on `(t, r]` and has a right limit at `t`. -/
theorem ladPRK : LadPRK := by
  intro ν c m tr t s f w u φ hS R hR r hr
  have hrs : r < s := hr.2
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    have hρI : ρ ∈ Ioo t s := ⟨hρ.1, lt_of_le_of_lt hρ.2 hrs⟩
    have hΦ := fp_cont hS hR hrs (ρ := ρ) ⟨hρ.1.le, hρ.2⟩
    refine ContinuousWithinAt.congr (hΦ.mono Ioc_subset_Icc_self) (fun y hy => ?_) ?_
    · exact ladK_eq_pair hS.smooth ⟨hy.1, lt_of_le_of_lt hy.2 hrs⟩
    · exact ladK_eq_pair hS.smooth hρI
  · have htq : t < (t + s) / 2 := by linarith [hS.hts]
    have hqs : (t + s) / 2 < s := by linarith [hS.hts]
    have hΦ := fp_cont hS hR hqs (ρ := t) ⟨le_refl t, htq.le⟩
    have hnhd : Icc t ((t + s) / 2) ∈ 𝓝[>] t :=
      mem_of_superset (Ioo_mem_nhdsGT htq) (fun y hy => ⟨hy.1.le, hy.2.le⟩)
    have hle : 𝓝[>] t ≤ 𝓝[Icc t ((t + s) / 2)] t := nhdsWithin_le_of_mem hnhd
    have hT := hΦ.mono_left hle
    refine ⟨∫ x in B0579.cell c, w t x * ladCutPhi (ladDW t s φ) R t x, ?_⟩
    refine Tendsto.congr' ?_ hT
    filter_upwards [Ioo_mem_nhdsGT htq] with y hy
    exact (ladK_eq_pair hS.smooth ⟨hy.1, lt_of_lt_of_le hy.2 hqs.le⟩).symm
