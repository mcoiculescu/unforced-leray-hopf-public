import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.PairCont

/-!
# The derivative of the cut pairing (`LadPRDeriv`, SP 3074-3075)

Difference quotients in `ρ`: the frozen-test identity splits the increment of the cut pairing
into a `G`-integral over `[ρ, ρ+h]` and an `X_{-m}`-difference quotient of the cut test; the first
tends to `G(ρ, ρ)` by joint continuity of `G`, the second to `∫ w(ρ) χ_R ∂_ρφ(ρ)` by uniform
convergence of the difference quotients of `φ` on the compact box `|η| ≤ 2R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadPRDerivAux

open LadPRPairAux

lemma ladDt_eq_fderiv {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {τ : ℝ} (hτ : τ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladDt φ τ x = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (τ, x) (1, 0) := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hΦU : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ univ) :=
    hφs.mono (prod_mono Ioo_subset_Ico_self (subset_refl _))
  have hpt : (τ, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hτ, mem_univ _⟩
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (τ, x) :=
    (hΦU.contDiffAt (hU.mem_nhds hpt)).differentiableAt (by simp)
  have hline : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt τ hline
  exact ladDt_eq_of_hasDerivAt hcomp

lemma hasDerivAt_phi {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {τ : ℝ} (hτ : τ ∈ Ioo t s) (x : ℝ × ℝ) :
    HasDerivAt (fun r => φ r x) (ladDt φ τ x) τ := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hΦU : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ univ) :=
    hφs.mono (prod_mono Ioo_subset_Ico_self (subset_refl _))
  have hpt : (τ, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hτ, mem_univ _⟩
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (τ, x) :=
    (hΦU.contDiffAt (hU.mem_nhds hpt)).differentiableAt (by simp)
  have hline : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt τ hline
  rw [ladDt_eq_fderiv hφs hτ x]
  exact hcomp

lemma continuousOn_ladDt {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2) (Ioo t s ×ˢ univ) := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hΦU : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ univ) :=
    hφs.mono (prod_mono Ioo_subset_Ico_self (subset_refl _))
  have hfd := hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hev : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) p ((1 : ℝ), (0 : ℝ × ℝ)))
      (Ioo t s ×ˢ univ) :=
    (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).continuous.comp_continuousOn hfd
  refine hev.congr ?_
  intro p hp
  exact ladDt_eq_fderiv hφs hp.1 p.2

/-- The mean-value bound for a difference quotient. -/
lemma quot_bound {g g' : ℝ → ℂ} {ρ δ ε h : ℝ} (hδ : 0 ≤ δ) (hh : h ≠ 0) (hhδ : |h| ≤ δ)
    (hd : ∀ τ ∈ Icc (ρ - δ) (ρ + δ), HasDerivAt g (g' τ) τ)
    (hb : ∀ τ ∈ Icc (ρ - δ) (ρ + δ), ‖g' τ - g' ρ‖ ≤ ε) :
    ‖h⁻¹ • (g (ρ + h) - g ρ) - g' ρ‖ ≤ ε := by
  set s := Icc (ρ - δ) (ρ + δ) with hs
  obtain ⟨h1, h2⟩ := abs_le.1 hhδ
  have hρs : ρ ∈ s := ⟨by linarith, by linarith⟩
  have hρh : ρ + h ∈ s := ⟨by linarith, by linarith⟩
  set k : ℝ → ℂ := fun τ => g τ - (τ : ℂ) * g' ρ with hk
  have hkd : ∀ τ ∈ s, HasDerivWithinAt k (g' τ - g' ρ) s τ := by
    intro τ hτ
    have h1' : HasDerivAt (fun τ : ℝ => (τ : ℂ) * g' ρ) (1 * g' ρ) τ :=
      (hasDerivAt_id' τ).ofReal_comp.mul_const (g' ρ)
    have := (hd τ hτ).sub h1'
    rw [one_mul] at this
    exact this.hasDerivWithinAt
  have hbd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hkd
    (fun τ hτ => hb τ hτ) (convex_Icc _ _) hρs hρh
  have hk' : k (ρ + h) - k ρ = (g (ρ + h) - g ρ) - (h : ℂ) * g' ρ := by
    simp only [hk]; push_cast; ring
  rw [hk', show ρ + h - ρ = h by ring, Real.norm_eq_abs] at hbd
  have hC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh
  have e : h⁻¹ • (g (ρ + h) - g ρ) - g' ρ =
      h⁻¹ • ((g (ρ + h) - g ρ) - (h : ℂ) * g' ρ) := by
    have hc : h⁻¹ • ((h : ℂ) * g' ρ) = g' ρ := by
      rw [Complex.real_smul]
      push_cast
      field_simp
    simp only [smul_sub]
    rw [hc]
  have hpos : 0 < |h| := abs_pos.2 hh
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv]
  calc |h|⁻¹ * ‖(g (ρ + h) - g ρ) - (h : ℂ) * g' ρ‖ ≤ |h|⁻¹ * (ε * |h|) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hpos.le)
    _ = ε := by field_simp

/-- Uniform difference quotients of `φ` in `ρ` on a compact set in `x`. -/
lemma dq_unif {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| ≤ δ → ∀ x ∈ K,
      ‖h⁻¹ • (φ (ρ + h) x - φ ρ x) - ladDt φ ρ x‖ ≤ ε := by
  set δ1 : ℝ := min (ρ - t) (s - ρ) / 2 with hδ1
  have hm1 : 0 < min (ρ - t) (s - ρ) := lt_min (by linarith [hρ.1]) (by linarith [hρ.2])
  have hδ1pos : 0 < δ1 := half_pos hm1
  have hδ1a : δ1 < ρ - t := by
    have := min_le_left (ρ - t) (s - ρ); linarith
  have hδ1b : δ1 < s - ρ := by
    have := min_le_right (ρ - t) (s - ρ); linarith
  have hIcc : Icc (ρ - δ1) (ρ + δ1) ⊆ Ioo t s := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hS : IsCompact (Icc (ρ - δ1) (ρ + δ1) ×ˢ K) := isCompact_Icc.prod hK
  have hsub : Icc (ρ - δ1) (ρ + δ1) ×ˢ K ⊆ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono hIcc (subset_univ _)
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2)
      (Icc (ρ - δ1) (ρ + δ1) ×ˢ K) :=
    (continuousOn_ladDt hφs).mono hsub
  have hunif := hS.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨η, hη, hηd⟩ := hunif ε hε
  refine ⟨min δ1 (η / 2), lt_min hδ1pos (half_pos hη), ?_⟩
  intro h hh0 hhδ x hxK
  have hbdD : ∀ τ ∈ Icc (ρ - min δ1 (η / 2)) (ρ + min δ1 (η / 2)),
      ‖ladDt φ τ x - ladDt φ ρ x‖ ≤ ε := by
    intro τ hτ
    have hτ1 : τ ∈ Icc (ρ - δ1) (ρ + δ1) :=
      ⟨by linarith [hτ.1, min_le_left δ1 (η / 2)], by linarith [hτ.2, min_le_left δ1 (η / 2)]⟩
    have h1 : |τ - ρ| ≤ min δ1 (η / 2) := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have hdist : dist ((τ, x) : ℝ × (ℝ × ℝ)) (ρ, x) < η := by
      rw [Prod.dist_eq, dist_self, max_lt_iff, Real.dist_eq]
      refine ⟨by linarith [min_le_right δ1 (η / 2)], hη⟩
    have hρ1 : ρ ∈ Icc (ρ - δ1) (ρ + δ1) := ⟨by linarith, by linarith⟩
    have := hηd (τ, x) ⟨hτ1, hxK⟩ (ρ, x) ⟨hρ1, hxK⟩ hdist
    rw [dist_eq_norm] at this
    exact this.le
  exact quot_bound (g := fun r => φ r x) (g' := fun τ => ladDt φ τ x) (ρ := ρ)
    (δ := min δ1 (η / 2)) (le_of_lt (lt_min hδ1pos (half_pos hη))) hh0 hhδ
    (fun τ hτ => hasDerivAt_phi hφs
      (hIcc ⟨by linarith [hτ.1, min_le_left δ1 (η / 2)], by linarith [hτ.2, min_le_left δ1 (η / 2)]⟩) x)
    hbdD


lemma ladDt_slice_cont {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) : Continuous (fun x : ℝ × ℝ => ladDt φ ρ x) := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => ladDt φ ρ x) univ :=
    (continuousOn_ladDt hφs).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hρ, mem_univ x⟩)
  exact continuousOn_univ.1 h1

lemma memLp_of_cont_box {c n R : ℝ} {F : ℝ × ℝ → ℂ} (hcc : Continuous F)
    (hvan : ∀ x ∈ B0579.cell c, x ∉ B0579.box c (2 * R) → F x = 0) :
    MemLp F 2 (B0579.cellMeasure c n) := by
  have hK : IsCompact (B0579.box c (2 * R)) := B0579.isCompact_box c (2 * R)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcc.continuousOn
  refine ⟨hcc.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (LadPRPairAux.eLpNorm_le_of_bdd (m := n) hK (abs_nonneg C) hvan ?_) ?_
  · intro x hx; exact (hC x hx).trans (le_abs_self C)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (LadPRPairAux.cellMeasure_lt_top hK).ne))

lemma toReal_le_of_bdd {c n : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) {F : ℝ × ℝ → ℂ}
    {ε : ℝ} (hε : 0 ≤ ε) (hF : ∀ x ∈ B0579.cell c, x ∉ K → F x = 0)
    (hb : ∀ x ∈ K, ‖F x‖ ≤ ε) :
    (eLpNorm F 2 (B0579.cellMeasure c n)).toReal ≤
      ε * (B0579.cellMeasure c n K).toReal ^ (2⁻¹ : ℝ) := by
  have h := LadPRPairAux.eLpNorm_le_of_bdd (m := n) hK hε hF hb
  have hne : ENNReal.ofReal ε * (B0579.cellMeasure c n K) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (LadPRPairAux.cellMeasure_lt_top hK).ne)
  have hreal := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, ← ENNReal.toReal_rpow] at hreal
  exact hreal

/-- A uniform bound of a family vanishing off a compact box tends to `0` in `X_{-m,c}`. -/
lemma tendsto_of_unif {α : Type*} {l : Filter α} {F : α → ℝ × ℝ → ℂ} {c n : ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hF : ∀ a, ∀ x ∈ B0579.cell c, x ∉ K → F a x = 0)
    (hb : ∀ ε > 0, ∀ᶠ a in l, ∀ x ∈ K, ‖F a x‖ ≤ ε) :
    Tendsto (fun a => (eLpNorm (F a) 2 (B0579.cellMeasure c n)).toReal) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set A : ℝ := ((B0579.cellMeasure c n K).toReal) ^ (2⁻¹ : ℝ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hε' : 0 < ε / (A + 1) := by positivity
  filter_upwards [hb _ hε'] with a ha
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have hbd := toReal_le_of_bdd (c := c) (n := n) hK hε'.le (hF a) ha
  have key : ε / (A + 1) * A < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt hbd key

lemma norm_cut_mul_le {R : ℝ} (x : ℝ × ℝ) (Z : ℂ) :
    ‖(ladCut R x : ℂ) * Z‖ ≤ ‖Z‖ := by
  rw [norm_mul]
  have hc : ‖(ladCut R x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (cut_nonneg R x)]
    exact cut_le_one R x
  calc ‖(ladCut R x : ℂ)‖ * ‖Z‖ ≤ 1 * ‖Z‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖Z‖ := one_mul _

lemma Q_eq {R : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {ρ h : ℝ} (x : ℝ × ℝ) :
    ((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x =
      (ladCut R x : ℂ) * (((h⁻¹ : ℝ) : ℂ) * (φ (ρ + h) x - φ ρ x) - ladDt φ ρ x) := by
  unfold ladCutPhi; ring

/-- The `X_{-m,c}`-difference quotients of the cut test converge to `χ_R ∂_ρφ(ρ)`. -/
lemma tendsto_dq_L2 {c n t s R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ × ℝ → ℂ}
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) :
    Tendsto (fun h : ℝ => (eLpNorm (fun x => ((h⁻¹ : ℝ) : ℂ) *
        (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)
        2 (B0579.cellMeasure c n)).toReal) (𝓝[≠] 0) (𝓝 0) := by
  refine tendsto_of_unif (F := fun h x => ((h⁻¹ : ℝ) : ℂ) *
      (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)
    (B0579.isCompact_box c (2 * R)) ?_ ?_
  · intro h x hx hxK
    unfold ladCutPhi
    rw [cut_zero hR (not_mem_box_gt hx hxK)]
    simp
  · intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := dq_unif hφs hρ (B0579.isCompact_box c (2 * R)) hε
    have h0 : ∀ᶠ h in 𝓝 (0 : ℝ), |h| ≤ δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [nhdsWithin_le_nhds h0, self_mem_nhdsWithin] with h hh hne
    have hne' : h ≠ 0 := Set.mem_compl_singleton_iff.1 hne
    intro x hx
    rw [Q_eq x]
    have hZ : ‖((h⁻¹ : ℝ) : ℂ) * (φ (ρ + h) x - φ ρ x) - ladDt φ ρ x‖ ≤ ε := by
      have := hδ' h hne' hh x hx
      rwa [Complex.real_smul] at this
    exact (norm_cut_mul_le x _).trans hZ

/-- The `G`-integral over `[ρ, ρ+h]` divided by `h` tends to `G(ρ, ρ)`. -/
lemma G_limit {t r : ℝ} {G : ℝ × ℝ → ℂ} (hG : ContinuousOn G (Icc t r ×ˢ Icc t r))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t r) :
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) * ∫ σ in ρ..ρ + h, G (σ, ρ + h)) (𝓝[≠] 0)
      (𝓝 (G (ρ, ρ))) := by
  have hρI : ρ ∈ Icc t r := ⟨hρ.1.le, hρ.2.le⟩
  have hcw : ContinuousWithinAt G (Icc t r ×ˢ Icc t r) (ρ, ρ) := hG (ρ, ρ) ⟨hρI, hρI⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδG⟩ := hcw (ε / 2) (half_pos hε)
  have hm0 : 0 < min (ρ - t) (r - ρ) := lt_min (by linarith [hρ.1]) (by linarith [hρ.2])
  have hδ2 : 0 < min δ (min (ρ - t) (r - ρ)) := lt_min hδ hm0
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ2),
    self_mem_nhdsWithin] with h hh hne
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
  have hh0 : h ≠ 0 := Set.mem_compl_singleton_iff.1 hne
  have hhδ : |h| < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have hhδ0 : |h| < min (ρ - t) (r - ρ) := lt_of_lt_of_le hh (min_le_right _ _)
  have hm1 : min (ρ - t) (r - ρ) ≤ ρ - t := min_le_left _ _
  have hm2 : min (ρ - t) (r - ρ) ≤ r - ρ := min_le_right _ _
  have h1 := abs_lt.1 hhδ0
  have hρh : ρ + h ∈ Icc t r := ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hsub : ∀ σ ∈ uIcc ρ (ρ + h), σ ∈ Icc t r := fun σ hσ => Set.uIcc_subset_Icc hρI hρh hσ
  have hint : IntervalIntegrable (fun σ => G (σ, ρ + h)) volume ρ (ρ + h) := by
    apply ContinuousOn.intervalIntegrable
    exact hG.comp (ContinuousOn.prodMk continuousOn_id continuousOn_const)
      (fun σ hσ => ⟨hsub σ hσ, hρh⟩)
  have hbound : ‖∫ σ in ρ..ρ + h, (G (σ, ρ + h) - G (ρ, ρ))‖ ≤ ε / 2 * |h| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := ρ) (b := ρ + h)
      (C := ε / 2) (f := fun σ => G (σ, ρ + h) - G (ρ, ρ)) ?_
    · have e : ρ + h - ρ = h := by ring
      rw [e] at this
      exact this
    · intro σ hσ
      have hσI : σ ∈ uIcc ρ (ρ + h) := Set.uIoc_subset_uIcc hσ
      have hσh : |σ - ρ| ≤ |h| := by
        rcases Set.mem_uIcc.1 hσI with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases abs_cases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> rw [hA] <;> rw [abs_le] <;>
          constructor <;> linarith
      have hdist : dist ((σ, ρ + h) : ℝ × ℝ) (ρ, ρ) < δ := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
        exact ⟨lt_of_le_of_lt hσh hhδ, by rw [show ρ + h - ρ = h by ring]; exact hhδ⟩
      have := hδG (show (σ, ρ + h) ∈ Icc t r ×ˢ Icc t r from ⟨hsub σ hσI, hρh⟩) hdist
      rw [dist_eq_norm] at this
      exact this.le
  have hint2 : ∫ σ in ρ..ρ + h, (G (σ, ρ + h) - G (ρ, ρ)) =
      (∫ σ in ρ..ρ + h, G (σ, ρ + h)) - (h : ℂ) * G (ρ, ρ) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
  have hinv : ((h⁻¹ : ℝ) : ℂ) * (h : ℂ) = 1 := by
    have hC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh0
    push_cast
    field_simp
  have hI : ((h⁻¹ : ℝ) : ℂ) * (∫ σ in ρ..ρ + h, G (σ, ρ + h)) - G (ρ, ρ) =
      ((h⁻¹ : ℝ) : ℂ) * ∫ σ in ρ..ρ + h, (G (σ, ρ + h) - G (ρ, ρ)) := by
    rw [hint2, mul_sub, ← mul_assoc, hinv, one_mul]
  rw [dist_eq_norm, hI, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  calc |h|⁻¹ * ‖∫ σ in ρ..ρ + h, (G (σ, ρ + h) - G (ρ, ρ))‖
      ≤ |h|⁻¹ * (ε / 2 * |h|) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 (abs_nonneg _))
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The increment of the cut pairing: the frozen-test identity splits it. -/
lemma incr_split {c m t r : ℝ} (w Ψ : ℝ → ℝ × ℝ → ℂ) (Gf : ℝ × ℝ → ℂ) {ρ h : ℝ}
    (hweak : ∀ ρ' ∈ Icc t r, ∀ a b : ℝ, t ≤ a → a ≤ b →
      (∫ x in B0579.cell c, w b x * Ψ ρ' x) - (∫ x in B0579.cell c, w a x * Ψ ρ' x) =
        ∫ σ in a..b, Gf (σ, ρ'))
    (hρ : ρ ∈ Icc t r) (hρh : ρ + h ∈ Icc t r)
    (hwρ : MemLp (w ρ) 2 (B0579.cellMeasure c m))
    (hΨ : ∀ ρ' ∈ Icc t r, MemLp (Ψ ρ') 2 (B0579.cellMeasure c (-m))) :
    (∫ x in B0579.cell c, w (ρ + h) x * Ψ (ρ + h) x) - (∫ x in B0579.cell c, w ρ x * Ψ ρ x) =
      (∫ σ in ρ..ρ + h, Gf (σ, ρ + h)) +
        ∫ x in B0579.cell c, w ρ x * (Ψ (ρ + h) x - Ψ ρ x) := by
  have hA : (∫ x in B0579.cell c, w (ρ + h) x * Ψ (ρ + h) x) -
      (∫ x in B0579.cell c, w ρ x * Ψ (ρ + h) x) = ∫ σ in ρ..ρ + h, Gf (σ, ρ + h) := by
    rcases le_total 0 h with h0 | h0
    · exact hweak (ρ + h) hρh ρ (ρ + h) hρ.1 (by linarith)
    · have h1 := hweak (ρ + h) hρh (ρ + h) ρ hρh.1 (by linarith)
      rw [intervalIntegral.integral_symm] at h1
      linear_combination -h1
  have i1 := (PairContAux.holder hwρ (hΨ (ρ + h) hρh)).1
  have i2 := (PairContAux.holder hwρ (hΨ ρ hρ)).1
  have hsplit : ∫ x in B0579.cell c, w ρ x * (Ψ (ρ + h) x - Ψ ρ x) =
      (∫ x in B0579.cell c, w ρ x * Ψ (ρ + h) x) - ∫ x in B0579.cell c, w ρ x * Ψ ρ x := by
    rw [← integral_sub i1 i2]
    congr 1; funext x; ring
  linear_combination hA - hsplit

end LadPRDerivAux



open LadPRDerivAux in
/-- **Leaf 6** (`LadPRDeriv`): the derivative of the cut pairing is the cut rate on `(t, r)`. -/
theorem ladPRDeriv : LadPRDeriv := by
  intro ν c m tr t s f w u φ hS R hR r hr hG hweak ρ hρ
  have hρI : ρ ∈ Icc t r := ⟨hρ.1.le, hρ.2.le⟩
  have hρs : ρ ∈ Ioo t s := ⟨hρ.1, lt_trans hρ.2 hr.2⟩
  have hwm : ∀ r' ∈ Icc t r, MemLp (w r') 2 (B0579.cellMeasure c m) :=
    fun r' h => hS.flow.memX r' h.1
  have hΨ : ∀ r' ∈ Icc t r, MemLp (ladCutPhi φ R r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => LadPRPairAux.memLp_cutPhi hR hS.smooth ⟨h.1, lt_of_le_of_lt h.2 hr.2⟩ (-m)
  have hwρ := hwm ρ hρI
  have hDmem : MemLp (fun x => (ladCut R x : ℂ) * ladDt φ ρ x) 2
      (B0579.cellMeasure c (-m)) := by
    refine memLp_of_cont_box (c := c) (n := -m) (R := R) ?_ ?_
    · exact (Complex.continuous_ofReal.comp (LadPRPairAux.cut_continuous R)).mul
        (ladDt_slice_cont hS.smooth hρs)
    · intro x hx hxK
      simp only [LadPRPairAux.cut_zero hR (LadPRPairAux.not_mem_box_gt hx hxK),
        Complex.ofReal_zero, zero_mul]
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ρ + h ∈ Icc t r := by
    have hopen : ∀ᶠ h in 𝓝 (0 : ℝ), ρ + h ∈ Ioo t r := by
      have hc : Tendsto (fun h : ℝ => ρ + h) (𝓝 0) (𝓝 ρ) := by
        have : Tendsto (fun h : ℝ => ρ + h) (𝓝 0) (𝓝 (ρ + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at this
        exact this
      exact hc.eventually (isOpen_Ioo.mem_nhds hρ)
    filter_upwards [nhdsWithin_le_nhds hopen] with h hh
    exact ⟨hh.1.le, hh.2.le⟩
  have hG1 := G_limit hG hρ
  have hG2 : Tendsto (fun h : ℝ => ∫ x in B0579.cell c, w ρ x *
      (((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x)) (𝓝[≠] 0) (𝓝 0) := by
    have hdq := tendsto_dq_L2 (c := c) (n := -m) hR hS.smooth hρs
    have ha := hdq.const_mul (eLpNorm (w ρ) 2 (B0579.cellMeasure c m)).toReal
    rw [mul_zero] at ha
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [hev] with h hh
    have hQ : MemLp (fun x => ((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x) 2 (B0579.cellMeasure c (-m)) :=
      (((hΨ (ρ + h) hh).sub (hΨ ρ hρI)).const_mul _).sub hDmem
    exact (PairContAux.holder hwρ hQ).2
  have hI : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      h⁻¹ • (ladCutPair c R w φ (ρ + h) - ladCutPair c R w φ ρ) =
        ((h⁻¹ : ℝ) : ℂ) * (∫ σ in ρ..ρ + h, ladG tr w u φ R (σ, ρ + h)) +
          (∫ x in B0579.cell c, w ρ x * (((h⁻¹ : ℝ) : ℂ) *
            (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)) +
          ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) := by
    filter_upwards [hev] with h hh
    have hsplit := incr_split (c := c) (m := m) (t := t) (r := r) w (ladCutPhi φ R)
      (ladG tr w u φ R) hweak hρI hh hwρ hΨ
    have hQ : MemLp (fun x => ((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x) 2 (B0579.cellMeasure c (-m)) :=
      (((hΨ (ρ + h) hh).sub (hΨ ρ hρI)).const_mul _).sub hDmem
    have iQ := (PairContAux.holder hwρ hQ).1
    have iD := (PairContAux.holder hwρ hDmem).1
    have hJ : ((h⁻¹ : ℝ) : ℂ) * (∫ x in B0579.cell c,
        w ρ x * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x)) =
        (∫ x in B0579.cell c, w ρ x * (((h⁻¹ : ℝ) : ℂ) *
          (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)) +
        ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) := by
      rw [← integral_add iQ iD, ← integral_const_mul]
      congr 1
      funext x
      ring
    unfold ladCutPair
    rw [hsplit, Complex.real_smul, mul_add, hJ]
    ring
  have hlim := (hG1.add hG2).add
    (tendsto_const_nhds (x := ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)))
  rw [add_zero] at hlim
  rw [hasDerivAt_iff_tendsto_slope_zero, ladRate_eq]
  unfold ladK
  exact Tendsto.congr' (hI.mono fun h hh => hh.symm) hlim

end UnforcedLeray.Short.IIIa
