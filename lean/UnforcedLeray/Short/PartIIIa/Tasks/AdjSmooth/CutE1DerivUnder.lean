import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutE1DU

lemma isOpen_strip (t s : ℝ) : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioo.prod isOpen_univ

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

section Strip

variable {t s : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}

/-- The slice-derivative symbol: `Ψ(r, x) = ψ r x` on the strip. -/
def gStrip (ψ : ℝ → ℝ × ℝ → ℂ) (k : Fin 2) (m : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  B0579.jb p.2 ^ (-m) * (2 * ((starRingEnd ℂ)
    (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2) p (0, B0579.dir k)) *
    fderiv ℝ (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2)) p (0, B0579.dir k)
      ((1 : ℝ), (0 : ℝ × ℝ))).re)

lemma strip_two (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ioo t s ×ˢ univ) :=
  (hj.mono (prod_mono Ioo_subset_Ico_self (subset_refl _))).of_le (by simp)

lemma strip_cont_fderiv (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ 1 (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (Ioo t s ×ˢ univ) :=
  (strip_two hj).fderiv_of_isOpen (isOpen_strip t s) (by norm_num)

lemma strip_cont_fderiv2_on (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))) (Ioo t s ×ˢ univ) :=
  (strip_cont_fderiv hj).continuousOn_fderiv_of_isOpen (isOpen_strip t s) le_rfl

lemma strip_cont_fderiv_on (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContinuousOn (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (Ioo t s ×ˢ univ) :=
  (strip_two hj).continuousOn_fderiv_of_isOpen (isOpen_strip t s) (by norm_num)

lemma symm_strip (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) (v w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x) v w =
      fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x) w v := by
  have hc : ContDiffAt ℝ 2 (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, x) :=
    (strip_two hj).contDiffAt ((isOpen_strip t s).mem_nhds ⟨hρ, mem_univ x⟩)
  exact (hc.isSymmSndFDerivAt (by simp)).eq v w

lemma pdCx_eq_strip (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ioo t s) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (ψ r) x = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x) (0, B0579.dir k) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x) :=
    ((strip_two hj).contDiffAt ((isOpen_strip t s).mem_nhds ⟨hr, mem_univ x⟩)).differentiableAt
      (by norm_num)
  have hl : HasFDerivAt (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have h : HasFDerivAt (ψ r)
      ((fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    hd.hasFDerivAt.comp x hl
  unfold pdCx
  rw [h.fderiv]
  rfl

lemma ladDt_eq_strip (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladDt ψ ρ x = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  rw [ladDt_eq_fderivWithin hj hρ x,
    fderivWithin_of_mem_nhds (prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem)]

lemma hasFDerivAt_fderiv_strip
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    HasFDerivAt (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x)) (ρ, x) :=
  (((strip_cont_fderiv hj).contDiffAt ((isOpen_strip t s).mem_nhds ⟨hρ, mem_univ x⟩)).differentiableAt
    (by norm_num)).hasFDerivAt

lemma pdCx_ladDt_eq (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (ladDt ψ ρ) x = fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x)
      (0, B0579.dir k) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  have hl : HasFDerivAt (fun y : ℝ × ℝ => ((ρ, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
  have hc : HasFDerivAt (fun y : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, y))
      ((fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_fderiv_strip hj hρ x).comp x hl
  have hu : HasFDerivAt (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ × ℝ)))
      (0 : (ℝ × ℝ) →L[ℝ] (ℝ × (ℝ × ℝ))) x :=
    hasFDerivAt_const _ x
  have hcl := hc.clm_apply hu
  have hfun : ladDt ψ ρ = fun y => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, y)
      ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun y => ladDt_eq_strip hj hρ y
  unfold pdCx
  rw [hfun, hcl.fderiv]
  simp

lemma hasDerivAt_pdCx_r
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (k : Fin 2) (x : ℝ × ℝ) :
    HasDerivAt (fun r => pdCx k (ψ r) x) (pdCx k (ladDt ψ ρ) x) ρ := by
  have hline : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  have h1 : HasDerivAt (fun r : ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ))) ρ :=
    (hasFDerivAt_fderiv_strip hj hρ x).comp_hasDerivAt ρ hline
  have h2 := h1.clm_apply (hasDerivAt_const ρ (((0 : ℝ), B0579.dir k) : ℝ × (ℝ × ℝ)))
  have h3 : HasDerivAt (fun r => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x)
      (0, B0579.dir k))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ))
        (0, B0579.dir k)) ρ := by
    exact h2.congr_deriv (by simp)
  have hev : (fun r => pdCx k (ψ r) x) =ᶠ[𝓝 ρ]
      (fun r => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (r, x) (0, B0579.dir k)) := by
    filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with r hr
    exact pdCx_eq_strip hj hr k x
  rw [pdCx_ladDt_eq hj hρ k x, ← symm_strip hj hρ x ((1 : ℝ), (0 : ℝ × ℝ)) (0, B0579.dir k)]
  exact h3.congr_of_eventuallyEq hev

lemma continuous_pdCx_strip
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ioo t s) (k : Fin 2) : Continuous (fun x => pdCx k (ψ r) x) := by
  have hA : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2) p (0, B0579.dir k)) (Ioo t s ×ˢ univ) :=
    (strip_cont_fderiv_on hj).clm_apply continuousOn_const
  have hc : Continuous (fun x : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2) (r, x) (0, B0579.dir k)) :=
    hA.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hr, mem_univ x⟩)
  have e : (fun x => pdCx k (ψ r) x) = fun x =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2) (r, x) (0, B0579.dir k) :=
    funext fun x => pdCx_eq_strip hj hr k x
  rw [e]
  exact hc

lemma continuous_pdCx_ladDt
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (k : Fin 2) :
    Continuous (fun x => pdCx k (ladDt ψ ρ) x) := by
  have hB : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2)) p (0, B0579.dir k)
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ioo t s ×ˢ univ) :=
    ((strip_cont_fderiv2_on hj).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hc : Continuous (fun x : ℝ × ℝ =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2)) (ρ, x) (0, B0579.dir k)
        ((1 : ℝ), (0 : ℝ × ℝ))) :=
    hB.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hρ, mem_univ x⟩)
  have e : (fun x => pdCx k (ladDt ψ ρ) x) = fun x =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2)) (ρ, x) (0, B0579.dir k)
        ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun x => pdCx_ladDt_eq hj hρ k x
  rw [e]
  exact hc

lemma gStrip_continuousOn
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    (k : Fin 2) (m : ℝ) : ContinuousOn (gStrip ψ k m) (Ioo t s ×ˢ univ) := by
  have hA : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2) p (0, B0579.dir k)) (Ioo t s ×ˢ univ) :=
    (strip_cont_fderiv_on hj).clm_apply continuousOn_const
  have hB : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => ψ q.1 q.2)) p (0, B0579.dir k)
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ioo t s ×ˢ univ) :=
    ((strip_cont_fderiv2_on hj).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hJ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.jb p.2 ^ (-m)) (Ioo t s ×ˢ univ) :=
    ((B0579.continuous_jb_rpow (-m)).comp continuous_snd).continuousOn
  unfold gStrip
  exact hJ.mul (continuousOn_const.mul
    (Complex.continuous_re.comp_continuousOn ((Complex.continuous_conj.comp_continuousOn hA).mul hB)))

/-- The rewriting of the integrand on the strip. -/
lemma integrand_eq_gStrip
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ioo t s) (k : Fin 2) (m R : ℝ) (x : ℝ × ℝ) :
    ladCut R x ^ 2 * (B0579.jb x ^ (-m) * (2 * ((starRingEnd ℂ) (pdCx k (ψ r) x) *
        pdCx k (ladDt ψ r) x).re)) =
      ladCut R x ^ 2 * gStrip ψ k m (r, x) := by
  rw [pdCx_eq_strip hj hr k x, pdCx_ladDt_eq hj hr k x]
  rfl

/-- The per-component derivative of the cut energy, under the integral sign. -/
lemma hasDerivAt_cut_k
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {c m R : ℝ} (hc : 0 < c) (hR : 0 < R) {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (k : Fin 2) :
    HasDerivAt (fun r => ∫ x in B0579.cell c,
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (ψ r) x‖ ^ 2))
      (∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        (2 * ((starRingEnd ℂ) (pdCx k (ψ ρ) x) * pdCx k (ladDt ψ ρ) x).re))) ρ := by
  have hmin : 0 < min (ρ - t) (s - ρ) := lt_min (sub_pos.2 hρ.1) (sub_pos.2 hρ.2)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ρ - t ∧ δ < s - ρ :=
    ⟨min (ρ - t) (s - ρ) / 2, half_pos hmin, by linarith [min_le_left (ρ - t) (s - ρ)],
      by linarith [min_le_right (ρ - t) (s - ρ)]⟩
  have hsub : Icc (ρ - δ) (ρ + δ) ⊆ Ioo t s := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hs : Ioo (ρ - δ) (ρ + δ) ∈ 𝓝 ρ := Ioo_mem_nhds (by linarith) (by linarith)
  have hK : IsCompact (Icc (ρ - δ) (ρ + δ) ×ˢ B0579.box c (2 * R)) :=
    isCompact_Icc.prod (B0579.isCompact_box c (2 * R))
  have hKO : Icc (ρ - δ) (ρ + δ) ×ˢ B0579.box c (2 * R) ⊆
      Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := fun p hp => ⟨hsub hp.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((gStrip_continuousOn hj k m).mono hKO)
  have hC₀nn : 0 ≤ max C 0 := le_max_right _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (B0579.cell c))
    (F := fun r x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (ψ r) x‖ ^ 2))
    (F' := fun r x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        (2 * ((starRingEnd ℂ) (pdCx k (ψ r) x) * pdCx k (ladDt ψ r) x).re)))
    (bound := fun x => max C 0 * ladCut (2 * R) x)
    hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · -- measurability of the integrands near ρ
    filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with r hr
    exact (((ladCut_continuous R).pow 2).mul ((B0579.continuous_jb_rpow (-m)).mul
      ((continuous_pdCx_strip hj hr k).norm.pow 2))).aestronglyMeasurable
  · -- integrability at ρ
    refine integrableOn_cell_of_vanish (c := c) (R := R) hR ?_ (fun x hx => ?_)
    · exact ((ladCut_continuous R).pow 2).mul ((B0579.continuous_jb_rpow (-m)).mul
        ((continuous_pdCx_strip hj hρ k).norm.pow 2))
    · simp [ladCut_eq_zero_of hR hx]
  · -- measurability of the derivative at ρ
    refine Continuous.aestronglyMeasurable ?_
    exact ((ladCut_continuous R).pow 2).mul ((B0579.continuous_jb_rpow (-m)).mul
      (continuous_const.mul (Complex.continuous_re.comp
        ((Complex.continuous_conj.comp (continuous_pdCx_strip hj hρ k)).mul
          (continuous_pdCx_ladDt hj hρ k)))))
  · -- the uniform bound
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (ae_of_all _ fun x hx r hr => ?_)
    have hr' : r ∈ Ioo t s := hsub (Ioo_subset_Icc_self hr)
    show ‖ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        (2 * ((starRingEnd ℂ) (pdCx k (ψ r) x) * pdCx k (ladDt ψ r) x).re))‖ ≤
      max C 0 * ladCut (2 * R) x
    by_cases hx2 : 2 * R ^ 2 ≤ x.2 ^ 2
    · rw [ladCut_eq_zero_of hR hx2, zero_pow two_ne_zero, zero_mul, norm_zero]
      exact mul_nonneg hC₀nn (ladCut_nonneg _ _)
    · push Not at hx2
      have habs : |x.2| ≤ 2 * R := by nlinarith [sq_abs x.2, abs_nonneg x.2]
      have hl1 : ladCut (2 * R) x = 1 :=
        ladCut_eq_one_of (by linarith) (by nlinarith [sq_abs x.2, abs_nonneg x.2])
      have hxK : x ∈ B0579.box c (2 * R) := ⟨Ico_subset_Icc_self hx.1, abs_le.1 habs⟩
      have hG : ‖gStrip ψ k m (r, x)‖ ≤ C := hC (r, x) ⟨Ioo_subset_Icc_self hr, hxK⟩
      rw [integrand_eq_gStrip hj hr' k m R x, hl1, mul_one, norm_mul,
        Real.norm_of_nonneg (pow_nonneg (ladCut_nonneg R x) 2)]
      have h1 : ladCut R x ^ 2 ≤ 1 := pow_le_one₀ (ladCut_nonneg R x) (ladCut_le_one R x)
      calc ladCut R x ^ 2 * ‖gStrip ψ k m (r, x)‖
          ≤ 1 * ‖gStrip ψ k m (r, x)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ max C 0 := by rw [one_mul]; exact le_trans hG (le_max_left _ _)
  · -- integrability of the bound
    exact integrableOn_cell_of_vanish (c := c) (R := 2 * R) (by linarith)
      (continuous_const.mul (ladCut_continuous _))
      (fun x hx => by simp [ladCut_eq_zero_of (R := 2 * R) (by linarith) hx])
  · -- pointwise derivative in the age
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (ae_of_all _ fun x _ r hr => ?_)
    have hr' : r ∈ Ioo t s := hsub (Ioo_subset_Icc_self hr)
    have hz := ((hasDerivAt_pdCx_r hj hr' k x).norm_sq).const_mul (B0579.jb x ^ (-m))
    have hz2 := hz.const_mul (ladCut R x ^ 2)
    have hinner : inner ℝ (pdCx k (ψ r) x) (pdCx k (ladDt ψ r) x) =
        ((starRingEnd ℂ) (pdCx k (ψ r) x) * pdCx k (ladDt ψ r) x).re := by
      rw [Complex.inner, mul_comm]
    rw [hinner] at hz2
    exact hz2

end Strip

end CutE1DU

open CutE1DU in
theorem cutE1DerivUnder : UnforcedLeray.Short.IIIa.CutE1DerivUnder := by
  intro c m R t s ψ hc hR hj ρ hρ
  unfold cutE1
  exact HasDerivAt.fun_sum (fun k _ => hasDerivAt_cut_k hj hc hR hρ k)

end UnforcedLeray.Short.IIIa
