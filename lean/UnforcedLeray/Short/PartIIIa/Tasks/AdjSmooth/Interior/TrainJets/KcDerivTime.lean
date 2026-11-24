import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WPeriodic
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.KcDerivSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `PartIII-a:T21/2/7/2/1/1/2/13`: the age derivative passes under `K_c`

Proof of `TjKcDerivTime` (`Sub/AdjInterior/Train/Defs.lean`, SP 3052-3058).

* At `ρ > 0` the line `s ↦ (ρ, x) + s stDir 0` stays in the interior of `tjU` near `s = 0`, so
  the age derivative of `h` is the derivative of that line (`tj_time_hasDerivAt`). The reflected
  form of `K_c g` on the line is the cell integral of `g(ρ + s, x - y) • bsKernel c y`, and
  differentiation under the integral is dominated by `C (1 + (x₂ - y₂)²)^{-(m+1)/2} ‖bsKernel c y‖`
  (no spatial shift is needed in the age direction).
* At `ρ = 0` the vector fields `tjW [0] h` and `tjKc c (tjW [0] g)` are continuous within `tjU`
  (`tj_kc_continuousWithinAt`, by dominated convergence with the spatial shift controlled by
  `tj_wt_compare`), and they agree on the path `s ↦ (s, x)`, `s > 0`; the limit gives equality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The derivative along the age direction at a point of positive age (vector valued). -/
theorem tj_time_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × (ℝ × ℝ) → F} (hh : ContDiffOn ℝ ∞ h tjU) {q : ℝ × (ℝ × ℝ)} {t : ℝ}
    (ht : 0 < (q + t • stDir 0).1) :
    HasDerivAt (fun s : ℝ => h (q + s • stDir 0)) (tjW [0] h (q + t • stDir 0)) t := by
  have hn : tjU ∈ 𝓝 (q + t • stDir 0) :=
    mem_of_superset (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem)
      (fun z hz => ⟨Ioi_subset_Ici_self hz.1, mem_univ _⟩)
  have hW : tjW [0] h (q + t • stDir 0) = fderiv ℝ h (q + t • stDir 0) (stDir 0) := by
    show fderivWithin ℝ h tjU (q + t • stDir 0) (stDir 0) = _
    rw [fderivWithin_of_mem_nhds hn]
  have hd : HasFDerivAt h (fderiv ℝ h (q + t • stDir 0)) (q + t • stDir 0) :=
    ((hh.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => q + s • stDir 0) (stDir 0) t := by
    have := ((hasDerivAt_id t).smul_const (stDir 0)).const_add q
    simpa using this
  have := hd.comp_hasDerivAt t hγ
  rw [hW]
  exact this

/-- The age derivative at a point of positive age, for the reflected form of `K_c`. -/
theorem tj_time_interior {c m : ℝ} (hc : 1 ≤ c) (hm : 0 < m)
    {g : ℝ × (ℝ × ℝ) → ℝ} {h : ℝ × (ℝ × ℝ) → UnforcedLeray.Cyl.Vec2}
    (hg : ContDiffOn ℝ ∞ g tjU) (hh : ContDiffOn ℝ ∞ h tjU)
    (hper : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, g (ρ, (x.1 + c, x.2)) = g (ρ, x))
    (hgW : TjWBdd m g) (hDW : TjWBdd m (tjW [0] g))
    (hEq : EqOn h (tjKc c g) tjU) (ρ : ℝ) (x : ℝ × ℝ) (hρ : 0 < ρ) :
    tjW [0] h (ρ, x) = tjKc c (tjW [0] g) (ρ, x) := by
  have hρ0 : 0 ≤ ρ := hρ.le
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hσ : (0 : ℝ) ≤ (m + 1) / 2 := by linarith
  obtain ⟨C, hC⟩ := hDW (2 * ρ) (by linarith)
  obtain ⟨Cg, hCg⟩ := hgW (2 * ρ) (by linarith)
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _)) (hC ρ ⟨hρ0, by linarith⟩ (0, 0))
  have hCg0 : 0 ≤ Cg :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _)) (hCg ρ ⟨hρ0, by linarith⟩ (0, 0))
  -- the derivative of `h` along the age line
  have H1 : HasDerivAt (fun s : ℝ => h ((ρ, x) + s • stDir 0)) (tjW [0] h (ρ, x)) 0 := by
    have := tj_time_hasDerivAt hh (q := (ρ, x)) (t := 0) (by simpa [stDir] using hρ)
    rwa [zero_smul, add_zero] at this
  have hq : ∀ s : ℝ, (ρ, x) + s • stDir 0 = (ρ + s, x) := fun s =>
    Prod.ext (by simp [stDir]) (by simp [stDir])
  -- `h = K_c g` on the line near `s = 0`
  have hev : (fun s : ℝ => tjKc c g ((ρ, x) + s • stDir 0)) =ᶠ[𝓝 0]
      (fun s : ℝ => h ((ρ, x) + s • stDir 0)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with s hs
    have hs' : |s| < ρ := by rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    have hmem : ((ρ, x) + s • stDir 0) ∈ tjU := by
      rw [hq s]
      exact mem_prod.2 ⟨show (ρ + s) ∈ Ici (0 : ℝ) from mem_Ici.2 (by linarith [(abs_lt.1 hs').1]),
        mem_univ _⟩
    exact (hEq hmem).symm
  have H2 : HasDerivAt (fun s : ℝ => tjKc c g ((ρ, x) + s • stDir 0)) (tjW [0] h (ρ, x)) 0 :=
    H1.congr_of_eventuallyEq hev
  -- the reflected form of `K_c g` on the line
  have hK_g : ∀ s : ℝ, |s| < ρ → tjKc c g ((ρ, x) + s • stDir 0) =
      ∫ y in UnforcedLeray.Cyl.cell c, g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y := by
    intro s hs
    have hpos' : 0 ≤ ρ + s := by linarith [(abs_lt.1 hs).1]
    have hωs : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => g (ρ + s, w)) :=
      fun z => hper (ρ + s) hpos' z
    rw [hq s]
    exact UnforcedLeray.Cyl.K_eq_reflect hc0 hωs x
  have hfunK : (fun s : ℝ => tjKc c g ((ρ, x) + s • stDir 0)) =ᶠ[𝓝 0]
      (fun s : ℝ => ∫ y in UnforcedLeray.Cyl.cell c,
        g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with s hs
    exact hK_g s (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs)
  -- measurability and integrability
  have hgcont : ContinuousOn g tjU := hg.continuousOn
  have hWcont : ContinuousOn (tjW [0] g) tjU := (tjW_contDiffOn hg [0]).continuousOn
  have hmeasG : ∀ s : ℝ, |s| < ρ → AEStronglyMeasurable
      (fun y : ℝ × ℝ => g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro s hs
    have hpos' : 0 ≤ ρ + s := by linarith [(abs_lt.1 hs).1]
    have hc1 : Continuous (fun y : ℝ × ℝ => g (ρ + s, x - y)) :=
      hgcont.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id))
        (fun y => mem_prod.2 ⟨show (ρ + s) ∈ Ici (0 : ℝ) from mem_Ici.2 hpos', mem_univ _⟩)
    exact hc1.aestronglyMeasurable.smul
      (UnforcedLeray.Cyl.measurable_bsKernel c).aestronglyMeasurable
  have hmeasF' : ∀ s : ℝ, |s| < ρ → AEStronglyMeasurable
      (fun y : ℝ × ℝ => tjW [0] g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro s hs
    have hpos' : 0 ≤ ρ + s := by linarith [(abs_lt.1 hs).1]
    have hc1 : Continuous (fun y : ℝ × ℝ => tjW [0] g (ρ + s, x - y)) :=
      hWcont.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id))
        (fun y => mem_prod.2 ⟨show (ρ + s) ∈ Ici (0 : ℝ) from mem_Ici.2 hpos', mem_univ _⟩)
    exact hc1.aestronglyMeasurable.smul
      (UnforcedLeray.Cyl.measurable_bsKernel c).aestronglyMeasurable
  have hvx : ∀ y : ℝ × ℝ, (x - y).2 = x.2 - y.2 := fun y => by simp
  have hbd : ∀ s ∈ Metric.ball (0 : ℝ) (ρ / 2), ∀ y : ℝ × ℝ,
      ‖tjW [0] g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y‖ ≤
        C * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖) := by
    intro s hs y
    have hs' : |s| < ρ / 2 := by rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    have hmem : ρ + s ∈ Icc (0 : ℝ) (2 * ρ) :=
      ⟨by linarith [(abs_lt.1 hs').1], by linarith [(abs_lt.1 hs').2]⟩
    have hD := tj_abs_le_of_wt (v := (x - y).2) hC0 (hC (ρ + s) hmem (x - y))
    rw [hvx y] at hD
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_of_eq (by ring))
  have hF0 : Integrable (fun y : ℝ × ℝ => g (ρ + 0, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    refine Integrable.mono' ((tj_wt_integrable hm hc x.2).const_mul Cg)
      (hmeasG 0 (by simpa using hρ)) (ae_of_all _ fun y => ?_)
    have hmem : ρ + 0 ∈ Icc (0 : ℝ) (2 * ρ) := ⟨by linarith, by linarith⟩
    have hD := tj_abs_le_of_wt (v := (x - y).2) hCg0 (hCg (ρ + 0) hmem (x - y))
    rw [hvx y] at hD
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_of_eq (by ring))
  -- the derivative of the integrand in `s`
  have hdiff : ∀ᵐ y ∂(volume.restrict (UnforcedLeray.Cyl.cell c)),
      ∀ s ∈ Metric.ball (0 : ℝ) (ρ / 2),
        HasDerivAt (fun s' : ℝ => g (ρ + s', x - y) • UnforcedLeray.Cyl.bsKernel c y)
          (tjW [0] g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y) s := by
    refine ae_of_all _ (fun y s hs => ?_)
    have hs' : |s| < ρ / 2 := by rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    have e1 : ∀ s' : ℝ, (ρ, x - y) + s' • stDir 0 = (ρ + s', x - y) := fun s' =>
      Prod.ext (by simp [stDir]) (by simp [stDir])
    have hpos : 0 < ((ρ, x - y) + s • stDir 0).1 := by
      rw [e1 s]
      show 0 < ρ + s
      linarith [(abs_lt.1 hs').1]
    have hline := tj_time_hasDerivAt hg (q := (ρ, x - y)) (t := s)
      hpos
    simp only [e1] at hline
    exact hline.smul_const (UnforcedLeray.Cyl.bsKernel c y)
  have hbI : Integrable (fun y : ℝ × ℝ => C * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
      ‖UnforcedLeray.Cyl.bsKernel c y‖)) (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    (tj_wt_integrable hm hc x.2).const_mul C
  have hD : HasDerivAt (fun s : ℝ => ∫ y in UnforcedLeray.Cyl.cell c,
        g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (∫ y in UnforcedLeray.Cyl.cell c, tjW [0] g (ρ, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      0 := by
    have hFm : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable
        (fun y : ℝ × ℝ => g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
        (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) (half_pos hρ))
        (fun s hs => hmeasG s (by
          have := (Metric.mem_ball.1 hs)
          rw [Real.dist_eq, sub_zero] at this
          linarith))
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (UnforcedLeray.Cyl.cell c))
      (F := fun s y => g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (F' := fun s y => tjW [0] g (ρ + s, x - y) • UnforcedLeray.Cyl.bsKernel c y)
      (x₀ := 0)
      (bound := fun y => C * ((1 + (x.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
        ‖UnforcedLeray.Cyl.bsKernel c y‖))
      (Metric.ball_mem_nhds 0 (half_pos hρ)) hFm hF0 (hmeasF' 0 (by simpa using hρ))
      (ae_of_all _ (fun y s hs => hbd s hs y)) hbI hdiff
    simpa only [add_zero] using key.2
  -- the value of `K_c (∂_ρ g)` as a reflected integral
  have hR : tjKc c (tjW [0] g) (ρ, x) =
      ∫ y in UnforcedLeray.Cyl.cell c, tjW [0] g (ρ, x - y) • UnforcedLeray.Cyl.bsKernel c y := by
    have hωW : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tjW [0] g (ρ, w)) :=
      fun z => tjWPeriodic c g hg hper [0] ρ hρ0 z
    exact UnforcedLeray.Cyl.K_eq_reflect hc0 hωW x
  have H3 : HasDerivAt (fun s : ℝ => tjKc c g ((ρ, x) + s • stDir 0))
      (tjKc c (tjW [0] g) (ρ, x)) 0 := by
    rw [hR]
    exact hD.congr_of_eventuallyEq hfunK
  exact H2.unique H3

/-- **Continuity of `K_c` within the half-space** (dominated convergence): for a continuous,
`c`-periodic `G` with `TjWBdd m G`, `K_c G` is continuous within `tjU` at every point of `tjU`. -/
theorem tj_kc_continuousWithinAt {c m : ℝ} (hc : 1 ≤ c) (hm : 0 < m)
    (G : ℝ × (ℝ × ℝ) → ℝ) (hG : ContinuousOn G tjU)
    (hper : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, G (ρ, (x.1 + c, x.2)) = G (ρ, x))
    (hGW : TjWBdd m G) (p0 : ℝ × (ℝ × ℝ)) (hp0 : p0 ∈ tjU) :
    ContinuousWithinAt (tjKc c G) tjU p0 := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hσ : (0 : ℝ) ≤ (m + 1) / 2 := by linarith
  have hp0ρ : 0 ≤ p0.1 := mem_Ici.1 (mem_prod.1 hp0).1
  obtain ⟨C, hC⟩ := hGW (p0.1 + 1) (by linarith)
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _))
      (hC p0.1 ⟨hp0ρ, by linarith⟩ (0, 0))
  -- the reflected form of `K_c G` on `tjU`
  have hrefl : ∀ p ∈ tjU, tjKc c G p =
      ∫ y in UnforcedLeray.Cyl.cell c, G (p.1, p.2 - y) • UnforcedLeray.Cyl.bsKernel c y := by
    intro p hp
    have hω : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => G (p.1, w)) :=
      fun z => hper p.1 (mem_Ici.1 (mem_prod.1 hp).1) z
    exact UnforcedLeray.Cyl.K_eq_reflect hc0 hω p.2
  -- pointwise continuity of the integrand within `tjU`
  have hcontY : ∀ y : ℝ × ℝ, ContinuousWithinAt
      (fun p : ℝ × (ℝ × ℝ) => G (p.1, p.2 - y)) tjU p0 := by
    intro y
    have hmaps : MapsTo (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2 - y)) tjU tjU :=
      fun p hp => mem_prod.2 ⟨(mem_prod.1 hp).1, mem_univ _⟩
    have hcontφ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2 - y)) tjU :=
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
    exact (hG.comp hcontφ hmaps).continuousWithinAt hp0
  -- eventually near `p0` within `tjU`
  have hev1 : ∀ᶠ p in 𝓝[tjU] p0, |p.2.2 - p0.2.2| < 1 := by
    have ht : Tendsto (fun p : ℝ × (ℝ × ℝ) => |p.2.2 - p0.2.2|) (𝓝 p0) (𝓝 0) := by
      have hcont : Continuous (fun p : ℝ × (ℝ × ℝ) => |p.2.2 - p0.2.2|) :=
        ((continuous_snd.comp continuous_snd).sub continuous_const).abs
      have h0 : |p0.2.2 - p0.2.2| = 0 := by simp
      have := hcont.tendsto p0
      rwa [h0] at this
    exact (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds one_pos)
  have hev1' : ∀ᶠ p in 𝓝[tjU] p0, p.1 < p0.1 + 1 := by
    have ht : Tendsto (fun p : ℝ × (ℝ × ℝ) => p.1) (𝓝 p0) (𝓝 p0.1) :=
      (continuous_fst.tendsto p0)
    exact (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ p in 𝓝[tjU] p0, tjKc c G p =
      ∫ y in UnforcedLeray.Cyl.cell c, G (p.1, p.2 - y) • UnforcedLeray.Cyl.bsKernel c y :=
    eventually_nhdsWithin_of_forall (fun p hp => hrefl p hp)
  -- dominated convergence along `𝓝[tjU] p0`
  have hdom : Tendsto (fun p : ℝ × (ℝ × ℝ) => ∫ y in UnforcedLeray.Cyl.cell c,
      G (p.1, p.2 - y) • UnforcedLeray.Cyl.bsKernel c y) (𝓝[tjU] p0)
      (𝓝 (∫ y in UnforcedLeray.Cyl.cell c,
        G (p0.1, p0.2 - y) • UnforcedLeray.Cyl.bsKernel c y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun y => (C * (3 : ℝ) ^ ((m + 1) / 2)) *
        ((1 + (p0.2.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) * ‖UnforcedLeray.Cyl.bsKernel c y‖))
      ?_ ?_ ((tj_wt_integrable hm hc p0.2.2).const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      have hc1 : Continuous (fun y : ℝ × ℝ => G (p.1, p.2 - y)) :=
        hG.comp_continuous (continuous_const.prodMk (continuous_const.sub continuous_id))
          (fun y => mem_prod.2 ⟨(mem_prod.1 hp).1, mem_univ _⟩)
      exact hc1.aestronglyMeasurable.smul
        (UnforcedLeray.Cyl.measurable_bsKernel c).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, hev1, hev1'] with p hp hp1 hp2
      refine ae_of_all _ (fun y => ?_)
      have hpρ : 0 ≤ p.1 := (mem_Ici.1 (mem_prod.1 hp).1)
      have hD := tj_abs_le_of_wt (v := (p.2 - y).2) hC0 (hC p.1 ⟨hpρ, by linarith⟩ (p.2 - y))
      have hsame : (p.2 - y).2 = (p0.2.2 - y.2) + (p.2.2 - p0.2.2) := by simp
      rw [hsame] at hD
      have hcmp := tj_wt_compare hσ (p0.2.2 - y.2) (p.2.2 - p0.2.2) hp1.le
      rw [norm_smul, Real.norm_eq_abs]
      calc |G (p.1, p.2 - y)| * ‖UnforcedLeray.Cyl.bsKernel c y‖
          ≤ (C * ((3 : ℝ) ^ ((m + 1) / 2) * (1 + (p0.2.2 - y.2) ^ 2) ^ (-((m + 1) / 2)))) *
              ‖UnforcedLeray.Cyl.bsKernel c y‖ :=
            mul_le_mul_of_nonneg_right (hD.trans (mul_le_mul_of_nonneg_left hcmp hC0))
              (norm_nonneg _)
        _ = (C * (3 : ℝ) ^ ((m + 1) / 2)) * ((1 + (p0.2.2 - y.2) ^ 2) ^ (-((m + 1) / 2)) *
            ‖UnforcedLeray.Cyl.bsKernel c y‖) := by ring
    · refine ae_of_all _ (fun y => ?_)
      exact (hcontY y).smul continuousWithinAt_const
  exact (show ContinuousWithinAt (fun p : ℝ × (ℝ × ℝ) => ∫ y in UnforcedLeray.Cyl.cell c,
      G (p.1, p.2 - y) • UnforcedLeray.Cyl.bsKernel c y) tjU p0 from hdom).congr_of_eventuallyEq
    hev2 (hrefl p0 hp0)

theorem tjKcDerivTime : TjKcDerivTime := by
  intro c m hc hm g h hg hh hper hgW hDW hEq
  have hG_cont : ContinuousOn (tjW [0] g) tjU := (tjW_contDiffOn hg [0]).continuousOn
  have hperW : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ,
      tjW [0] g (ρ, (x.1 + c, x.2)) = tjW [0] g (ρ, x) :=
    fun ρ hρ x => tjWPeriodic c g hg hper [0] ρ hρ x
  rintro ⟨ρ, x⟩ hp
  rcases (mem_Ici.1 (mem_prod.1 hp).1).lt_or_eq with hρ | hρ
  · exact tj_time_interior hc hm hg hh hper hgW hDW hEq ρ x hρ
  · subst hρ
    have hcont1 : ContinuousWithinAt (tjW [0] h) tjU (0, x) :=
      (tjW_contDiffOn hh [0]).continuousOn.continuousWithinAt hp
    have hcont2 : ContinuousWithinAt (tjKc c (tjW [0] g)) tjU (0, x) :=
      tj_kc_continuousWithinAt hc hm (tjW [0] g) hG_cont hperW hDW (0, x) hp
    have hφ : Tendsto (fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) (𝓝[Ioi 0] 0) (𝓝[tjU] (0, x)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_id.prodMk (continuous_const (y := x))).tendsto (0 : ℝ)).mono_left
          nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall (fun s hs =>
          mem_prod.2 ⟨show s ∈ Ici (0 : ℝ) from mem_Ici.2 (le_of_lt hs), mem_univ _⟩)
    have hT1 : Tendsto (tjW [0] h ∘ fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) (𝓝[Ioi 0] 0)
        (𝓝 (tjW [0] h (0, x))) := Tendsto.comp hcont1 hφ
    have hT2 : Tendsto (tjKc c (tjW [0] g) ∘ fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) (𝓝[Ioi 0] 0)
        (𝓝 (tjKc c (tjW [0] g) (0, x))) := Tendsto.comp hcont2 hφ
    have hEqev : (tjW [0] h ∘ fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) =ᶠ[𝓝[Ioi 0] 0]
        (tjKc c (tjW [0] g) ∘ fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
      eventually_nhdsWithin_of_forall (fun s hs =>
        tj_time_interior hc hm hg hh hper hgW hDW hEq s x hs)
    exact tendsto_nhds_unique_of_eventuallyEq hT1 hT2 hEqev

end UnforcedLeray.Short.IIIa
