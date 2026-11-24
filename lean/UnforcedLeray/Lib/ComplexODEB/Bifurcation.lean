import UnforcedLeray.Lib.ComplexODEB.BifurcationError
import UnforcedLeray.Lib.ComplexODEB.Continuation
import UnforcedLeray.Lib.ComplexODEB.NeutralExistence

/-!
# B0034 helper: local bifurcation below a neutral wavenumber

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

The local bifurcation input of the continuation behind B0034 (`paper/main.tex`,
lines 1012–1021; Lin 2003, Theorem 5.9; whole-line analogue: Lemma "Bifurcation at
`α_max`" of the Lin-free route, commit 4dd0a82). If `α > 1` is a neutral wavenumber of
`[a, b]` and `a < t_* < b`, then every `β` slightly below `α` is unstable
(`bifurcatesBelow_of_neutral`).

Proof. Put `ε = α² - β²`, `M = ∫ g²`, `I₊ = cauchyLimit a b (W g²)`; `Im I₊ > 0`
because `g(t_*) ≠ 0` (`neutralReal_pos`). With `z₀ = -ε M / I₊` and
`r = Im z₀ / 2`, the closed disc `|z - z₀| ≤ r` lies in the cone
`‖z‖ ≤ C Im z`, `C = 3‖I₊‖/Im I₊`, and in `‖z‖ ≤ (3/2)‖z₀‖`. By `bifurcation_error`,
the nontangential limits (`tendsto_cauchyIntegral`, and the `L¹` coefficient limit
of the draft `NontangentialCoefficientLimit`),
`‖D(β, a_*+z) G'(b) - I₊ (z - z₀)‖ = o(ε)` uniformly on the disc, while
`‖I₊‖ r ≍ ε`; the minimum-modulus lemma `exists_zero_of_affine_approximation`
gives a zero in the disc.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory Complex Metric
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential NonUniqueEuler.LinODE

theorem coeffDist_le {a b α β : ℝ} (hab : a ≤ b) {c : ℂ} (hc : 0 < c.im) :
    coeffDist a b α β c ≤
      |α ^ 2 - β ^ 2| * (b - a) +
        ∫ t in Ioc a b, ‖rayleighPotential α t c - neutralPotential α t‖ := by
  unfold coeffDist
  have hVc : Continuous (fun t => rayleighPotential β t c) := continuous_rayleighPotential β hc
  have hVc' : Continuous (fun t => rayleighPotential α t c) := continuous_rayleighPotential α hc
  have hVα : Continuous (neutralPotential α) := continuous_neutralPotential α
  rw [← intervalIntegral.integral_of_le hab]
  have j1 : IntervalIntegrable (fun t => ‖rayleighPotential β t c - neutralPotential α t‖)
      volume a b := (hVc.sub hVα).norm.intervalIntegrable a b
  have j2 : IntervalIntegrable (fun t => |α ^ 2 - β ^ 2| +
      ‖rayleighPotential α t c - neutralPotential α t‖) volume a b :=
    (continuous_const.add (hVc'.sub hVα).norm).intervalIntegrable a b
  have j3 : IntervalIntegrable (fun t => ‖rayleighPotential α t c - neutralPotential α t‖)
      volume a b := (hVc'.sub hVα).norm.intervalIntegrable a b
  calc (∫ t in a..b, ‖rayleighPotential β t c - neutralPotential α t‖)
      ≤ ∫ t in a..b, (|α ^ 2 - β ^ 2| + ‖rayleighPotential α t c - neutralPotential α t‖) := by
        apply intervalIntegral.integral_mono_on hab j1 j2
        intro t _
        have hsplit : rayleighPotential β t c - neutralPotential α t =
            (((β ^ 2 - α ^ 2 : ℝ) : ℂ)) + (rayleighPotential α t c - neutralPotential α t) := by
          unfold rayleighPotential
          push_cast
          ring
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    _ = |α ^ 2 - β ^ 2| * (b - a) +
          ∫ t in a..b, ‖rayleighPotential α t c - neutralPotential α t‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const j3,
          intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- Geometry of the disc `|z - z₀| ≤ Im z₀ / 2`, `z₀ = -ε M / I₊`. -/
theorem disc_props {Ip z₀ : ℂ} {ε M r : ℝ} (hIm : 0 < Ip.im) (hε : 0 < ε) (hM : 0 < M)
    (hz₀ : z₀ = -((ε * M : ℝ) : ℂ) / Ip) (hr : r = z₀.im / 2) :
    0 < r ∧ ‖Ip‖ * r = ε * (M * Ip.im / (2 * ‖Ip‖)) ∧
      ∀ z ∈ closedBall z₀ r, r ≤ z.im ∧ ‖z‖ ≤ 3 * M / (2 * ‖Ip‖) * ε ∧
        z ∈ criticalApproachCone (3 * ‖Ip‖ / Ip.im) := by
  have hIne : Ip ≠ 0 := fun h => by rw [h] at hIm; simp at hIm
  have hnI : 0 < ‖Ip‖ := norm_pos_iff.mpr hIne
  have hz₀im : z₀.im = ε * M * Ip.im / ‖Ip‖ ^ 2 := by
    rw [hz₀, Complex.div_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hz₀norm : ‖z₀‖ = ε * M / ‖Ip‖ := by
    rw [hz₀, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos hε hM)]
  have hr0 : 0 < r := by rw [hr, hz₀im]; positivity
  have hrle : r ≤ ‖z₀‖ / 2 := by
    rw [hr]
    have := (Complex.abs_im_le_norm z₀).trans' (le_abs_self _)
    linarith
  refine ⟨hr0, ?_, ?_⟩
  · rw [hr, hz₀im]
    field_simp
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have him : |z.im - z₀.im| ≤ r := by
    have := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im] at this
    linarith
  have hzim : r ≤ z.im := by
    rw [abs_le] at him
    have : z₀.im = 2 * r := by rw [hr]; ring
    linarith [him.1]
  have hznorm : ‖z‖ ≤ 3 / 2 * (ε * M / ‖Ip‖) := by
    have h1 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
      have := norm_add_le z₀ (z - z₀); simpa using this
    rw [hz₀norm] at h1 hrle
    linarith
  refine ⟨hzim, ?_, ⟨hr0.trans_le hzim, ?_⟩⟩
  · calc ‖z‖ ≤ 3 / 2 * (ε * M / ‖Ip‖) := hznorm
      _ = 3 * M / (2 * ‖Ip‖) * ε := by field_simp
  · have hCr : 3 * ‖Ip‖ / Ip.im * r = 3 / 2 * (ε * M / ‖Ip‖) := by
      rw [hr, hz₀im]
      field_simp
    have hCz : 3 * ‖Ip‖ / Ip.im * r ≤ 3 * ‖Ip‖ / Ip.im * z.im :=
      mul_le_mul_of_nonneg_left hzim (by positivity)
    linarith

/-- The affine approximation at one point of the disc. -/
theorem affine_bound {a b α β : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hb : neutralReal α a b = 0) {C B CR m K₀ K₁ K₂ lam ε M : ℝ} {Ip I1 z z₀ : ℂ}
    (hC : 0 < C) (hB : ∀ t ∈ Icc a b, |neutralReal α a t| ≤ B)
    (hCR : CR = B * Real.exp ((b - a) + (∫ t in a..b, ‖neutralPotential α t‖) + 1))
    (hm : m = offsetLower a b) (hK₀ : K₀ = 8 * B * (b - a) * (2 * C + 1) / m)
    (hK₁ : K₁ = (b - a) * B + K₂ * (‖I1‖ + 1 + K₀)) (hK₂0 : 0 ≤ K₂)
    (hε : ε = α ^ 2 - β ^ 2) (hε0 : 0 < ε)
    (hM : M = ∫ t in a..b, neutralReal α a t ^ 2) (hz₀ : z₀ = -((ε * M : ℝ) : ℂ) / Ip)
    (hIne : Ip ≠ 0) (hzcone : z ∈ criticalApproachCone C) (hznorm : ‖z‖ ≤ K₂ * ε)
    (hεba : ε * (b - a) ≤ lam) (hlam : lam ≤ 1 / 2)
    (hL0 : (∫ t in Ioc a b, ‖rayleighPotential α t (criticalShiftSpeed z) -
      neutralPotential α t‖) < lam)
    (hIz : ‖cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z - Ip‖ < lam)
    (hI1z : ‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ < ‖I1‖ + 1) :
    ‖evansFunction β a b (criticalShiftSpeed z) * neutralNormalizedDerivative α a b -
        Ip * (z - z₀)‖ ≤ ε * (lam * (2 * CR * K₁ + K₂)) := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a (left_mem_Icc.mpr hab.le))
  have hCR0 : 0 ≤ CR := by rw [hCR]; exact mul_nonneg hB0 (Real.exp_pos _).le
  have hm0 : 0 < m := by rw [hm]; exact offsetLower_pos a b
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]; apply div_nonneg _ hm0.le
    have := sub_pos.mpr hab
    positivity
  have hczim : 0 < (criticalShiftSpeed z).im := by simpa using hzcone.1
  have hlam0 : 0 ≤ lam := (norm_nonneg _).trans hIz.le
  have habs : |α ^ 2 - β ^ 2| = ε := by rw [hε]; exact abs_of_pos (hε ▸ hε0)
  have hL1 : coeffDist a b α β (criticalShiftSpeed z) ≤ 2 * lam := by
    have := coeffDist_le hab.le (α := α) (β := β) hczim
    rw [habs] at this
    linarith
  have hL1' : coeffDist a b α β (criticalShiftSpeed z) ≤ 1 := by linarith
  have herr := bifurcation_error hcrit hb hC hB hzcone hL1'
  rw [← hCR, ← hm, habs, ← hK₀] at herr
  rw [← hM] at herr
  have hcL : 0 ≤ coeffDist a b α β (criticalShiftSpeed z) :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)
  -- decompose
  have hdecomp : evansFunction β a b (criticalShiftSpeed z) * neutralNormalizedDerivative α a b -
      Ip * (z - z₀) =
      (evansFunction β a b (criticalShiftSpeed z) * neutralNormalizedDerivative α a b -
        (((α ^ 2 - β ^ 2 : ℝ) : ℂ) * ((M : ℝ) : ℂ) +
          z * cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z)) +
        z * (cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z - Ip) := by
    rw [hz₀, ← hε]
    field_simp
    push_cast
    ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hin : ε * (b - a) * B +
      ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀) ≤ ε * K₁ := by
    rw [hK₁]
    have h1 : ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀) ≤
        K₂ * ε * (‖I1‖ + 1 + K₀) :=
      mul_le_mul hznorm (by linarith) (by positivity) (by positivity)
    nlinarith
  have hin0 : 0 ≤ ε * (b - a) * B +
      ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀) := by
    have := sub_pos.mpr hab
    positivity
  have hfirst : CR * coeffDist a b α β (criticalShiftSpeed z) *
      (ε * (b - a) * B + ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀))
      ≤ CR * (2 * lam) * (ε * K₁) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 hCR0) hin0).trans
      (mul_le_mul_of_nonneg_left hin (by positivity))
  have hsecond : ‖z‖ * ‖cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z - Ip‖ ≤
      K₂ * ε * lam :=
    mul_le_mul hznorm hIz.le (norm_nonneg _) (by positivity)
  have herr' := herr.trans (by
    have : (ε * (b - a) * B +
        ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀)) =
        (ε * (b - a) * B +
        ‖z‖ * (‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ + K₀)) := rfl
    exact le_of_eq rfl)
  calc _ ≤ CR * (2 * lam) * (ε * K₁) + K₂ * ε * lam := by
        refine add_le_add ?_ hsecond
        refine le_trans ?_ hfirst
        refine le_of_le_of_eq herr ?_
        ring
    _ = ε * (lam * (2 * CR * K₁ + K₂)) := by ring

/-- Local bifurcation (Lin 2003, Theorem 5.9) for the Gaussian on `[a, b]`. -/
theorem bifurcatesBelow_of_neutral {a b α : ℝ} (hα : 1 < α)
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hb : neutralReal α a b = 0) :
    BifurcatesBelow a b α := by
  have hab : a < b := hcrit.1.trans hcrit.2
  have hgpos := neutralReal_pos hα hcrit hb
  -- the mass
  obtain ⟨M, hMdef⟩ : ∃ M, M = ∫ t in a..b, neutralReal α a t ^ 2 := ⟨_, rfl⟩
  have hM : 0 < M := by
    rw [hMdef]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (((continuous_neutralReal α a).pow 2).intervalIntegrable a b)
      (fun t ht => pow_pos (hgpos t ht) 2) hab
  -- the Cauchy limits
  have hWs : ContDiff ℝ 1 Wlog := Wlog_smooth.of_le (by exact_mod_cast le_top)
  have hgs : ContDiff ℝ 1 (neutralReal α a) :=
    (neutralReal_smooth α a).of_le (by exact_mod_cast le_top)
  have hφ₂s : ContDiff ℝ 1 (fun t => Wlog t * neutralReal α a t ^ 2) := hWs.mul (hgs.pow 2)
  have hφ₁s : ContDiff ℝ 1 (fun t => Wlog t * neutralReal α a t) := hWs.mul hgs
  obtain ⟨Ip, hIpdef⟩ : ∃ I, I = cauchyLimit a b (fun t => Wlog t * neutralReal α a t ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨I1, hI1def⟩ : ∃ I, I = cauchyLimit a b (fun t => Wlog t * neutralReal α a t) :=
    ⟨_, rfl⟩
  have hIm : 0 < Ip.im := by
    rw [hIpdef, im_cauchyLimit]
    have hφ : 0 < Wlog neutralCriticalTime * neutralReal α a neutralCriticalTime ^ 2 :=
      mul_pos (Wlog_pos _) (pow_pos (hgpos _ hcrit) 2)
    have hJ' := offsetDeriv_neg neutralCriticalTime
    unfold cauchyCoeff
    have : Wlog neutralCriticalTime * neutralReal α a neutralCriticalTime ^ 2 /
        offsetDeriv neutralCriticalTime < 0 := div_neg_of_pos_of_neg hφ hJ'
    nlinarith [Real.pi_pos]
  have hIne : Ip ≠ 0 := fun h => by rw [h] at hIm; simp at hIm
  have hnI : 0 < ‖Ip‖ := norm_pos_iff.mpr hIne
  obtain ⟨C, hCdef⟩ : ∃ C, C = 3 * ‖Ip‖ / Ip.im := ⟨_, rfl⟩
  have hC : 0 < C := by rw [hCdef]; positivity
  -- uniform constants
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_neutralReal α a).continuousOn (s := Icc a b))
  have hB' : ∀ t ∈ Icc a b, |neutralReal α a t| ≤ B := fun t ht => by
    have := hB t ht; rwa [Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' a (left_mem_Icc.mpr hab.le))
  obtain ⟨CR, hCRdef⟩ : ∃ K, K = B * Real.exp ((b - a) +
      (∫ t in a..b, ‖neutralPotential α t‖) + 1) := ⟨_, rfl⟩
  have hCR0 : 0 ≤ CR := by rw [hCRdef]; exact mul_nonneg hB0 (Real.exp_pos _).le
  obtain ⟨m, hmdef⟩ : ∃ m, m = offsetLower a b := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact offsetLower_pos a b
  obtain ⟨K₀, hK₀⟩ : ∃ K, K = 8 * B * (b - a) * (2 * C + 1) / m := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]; apply div_nonneg _ hm.le
    have := sub_pos.mpr hab
    positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K, K = 3 * M / (2 * ‖Ip‖) := ⟨_, rfl⟩
  have hK₂0 : 0 < K₂ := by rw [hK₂]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K, K = (b - a) * B + K₂ * (‖I1‖ + 1 + K₀) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    have := sub_pos.mpr hab
    rw [hK₁]; positivity
  obtain ⟨κt, hκt⟩ : ∃ k, k = M * Ip.im / (2 * ‖Ip‖) := ⟨_, rfl⟩
  have hκt0 : 0 < κt := by rw [hκt]; positivity
  obtain ⟨lam, hlam⟩ : ∃ l, l = min (1 / 2) (κt / (4 * (2 * CR * K₁ + K₂ + 1))) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact lt_min (by norm_num) (by positivity)
  have hlam1 : lam ≤ 1 / 2 := by rw [hlam]; exact min_le_left _ _
  have hlam2 : lam ≤ κt / (4 * (2 * CR * K₁ + K₂ + 1)) := by rw [hlam]; exact min_le_right _ _
  have hlamk : 2 * (lam * (2 * CR * K₁ + K₂)) < κt := by
    have hpos : 0 < 4 * (2 * CR * K₁ + K₂ + 1) := by positivity
    have h := mul_le_mul_of_nonneg_right hlam2 (by positivity : (0 : ℝ) ≤ 2 * CR * K₁ + K₂)
    have h2 : κt / (4 * (2 * CR * K₁ + K₂ + 1)) * (2 * CR * K₁ + K₂) < κt / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith
    linarith
  -- the three nontangential limits
  have hL := tendsto_setIntegral_norm_criticalPotential_sub_neutral_nontangential α (Ioc a b)
    hC.le
  have hI := tendsto_cauchyIntegral hcrit hφ₂s hC
  have hI₁ := tendsto_cauchyIntegral hcrit hφ₁s hC
  rw [← hIpdef] at hI
  rw [← hI1def] at hI₁
  have hev : ∀ᶠ z in 𝓝[criticalApproachCone C] (0 : ℂ),
      (∫ t in Ioc a b, ‖rayleighPotential α t (criticalShiftSpeed z) - neutralPotential α t‖)
          < lam ∧
        ‖cauchyInt a b (fun t => Wlog t * neutralReal α a t ^ 2) z - Ip‖ < lam ∧
        ‖cauchyInt a b (fun t => Wlog t * neutralReal α a t) z‖ < ‖I1‖ + 1 :=
    (hL.eventually (gt_mem_nhds hlam0)).and
      (((tendsto_iff_norm_sub_tendsto_zero.mp hI).eventually (gt_mem_nhds hlam0)).and
        (hI₁.norm.eventually (gt_mem_nhds (by linarith))))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  -- the size of the wavenumber window
  obtain ⟨ε₀, hε₀⟩ : ∃ e, e = min (lam / (b - a)) (ρ / (2 * K₂)) := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]; exact lt_min (div_pos hlam0 (sub_pos.mpr hab)) (by positivity)
  refine ⟨min α (ε₀ / (2 * α)), lt_min (by linarith) (by positivity), ?_⟩
  intro β hβ
  obtain ⟨ε, hεdef⟩ : ∃ e, e = α ^ 2 - β ^ 2 := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    have := min_le_left α (ε₀ / (2 * α))
    linarith [hβ.1]
  have hε0 : 0 < ε := by rw [hεdef]; nlinarith [hβ.2]
  have hεε₀ : ε < ε₀ := by
    have h1 : α - β < ε₀ / (2 * α) := by
      have := min_le_right α (ε₀ / (2 * α))
      linarith [hβ.1]
    have h2 : ε = (α - β) * (α + β) := by rw [hεdef]; ring
    have h3 : α + β < 2 * α := by linarith [hβ.2]
    rw [h2]
    calc (α - β) * (α + β) < ε₀ / (2 * α) * (2 * α) :=
          mul_lt_mul'' h1 h3 (by linarith [hβ.2]) (by linarith)
      _ = ε₀ := by field_simp
  have hεba : ε * (b - a) ≤ lam := by
    have := min_le_left (lam / (b - a)) (ρ / (2 * K₂))
    rw [← hε₀] at this
    have h := mul_le_mul_of_nonneg_right (hεε₀.le.trans this) (sub_pos.mpr hab).le
    rwa [div_mul_cancel₀ _ (sub_pos.mpr hab).ne'] at h
  have hεK₂ : K₂ * ε < ρ := by
    have := min_le_right (lam / (b - a)) (ρ / (2 * K₂))
    rw [← hε₀] at this
    have h := mul_lt_mul_of_pos_left (hεε₀.trans_le this) hK₂0
    have h' : K₂ * (ρ / (2 * K₂)) = ρ / 2 := by field_simp
    linarith
  -- the disc
  obtain ⟨z₀, hz₀⟩ : ∃ z, z = -((ε * M : ℝ) : ℂ) / Ip := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = z₀.im / 2 := ⟨_, rfl⟩
  obtain ⟨hr0, hIr, hdisc⟩ := disc_props hIm hε0 hM hz₀ hr
  rw [← hCdef, ← hK₂] at hdisc
  rw [← hκt] at hIr
  -- the function
  have hneutral : neutralNormalizedF α a b = 0 := by
    rw [(neutralNormalizedF_eq_ofReal α a b).1]; exact_mod_cast hb
  have hG'b : neutralNormalizedDerivative α a b ≠ 0 :=
    neutralNormalizedDerivative_ne_zero_of_value_zero α a b hneutral
  have hfd : DiffContOnCl ℂ (fun z => evansFunction β a b (criticalShiftSpeed z) *
      neutralNormalizedDerivative α a b) (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr0.ne']
    intro z hz
    have hzim : 0 < z.im := hr0.trans_le (hdisc z hz).1
    have hshift : DifferentiableAt ℂ (fun w : ℂ => criticalShiftSpeed w) z := by
      unfold criticalShiftSpeed; fun_prop
    have hev : DifferentiableAt ℂ (evansFunction β a b) (criticalShiftSpeed z) :=
      (differentiableOn_evansFunction β a b).differentiableAt
        (isOpen_upperHalfPlane.mem_nhds (by simpa [upperHalfPlane] using hzim))
    exact ((hev.comp z hshift).mul_const _).differentiableWithinAt
  have hηlt : 2 * (ε * (lam * (2 * CR * K₁ + K₂))) < ‖Ip‖ * r := by
    rw [hIr]
    nlinarith [mul_lt_mul_of_pos_left hlamk hε0]
  have happrox : ∀ z ∈ closedBall z₀ r,
      ‖evansFunction β a b (criticalShiftSpeed z) * neutralNormalizedDerivative α a b -
        Ip * (z - z₀)‖ ≤ ε * (lam * (2 * CR * K₁ + K₂)) := by
    intro z hz
    obtain ⟨-, hznorm, hzcone⟩ := hdisc z hz
    have hzρ : ‖z‖ < ρ := hznorm.trans_lt hεK₂
    have hmem : z ∈ ball (0 : ℂ) ρ ∩ criticalApproachCone C :=
      ⟨by rw [mem_ball, dist_zero_right]; exact hzρ, hzcone⟩
    obtain ⟨hL0, hIz, hI1z⟩ := hρsub hmem
    exact affine_bound hcrit hb hC hB' hCRdef hmdef hK₀ hK₁ hK₂0.le hεdef hε0 hMdef hz₀ hIne
      hzcone hznorm hεba hlam1 hL0 hIz hI1z
  obtain ⟨z, hz, hfz⟩ := exists_zero_of_affine_approximation hr0 hfd hηlt happrox
  refine ⟨criticalShiftSpeed z, by simpa using hr0.trans_le (hdisc z hz).1, ?_⟩
  exact (mul_eq_zero.mp hfz).resolve_right hG'b

end UnforcedLeray.ComplexODEB
