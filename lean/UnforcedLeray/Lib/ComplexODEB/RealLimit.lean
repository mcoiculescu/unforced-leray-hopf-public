import UnforcedLeray.Lib.ComplexODEB.Normalized
import UnforcedLeray.Lib.ComplexODEB.RealExclusion
import UnforcedLeray.Lib.ComplexODEB.Continuation
import UnforcedLeray.Analysis.Rayleigh.Compactness
import UnforcedLeray.Analysis.Rayleigh.SpeedBound
import NonUniqueEuler.P.Infra.ODE.Existence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# B0034 helper: no real limiting speed below a neutral wavenumber

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

The second analytic input of the continuation behind B0034 (`paper/main.tex`,
lines 1012–1048; Lin 2003, Lemma 5.8; whole-line analogue: the closedness step of
§3.4 of the Lin-free route, commit 4dd0a82): `NoRealLimitSpeed a b α` holds when `α` is a
neutral wavenumber of `[a, b]` and `a < t_* < b` (`noRealLimitSpeed_of_neutral`).

Proof. Normalize the unstable modes in `L²` (`exists_normalizedDirichlet`). Their
derivatives are uniformly bounded and `1/2`-Hölder (bounds without `1/Im c`), so by
Arzelà–Ascoli (the compiled `exists_uniformOnCompacts_subsequence_of_sup_sqrt_bound`)
a subsequence of derivatives converges uniformly on `[a, b]`; the modes converge
uniformly to `U = ∫ v`. Away from `Ω = c` the coefficients converge uniformly, so the
limit solves the real equation there. This is a `RealLimitMode`, which cannot exist
(`RealLimitMode.false`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Rayleigh.RealSpeed
open UnforcedLeray.Sturm UnforcedLeray.GaussianPotential

/-- Uniform convergence of products with bounded limits. -/
theorem tendstoUniformlyOn_mul_bounded {S : Set ℝ} {F G : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    {Mf Mg : ℝ} (hF : TendstoUniformlyOn F f atTop S) (hG : TendstoUniformlyOn G g atTop S)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ Mf) (hg : ∀ x ∈ S, ‖g x‖ ≤ Mg) :
    TendstoUniformlyOn (fun k x => F k x * G k x) (fun x => f x * g x) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  set η : ℝ := min 1 (ε / (2 * (1 + |Mf| + |Mg|))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε / (2 * (1 + |Mf| + |Mg|)) := min_le_right _ _
  filter_upwards [hF η hη0, hG η hη0] with k hk1 hk2 x hx
  simp only [dist_eq_norm] at hk1 hk2 ⊢
  have e : f x * g x - F k x * G k x = (f x - F k x) * g x + F k x * (g x - G k x) := by ring
  rw [e]
  have hFk : ‖F k x‖ ≤ |Mf| + 1 := by
    have := norm_le_norm_add_norm_sub' (F k x) (f x)
    have h1 : ‖F k x - f x‖ < η := by rw [norm_sub_rev]; exact hk1 x hx
    linarith [hf x hx, le_abs_self Mf]
  have hgx : ‖g x‖ ≤ |Mg| := (hg x hx).trans (le_abs_self _)
  calc ‖(f x - F k x) * g x + F k x * (g x - G k x)‖
      ≤ ‖f x - F k x‖ * ‖g x‖ + ‖F k x‖ * ‖g x - G k x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ η * |Mg| + (|Mf| + 1) * η :=
        add_le_add (mul_le_mul (hk1 x hx).le hgx (norm_nonneg _) hη0.le)
          (mul_le_mul hFk (hk2 x hx).le (norm_nonneg _) (by positivity))
    _ = η * (1 + |Mf| + |Mg|) := by ring
    _ ≤ ε / (2 * (1 + |Mf| + |Mg|)) * (1 + |Mf| + |Mg|) :=
        mul_le_mul_of_nonneg_right hη2 (by positivity)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg Mf, abs_nonneg Mg]

theorem abs_gaussianRayleighCoefficient_le (t : ℝ) : |gaussianRayleighCoefficient t| ≤ 8 := by
  unfold gaussianRayleighCoefficient
  have hJ : |gaussianOffset t| ≤ 1 := by
    have := gaussianOffset_sq_le_one t
    nlinarith [abs_nonneg (gaussianOffset t), sq_abs (gaussianOffset t)]
  rw [abs_mul, abs_neg, abs_of_pos (Wlog_pos t)]
  nlinarith [Wlog_le_eight t, Wlog_pos t, abs_nonneg (gaussianOffset t)]

/-- Uniform convergence of the coefficients away from the critical layer. -/
theorem tendstoUniformlyOn_rayleighPotential {S : Set ℝ} {d βs cs : ℝ} (hd : 0 < d)
    (hS : ∀ τ ∈ S, d ≤ |neutralOmega τ - cs|) {β : ℕ → ℝ} {c : ℕ → ℂ}
    (hβ : Tendsto β atTop (𝓝 βs)) (hc : Tendsto c atTop (𝓝 (cs : ℂ))) :
    TendstoUniformlyOn (fun k τ => rayleighPotential (β k) τ (c k))
      (fun τ => (realPotential βs cs τ : ℂ)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hβ2 : Tendsto (fun k => β k ^ 2) atTop (𝓝 (βs ^ 2)) := hβ.pow 2
  have h1 := (Metric.tendsto_nhds.mp hβ2) (ε / 2) (by positivity)
  have h2 := (Metric.tendsto_nhds.mp hc) (min (d / 2) (ε * d ^ 2 / 32)) (by positivity)
  filter_upwards [h1, h2] with k hk1 hk2 τ hτ
  rw [dist_eq_norm]
  have hdτ := hS τ hτ
  have hck : ‖c k - (cs : ℂ)‖ < min (d / 2) (ε * d ^ 2 / 32) := by
    rw [← dist_eq_norm]; exact hk2
  have hck1 : ‖c k - (cs : ℂ)‖ < d / 2 := hck.trans_le (min_le_left _ _)
  have hck2 : ‖c k - (cs : ℂ)‖ < ε * d ^ 2 / 32 := hck.trans_le (min_le_right _ _)
  have hd1 : d ≤ ‖(neutralOmega τ : ℂ) - (cs : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hdτ
  have hd2 : d / 2 ≤ ‖(neutralOmega τ : ℂ) - c k‖ := by
    have := norm_sub_norm_le ((neutralOmega τ : ℂ) - (cs : ℂ)) ((neutralOmega τ : ℂ) - c k)
    have e : ((neutralOmega τ : ℂ) - (cs : ℂ)) - ((neutralOmega τ : ℂ) - c k) = c k - cs := by
      ring
    rw [e] at this
    linarith
  have hne1 : (neutralOmega τ : ℂ) - (cs : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hd1; linarith
  have hne2 : (neutralOmega τ : ℂ) - c k ≠ 0 := by
    intro h; rw [h, norm_zero] at hd2; linarith
  have hdiff : (realPotential βs cs τ : ℂ) - rayleighPotential (β k) τ (c k) =
      ((βs ^ 2 - β k ^ 2 : ℝ) : ℂ) + (gaussianRayleighCoefficient τ : ℂ) * ((cs : ℂ) - c k) /
        (((neutralOmega τ : ℂ) - (cs : ℂ)) * ((neutralOmega τ : ℂ) - c k)) := by
    unfold realPotential rayleighPotential
    push_cast
    field_simp
    ring
  rw [hdiff]
  have hA := abs_gaussianRayleighCoefficient_le τ
  have hb1 : ‖((βs ^ 2 - β k ^ 2 : ℝ) : ℂ)‖ < ε / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [Real.dist_eq] at hk1; exact hk1
  have hb2 : ‖(gaussianRayleighCoefficient τ : ℂ) * ((cs : ℂ) - c k) /
      (((neutralOmega τ : ℂ) - (cs : ℂ)) * ((neutralOmega τ : ℂ) - c k))‖ ≤ ε / 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev (cs : ℂ)]
    have hden : d * (d / 2) ≤ ‖(neutralOmega τ : ℂ) - (cs : ℂ)‖ * ‖(neutralOmega τ : ℂ) - c k‖ :=
      mul_le_mul hd1 hd2 (by positivity) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    calc |gaussianRayleighCoefficient τ| * ‖c k - (cs : ℂ)‖ ≤ 8 * (ε * d ^ 2 / 32) :=
          mul_le_mul hA hck2.le (norm_nonneg _) (by norm_num)
      _ = ε / 2 * (d * (d / 2)) := by ring
      _ ≤ ε / 2 * (‖(neutralOmega τ : ℂ) - (cs : ℂ)‖ * ‖(neutralOmega τ : ℂ) - c k‖) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  calc _ ≤ ‖((βs ^ 2 - β k ^ 2 : ℝ) : ℂ)‖ + ‖(gaussianRayleighCoefficient τ : ℂ) *
        ((cs : ℂ) - c k) / (((neutralOmega τ : ℂ) - (cs : ℂ)) * ((neutralOmega τ : ℂ) - c k))‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hb1 hb2
    _ = ε := by ring

/-- Uniform convergence of the primitives `t ↦ ∫_a^t` on `[a, b]`. -/
theorem tendstoUniformlyOn_primitive {a b : ℝ} (hab : a ≤ b) {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hu : TendstoUniformlyOn F f atTop (Icc a b)) :
    TendstoUniformlyOn (fun n t => ∫ s in a..t, F n s) (fun t => ∫ s in a..t, f s) atTop
      (Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu (ε / (b - a + 1)) (div_pos hε (by linarith))] with n hn t ht
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    ((hF n).intervalIntegrable _ _)]
  have hb : ∀ x ∈ uIoc a t, ‖f x - F n x‖ ≤ ε / (b - a + 1) := by
    intro x hx
    rw [uIoc_of_le ht.1] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.trans ht.2⟩
    rw [← dist_eq_norm]
    exact (hn x hx').le
  have hta : |t - a| ≤ b - a := by
    rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  calc ‖∫ s in a..t, f s - F n s‖ ≤ ε / (b - a + 1) * |t - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ ≤ ε / (b - a + 1) * (b - a) :=
        mul_le_mul_of_nonneg_left hta (div_nonneg hε.le (by linarith))
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Uniform convergence of squared norms against a bounded limit. -/
theorem tendstoUniformlyOn_norm_sq {S : Set ℝ} {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {C : ℝ}
    (hF : TendstoUniformlyOn F f atTop S) (hf : ∀ x ∈ S, ‖f x‖ ≤ C) :
    TendstoUniformlyOn (fun n x => ‖F n x‖ ^ 2) (fun x => ‖f x‖ ^ 2) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  set η : ℝ := min 1 (ε / (2 * |C| + 2)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε / (2 * |C| + 2) := min_le_right _ _
  filter_upwards [hF η hη0] with n hn x hx
  have h1 : ‖f x - F n x‖ < η := by rw [← dist_eq_norm]; exact hn x hx
  have h2 := norm_sub_norm_le (f x) (F n x)
  have h3 := norm_sub_norm_le (F n x) (f x)
  rw [norm_sub_rev] at h3
  have hfx : ‖f x‖ ≤ |C| := (hf x hx).trans (le_abs_self C)
  rw [Real.dist_eq]
  have e : ‖f x‖ ^ 2 - ‖F n x‖ ^ 2 = (‖f x‖ - ‖F n x‖) * (‖f x‖ + ‖F n x‖) := by ring
  rw [e, abs_mul]
  have hd : |‖f x‖ - ‖F n x‖| < η := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have hs : |‖f x‖ + ‖F n x‖| ≤ 2 * |C| + 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  calc |‖f x‖ - ‖F n x‖| * |‖f x‖ + ‖F n x‖| ≤ η * (2 * |C| + 1) :=
        mul_le_mul hd.le hs (abs_nonneg _) hη0.le
    _ ≤ ε / (2 * |C| + 2) * (2 * |C| + 1) :=
        mul_le_mul_of_nonneg_right hη2 (by positivity)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

/-- The clamp `x ↦ max a (min b x)` onto `[a, b]` is `1`-Lipschitz. -/
theorem abs_clamp_sub_le (a b x y : ℝ) :
    |max a (min b x) - max a (min b y)| ≤ |x - y| := by
  have h1 := abs_max_sub_max_le_max a (min b x) a (min b y)
  have h2 := abs_min_sub_min_le_max b x b y
  simp only [sub_self, abs_zero] at h1 h2
  have h2' : |min b x - min b y| ≤ |x - y| := h2.trans (max_le (abs_nonneg _) le_rfl)
  exact h1.trans (max_le (abs_nonneg _) h2')

/-- Bound for the real limiting coefficient away from the critical layer. -/
theorem norm_realPotential_le {βs cs τ d : ℝ} (hd : 0 < d)
    (hτ : d ≤ |neutralOmega τ - cs|) :
    ‖(realPotential βs cs τ : ℂ)‖ ≤ βs ^ 2 + 8 / d := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold realPotential
  have hA := abs_gaussianRayleighCoefficient_le τ
  have hpos : 0 < |neutralOmega τ - cs| := lt_of_lt_of_le hd hτ
  have hfrac : |gaussianRayleighCoefficient τ / (neutralOmega τ - cs)| ≤ 8 / d := by
    rw [abs_div, div_le_div_iff₀ hpos hd]
    nlinarith [abs_nonneg (gaussianRayleighCoefficient τ)]
  calc |βs ^ 2 + gaussianRayleighCoefficient τ / (neutralOmega τ - cs)|
      ≤ |βs ^ 2| + |gaussianRayleighCoefficient τ / (neutralOmega τ - cs)| := abs_add_le _ _
    _ ≤ βs ^ 2 + 8 / d := by
        rw [abs_of_nonneg (sq_nonneg _)]
        linarith

/-- Exclusion of real limiting speeds (Lin 2003, Lemma 5.8) for the Gaussian on `[a, b]`
below a neutral wavenumber `α` (`neutralReal α a b = 0`), with `a < t_* < b`.
Step of B0034 (`paper/main.tex`, lines 1012–1021). -/
theorem noRealLimitSpeed_of_neutral {a b α : ℝ} (hcrit : neutralCriticalTime ∈ Ioo a b)
    (hα : neutralReal α a b = 0) : NoRealLimitSpeed a b α := by
  intro β c βs cs hβs hβ hc hcim hcz
  have hab : a < b := hcrit.1.trans hcrit.2
  obtain ⟨Bβ, hBβ⟩ := (hβ.pow 4).bddAbove_range
  have hβB : ∀ k, β k ^ 4 ≤ Bβ := fun k => hBβ ⟨k, rfl⟩
  choose u u' hu using fun k => exists_normalizedDirichlet hab (hcim k) (hcz k)
  set Kc : ℝ := Real.sqrt (2 * Bβ + 128) with hKc
  set M : ℝ := 2 * (Kc * Real.sqrt (b - a)) with hM
  have hKk : ∀ k, Real.sqrt (2 * β k ^ 4 + 128) ≤ Kc := fun k =>
    Real.sqrt_le_sqrt (by linarith [hβB k])
  -- clamp the derivatives to `[a, b]`
  set p : ℝ → ℝ := fun x => max a (min b x) with hp
  have hpmem : ∀ x, p x ∈ Icc a b := fun x =>
    ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
  have hpid : ∀ x ∈ Icc a b, p x = x := fun x hx => by
    simp only [hp, min_eq_right hx.2, max_eq_right hx.1]
  have hpc : Continuous p := continuous_const.max (continuous_const.min continuous_id)
  set G : ℕ → ℝ → ℂ := fun k x => u' k (p x) with hG
  have hGc : ∀ k, Continuous (G k) := fun k => (hu k).smooth'.continuous.comp hpc
  have hGsup : ∀ k x, ‖G k x‖ ≤ M := fun k x => by
    refine ((hu k).sup hab (hpmem x)).trans ?_
    rw [hM]
    gcongr
    exact hKk k
  have hGmod : ∀ k x y, ‖G k x - G k y‖ ≤ Kc * Real.sqrt |x - y| := fun k x y =>
    ((hu k).holder hab.le (hpmem y) (hpmem x)).trans
      (mul_le_mul (hKk k) (Real.sqrt_le_sqrt (abs_clamp_sub_le a b x y)) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
  -- Arzelà–Ascoli
  obtain ⟨v, φ, hvc, hφ, hunif, -, -⟩ :=
    exists_uniformOnCompacts_subsequence_of_sup_sqrt_bound G hGc M Kc hGsup hGmod
  have hv : TendstoUniformlyOn (fun n => u' (φ n)) v atTop (Icc a b) :=
    (hunif _ isCompact_Icc).congr (Eventually.of_forall fun n x hx => by
      simp only [hG, hpid x hx])
  -- the limit mode
  set U : ℝ → ℂ := fun t => ∫ s in a..t, v s with hU
  have hUd : ∀ t, HasDerivAt U (v t) t := fun t =>
    (hvc.integral_hasStrictDerivAt a t).hasDerivAt
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t => (hUd t).continuousAt
  have hUa : U a = 0 := by simp [hU]
  have huint : ∀ k t, u k t = ∫ s in a..t, u' k s := fun k t => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hu k).hasDeriv x)
      ((hu k).smooth'.continuous.intervalIntegrable _ _), (hu k).left, sub_zero]
  have huU : TendstoUniformlyOn (fun n => u (φ n)) U atTop (Icc a b) :=
    (tendstoUniformlyOn_primitive hab.le (fun n => (hu (φ n)).smooth'.continuous) hvc hv).congr
      (Eventually.of_forall fun n x _ => (huint (φ n) x).symm)
  have hUb : U b = 0 := by
    have h := huU.tendsto_at (right_mem_Icc.mpr hab.le)
    have e : (fun n => u (φ n) b) = fun _ => (0 : ℂ) := funext fun n => (hu (φ n)).right
    rw [e] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  obtain ⟨CU, hCU⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := U) (s := Icc a b)
    hUc.continuousOn
  have hmass : (∫ t in a..b, ‖U t‖ ^ 2) = 1 := by
    have hsq := tendstoUniformlyOn_norm_sq huU hCU
    rw [← uIcc_of_le hab.le] at hsq
    have huc : ∀ k, Continuous (u k) := fun k =>
      continuous_iff_continuousAt.mpr fun t => ((hu k).hasDeriv t).continuousAt
    have hlim := hsq.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      (Eventually.of_forall fun n =>
        (show Continuous fun t => ‖u (φ n) t‖ ^ 2 from ((huc (φ n)).norm.pow 2)).continuousOn)
    have e : (fun n => ∫ t in a..b, ‖u (φ n) t‖ ^ 2) = fun _ => (1 : ℝ) :=
      funext fun n => (hu (φ n)).mass
    rw [e] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  have hode : ∀ t ∈ Ioo a b, neutralOmega t ≠ cs →
      HasDerivAt v ((realPotential βs cs t : ℂ) * U t) t := by
    intro t ht hne
    set d0 : ℝ := |neutralOmega t - cs| with hd0
    have hd0pos : 0 < d0 := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hnear : ∀ᶠ τ in 𝓝 t, d0 / 2 < |neutralOmega τ - cs| := by
      have hcont : Continuous fun τ => |neutralOmega τ - cs| :=
        (continuous_neutralOmega.sub continuous_const).abs
      exact hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (hnear.and (Ioo_mem_nhds ht.1 ht.2))
    have hsS : ∀ τ ∈ Metric.ball t δ, d0 / 2 ≤ |neutralOmega τ - cs| := fun τ hτ =>
      (hδ' hτ).1.le
    have hsab : Metric.ball t δ ⊆ Icc a b := fun τ hτ => Ioo_subset_Icc_self (hδ' hτ).2
    have hd2 : 0 < d0 / 2 := by linarith
    have hV := tendstoUniformlyOn_rayleighPotential hd2 hsS (hβ.comp hφ.tendsto_atTop)
      (hc.comp hφ.tendsto_atTop)
    have hprod := tendstoUniformlyOn_mul_bounded hV (huU.mono hsab)
      (fun τ hτ => norm_realPotential_le hd2 (hsS τ hτ)) (fun τ hτ => hCU τ (hsab hτ))
    exact hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hprod
      (Eventually.of_forall fun n x _ => (hu (φ n)).hasDeriv' x)
      (fun x hx => hv.tendsto_at (hsab hx)) (Metric.mem_ball_self hδ)
  exact RealLimitMode.false ⟨hvc, hUd, hUa, hUb, hmass, hode⟩ hβs hcrit hα

end UnforcedLeray.ComplexODEB
