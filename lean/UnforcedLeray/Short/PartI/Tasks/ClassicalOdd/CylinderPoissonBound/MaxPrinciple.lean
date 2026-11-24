import UnforcedLeray.Short.PartI.Sub.T02_3_8
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Part I, task `PartI:T02/3/8/MaxPrinciple`: the maximum principle for `h'' = λ² h + g` (leaf O4)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the bounded
periodic pressure equation, whose `q`-modes `m_n` solve `m_n'' - λ_n² m_n = (Δq)_n`).

Target: `cylPoisMaxPrinciple : CylPoisMaxPrinciple` (`Short/PartI/Sub/T02_3_8.lean`).

Proof (real/imaginary route).  For a real `C²` function `u` with `u'' - λ² u = k`, `|k| ≤ G`, and
`u → 0` at infinity, a point where `u` attains a positive global maximum satisfies `u' = 0` and
`u'' ≤ 0`, hence `λ² u ≤ u'' + G ≤ G`.  Applying this to `-u` gives `|u| ≤ G/λ²`.  For complex `h`
apply the real statement to `Re h` and `Im h` (their second derivatives are the real and imaginary
parts of `h''`, and `|Re z| ≤ ‖z‖`), then use `‖z‖ ≤ |Re z| + |Im z|`.

All auxiliary names start with `cpMP`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- At a local maximum `x` of a `C⁰` real function whose second derivative exists, `u''(x) ≤ 0`.
Proof: if `u''(x) > 0`, the second-derivative test makes `x` a local minimum too, so `u` agrees with
its value at `x` on a neighbourhood, and then `u''(x) = 0`. -/
theorem cpMP_dd_nonpos {u : ℝ → ℝ} (hc : Continuous u) {x : ℝ} (hmax : IsLocalMax u x) :
    deriv (deriv u) x ≤ 0 := by
  by_contra hpos
  have hpos' : 0 < deriv (deriv u) x := not_le.1 hpos
  have hd : deriv u x = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin u x := isLocalMin_of_deriv_deriv_pos hpos' hd hc.continuousAt
  have h1 : ∀ᶠ y in 𝓝 x, u x ≤ u y := hmin
  have h2 : ∀ᶠ y in 𝓝 x, u y ≤ u x := hmax
  have hconst : u =ᶠ[𝓝 x] fun _ => u x := by
    filter_upwards [h1, h2] with y hy1 hy2
    exact le_antisymm hy2 hy1
  have h0 : deriv u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have h3 := hconst.deriv
    rw [deriv_const'] at h3
    exact h3
  have hdd : deriv (deriv u) x = 0 := by
    rw [h0.deriv_eq]
    exact deriv_const x 0
  linarith

/-- A continuous real function tending to `0` at infinity and positive at `η₁` attains a global
maximum, which is at least its value at `η₁`.  Proof: the set `{u < u η₁}` has compact complement;
take the maximum of `u` on that compact set together with `η₁`. -/
theorem cpMP_exists_max {u : ℝ → ℝ} (hc : Continuous u) (hlim : Tendsto u (cocompact ℝ) (𝓝 0))
    {η₁ : ℝ} (hpos : 0 < u η₁) : ∃ η₀, IsMaxOn u univ η₀ ∧ u η₁ ≤ u η₀ := by
  have hev : ∀ᶠ η in cocompact ℝ, u η < u η₁ := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  have hη₁S : η₁ ∈ K ∪ {η₁} := Set.mem_union_right _ (Set.mem_singleton η₁)
  have hS : IsCompact (K ∪ {η₁}) := hK.union isCompact_singleton
  obtain ⟨η₀, _, hmax⟩ := hS.exists_isMaxOn ⟨η₁, hη₁S⟩ hc.continuousOn
  have hmaxS : ∀ x ∈ K ∪ {η₁}, u x ≤ u η₀ := fun x hx => isMaxOn_iff.1 hmax x hx
  refine ⟨η₀, isMaxOn_iff.2 fun η _ => ?_, hmaxS η₁ hη₁S⟩
  by_cases hηK : η ∈ K
  · exact hmaxS η (Set.mem_union_left _ hηK)
  · have hlt : u η < u η₁ := hKs hηK
    exact le_trans hlt.le (hmaxS η₁ hη₁S)

/-- Real maximum principle, upper half: if `u` is `C²`, `|u'' - λ² u| ≤ G` with `λ > 0`, and
`u → 0` at infinity, then `u ≤ G/λ²`. -/
theorem cpMP_real_upper {u : ℝ → ℝ} {lam G : ℝ} (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) (η₁ : ℝ) : u η₁ ≤ G / lam ^ 2 := by
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG 0)
  have hdiv : 0 ≤ G / lam ^ 2 := div_nonneg hG0 (sq_nonneg _)
  by_cases hpos : 0 < u η₁
  · obtain ⟨η₀, hmax, hle⟩ := cpMP_exists_max hu.continuous hlim hpos
    have hloc : IsLocalMax u η₀ := hmax.isLocalMax Filter.univ_mem
    have h2 : deriv (deriv u) η₀ ≤ 0 := cpMP_dd_nonpos hu.continuous hloc
    have h1 : -G ≤ deriv (deriv u) η₀ - lam ^ 2 * u η₀ := (abs_le.1 (hG η₀)).1
    have hkey : u η₀ * lam ^ 2 ≤ G := by
      linarith [mul_comm (u η₀) (lam ^ 2)]
    have hu0 : u η₀ ≤ G / lam ^ 2 := by
      rw [le_div_iff₀ (pow_pos hlam 2)]
      exact hkey
    exact le_trans hle hu0
  · exact le_trans (not_lt.1 hpos) hdiv

/-- Real maximum principle, two-sided form: `|u| ≤ G/λ²`.  The lower bound is the upper bound for
`-u`, whose second derivative is the negative of that of `u`. -/
theorem cpMP_real_abs {u : ℝ → ℝ} {lam G : ℝ} (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) (η : ℝ) : |u η| ≤ G / lam ^ 2 := by
  have hdd : deriv (deriv (-u)) = fun x => -deriv (deriv u) x := by
    rw [deriv.neg']
    exact (deriv.neg' : deriv (-deriv u) = fun x => -deriv (deriv u) x)
  have hnegG : ∀ x, |deriv (deriv (-u)) x - lam ^ 2 * (-u) x| ≤ G := by
    intro x
    rw [hdd]
    show |-deriv (deriv u) x - lam ^ 2 * (-u x)| ≤ G
    have e : -deriv (deriv u) x - lam ^ 2 * (-u x)
        = -(deriv (deriv u) x - lam ^ 2 * u x) := by ring
    rw [e, abs_neg]
    exact hG x
  have hneglim : Tendsto (-u) (cocompact ℝ) (𝓝 0) := by
    have h4 := hlim.neg
    rw [neg_zero] at h4
    exact h4
  have hup : -u η ≤ G / lam ^ 2 := cpMP_real_upper (u := -u) hu.neg hlam hnegG hneglim η
  have hup' : u η ≤ G / lam ^ 2 := cpMP_real_upper hu hlam hG hlim η
  rw [abs_le]
  exact ⟨by linarith, hup'⟩

/-- The real part of a differentiable complex function has the real part of its derivative. -/
theorem cpMP_hasDerivAt_re {h : ℝ → ℂ} {x : ℝ} {d : ℂ} (hd : HasDerivAt h d x) :
    HasDerivAt (fun y => (h y).re) d.re x := by
  have h1 : HasDerivAt (fun y => Complex.reCLM (h y)) (Complex.reCLM d) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Complex.reCLM_apply] using h1

/-- The imaginary part of a differentiable complex function has the imaginary part of its
derivative. -/
theorem cpMP_hasDerivAt_im {h : ℝ → ℂ} {x : ℝ} {d : ℂ} (hd : HasDerivAt h d x) :
    HasDerivAt (fun y => (h y).im) d.im x := by
  have h1 : HasDerivAt (fun y => Complex.imCLM (h y)) (Complex.imCLM d) x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Complex.imCLM_apply] using h1

/-- **Leaf O4** (maximum principle for `h'' = λ² h + g` with `h → 0`): if `h : ℝ → ℂ` is `C²`,
`λ > 0`, `‖h'' - λ² h‖ ≤ G` and `h → 0` at infinity, then `‖h‖ ≤ 2G/λ²`.  Proof: real and imaginary
parts satisfy the real two-sided bound `|·| ≤ G/λ²`, and `‖z‖ ≤ |Re z| + |Im z|`. -/
theorem cylPoisMaxPrinciple : CylPoisMaxPrinciple := by
  unfold CylPoisMaxPrinciple
  intro h lam G hh hlam hG hlim η
  have hh1 : ContDiff ℝ (1 + 1) h := hh
  have hdiff : Differentiable ℝ h := hh1.differentiable (by norm_num)
  have hdh : Differentiable ℝ (deriv h) := hh1.deriv'.differentiable (by norm_num)
  -- derivatives of the real part
  have hre1 : deriv (fun z => (h z).re) = fun y => (deriv h y).re := by
    funext y
    exact (cpMP_hasDerivAt_re (hdiff y).hasDerivAt).deriv
  have hre2 : deriv (deriv (fun z => (h z).re)) = fun y => (deriv (deriv h) y).re := by
    rw [hre1]
    funext y
    exact (cpMP_hasDerivAt_re (hdh y).hasDerivAt).deriv
  -- derivatives of the imaginary part
  have him1 : deriv (fun z => (h z).im) = fun y => (deriv h y).im := by
    funext y
    exact (cpMP_hasDerivAt_im (hdiff y).hasDerivAt).deriv
  have him2 : deriv (deriv (fun z => (h z).im)) = fun y => (deriv (deriv h) y).im := by
    rw [him1]
    funext y
    exact (cpMP_hasDerivAt_im (hdh y).hasDerivAt).deriv
  -- the real-part hypothesis
  have hreG : ∀ x, |deriv (deriv (fun z => (h z).re)) x - lam ^ 2 * (fun z => (h z).re) x| ≤ G := by
    intro x
    rw [hre2]
    show |(deriv (deriv h) x).re - lam ^ 2 * (h x).re| ≤ G
    calc |(deriv (deriv h) x).re - lam ^ 2 * (h x).re|
        = |(deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x).re| := by
          rw [Complex.sub_re, Complex.re_ofReal_mul]
      _ ≤ ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := Complex.abs_re_le_norm _
      _ ≤ G := hG x
  -- the imaginary-part hypothesis
  have himG : ∀ x, |deriv (deriv (fun z => (h z).im)) x - lam ^ 2 * (fun z => (h z).im) x| ≤ G := by
    intro x
    rw [him2]
    show |(deriv (deriv h) x).im - lam ^ 2 * (h x).im| ≤ G
    calc |(deriv (deriv h) x).im - lam ^ 2 * (h x).im|
        = |(deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x).im| := by
          rw [Complex.sub_im, Complex.im_ofReal_mul]
      _ ≤ ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := Complex.abs_im_le_norm _
      _ ≤ G := hG x
  -- decay of the real and imaginary parts
  have hreLim : Tendsto (fun z => (h z).re) (cocompact ℝ) (𝓝 0) := by
    have h0 : Tendsto (fun z => (h z).re) (cocompact ℝ) (𝓝 ((0 : ℂ).re)) :=
      (Complex.continuous_re.tendsto (0 : ℂ)).comp hlim
    simpa using h0
  have himLim : Tendsto (fun z => (h z).im) (cocompact ℝ) (𝓝 0) := by
    have h0 : Tendsto (fun z => (h z).im) (cocompact ℝ) (𝓝 ((0 : ℂ).im)) :=
      (Complex.continuous_im.tendsto (0 : ℂ)).comp hlim
    simpa using h0
  -- smoothness of the real and imaginary parts
  have hcre : ContDiff ℝ 2 (fun z => (h z).re) := Complex.reCLM.contDiff.comp hh
  have hcim : ContDiff ℝ 2 (fun z => (h z).im) := Complex.imCLM.contDiff.comp hh
  -- real bounds and the complex conclusion
  have hu_re := cpMP_real_abs hcre hlam hreG hreLim η
  have hu_im := cpMP_real_abs hcim hlam himG himLim η
  calc ‖h η‖ ≤ |(h η).re| + |(h η).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ G / lam ^ 2 + G / lam ^ 2 := add_le_add hu_re hu_im
    _ = 2 * G / lam ^ 2 := by ring

end UnforcedLeray.Short.PartI
