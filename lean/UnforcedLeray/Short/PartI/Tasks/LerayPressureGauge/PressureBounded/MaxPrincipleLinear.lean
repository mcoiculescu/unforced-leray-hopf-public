import UnforcedLeray.Short.PartI.Sub.T02_2_3
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Part I, task `PartI:T02/2/3/MaxPrincipleLinear`: Phragmen-Lindelof maximum principle with linear growth

Source of record: `the November 2 reference manuscript`, lines 276-288 (the bounded
periodic pressure equation, whose `q`-modes `m_n` solve `m_n'' - lambda_n^2 m_n = (Delta q)_n`) and
line 447 (the decaying pressure gauge).

Target: `pbMaxPrincipleLinear : PbMaxPrincipleLinear` (`Sub/T02_2_3.lean`).  The decaying version is
`cylPoisMaxPrinciple` (`Tasks/ClassicalOdd/CylinderPoissonBound/MaxPrinciple.lean`); here decay is
replaced by linear growth, and the auxiliary barrier is a parabola instead of a cosh.

## Mathematics

Real statement (`pbPL_real_upper`): if `u : R -> R` is `C^2`, `|u'' - lam^2 u| <= G` and
`|u eta| <= C (1 + |eta|)`, then `u eta <= G / lam^2`.

For `eps > 0` put `w(eta) = u(eta) - G/lam^2 - eps (2/lam^2 + eta^2)`.  Then `w'' = u'' - 2 eps`.
Since `w` is continuous and `w(eta) < 0` once `|eta| >= R` (linear against quadratic growth), a
positive value `w(eta1)` is dominated by a global maximum `w(eta2)` of `w` on a compact interval,
and `w(eta2) > 0`.  At `eta2`, `w'' <= 0` gives `u''(eta2) <= 2 eps`; with `u'' >= lam^2 u - G`
this gives `u(eta2) <= G/lam^2 + 2 eps/lam^2`, so `w(eta2) <= 0`, a contradiction.  Hence
`u eta <= G/lam^2 + eps (2/lam^2 + eta^2)` for every `eps > 0`, and letting `eps -> 0` gives the claim.
Applying this to `-u` gives `|u| <= G/lam^2`.  For complex `h` apply the real statement to `Re h` and
`Im h` (`|Re z| <= ||z||`) and use `||z|| <= |Re z| + |Im z|`.

All auxiliary names start with `pbPL`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- At a local maximum `x` of a continuous real function whose second derivative exists,
`u''(x) <= 0`.  (Same argument as `cpMP_dd_nonpos` of the decaying file.) -/
theorem pbPL_dd_nonpos {u : ℝ → ℝ} (hc : Continuous u) {x : ℝ} (hmax : IsLocalMax u x) :
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

/-- Real upper bound with a parabolic barrier: if `u` is `C^2`, `|u'' - lam^2 u| <= G`, `lam > 0` and
`u` grows at most linearly, then `u eta1 <= G/lam^2 + eps (2/lam^2 + eta1^2)` for every `eps > 0`.

Proof: suppose `w(eta1) > 0` for `w(eta) = u eta - (G/lam^2 + eps (2/lam^2 + eta^2))`.  `w` is
continuous and negative for `|eta| >= R`, `R = 2 + 2M/eps`, `M = |C| + |G/lam^2|`; so its maximum on
`[-R, R]` is a global maximum `eta2` with `w(eta2) > 0`.  There `w''(eta2) <= 0`, i.e.
`u''(eta2) <= 2 eps`, and `u'' >= lam^2 u - G` gives `u(eta2) <= G/lam^2 + 2 eps / lam^2`, contradicting
`w(eta2) > 0`. -/
theorem pbPL_real_eps {u : ℝ → ℝ} {lam G C : ℝ} (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hC : ∀ η, |u η| ≤ C * (1 + |η|)) {ε : ℝ} (hε : 0 < ε) (η₁ : ℝ) :
    u η₁ ≤ G / lam ^ 2 + ε * (2 / lam ^ 2 + η₁ ^ 2) := by
  have hl2 : 0 < lam ^ 2 := pow_pos hlam 2
  have hεne : ε ≠ 0 := hε.ne'
  have hu1 : ContDiff ℝ (1 + 1) u := hu
  have hdiff : Differentiable ℝ u := hu1.differentiable (by norm_num)
  have hdu : Differentiable ℝ (deriv u) := hu1.deriv'.differentiable (by norm_num)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |C| + |G / lam ^ 2| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hcM : -(G / lam ^ 2) ≤ M := by
    rw [hM]; linarith [neg_le_abs (G / lam ^ 2), abs_nonneg C]
  have hub : ∀ η, u η ≤ M * (1 + |η|) := by
    intro η
    have h1 : u η ≤ |u η| := le_abs_self _
    have h2 : C * (1 + |η|) ≤ |C| * (1 + |η|) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h3 : |C| * (1 + |η|) ≤ M * (1 + |η|) :=
      mul_le_mul_of_nonneg_right (by rw [hM]; linarith [abs_nonneg (G / lam ^ 2)]) (by positivity)
    linarith [hC η]
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, w = fun η => u η - (G / lam ^ 2 + ε * (2 / lam ^ 2 + η ^ 2)) :=
    ⟨_, rfl⟩
  have hw_val : ∀ η, w η = u η - (G / lam ^ 2 + ε * (2 / lam ^ 2 + η ^ 2)) := fun η => by
    rw [hw]
  have hw_deriv : ∀ x, HasDerivAt w (deriv u x - ε * (2 * x)) x := by
    intro x
    rw [hw]
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hq : HasDerivAt (fun y : ℝ => G / lam ^ 2 + ε * (2 / lam ^ 2 + y ^ 2)) (ε * (2 * x)) x :=
      ((hp.const_add (2 / lam ^ 2)).const_mul ε).const_add (G / lam ^ 2)
    exact (hdiff x).hasDerivAt.sub hq
  have hw_cont : Continuous w :=
    continuous_iff_continuousAt.2 fun x => (hw_deriv x).continuousAt
  have hdw : deriv w = fun y => deriv u y - ε * (2 * y) :=
    funext fun y => (hw_deriv y).deriv
  have hdd_w : ∀ x, deriv (deriv w) x = deriv (deriv u) x - ε * 2 := by
    intro x
    rw [hdw]
    have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
    have hl : HasDerivAt (fun y : ℝ => ε * (2 * y)) (ε * 2) x := h2x.const_mul ε
    exact ((hdu x).hasDerivAt.sub hl).deriv
  -- the radius outside of which `w < 0`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 + 2 * M / ε := ⟨_, rfl⟩
  have hR2 : 2 ≤ R := by
    have : 0 ≤ 2 * M / ε := div_nonneg (by linarith) hε.le
    rw [hR]; linarith
  have hbound : ∀ η : ℝ, R ≤ |η| → w η < 0 := by
    intro η hη
    have ht2 : 2 ≤ |η| := le_trans hR2 hη
    have ht0 : 0 ≤ |η| := abs_nonneg η
    have h3 : ε * (2 * M / ε) = 2 * M := by field_simp
    have hεt : 2 * ε + 2 * M ≤ ε * |η| := by
      have h1 : ε * R ≤ ε * |η| := mul_le_mul_of_nonneg_left hη hε.le
      have h2 : ε * R = 2 * ε + 2 * M := by rw [hR, mul_add, h3]; ring
      linarith
    have hMt : M * 2 ≤ M * |η| := mul_le_mul_of_nonneg_left ht2 hM0
    have hkey : (2 * ε + 2 * M) * |η| ≤ ε * |η| ^ 2 := by
      have := mul_le_mul_of_nonneg_right hεt ht0
      nlinarith
    have hsq : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
    have hexp : ε * (2 / lam ^ 2 + η ^ 2) = ε * (2 / lam ^ 2) + ε * |η| ^ 2 := by
      rw [hsq]; ring
    have hpos : 0 ≤ ε * (2 / lam ^ 2) := by positivity
    have hub' := hub η
    rw [hw_val, hexp]
    linarith
  by_contra hcon
  push_neg at hcon
  have hw_at : 0 < w η₁ := by
    rw [hw_val η₁]
    linarith
  have hw1 : |η₁| < R := by
    by_contra hlt
    push_neg at hlt
    linarith [hbound η₁ hlt]
  have hη₁K : η₁ ∈ Icc (-R) R := Set.mem_Icc.2 (abs_le.1 hw1.le)
  obtain ⟨η₂, hη₂K, hmax⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_isMaxOn
    ⟨η₁, hη₁K⟩ hw_cont.continuousOn
  have hw_le : w η₁ ≤ w η₂ := isMaxOn_iff.1 hmax η₁ hη₁K
  have hw2 : 0 < w η₂ := lt_of_lt_of_le hw_at hw_le
  have hglob : IsMaxOn w univ η₂ := by
    refine isMaxOn_iff.2 fun η _ => ?_
    by_cases hηK : η ∈ Icc (-R) R
    · exact isMaxOn_iff.1 hmax η hηK
    · have hRlt : R ≤ |η| := by
        by_contra hlt
        push_neg at hlt
        exact hηK (Set.mem_Icc.2 (abs_le.1 hlt.le))
      linarith [hbound η hRlt]
  have hloc : IsLocalMax w η₂ := hglob.isLocalMax Filter.univ_mem
  have hdd := pbPL_dd_nonpos hw_cont hloc
  rw [hdd_w η₂] at hdd
  have hGlow := (abs_le.1 (hG η₂)).1
  have h1 : lam ^ 2 * u η₂ ≤ G + 2 * ε := by linarith
  have h3 : u η₂ ≤ (G + 2 * ε) / lam ^ 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  have h4 : (G + 2 * ε) / lam ^ 2 = G / lam ^ 2 + ε * (2 / lam ^ 2) := by ring
  have hexp2 : ε * (2 / lam ^ 2 + η₂ ^ 2) = ε * (2 / lam ^ 2) + ε * η₂ ^ 2 := by ring
  have hεη : 0 ≤ ε * η₂ ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  rw [hw_val η₂] at hw2
  linarith

/-- Real upper bound: `u eta1 <= G/lam^2` (the `eps -> 0` limit of `pbPL_real_eps`). -/
theorem pbPL_real_upper {u : ℝ → ℝ} {lam G C : ℝ} (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hC : ∀ η, |u η| ≤ C * (1 + |η|)) (η₁ : ℝ) : u η₁ ≤ G / lam ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hδ : 0 < u η₁ - G / lam ^ 2 := by linarith
  have hD : 0 < 2 * (2 / lam ^ 2 + η₁ ^ 2 + 1) := by positivity
  have hε : 0 < (u η₁ - G / lam ^ 2) / (2 * (2 / lam ^ 2 + η₁ ^ 2 + 1)) := div_pos hδ hD
  have hkey := pbPL_real_eps hu hlam hG hC hε η₁
  have hmul : (u η₁ - G / lam ^ 2) / (2 * (2 / lam ^ 2 + η₁ ^ 2 + 1)) * (2 / lam ^ 2 + η₁ ^ 2)
      ≤ (u η₁ - G / lam ^ 2) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hD (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hδ]
  linarith

/-- Real two-sided bound: `|u eta| <= G/lam^2` for `u` as in `pbPL_real_upper`. -/
theorem pbPL_real_abs {u : ℝ → ℝ} {lam G C : ℝ} (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hC : ∀ η, |u η| ≤ C * (1 + |η|)) (η : ℝ) : |u η| ≤ G / lam ^ 2 := by
  have hu1 : ContDiff ℝ (1 + 1) u := hu
  have hdiff : Differentiable ℝ u := hu1.differentiable (by norm_num)
  have hdu : Differentiable ℝ (deriv u) := hu1.deriv'.differentiable (by norm_num)
  have e1 : deriv (fun y => -u y) = fun y => -deriv u y :=
    funext fun y => ((hdiff y).hasDerivAt.neg).deriv
  have e2 : ∀ x, deriv (deriv (fun y => -u y)) x = -deriv (deriv u) x := by
    intro x
    rw [e1]
    exact ((hdu x).hasDerivAt.neg).deriv
  have hneg : ContDiff ℝ 2 (fun y => -u y) := hu.neg
  have hG' : ∀ x, |deriv (deriv (fun y => -u y)) x - lam ^ 2 * (fun y => -u y) x| ≤ G := by
    intro x
    rw [e2 x]
    have e : -deriv (deriv u) x - lam ^ 2 * (-u x) = -(deriv (deriv u) x - lam ^ 2 * u x) := by
      ring
    show |-deriv (deriv u) x - lam ^ 2 * -u x| ≤ G
    rw [e, abs_neg]
    exact hG x
  have hC' : ∀ x, |(fun y => -u y) x| ≤ C * (1 + |x|) := by
    intro x
    show |-u x| ≤ C * (1 + |x|)
    rw [abs_neg]
    exact hC x
  have hup : -u η ≤ G / lam ^ 2 := pbPL_real_upper hneg hlam hG' hC' η
  have hup' : u η ≤ G / lam ^ 2 := pbPL_real_upper hu hlam hG hC η
  rw [abs_le]
  exact ⟨by linarith, hup'⟩

/-- The real part of a differentiable complex function has the real part of its derivative. -/
theorem pbPL_hasDerivAt_re {h : ℝ → ℂ} {x : ℝ} {d : ℂ} (hd : HasDerivAt h d x) :
    HasDerivAt (fun y => (h y).re) d.re x := by
  have h1 : HasDerivAt (fun y => Complex.reCLM (h y)) (Complex.reCLM d) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Complex.reCLM_apply] using h1

/-- The imaginary part of a differentiable complex function has the imaginary part of its
derivative. -/
theorem pbPL_hasDerivAt_im {h : ℝ → ℂ} {x : ℝ} {d : ℂ} (hd : HasDerivAt h d x) :
    HasDerivAt (fun y => (h y).im) d.im x := by
  have h1 : HasDerivAt (fun y => Complex.imCLM (h y)) (Complex.imCLM d) x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Complex.imCLM_apply] using h1

/-- **Leaf of `PbOscLinear`** (Phragmen-Lindelof maximum principle with linear growth): if
`h : R -> C` is `C^2`, `lam > 0`, `||h'' - lam^2 h|| <= G` and `h` grows at most linearly, then
`||h|| <= 2G/lam^2`.  Proof: real and imaginary parts satisfy the real two-sided bound
`|.| <= G/lam^2` (`pbPL_real_abs`), and `||z|| <= |Re z| + |Im z|`. -/
theorem pbMaxPrincipleLinear : PbMaxPrincipleLinear := by
  unfold PbMaxPrincipleLinear
  intro h lam G hh hlam hG hC η
  obtain ⟨C, hC⟩ := hC
  have hh1 : ContDiff ℝ (1 + 1) h := hh
  have hdiff : Differentiable ℝ h := hh1.differentiable (by norm_num)
  have hdh : Differentiable ℝ (deriv h) := hh1.deriv'.differentiable (by norm_num)
  -- derivatives of the real part
  have hre1 : deriv (fun z => (h z).re) = fun y => (deriv h y).re := by
    funext y
    exact (pbPL_hasDerivAt_re (hdiff y).hasDerivAt).deriv
  have hre2 : deriv (deriv (fun z => (h z).re)) = fun y => (deriv (deriv h) y).re := by
    rw [hre1]
    funext y
    exact (pbPL_hasDerivAt_re (hdh y).hasDerivAt).deriv
  -- derivatives of the imaginary part
  have him1 : deriv (fun z => (h z).im) = fun y => (deriv h y).im := by
    funext y
    exact (pbPL_hasDerivAt_im (hdiff y).hasDerivAt).deriv
  have him2 : deriv (deriv (fun z => (h z).im)) = fun y => (deriv (deriv h) y).im := by
    rw [him1]
    funext y
    exact (pbPL_hasDerivAt_im (hdh y).hasDerivAt).deriv
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
  -- smoothness and linear growth of the real and imaginary parts
  have hcre : ContDiff ℝ 2 (fun z => (h z).re) := Complex.reCLM.contDiff.comp hh
  have hcim : ContDiff ℝ 2 (fun z => (h z).im) := Complex.imCLM.contDiff.comp hh
  have hCre : ∀ x, |(fun z => (h z).re) x| ≤ C * (1 + |x|) :=
    fun x => le_trans (Complex.abs_re_le_norm _) (hC x)
  have hCim : ∀ x, |(fun z => (h z).im) x| ≤ C * (1 + |x|) :=
    fun x => le_trans (Complex.abs_im_le_norm _) (hC x)
  -- real bounds and the complex conclusion
  have hu_re := pbPL_real_abs hcre hlam hreG hCre η
  have hu_im := pbPL_real_abs hcim hlam himG hCim η
  calc ‖h η‖ ≤ |(h η).re| + |(h η).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ G / lam ^ 2 + G / lam ^ 2 := add_le_add hu_re hu_im
    _ = 2 * G / lam ^ 2 := by ring

end UnforcedLeray.Short.PartI
