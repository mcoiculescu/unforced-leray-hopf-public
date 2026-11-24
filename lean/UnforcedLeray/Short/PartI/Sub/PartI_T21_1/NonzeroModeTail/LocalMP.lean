import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Localized 1D maximum principle and cylinder oscillation bound for `PartI:T21/1/1`

Source of record: `the November 2 reference manuscript`, lines 499-503, 517-525.

This module proves:
1. `cpMP_real_local`: the compact-interval maximum principle on `[η₀ - R, η₀ + R]` for
   `u'' - λ² u = g` using the barrier
   `Φ(η) = G_far / λ² + B (e^{λ(η - (η₀ + R))} + e^{-λ(η - (η₀ - R))})`.
2. `cpMP_real_abs_of_bdd`: global bound `|u η| ≤ G_all / λ²` for any bounded `C²` function `u`
   on `ℝ` satisfying `|u'' - λ² u| ≤ G_all`, obtained from `cpMP_real_local` by letting `R → ∞`.
3. `cpMP_complex_local_of_bdd`: complex two-scale bound
   `‖h η₀‖ ≤ 2 * (G_far + 2 * G_all * exp(-λ R)) / λ²` for any bounded `C²` mode `h : ℝ → ℂ`.
4. `cylPoisOscPartLocalBound_of_modeBdd`: pointwise bound on `|q z - hmean c q z.2|` for a `C²`
   `c`-periodic function `q : Plane → ℝ` with global Laplacian bound `G_all` and local Laplacian
   bound `G_far` on `{w | |w.2 - z.2| ≤ R}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

namespace PartI_T21

/-- Barrier function on `[η₀ - R, η₀ + R]` for `u'' - λ² u = g`:
`Φ(η) = G / λ² + B * (exp(λ (η - (η₀ + R))) + exp(-λ (η - (η₀ - R))))`. -/
def localBarrier (lam G B η₀ R η : ℝ) : ℝ :=
  G / lam ^ 2 +
    B * (Real.exp (lam * (η - (η₀ + R))) + Real.exp (-lam * (η - (η₀ - R))))

theorem hasDerivAt_localBarrier (lam G B η₀ R η : ℝ) :
    HasDerivAt (localBarrier lam G B η₀ R)
      (B * (lam * Real.exp (lam * (η - (η₀ + R))) -
        lam * Real.exp (-lam * (η - (η₀ - R))))) η := by
  unfold localBarrier
  have h1 : HasDerivAt (fun x : ℝ => lam * (x - (η₀ + R))) (lam * 1) η :=
    ((hasDerivAt_id η).sub_const (η₀ + R)).const_mul lam
  have h2 : HasDerivAt (fun x : ℝ => -lam * (x - (η₀ - R))) (-lam * 1) η :=
    ((hasDerivAt_id η).sub_const (η₀ - R)).const_mul (-lam)
  have he1 : HasDerivAt (fun x : ℝ => Real.exp (lam * (x - (η₀ + R))))
      (Real.exp (lam * (η - (η₀ + R))) * (lam * 1)) η := h1.exp
  have he2 : HasDerivAt (fun x : ℝ => Real.exp (-lam * (x - (η₀ - R))))
      (Real.exp (-lam * (η - (η₀ - R))) * (-lam * 1)) η := h2.exp
  have hsum := (he1.add he2).const_mul B
  have h0 : HasDerivAt (fun _ : ℝ => G / lam ^ 2) 0 η := hasDerivAt_const η (G / lam ^ 2)
  have htot := h0.add hsum
  have heq : 0 + B * (Real.exp (lam * (η - (η₀ + R))) * (lam * 1) +
      Real.exp (-lam * (η - (η₀ - R))) * (-lam * 1)) =
      B * (lam * Real.exp (lam * (η - (η₀ + R))) -
        lam * Real.exp (-lam * (η - (η₀ - R)))) := by ring
  rwa [heq] at htot

theorem deriv_localBarrier (lam G B η₀ R : ℝ) :
    deriv (localBarrier lam G B η₀ R) = fun η =>
      B * (lam * Real.exp (lam * (η - (η₀ + R))) -
        lam * Real.exp (-lam * (η - (η₀ - R)))) :=
  funext fun η => (hasDerivAt_localBarrier lam G B η₀ R η).deriv

theorem hasDerivAt_deriv_localBarrier (lam G B η₀ R η : ℝ) :
    HasDerivAt (deriv (localBarrier lam G B η₀ R))
      (B * (lam ^ 2 * Real.exp (lam * (η - (η₀ + R))) +
        lam ^ 2 * Real.exp (-lam * (η - (η₀ - R))))) η := by
  rw [deriv_localBarrier]
  have h1 : HasDerivAt (fun x : ℝ => lam * (x - (η₀ + R))) (lam * 1) η :=
    ((hasDerivAt_id η).sub_const (η₀ + R)).const_mul lam
  have h2 : HasDerivAt (fun x : ℝ => -lam * (x - (η₀ - R))) (-lam * 1) η :=
    ((hasDerivAt_id η).sub_const (η₀ - R)).const_mul (-lam)
  have he1 : HasDerivAt (fun x : ℝ => lam * Real.exp (lam * (x - (η₀ + R))))
      (lam * (Real.exp (lam * (η - (η₀ + R))) * (lam * 1))) η := h1.exp.const_mul lam
  have he2 : HasDerivAt (fun x : ℝ => lam * Real.exp (-lam * (x - (η₀ - R))))
      (lam * (Real.exp (-lam * (η - (η₀ - R))) * (-lam * 1))) η := h2.exp.const_mul lam
  have hsub := (he1.sub he2).const_mul B
  have heq : B * (lam * (Real.exp (lam * (η - (η₀ + R))) * (lam * 1)) -
      lam * (Real.exp (-lam * (η - (η₀ - R))) * (-lam * 1))) =
      B * (lam ^ 2 * Real.exp (lam * (η - (η₀ + R))) +
        lam ^ 2 * Real.exp (-lam * (η - (η₀ - R)))) := by ring
  rwa [heq] at hsub

theorem deriv_deriv_localBarrier (lam G B η₀ R η : ℝ) :
    deriv (deriv (localBarrier lam G B η₀ R)) η =
      B * (lam ^ 2 * Real.exp (lam * (η - (η₀ + R))) +
        lam ^ 2 * Real.exp (-lam * (η - (η₀ - R)))) :=
  (hasDerivAt_deriv_localBarrier lam G B η₀ R η).deriv

theorem localBarrier_ode {lam : ℝ} (hlam : 0 < lam) (G B η₀ R η : ℝ) :
    deriv (deriv (localBarrier lam G B η₀ R)) η - lam ^ 2 * localBarrier lam G B η₀ R η = -G := by
  rw [deriv_deriv_localBarrier]
  unfold localBarrier
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam.ne'
  field_simp
  ring

theorem continuous_localBarrier (lam G B η₀ R : ℝ) :
    Continuous (localBarrier lam G B η₀ R) := by
  unfold localBarrier
  fun_prop

theorem localBarrier_center (lam G B η₀ R : ℝ) :
    localBarrier lam G B η₀ R η₀ = G / lam ^ 2 + 2 * B * Real.exp (-lam * R) := by
  unfold localBarrier
  have h1 : lam * (η₀ - (η₀ + R)) = -lam * R := by ring
  have h2 : -lam * (η₀ - (η₀ - R)) = -lam * R := by ring
  rw [h1, h2]
  ring

theorem le_localBarrier_left (lam : ℝ) {G B : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B)
    (η₀ R : ℝ) :
    B ≤ localBarrier lam G B η₀ R (η₀ - R) := by
  unfold localBarrier
  have h0 : -lam * (η₀ - R - (η₀ - R)) = 0 := by ring
  rw [h0, Real.exp_zero]
  have hdiv : 0 ≤ G / lam ^ 2 := div_nonneg hG (sq_nonneg lam)
  have hexp : 0 ≤ Real.exp (lam * (η₀ - R - (η₀ + R))) := (Real.exp_pos _).le
  nlinarith

theorem le_localBarrier_right (lam : ℝ) {G B : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B)
    (η₀ R : ℝ) :
    B ≤ localBarrier lam G B η₀ R (η₀ + R) := by
  unfold localBarrier
  have h0 : lam * (η₀ + R - (η₀ + R)) = 0 := by ring
  rw [h0, Real.exp_zero]
  have hdiv : 0 ≤ G / lam ^ 2 := div_nonneg hG (sq_nonneg lam)
  have hexp : 0 ≤ Real.exp (-lam * (η₀ + R - (η₀ - R))) := (Real.exp_pos _).le
  nlinarith

/-- Upper bound on `[η₀ - R, η₀ + R]` by comparing `u` with `localBarrier`. -/
theorem cpMP_real_local_upper {u : ℝ → ℝ} {lam G B η₀ R : ℝ}
    (hu : ContDiff ℝ 2 u) (hlam : 0 < lam) (hR : 0 ≤ R) (hG0 : 0 ≤ G) (hB0 : 0 ≤ B)
    (hleft : u (η₀ - R) ≤ B) (hright : u (η₀ + R) ≤ B)
    (hG : ∀ η ∈ Icc (η₀ - R) (η₀ + R), |deriv (deriv u) η - lam ^ 2 * u η| ≤ G) :
    u η₀ ≤ G / lam ^ 2 + 2 * B * Real.exp (-lam * R) := by
  let Φ := localBarrier lam G B η₀ R
  let w : ℝ → ℝ := fun η => u η - Φ η
  have hw_cont : Continuous w := hu.continuous.sub (continuous_localBarrier lam G B η₀ R)
  have hη₀_mem : η₀ ∈ Icc (η₀ - R) (η₀ + R) := ⟨by linarith, by linarith⟩
  obtain ⟨η₁, hη₁_mem, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨η₀, hη₀_mem⟩ hw_cont.continuousOn
  have hw_le_zero : w η₁ ≤ 0 := by
    rcases eq_or_lt_of_le hη₁_mem.1 with h_eq_l | h_gt_l
    · rw [← h_eq_l]
      dsimp [w, Φ]
      linarith [le_localBarrier_left lam hG0 hB0 η₀ R]
    · rcases eq_or_lt_of_le hη₁_mem.2 with h_eq_r | h_lt_r
      · rw [h_eq_r]
        dsimp [w, Φ]
        linarith [le_localBarrier_right lam hG0 hB0 η₀ R]
      · have hloc : IsLocalMax w η₁ :=
          hmax.isLocalMax (Icc_mem_nhds h_gt_l h_lt_r)
        have hdd_nonpos : deriv (deriv w) η₁ ≤ 0 := cpMP_dd_nonpos hw_cont hloc
        have hu1 : ContDiff ℝ (1 + 1) u := hu
        have hdu : Differentiable ℝ u := hu1.differentiable (by norm_num)
        have hddu : Differentiable ℝ (deriv u) := hu1.deriv'.differentiable (by norm_num)
        have hdΦ : Differentiable ℝ Φ :=
          fun x => (hasDerivAt_localBarrier lam G B η₀ R x).differentiableAt
        have hddΦ : Differentiable ℝ (deriv Φ) :=
          fun x => (hasDerivAt_deriv_localBarrier lam G B η₀ R x).differentiableAt
        have hdw : deriv w = fun x => deriv u x - deriv Φ x := by
          funext x
          exact deriv_sub (hdu x) (hdΦ x)
        have hddw : deriv (deriv w) η₁ = deriv (deriv u) η₁ - deriv (deriv Φ) η₁ := by
          rw [hdw]
          exact deriv_sub (hddu η₁) (hddΦ η₁)
        have h_ode_u : -G ≤ deriv (deriv u) η₁ - lam ^ 2 * u η₁ :=
          (abs_le.1 (hG η₁ hη₁_mem)).1
        have h_ode_Φ : deriv (deriv Φ) η₁ - lam ^ 2 * Φ η₁ = -G :=
          localBarrier_ode hlam G B η₀ R η₁
        have h_ineq : lam ^ 2 * w η₁ ≤ deriv (deriv w) η₁ := by
          dsimp [w]
          linarith
        have h_lam2_pos : 0 < lam ^ 2 := sq_pos_of_pos hlam
        nlinarith
  have hw0 : w η₀ ≤ w η₁ := isMaxOn_iff.1 hmax η₀ hη₀_mem
  have hu0 : u η₀ ≤ Φ η₀ := by
    dsimp [w] at hw0 hw_le_zero
    linarith
  dsimp [Φ] at hu0
  rwa [localBarrier_center] at hu0

/-- Two-sided localized maximum principle on `[η₀ - R, η₀ + R]`. -/
theorem cpMP_real_local {u : ℝ → ℝ} {lam G B η₀ R : ℝ}
    (hu : ContDiff ℝ 2 u) (hlam : 0 < lam) (hR : 0 ≤ R) (hG0 : 0 ≤ G) (hB0 : 0 ≤ B)
    (hleft : |u (η₀ - R)| ≤ B) (hright : |u (η₀ + R)| ≤ B)
    (hG : ∀ η ∈ Icc (η₀ - R) (η₀ + R), |deriv (deriv u) η - lam ^ 2 * u η| ≤ G) :
    |u η₀| ≤ G / lam ^ 2 + 2 * B * Real.exp (-lam * R) := by
  have hup := cpMP_real_local_upper hu hlam hR hG0 hB0
    ((le_abs_self _).trans hleft) ((le_abs_self _).trans hright) hG
  have hdd : deriv (deriv (-u)) = fun x => -deriv (deriv u) x := by
    rw [deriv.neg']
    exact (deriv.neg' : deriv (-deriv u) = fun x => -deriv (deriv u) x)
  have hnegG : ∀ η ∈ Icc (η₀ - R) (η₀ + R),
      |deriv (deriv (-u)) η - lam ^ 2 * (-u) η| ≤ G := by
    intro η hη
    rw [hdd]
    show |-deriv (deriv u) η - lam ^ 2 * (-u η)| ≤ G
    have e : -deriv (deriv u) η - lam ^ 2 * (-u η) =
        -(deriv (deriv u) η - lam ^ 2 * u η) := by ring
    rw [e, abs_neg]
    exact hG η hη
  have hlow := cpMP_real_local_upper (u := -u) hu.neg hlam hR hG0 hB0
    ((neg_le_abs _).trans hleft) ((neg_le_abs _).trans hright) hnegG
  rw [abs_le]
  exact ⟨by dsimp at hlow; linarith, hup⟩

/-- Global real maximum principle for a bounded `C²` function `u` on `ℝ` (without requiring
`u → 0` at infinity), obtained by letting `R → +∞` in `cpMP_real_local`. -/
theorem cpMP_real_abs_of_bdd {u : ℝ → ℝ} {lam G M : ℝ}
    (hu : ContDiff ℝ 2 u) (hlam : 0 < lam)
    (hG : ∀ η, |deriv (deriv u) η - lam ^ 2 * u η| ≤ G)
    (hM : ∀ η, |u η| ≤ M) (η₀ : ℝ) :
    |u η₀| ≤ G / lam ^ 2 := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG η₀)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM η₀)
  have hbound : ∀ᶠ R : ℝ in atTop,
      |u η₀| ≤ G / lam ^ 2 + 2 * M * Real.exp (-lam * R) := by
    filter_upwards [ Filter.eventually_ge_atTop (0 : ℝ) ] with R hR
    exact cpMP_real_local hu hlam hR hG0 hM0 (hM (η₀ - R)) (hM (η₀ + R))
      (fun η _ => hG η)
  have hlim : Tendsto (fun R : ℝ => G / lam ^ 2 + 2 * M * Real.exp (-lam * R))
      atTop (𝓝 (G / lam ^ 2)) := by
    have hbot : Tendsto (fun R : ℝ => -lam * R) atTop atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hlam)
    have hexp : Tendsto (fun R : ℝ => Real.exp (-lam * R)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hbot
    simpa using (tendsto_const_nhds.add (hexp.const_mul (2 * M)))
  exact ge_of_tendsto hlim hbound

/-- Complex two-scale localized maximum principle for a bounded `C²` mode `h : ℝ → ℂ`. -/
theorem cpMP_complex_local_of_bdd {h : ℝ → ℂ} {lam G_all G_far η₀ R : ℝ}
    (hh : ContDiff ℝ 2 h) (hlam : 0 < lam) (hR : 0 ≤ R)
    (hGall0 : 0 ≤ G_all) (hGfar0 : 0 ≤ G_far)
    (hAll : ∀ η, ‖deriv (deriv h) η - ((lam ^ 2 : ℝ) : ℂ) * h η‖ ≤ G_all)
    (hFar : ∀ η ∈ Icc (η₀ - R) (η₀ + R),
      ‖deriv (deriv h) η - ((lam ^ 2 : ℝ) : ℂ) * h η‖ ≤ G_far)
    (hBdd : ∃ M : ℝ, ∀ η, ‖h η‖ ≤ M) :
    ‖h η₀‖ ≤ 2 * (G_far + 2 * G_all * Real.exp (-lam * R)) / lam ^ 2 := by
  obtain ⟨M, hM⟩ := hBdd
  have hh1 : ContDiff ℝ (1 + 1) h := hh
  have hdiff : Differentiable ℝ h := hh1.differentiable (by norm_num)
  have hdh : Differentiable ℝ (deriv h) := hh1.deriv'.differentiable (by norm_num)
  have hre1 : deriv (fun z => (h z).re) = fun y => (deriv h y).re :=
    funext fun y => (cpMP_hasDerivAt_re (hdiff y).hasDerivAt).deriv
  have hre2 : deriv (deriv (fun z => (h z).re)) = fun y => (deriv (deriv h) y).re := by
    rw [hre1]; funext y; exact (cpMP_hasDerivAt_re (hdh y).hasDerivAt).deriv
  have him1 : deriv (fun z => (h z).im) = fun y => (deriv h y).im :=
    funext fun y => (cpMP_hasDerivAt_im (hdiff y).hasDerivAt).deriv
  have him2 : deriv (deriv (fun z => (h z).im)) = fun y => (deriv (deriv h) y).im := by
    rw [him1]; funext y; exact (cpMP_hasDerivAt_im (hdh y).hasDerivAt).deriv
  have hre_ode : ∀ x, |deriv (deriv (fun z => (h z).re)) x - lam ^ 2 * (h x).re| ≤
      ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := by
    intro x
    rw [hre2]
    calc |(deriv (deriv h) x).re - lam ^ 2 * (h x).re|
        = |(deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x).re| := by
          rw [Complex.sub_re, Complex.re_ofReal_mul]
      _ ≤ ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := Complex.abs_re_le_norm _
  have him_ode : ∀ x, |deriv (deriv (fun z => (h z).im)) x - lam ^ 2 * (h x).im| ≤
      ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := by
    intro x
    rw [him2]
    calc |(deriv (deriv h) x).im - lam ^ 2 * (h x).im|
        = |(deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x).im| := by
          rw [Complex.sub_im, Complex.im_ofReal_mul]
      _ ≤ ‖deriv (deriv h) x - ((lam ^ 2 : ℝ) : ℂ) * h x‖ := Complex.abs_im_le_norm _
  have hcre : ContDiff ℝ 2 (fun z => (h z).re) := Complex.reCLM.contDiff.comp hh
  have hcim : ContDiff ℝ 2 (fun z => (h z).im) := Complex.imCLM.contDiff.comp hh
  have hre_all : ∀ η, |(h η).re| ≤ G_all / lam ^ 2 :=
    cpMP_real_abs_of_bdd hcre hlam (fun x => (hre_ode x).trans (hAll x))
      (fun x => (Complex.abs_re_le_norm (h x)).trans (hM x))
  have him_all : ∀ η, |(h η).im| ≤ G_all / lam ^ 2 :=
    cpMP_real_abs_of_bdd hcim hlam (fun x => (him_ode x).trans (hAll x))
      (fun x => (Complex.abs_im_le_norm (h x)).trans (hM x))
  have hB0 : 0 ≤ G_all / lam ^ 2 := div_nonneg hGall0 (sq_nonneg lam)
  have hre_loc := cpMP_real_local hcre hlam hR hGfar0 hB0
    (hre_all (η₀ - R)) (hre_all (η₀ + R))
    (fun η hη => (hre_ode η).trans (hFar η hη))
  have him_loc := cpMP_real_local hcim hlam hR hGfar0 hB0
    (him_all (η₀ - R)) (him_all (η₀ + R))
    (fun η hη => (him_ode η).trans (hFar η hη))
  calc ‖h η₀‖ ≤ |(h η₀).re| + |(h η₀).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (G_far / lam ^ 2 + 2 * (G_all / lam ^ 2) * Real.exp (-lam * R)) +
          (G_far / lam ^ 2 + 2 * (G_all / lam ^ 2) * Real.exp (-lam * R)) :=
        add_le_add hre_loc him_loc
    _ = 2 * (G_far + 2 * G_all * Real.exp (-lam * R)) / lam ^ 2 := by ring

/-- Pointwise oscillation bound on the cylinder `(ℝ / cℤ) × ℝ` from a global Laplacian bound
`G_all` and a local Laplacian bound `G_far` on `{w | |w.2 - z.2| ≤ R}`. -/
theorem cylPoisOscPartLocalBound_of_modeBdd {c G_all G_far R : ℝ}
    (hc : 0 < c) (hR : 0 ≤ R) (hGall0 : 0 ≤ G_all) (hGfar0 : 0 ≤ G_far)
    {q : Plane → ℝ} (hq : ContDiff ℝ 2 q) (hqp : Cyl.IsPeriodic c q) (z : Plane)
    (hAll : ∀ w : Plane, |Train.lapS q w| ≤ G_all)
    (hFar : ∀ w : Plane, |w.2 - z.2| ≤ R → |Train.lapS q w| ≤ G_far)
    (hBdd : ∀ (n : ℤ), n ≠ 0 →
      ∃ M : ℝ, ∀ η : ℝ, ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) η‖ ≤ M) :
    |q z - hmean c q z.2| ≤
      ((G_far + 2 * G_all * Real.exp (-(2 * Real.pi * R / c))) * c ^ 2 / (2 * Real.pi ^ 2)) *
        ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  set a : ℝ :=
    (G_far + 2 * G_all * Real.exp (-(2 * Real.pi * R / c))) * c ^ 2 / (2 * Real.pi ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hf2 : ContDiff ℝ 2 (fun w : Plane => ((q w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hfper : Cyl.IsPeriodic c (fun w : Plane => ((q w : ℝ) : ℂ)) :=
    fun w => by simp only [hqp w]
  have hsrc_all : ∀ w : Plane, ‖((Train.lapS q w : ℝ) : ℂ)‖ ≤ G_all := fun w => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hAll w
  have hmode : ∀ (n : ℤ), n ≠ 0 →
      ‖Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) z.2‖ ≤ a / (n : ℝ) ^ 2 := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hn1 : 1 ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    set lam : ℝ := 2 * Real.pi * |(n : ℝ)| / c
    have hlam : 0 < lam := by
      dsimp [lam]
      have : 0 < |(n : ℝ)| := abs_pos.2 hn'
      positivity
    have hlam2 : lam ^ 2 = (2 * Real.pi * n / c) ^ 2 := by
      dsimp [lam]
      rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
      ring
    obtain ⟨hm2, hm''⟩ := cylPoisModeC2 c hc n _ hf2
    have hlap_eq : ∀ e : ℝ,
        deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e -
          ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e =
        Cyl.qMode c hc n (fun w => ((Train.lapS q w : ℝ) : ℂ)) e := by
      intro e
      rw [hm'' e, cylPoisModeLaplace c hc n q hq hqp hn e, hlam2]
    have hlap_all : ∀ e : ℝ,
        ‖deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e -
          ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e‖ ≤
        G_all := by
      intro e
      rw [hlap_eq e]
      exact (cylPoisQModeEstimates c hc n _).1 G_all hsrc_all e
    have hlap_far : ∀ e ∈ Icc (z.2 - R) (z.2 + R),
        ‖deriv (deriv (Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)))) e -
          ((lam ^ 2 : ℝ) : ℂ) * Cyl.qMode c hc n (fun w : Plane => ((q w : ℝ) : ℂ)) e‖ ≤
        G_far := by
      intro e he
      rw [hlap_eq e]
      refine cpQE_slice_bound hc n (fun w => ((Train.lapS q w : ℝ) : ℂ)) e G_far (fun x => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine hFar (x, e) ?_
      rw [abs_le]
      exact ⟨by linarith [he.1], by linarith [he.2]⟩
    have hbd := cpMP_complex_local_of_bdd hm2 hlam hR hGall0 hGfar0
      hlap_all hlap_far (hBdd n hn)
    have hexp_le : Real.exp (-lam * R) ≤ Real.exp (-(2 * Real.pi * R / c)) := by
      apply Real.exp_le_exp.2
      have hlam_ge : 2 * Real.pi / c ≤ lam := by
        dsimp [lam]
        exact div_le_div_of_nonneg_right
          (by nlinarith [Real.pi_pos, hn1]) hc.le
      have : (2 * Real.pi / c) * R ≤ lam * R := mul_le_mul_of_nonneg_right hlam_ge hR
      linarith [show 2 * Real.pi * R / c = (2 * Real.pi / c) * R by ring]
    have hbd2 : 2 * (G_far + 2 * G_all * Real.exp (-lam * R)) / lam ^ 2 ≤
        2 * (G_far + 2 * G_all * Real.exp (-(2 * Real.pi * R / c))) / lam ^ 2 := by
      gcongr
    have heq_a : 2 * (G_far + 2 * G_all * Real.exp (-(2 * Real.pi * R / c))) / lam ^ 2 =
        a / (n : ℝ) ^ 2 := by
      rw [hlam2]
      dsimp [a]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hc0 : c ≠ 0 := hc.ne'
      field_simp
    exact (hbd.trans hbd2).trans (le_of_eq heq_a)
  have hA : Summable (fun n : ℤ => a / (n : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine (h.mul_left a).congr (fun n => ?_)
    rw [mul_one_div]
  have hA0 : ∀ n : ℤ, 0 ≤ a / (n : ℝ) ^ 2 := fun n => div_nonneg ha (sq_nonneg _)
  have hres := cylPoisFourierPointwise c hc (fun w : Plane => ((q w : ℝ) : ℂ))
    (fun n : ℤ => a / (n : ℝ) ^ 2) z.2 hf2.continuous hfper hA hA0 hmode z.1
  have hsum : ∑' n : ℤ, a / (n : ℝ) ^ 2 = a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [mul_one_div])
  have hq0m : Cyl.qMode c hc 0 (fun w : Plane => ((q w : ℝ) : ℂ)) z.2 =
      ((hmean c q z.2 : ℝ) : ℂ) := by
    rw [Cyl.qMode_zero hc]
    exact cylPoisQAvgReal c q z.2
  rw [hq0m, hsum] at hres
  calc |q z - hmean c q z.2| = ‖((q z : ℝ) : ℂ) - ((hmean c q z.2 : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ a * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := hres

end PartI_T21

end UnforcedLeray.Short.PartI
