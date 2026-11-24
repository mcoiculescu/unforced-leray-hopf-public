import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/1/6`: the cpow reduction

Target: `CpowScale` (defined in `Sub/T18_2_4_1.lean`, with `IsScalarHeatSol`, `ScalarGaussDecayLoc`,
`lapC`, `pdC`).

Statement: for `0 < a`, a smooth `c`-periodic `w` vanishing for `s ≤ a`, solving
`w_s - νΔw = h` with Gaussian decay, the function `u = s^{-μ} w` is smooth, solves
`u_s + (μ/s) u - νΔu = s^{-μ} h` for `s > 0`, and has Gaussian decay.

Proof sketch:
1. Smoothness: `u = 0` on the open set `{s < a}`, and on `{s > 0}` the map `s ↦ s^z` is smooth
   (`s^z = exp(log s · z)` there), so `u` is smooth near every point.
2. Equation: for `s > 0`, `d/ds s^{-μ} = -μ s^{-μ-1} = -μ s^{-μ}/s`; the `μ/s` terms cancel, and
   `lapC (k · f) = k · lapC f` (unconditional, since `fderiv (k · f) = k • fderiv f`).
3. Decay: `|s^{-μ}|` is bounded on `[a, s₂]` by compactness; the bound for `w` transfers, and
   `u = 0` for `s ≤ a`.

Source of record: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus helpers -/

/-- The derivative of a constant multiple, applied to a vector, with no differentiability
hypothesis (if `f` is not differentiable at `x` both sides vanish). -/
theorem cpS_fderiv_const_mul_apply (k : ℂ) (f : ℝ × ℝ → ℂ) (x v : ℝ × ℝ) :
    fderiv ℝ (fun y => k * f y) x v = k * fderiv ℝ f x v := by
  by_cases hf : DifferentiableAt ℝ f x
  · rw [fderiv_const_mul hf k, smul_apply, smul_eq_mul]
  · by_cases hk : k = 0
    · subst hk
      simp
    · have hnd : ¬ DifferentiableAt ℝ (fun y => k * f y) x := by
        intro h
        apply hf
        have h2 : DifferentiableAt ℝ (fun y => k⁻¹ * (k * f y)) x := h.const_mul k⁻¹
        have e : (fun y => k⁻¹ * (k * f y)) = f := by
          funext y
          rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
        rw [e] at h2
        exact h2
      rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hf]
      simp

/-- The derivative of a constant multiple of a differentiable function, as a continuous linear
map. -/
theorem cpS_fderiv_const_mul_clm (k : ℂ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => k * f y) x = k • fderiv ℝ f x :=
  fderiv_const_mul hf k

/-- `pdC` commutes with a constant multiple. -/
theorem cpS_pdC_const_mul (k : ℂ) (f : ℝ × ℝ → ℂ) (j : Fin 2) (x : ℝ × ℝ) :
    pdC j (fun y => k * f y) x = k * pdC j f x := by
  unfold pdC
  exact cpS_fderiv_const_mul_apply k f x _

/-- The planar Laplacian commutes with a constant multiple. -/
theorem cpS_lapC_const_mul (k : ℂ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    lapC (fun y => k * f y) x = k * lapC f x := by
  have e : ∀ j : Fin 2, pdC j (fun y => k * f y) = fun y => k * pdC j f y :=
    fun j => funext fun y => cpS_pdC_const_mul k f j y
  unfold lapC
  rw [e 0, e 1, cpS_pdC_const_mul, cpS_pdC_const_mul]
  ring

/-- `s ↦ s^z` is smooth at every `s₀ > 0`. -/
theorem cpS_ofReal_cpow_contDiffAt (z : ℂ) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (s : ℂ) ^ z) s0 := by
  have hev : ∀ᶠ s : ℝ in 𝓝 s0, (s : ℂ) ^ z = Complex.exp (((Real.log s : ℝ) : ℂ) * z) := by
    filter_upwards [Ioi_mem_nhds hs0] with s hs
    have hpos : (0 : ℝ) < s := hs
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Complex.cpow_def_of_ne_zero hs', Complex.ofReal_log hpos.le]
  have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => ((Real.log s : ℝ) : ℂ)) s0 := by
    have hl : ContDiffAt ℝ ∞ Real.log s0 := Real.contDiffAt_log.2 hs0.ne'
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp s0 hl
  have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => Complex.exp (((Real.log s : ℝ) : ℂ) * z)) s0 :=
    (h1.mul contDiffAt_const).cexp
  exact h2.congr_of_eventuallyEq hev

/-- Derivative of `s ↦ s^z` at `s₀ > 0`. -/
theorem cpS_hasDerivAt_cpow (z : ℂ) (s0 : ℝ) (hs0 : 0 < s0) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ z) (z * (s0 : ℂ) ^ (z - 1)) s0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const s0 (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hs0.ne' hz

/-- The time slice `s ↦ w(s, x)` of a smooth function is smooth. -/
theorem cpS_contDiff_time (w : ℝ × (ℝ × ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (x : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun s : ℝ => w (s, x)) :=
  hw.comp (ContDiff.prodMk contDiff_id contDiff_const)

/-- The spatial slice `y ↦ w(s, y)` of a smooth function is smooth. -/
theorem cpS_contDiff_slice (w : ℝ × (ℝ × ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (s : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => w (s, y)) :=
  hw.comp (ContDiff.prodMk contDiff_const contDiff_id)

/-! ## The three properties of `u = s^{-μ} w` -/

/-- Smoothness of `u`. -/
theorem cpS_contDiff (μ : ℂ) (a : ℝ) (w : ℝ × (ℝ × ℝ) → ℂ) (ha : 0 < a)
    (hw : ContDiff ℝ ∞ w) (hz : ∀ s x, s ≤ a → w (s, x) = 0) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p.1
  · have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => ((q.1 : ℂ) ^ (-μ))) p :=
      (cpS_ofReal_cpow_contDiffAt (-μ) p.1 hp).comp p contDiffAt_fst
    exact h1.mul hw.contDiffAt
  · have hlt : p.1 < a := lt_of_le_of_lt (not_lt.1 hp) ha
    have hev : (fun q : ℝ × (ℝ × ℝ) => ((q.1 : ℂ) ^ (-μ)) * w q) =ᶠ[𝓝 p]
        fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with q hq
      have hq' : q.1 < a := hq
      have hq0 : w q = 0 := hz q.1 q.2 hq'.le
      simp [hq0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The equation `u_s + (μ/s) u - νΔu = s^{-μ} h` for `s > 0`. -/
theorem cpS_eq (ν : ℝ) (μ : ℂ) (w h : ℝ × (ℝ × ℝ) → ℂ) (hw : ContDiff ℝ ∞ w)
    (hsol : IsScalarHeatSol ν w h) (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    deriv (fun s' : ℝ => ((s' : ℂ) ^ (-μ)) * w (s', x)) s +
        (μ / (s : ℂ)) * (((s : ℂ) ^ (-μ)) * w (s, x)) -
      (ν : ℂ) * lapC (fun y => ((s : ℂ) ^ (-μ)) * w (s, y)) x =
    ((s : ℂ) ^ (-μ)) * h (s, x) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hk := cpS_hasDerivAt_cpow (-μ) s hs
  have hwt : DifferentiableAt ℝ (fun s' : ℝ => w (s', x)) s :=
    (cpS_contDiff_time w hw x).differentiable (by simp) s
  have hprod := hk.mul hwt.hasDerivAt
  have hd : deriv (fun s' : ℝ => ((s' : ℂ) ^ (-μ)) * w (s', x)) s =
      (-μ) * (s : ℂ) ^ (-μ - 1) * w (s, x) +
        (s : ℂ) ^ (-μ) * deriv (fun s' : ℝ => w (s', x)) s :=
    hprod.deriv
  have hcs : (s : ℂ) ^ (-μ - 1) = (s : ℂ) ^ (-μ) / (s : ℂ) := by
    rw [Complex.cpow_sub (-μ) 1 hs', Complex.cpow_one]
  have hlap : lapC (fun y => ((s : ℂ) ^ (-μ)) * w (s, y)) x =
      ((s : ℂ) ^ (-μ)) * lapC (fun y => w (s, y)) x :=
    cpS_lapC_const_mul _ _ _
  have heat := hsol s x
  rw [hd, hcs, hlap]
  linear_combination ((s : ℂ) ^ (-μ)) * heat

/-- Gaussian decay of `u`. -/
theorem cpS_decay (μ : ℂ) (a : ℝ) (w : ℝ × (ℝ × ℝ) → ℂ) (ha : 0 < a)
    (hw : ContDiff ℝ ∞ w) (hz : ∀ s x, s ≤ a → w (s, x) = 0) (hdec : ScalarGaussDecayLoc w) :
    ScalarGaussDecayLoc (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w p) := by
  intro s₂
  obtain ⟨C, κ, hκ, hbound⟩ := hdec s₂
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (-μ)) (Icc a s₂) := by
    intro s hs
    exact (cpS_ofReal_cpow_contDiffAt (-μ) s (lt_of_lt_of_le ha hs.1)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := s₂)).exists_bound_of_continuousOn hcont
  refine ⟨max M 0 * max C 0, κ, hκ, fun s x hs => ?_⟩
  show ‖(s : ℂ) ^ (-μ) * w (s, x)‖ + ‖fderiv ℝ (fun y => (s : ℂ) ^ (-μ) * w (s, y)) x‖ ≤
    max M 0 * max C 0 * Real.exp (-κ * x.2 ^ 2)
  by_cases has : a < s
  · have hs0 : 0 < s := lt_trans ha has
    have hmem : s ∈ Icc a s₂ := ⟨has.le, hs⟩
    have hn : ‖(s : ℂ) ^ (-μ)‖ ≤ max M 0 := le_trans (hM s hmem) (le_max_left _ _)
    have hX : ‖w (s, x)‖ + ‖fderiv ℝ (fun y => w (s, y)) x‖ ≤
        max C 0 * Real.exp (-κ * x.2 ^ 2) :=
      le_trans (hbound s x hs)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h1 : ‖(s : ℂ) ^ (-μ) * w (s, x)‖ = ‖(s : ℂ) ^ (-μ)‖ * ‖w (s, x)‖ := norm_mul _ _
    have hdiff : DifferentiableAt ℝ (fun y => w (s, y)) x :=
      (cpS_contDiff_slice w hw s).differentiable (by simp) x
    have e : fderiv ℝ (fun y => (s : ℂ) ^ (-μ) * w (s, y)) x =
        (s : ℂ) ^ (-μ) • fderiv ℝ (fun y => w (s, y)) x :=
      fderiv_const_mul hdiff _
    have h2 : ‖fderiv ℝ (fun y => (s : ℂ) ^ (-μ) * w (s, y)) x‖ ≤
        ‖(s : ℂ) ^ (-μ)‖ * ‖fderiv ℝ (fun y => w (s, y)) x‖ := by
      rw [e]
      exact norm_smul_le ((s : ℂ) ^ (-μ)) (fderiv ℝ (fun y => w (s, y)) x)
    calc ‖(s : ℂ) ^ (-μ) * w (s, x)‖ + ‖fderiv ℝ (fun y => (s : ℂ) ^ (-μ) * w (s, y)) x‖
        ≤ ‖(s : ℂ) ^ (-μ)‖ * ‖w (s, x)‖ + ‖(s : ℂ) ^ (-μ)‖ * ‖fderiv ℝ (fun y => w (s, y)) x‖ := by
          rw [h1]
          linarith [h2]
      _ = ‖(s : ℂ) ^ (-μ)‖ * (‖w (s, x)‖ + ‖fderiv ℝ (fun y => w (s, y)) x‖) := by ring
      _ ≤ max M 0 * (max C 0 * Real.exp (-κ * x.2 ^ 2)) :=
          mul_le_mul hn hX (add_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
      _ = max M 0 * max C 0 * Real.exp (-κ * x.2 ^ 2) := by ring
  · have hs' : s ≤ a := not_lt.1 has
    have hz' : ∀ y : ℝ × ℝ, (s : ℂ) ^ (-μ) * w (s, y) = 0 := fun y => by
      rw [hz s y hs', mul_zero]
    have hL : ‖(s : ℂ) ^ (-μ) * w (s, x)‖ +
        ‖fderiv ℝ (fun y => (s : ℂ) ^ (-μ) * w (s, y)) x‖ = 0 := by
      simp [hz']
    rw [hL]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (Real.exp_pos _).le

/-! ## The cpow reduction -/

/-- **Leaf 6: the cpow reduction** (`PartIII-a:T18/2/4/1/6`). -/
theorem cpowScale : CpowScale := by
  intro c ν μ a h w ha hw _hper hz hsol hdec
  exact ⟨cpS_contDiff μ a w ha hw hz,
    fun s hs x => cpS_eq ν μ w h hw hsol s hs x,
    cpS_decay μ a w ha hw hz hdec⟩

end UnforcedLeray.Short.IIIa
