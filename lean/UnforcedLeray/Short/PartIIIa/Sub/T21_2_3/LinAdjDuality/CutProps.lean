import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadCutPropsAux

/-- The one-variable profile `y ↦ ζ(2 - y²)`. -/
def cutH (y : ℝ) : ℝ := Real.smoothTransition (2 - y ^ 2)

lemma cutH_contDiff : ContDiff ℝ ∞ cutH := by
  unfold cutH
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma cutH_smooth' : ContDiff ℝ ∞ (deriv cutH) :=
  (contDiff_infty_iff_deriv.1 cutH_contDiff).2

lemma cutH_differentiable : Differentiable ℝ cutH :=
  cutH_contDiff.differentiable (by simp)

lemma cutH_hasCompactSupport : HasCompactSupport cutH := by
  apply HasCompactSupport.intro (K := Icc (-2 : ℝ) 2) isCompact_Icc
  intro y hy
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  have h4 : (4 : ℝ) < y ^ 2 := by
    rcases hy with hy | hy <;> nlinarith
  unfold cutH
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Directional derivative along `dir j` as a one-variable derivative. -/
lemma hasDerivAt_dir (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2) (hφ : DifferentiableAt ℝ φ x) :
    HasDerivAt (fun t : ℝ => φ (x + t • B0579.dir j)) (B0579.pd j φ x) 0 := by
  have hf : HasDerivAt (fun t : ℝ => x + t • B0579.dir j) (B0579.dir j) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (B0579.dir j)).const_add x
    simpa using this
  have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • B0579.dir j) := by
    simpa using hφ.hasFDerivAt
  exact hφ'.comp_hasDerivAt (0 : ℝ) hf

lemma dir_zero_fst : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by
  simp [B0579.dir]

lemma dir_one_snd : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by
  simp [B0579.dir]

/-- The partial derivative of `(x ↦ a · h(η/R))` in `q` vanishes. -/
lemma pd0_comp (a R : ℝ) (h : ℝ → ℝ) (x : ℝ × ℝ) (hh : Differentiable ℝ h) :
    B0579.pd 0 (fun y : ℝ × ℝ => a * h (y.2 / R)) x = 0 := by
  have hφ : DifferentiableAt ℝ (fun y : ℝ × ℝ => a * h (y.2 / R)) x := by
    have h0 : DifferentiableAt ℝ (fun y : ℝ × ℝ => h (y.2 / R)) x :=
      (hh (x.2 / R)).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ × ℝ => y.2 / R) x)
    exact h0.const_mul a
  have h1 := hasDerivAt_dir _ x 0 hφ
  have hfun : (fun t : ℝ => (fun y : ℝ × ℝ => a * h (y.2 / R)) (x + t • B0579.dir 0))
      = fun _ : ℝ => a * h (x.2 / R) := by
    funext t
    simp [B0579.dir]
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_const (0 : ℝ) (a * h (x.2 / R)))

/-- The partial derivative of `(x ↦ a · h(η/R))` in `η`. -/
lemma pd1_comp (a R : ℝ) (h : ℝ → ℝ) (x : ℝ × ℝ) (hh : Differentiable ℝ h) (hR : R ≠ 0) :
    B0579.pd 1 (fun y : ℝ × ℝ => a * h (y.2 / R)) x = a * (deriv h (x.2 / R) * R⁻¹) := by
  have hφ : DifferentiableAt ℝ (fun y : ℝ × ℝ => a * h (y.2 / R)) x := by
    have h0 : DifferentiableAt ℝ (fun y : ℝ × ℝ => h (y.2 / R)) x :=
      (hh (x.2 / R)).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ × ℝ => y.2 / R) x)
    exact h0.const_mul a
  have h1 := hasDerivAt_dir _ x 1 hφ
  have hfun : (fun t : ℝ => (fun y : ℝ × ℝ => a * h (y.2 / R)) (x + t • B0579.dir 1))
      = fun t : ℝ => a * h ((x.2 + t) / R) := by
    funext t
    simp [B0579.dir]
  rw [hfun] at h1
  have hl : HasDerivAt (fun t : ℝ => (x.2 + t) / R) (R⁻¹) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add x.2).div_const R
    simpa [div_eq_mul_inv] using this
  have hH : HasDerivAt h (deriv h ((x.2 + 0) / R)) ((x.2 + 0) / R) :=
    (hh _).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => a * h ((x.2 + t) / R))
      (a * (deriv h (x.2 / R) * R⁻¹)) 0 := by
    have hc := (hH.comp (0 : ℝ) (by simpa using hl)).const_mul a
    simpa using hc
  exact h1.unique h2

lemma cutH_bounds : ∃ K : ℝ, 0 ≤ K ∧ (∀ y : ℝ, |deriv cutH y| ≤ K) ∧
    (∀ y : ℝ, |deriv (deriv cutH) y| ≤ K) := by
  obtain ⟨K1, hK1⟩ := cutH_smooth'.continuous.bounded_above_of_compact_support
    cutH_hasCompactSupport.deriv
  obtain ⟨K2, hK2⟩ := (cutH_smooth'.continuous_deriv (by simp)).bounded_above_of_compact_support
    cutH_hasCompactSupport.deriv.deriv
  refine ⟨|K1| + |K2|, by positivity, fun y => ?_, fun y => ?_⟩
  · have h1 := hK1 y
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self K1, abs_nonneg K2]
  · have h2 := hK2 y
    rw [Real.norm_eq_abs] at h2
    linarith [le_abs_self K2, abs_nonneg K1]

lemma ladCut_eq (R : ℝ) : ladCut R = fun x : ℝ × ℝ => (1 : ℝ) * cutH (x.2 / R) := by
  funext x
  simp only [ladCut, cutH, div_pow, one_mul]

end LadCutPropsAux

open LadCutPropsAux in
/-- **The cutoff** (calculus; SP 3074-3075 cutoff `χ_R`): `LadCutProps`. -/
theorem ladCutProps : LadCutProps := by
  obtain ⟨K, hK0, hK1, hK2⟩ := cutH_bounds
  refine ⟨K, hK0, fun R hR => ?_⟩
  have hR0 : R ≠ 0 := hR.ne'
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have hcut : ∀ x : ℝ × ℝ, ladCut R x = cutH (x.2 / R) := fun x => by
    simp only [ladCut, cutH, div_pow]
  refine ⟨fun c => ⟨?_, fun x => rfl, ⟨2 * R, fun x hx => ?_⟩⟩, fun x => ⟨Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩, ?_, ?_, ?_, ?_⟩
  · rw [ladCut_eq]
    exact contDiff_const.mul (cutH_contDiff.comp ((contDiff_snd).div_const R))
  · have h4 : 4 * R ^ 2 < x.2 ^ 2 := by
      nlinarith [sq_abs x.2, abs_nonneg x.2]
    have hq : 2 ≤ x.2 ^ 2 / R ^ 2 := (le_div_iff₀ hR2).2 (by nlinarith)
    unfold ladCut
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · intro x hx
    have hq : x.2 ^ 2 / R ^ 2 ≤ 1 := (div_le_one hR2).2 hx
    unfold ladCut
    exact Real.smoothTransition.one_of_one_le (by linarith)
  · intro x hx
    have hq : 2 ≤ x.2 ^ 2 / R ^ 2 := (le_div_iff₀ hR2).2 (by linarith)
    unfold ladCut
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · have h0 : ∀ x : ℝ × ℝ, |B0579.pd 0 (ladCut R) x| ≤ K / R := by
      intro x
      rw [ladCut_eq, pd0_comp 1 R cutH x cutH_differentiable]
      simpa using div_nonneg hK0 hR.le
    have h1 : ∀ x : ℝ × ℝ, |B0579.pd 1 (ladCut R) x| ≤ K / R := by
      intro x
      rw [ladCut_eq, pd1_comp 1 R cutH x cutH_differentiable hR0]
      have hb := hK1 (x.2 / R)
      have hi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
      calc |(1 : ℝ) * (deriv cutH (x.2 / R) * R⁻¹)|
          = |deriv cutH (x.2 / R)| * R⁻¹ := by
            rw [one_mul, abs_mul, abs_of_nonneg hi]
        _ ≤ K * R⁻¹ := mul_le_mul_of_nonneg_right hb hi
        _ = K / R := by rw [div_eq_mul_inv]
    intro x j
    fin_cases j
    · exact h0 x
    · exact h1 x
  · intro x
    have hpd1 : B0579.pd 1 (ladCut R) = fun y : ℝ × ℝ => R⁻¹ * deriv cutH (y.2 / R) := by
      funext y
      rw [ladCut_eq, pd1_comp 1 R cutH y cutH_differentiable hR0]
      ring
    have hpd0 : B0579.pd 0 (ladCut R) = fun _ : ℝ × ℝ => (0 : ℝ) := by
      funext y
      rw [ladCut_eq, pd0_comp 1 R cutH y cutH_differentiable]
    have hd1 : Differentiable ℝ (deriv cutH) := cutH_smooth'.differentiable (by simp)
    have hlap : lapP (ladCut R) x = R⁻¹ * (deriv (deriv cutH) (x.2 / R) * R⁻¹) := by
      unfold lapP
      rw [hpd0, hpd1, pd1_comp R⁻¹ R (deriv cutH) x hd1 hR0]
      simp [B0579.pd]
    rw [hlap]
    have hi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
    have hb := hK2 (x.2 / R)
    calc |R⁻¹ * (deriv (deriv cutH) (x.2 / R) * R⁻¹)|
        = R⁻¹ * (|deriv (deriv cutH) (x.2 / R)| * R⁻¹) := by
          rw [abs_mul, abs_of_nonneg hi, abs_mul, abs_of_nonneg hi]
      _ ≤ R⁻¹ * (K * R⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hi) hi
      _ = K / R ^ 2 := by ring
