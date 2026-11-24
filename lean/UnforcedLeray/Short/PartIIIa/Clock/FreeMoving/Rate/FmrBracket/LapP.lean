import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIsoRadial

/-!
# Part III-a, task `PartIII-a:T21/c2/2/3/1`: the Laplacian of the dilating weight

Source of record: `the November 2 reference manuscript`, lines 2947-2954.
With `r² = x.1² + x.2²`, `w = 1 + r²/a` and `p = w^m` (`movWeight m a`):
`∂_j∂_j p = m (m-1) w^(m-2) (2 x_j/a)² + m w^(m-1) (2/a)`, hence
`lapP p = (4m/a) w^(m-1) + 4m(m-1) (r²/a²) w^(m-2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

theorem fmrBracket_pdpd0 (m a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    B0579.pd 0 (B0579.pd 0 (movWeight m a)) x =
      m * ((m - 1) * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 2) * (2 * x.1 / a)) * (2 * x.1 / a) +
        m * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) * (2 / a) := by
  obtain ⟨q, η⟩ := x
  have hb : (1 + (q ^ 2 + η ^ 2) / a) ≠ 0 := by
    have : 0 ≤ (q ^ 2 + η ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have hfun : B0579.pd 0 (movWeight m a) = fun y : B0579.Plane =>
      m * (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ^ (m - 1) * (2 * y.1 / a) := by
    funext y; exact fmrIso_pd0 m a ha y
  have hdiff : Differentiable ℝ (fun y : B0579.Plane =>
      m * (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ^ (m - 1) * (2 * y.1 / a)) := by
    intro y
    have hy : (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ≠ 0 := by
      have : 0 ≤ (y.1 ^ 2 + y.2 ^ 2) / a := div_nonneg (by positivity) ha.le
      linarith
    have h1 : DifferentiableAt ℝ (fun y : B0579.Plane => 1 + (y.1 ^ 2 + y.2 ^ 2) / a) y := by
      fun_prop
    have h2 := h1.rpow_const (p := m - 1) (Or.inl hy)
    have h3 : DifferentiableAt ℝ (fun y : B0579.Plane => 2 * y.1 / a) y := by fun_prop
    exact (h2.const_mul m).mul h3
  rw [hfun]
  have h1 := B0579.hasDerivAt_fst hdiff q η
  have hh : HasDerivAt (fun t : ℝ => 1 + (t ^ 2 + η ^ 2) / a) (2 * q / a) q := by
    have := (((hasDerivAt_pow 2 q).add_const (η ^ 2)).div_const a).const_add 1
    exact this.congr_deriv (by norm_num)
  have hr := (hh.rpow_const (p := m - 1) (Or.inl hb)).const_mul m
  have hl : HasDerivAt (fun t : ℝ => 2 * t / a) (2 / a) q := by
    have := ((hasDerivAt_id' q).const_mul 2).div_const a
    simpa using this
  have h2 := hr.mul hl
  have := h1.unique h2
  rw [this, show m - 1 - 1 = m - 2 by ring]
  ring

theorem fmrBracket_pdpd1 (m a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    B0579.pd 1 (B0579.pd 1 (movWeight m a)) x =
      m * ((m - 1) * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 2) * (2 * x.2 / a)) * (2 * x.2 / a) +
        m * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) * (2 / a) := by
  obtain ⟨q, η⟩ := x
  have hb : (1 + (q ^ 2 + η ^ 2) / a) ≠ 0 := by
    have : 0 ≤ (q ^ 2 + η ^ 2) / a := div_nonneg (by positivity) ha.le
    linarith
  have hfun : B0579.pd 1 (movWeight m a) = fun y : B0579.Plane =>
      m * (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ^ (m - 1) * (2 * y.2 / a) := by
    funext y; exact fmrIso_pd1 m a ha y
  have hdiff : Differentiable ℝ (fun y : B0579.Plane =>
      m * (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ^ (m - 1) * (2 * y.2 / a)) := by
    intro y
    have hy : (1 + (y.1 ^ 2 + y.2 ^ 2) / a) ≠ 0 := by
      have : 0 ≤ (y.1 ^ 2 + y.2 ^ 2) / a := div_nonneg (by positivity) ha.le
      linarith
    have h1 : DifferentiableAt ℝ (fun y : B0579.Plane => 1 + (y.1 ^ 2 + y.2 ^ 2) / a) y := by
      fun_prop
    have h2 := h1.rpow_const (p := m - 1) (Or.inl hy)
    have h3 : DifferentiableAt ℝ (fun y : B0579.Plane => 2 * y.2 / a) y := by fun_prop
    exact (h2.const_mul m).mul h3
  rw [hfun]
  have h1 := B0579.hasDerivAt_snd hdiff q η
  have hh : HasDerivAt (fun t : ℝ => 1 + (q ^ 2 + t ^ 2) / a) (2 * η / a) η := by
    have := (((hasDerivAt_pow 2 η).const_add (q ^ 2)).div_const a).const_add 1
    exact this.congr_deriv (by norm_num)
  have hr := (hh.rpow_const (p := m - 1) (Or.inl hb)).const_mul m
  have hl : HasDerivAt (fun t : ℝ => 2 * t / a) (2 / a) η := by
    have := ((hasDerivAt_id' η).const_mul 2).div_const a
    simpa using this
  have h2 := hr.mul hl
  have := h1.unique h2
  rw [this, show m - 1 - 1 = m - 2 by ring]
  ring

theorem fmrBracket_lapP (m a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    lapP (movWeight m a) x =
      (4 * m / a) * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 1) +
        4 * m * (m - 1) * ((x.1 ^ 2 + x.2 ^ 2) / a ^ 2) * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ (m - 2) := by
  unfold lapP
  rw [fmrBracket_pdpd0 m a ha x, fmrBracket_pdpd1 m a ha x]
  ring

end UnforcedLeray.Short.IIIa
