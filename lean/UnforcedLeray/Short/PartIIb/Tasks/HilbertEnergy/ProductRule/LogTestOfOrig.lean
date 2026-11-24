import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1975-1979 (weak
product rule in the `H_2` measure; logarithmic chart `s = e^t`).

Target `LogTestOfOrig` (`Sub/T15_2.lean`): if `ψ` is smooth, `qShift c`-periodic and vanishes when
`x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|` (with `σ > 0`), then `ψ̃(x) = ψ(e^{x.1}, x.2)` is a `LogTest`
and `∂_t ψ̃(x) = e^{x.1} (∂_s ψ)(e^{x.1}, x.2)`.

Proof: the map `E(t, y) = (e^t, y)` is smooth and commutes with `qShift c`; the support bound
`T = |log σ| + |log (|H| + 1)| + 1` in `t` gives `e^t < σ` for `t < -T` and `e^t > H` for `t > T`;
the derivative is the chain rule along the `t`-line through `E x`, whose velocity is
`e^{x.1} • cdir 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Derivative of a function along the `s`-line through a point (copied from
`Tasks/HilbertEnergy/SPeriodic.lean`, `hasDerivAt_line`). -/
theorem logTO_hasDerivAt_line {F : Coord → ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x) :
    HasDerivAt (fun t : ℝ => F (x.1 + t, x.2)) (cpd 0 F x) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1 + t, x.2) : Coord)) (cdir 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.1
    have h2 : HasDerivAt (fun _ : ℝ => x.2) 0 0 := hasDerivAt_const _ _
    have h3 := h1.prodMk h2
    rw [show cdir 0 = (1, 0) by simp [cdir]]
    exact h3
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)

/-- **Target `PartII-b:T15/2`** (original tests give logarithmic tests; `LogTestOfOrig`). -/
theorem logTestOfOrig : UnforcedLeray.Short.IIb.LogTestOfOrig := by
  intro c ψ hψ hper hsupp
  obtain ⟨σ, H, L, hσ, hvan⟩ := hsupp
  -- the map `E(t, y) = (e^t, y)` is smooth
  have hE : ContDiff ℝ ∞ (fun x : Coord => (Real.exp x.1, x.2)) :=
    ContDiff.prodMk (Real.contDiff_exp.comp contDiff_fst) contDiff_snd
  have hΦc : ContDiff ℝ ∞ (fun x : Coord => ψ (Real.exp x.1, x.2)) := hψ.comp hE
  -- periodicity: `E` commutes with `qShift c`
  have hperΦ : ∀ x : Coord,
      (fun x : Coord => ψ (Real.exp x.1, x.2)) (qShift c x) =
        (fun x : Coord => ψ (Real.exp x.1, x.2)) x := by
    intro x
    exact hper (Real.exp x.1, x.2)
  -- compact support in `t`
  have hcompact : ∃ T L' : ℝ, ∀ x : Coord, (T < |x.1| ∨ L' < |x.2.2|) →
      (fun x : Coord => ψ (Real.exp x.1, x.2)) x = 0 := by
    refine ⟨|Real.log σ| + |Real.log (|H| + 1)| + 1, L, ?_⟩
    intro x hx
    show ψ (Real.exp x.1, x.2) = 0
    rcases hx with hx | hx
    · rcases lt_abs.mp hx with h1 | h1
      · -- `x.1 > T`: `e^{x.1} > |H| + 1 > H`
        have hlt : Real.log (|H| + 1) < x.1 := by
          linarith [abs_nonneg (Real.log σ), le_abs_self (Real.log (|H| + 1))]
        have hexp : |H| + 1 < Real.exp x.1 := by
          have h := Real.exp_lt_exp.mpr hlt
          rwa [Real.exp_log (by positivity)] at h
        exact hvan (Real.exp x.1, x.2)
          (Or.inr (Or.inl (by show H < Real.exp x.1; linarith [le_abs_self H])))
      · -- `x.1 < -T`: `e^{x.1} < σ`
        have hlt : x.1 < Real.log σ := by
          linarith [neg_abs_le (Real.log σ), abs_nonneg (Real.log (|H| + 1))]
        have hexp : Real.exp x.1 < σ := by
          have h := Real.exp_lt_exp.mpr hlt
          rwa [Real.exp_log hσ] at h
        exact hvan (Real.exp x.1, x.2) (Or.inl hexp)
    · exact hvan (Real.exp x.1, x.2) (Or.inr (Or.inr hx))
  -- derivative: chain rule along the `t`-line, velocity `e^{x.1} • cdir 0`
  have hderiv : ∀ x : Coord, cpd 0 (fun y : Coord => ψ (Real.exp y.1, y.2)) x =
      Real.exp x.1 * cpd 0 ψ (Real.exp x.1, x.2) := by
    intro x
    have hΦd : DifferentiableAt ℝ (fun y : Coord => ψ (Real.exp y.1, y.2)) x :=
      (hΦc.differentiable (by simp)).differentiableAt
    have hψd : DifferentiableAt ℝ ψ (Real.exp x.1, x.2) :=
      (hψ.differentiable (by simp)).differentiableAt
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (x.1 + t)) (Real.exp x.1) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => x.1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.1
      simpa using h1.exp
    have hcurve : HasDerivAt (fun t : ℝ => ((Real.exp (x.1 + t), x.2) : Coord))
        ((Real.exp x.1, (0 : ℝ × ℝ)) : Coord) 0 :=
      hexp.prodMk (hasDerivAt_const (0 : ℝ) x.2)
    have hdir : ((Real.exp x.1, (0 : ℝ × ℝ)) : Coord) = Real.exp x.1 • cdir 0 := by
      simp [cdir, Prod.ext_iff]
    have hcomp := hψd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
    have h := logTO_hasDerivAt_line hΦd
    have key := h.unique hcomp
    rw [key, hdir, map_smul, smul_eq_mul]
    rfl
  exact ⟨⟨hΦc, hperΦ, hcompact⟩, hderiv⟩

end UnforcedLeray.Short.IIb
