import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_8
import UnforcedLeray.Short.PartIIIa.StressInputs

/-!
# Part III-a, task `PartIII-a:T23/10`: the transverse tail of the exact split

Source of record: `the November 2 reference manuscript`, lines 2664-2745.

`StressTransverse` is assembled from `RawTransverseTail` and `InletTransverseTail` at the
levels of an exact split. The coefficients satisfy `|coord z i| ≤ rhoB ≤ |C₀| ν^{-k₀}`, and
`1 + 2|C₀|ν^{-k₀} ≤ exp(ν^{-1})` for small `ν`, so the two tails with `D + 1` give `e^{-D/ν}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- Absorption of a polynomial by the exponential: `1 + A x^k ≤ exp x` for `x` large. -/
theorem t10_exp_absorb (A : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ x : ℝ, X0 ≤ x → 1 + A * x ^ k ≤ Real.exp x := by
  refine ⟨max 1 (((k + 1).factorial : ℝ) * (A + 1)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxB : ((k + 1).factorial : ℝ) * (A + 1) ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxk : 1 ≤ x ^ k := one_le_pow₀ hx1
  have hexp := Real.pow_div_factorial_le_exp x hxpos.le (k + 1)
  have hf : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hkey : (A + 1) * x ^ k ≤ x ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    rw [le_div_iff₀ hf, pow_succ]
    have h := mul_le_mul_of_nonneg_left hxB (le_of_lt (pow_pos hxpos k))
    nlinarith [h]
  nlinarith [hkey, hexp, hxk]

/-- The repair coefficient is bounded by `|C₀| ν^{-k₀}` under the window condition. -/
theorem t10_rhoB_le (p : Params) (d dm dp m0 C0 : ℝ) (k0 : ℕ) (hreg : BgRegime p d dm dp)
    (hm0le : m0 ≤ 3 * dm / 11) :
    rhoB p m0 C0 k0 ≤ |C0| * (p.ν ^ k0)⁻¹ := by
  have hνpos : 0 < p.ν := p.ν_pos
  unfold rhoB
  have hεe : p.ε ^ (3 / 11 : ℝ) = Real.exp (-d / p.ν * (3 / 11)) := by
    rw [hreg.eps_eq, ← Real.exp_mul]
  have hq : Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ) ≤ 1 := by
    rw [hεe, ← Real.exp_add, Real.exp_le_one_iff]
    have hmd : m0 - 3 * d / 11 ≤ 0 := by linarith [hreg.dm_le]
    have hcomb : m0 / p.ν + -d / p.ν * (3 / 11) = (m0 - 3 * d / 11) * p.ν⁻¹ := by ring
    rw [hcomb]
    exact mul_nonpos_of_nonpos_of_nonneg hmd (inv_nonneg.2 hνpos.le)
  have ha : 0 ≤ (p.ν ^ k0)⁻¹ := inv_nonneg.2 (pow_nonneg hνpos.le _)
  have hq0 : 0 ≤ Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg p.ε_pos.le _)
  calc C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)
      = C0 * (p.ν ^ k0)⁻¹ * (Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
    _ ≤ |C0| * (p.ν ^ k0)⁻¹ * (Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hq0
        exact mul_le_mul_of_nonneg_right (le_abs_self C0) ha
    _ ≤ |C0| * (p.ν ^ k0)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg (abs_nonneg _) ha)
    _ = |C0| * (p.ν ^ k0)⁻¹ := mul_one _

/-- **`stress-short:transverse`** (SP 2731-2745), assembled from the raw and inlet transverse
tails at an exact split. -/
theorem stressTransverse_of (h4 : UnforcedLeray.Short.IIIa.RawTransverseTail)
    (h5 : UnforcedLeray.Short.IIIa.InletTransverseTail) :
    UnforcedLeray.Short.IIIa.StressTransverse := by
  intro dm dp hdm m0 C0 k0 hm0 hm0le mZ hmZ bexp Dperp hb hDp Sig lam q hSig hq
  obtain ⟨Cp1, n1, hn1, hA⟩ := h4 dm dp hdm mZ hmZ bexp (Dperp + 1) hb (by linarith)
  obtain ⟨Cp2, n2, hn2, hB⟩ :=
    h5 dm dp hdm mZ hmZ bexp (Dperp + 1) hb (by linarith) Sig lam q hSig hq
  obtain ⟨X0, hX0, habs⟩ := t10_exp_absorb (2 * |C0|) (by positivity) k0
  refine ⟨max Cp1 Cp2, min n1 (min n2 X0⁻¹), lt_min hn1 (lt_min hn2 (inv_pos.2 hX0)), ?_⟩
  intro p d hreg hν hSg hmode S_in V rb hsplit pt hpt0 hpe hη
  have hνpos : 0 < p.ν := p.ν_pos
  have hνa : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have hνb : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνc : p.ν ≤ X0⁻¹ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hXnn : 0 ≤ p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1 := by
    have hc0 : 0 ≤ p.c / p.ν := div_nonneg p.c_pos.le hνpos.le
    have := Real.sqrt_nonneg (p.ε ^ (-bexp))
    linarith
  have hηA : Cp1 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn) hη
  have hηB : Cp2 * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) hXnn) hη
  have hR := hA p d hreg hνa pt hpt0 hpe hηA
  have hI := hB p d hreg hνb hSg hmode
  have hI0 := hI 0 pt hpt0 hpe hηB
  have hI1 := hI 1 pt hpt0 hpe hηB
  obtain ⟨z, _, hVz, _, hcoord⟩ := hsplit.state
  have hVeq : V = fun t y => p.raw t y + p.coord z 0 • p.inlet 0 t y + p.coord z 1 • p.inlet 1 t y := by
    funext τ y
    rw [hVz τ y, Fin.sum_univ_two, add_assoc]
  have hchart : chartCoeff p.R V pt = chartCoeff p.R p.raw pt + p.coord z 0 • chartCoeff p.R (p.inlet 0) pt
      + p.coord z 1 • chartCoeff p.R (p.inlet 1) pt := by
    rw [hVeq]
    exact chartCoeff_sum2 p.R _ _ p.raw (p.inlet 0) (p.inlet 1) pt
  rw [hchart]
  -- coefficient bounds
  have hρ := t10_rhoB_le p d dm dp m0 C0 k0 hreg hm0le
  have hB0 : |p.coord z 0| ≤ |C0| * (p.ν ^ k0)⁻¹ := (hcoord 0).trans hρ
  have hB1' : |p.coord z 1| ≤ |C0| * (p.ν ^ k0)⁻¹ := (hcoord 1).trans hρ
  have hBnn : 0 ≤ |C0| * (p.ν ^ k0)⁻¹ := mul_nonneg (abs_nonneg _) (inv_nonneg.2 (pow_nonneg hνpos.le _))
  -- absorption of the polynomial by the exponential
  have hxX : X0 ≤ p.ν⁻¹ := (le_inv_comm₀ hX0 hνpos).2 hνc
  have hab := habs p.ν⁻¹ hxX
  rw [inv_pow] at hab
  have hB1 : 1 + 2 * (|C0| * (p.ν ^ k0)⁻¹) ≤ Real.exp p.ν⁻¹ := by
    calc 1 + 2 * (|C0| * (p.ν ^ k0)⁻¹) = 1 + 2 * |C0| * (p.ν ^ k0)⁻¹ := by ring
      _ ≤ Real.exp p.ν⁻¹ := hab
  have hE0 : 0 ≤ Real.exp (-(Dperp + 1) / p.ν) := (Real.exp_pos _).le
  have hEv : Real.exp p.ν⁻¹ * Real.exp (-(Dperp + 1) / p.ν) = Real.exp (-Dperp / p.ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hw0 : 0 ≤ Real.sqrt pt.1 * transWeight mZ pt :=
    mul_nonneg (Real.sqrt_nonneg _) (by unfold transWeight; positivity)
  -- the three pieces
  have htri : ‖chartCoeff p.R p.raw pt + p.coord z 0 • chartCoeff p.R (p.inlet 0) pt
      + p.coord z 1 • chartCoeff p.R (p.inlet 1) pt‖ ≤
      ‖chartCoeff p.R p.raw pt‖ + |p.coord z 0| * ‖chartCoeff p.R (p.inlet 0) pt‖
        + |p.coord z 1| * ‖chartCoeff p.R (p.inlet 1) pt‖ := by
    have h1 := norm_add_le (chartCoeff p.R p.raw pt + p.coord z 0 • chartCoeff p.R (p.inlet 0) pt)
      (p.coord z 1 • chartCoeff p.R (p.inlet 1) pt)
    have h2 := norm_add_le (chartCoeff p.R p.raw pt) (p.coord z 0 • chartCoeff p.R (p.inlet 0) pt)
    have h3 : ‖p.coord z 0 • chartCoeff p.R (p.inlet 0) pt‖ =
        |p.coord z 0| * ‖chartCoeff p.R (p.inlet 0) pt‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have h4' : ‖p.coord z 1 • chartCoeff p.R (p.inlet 1) pt‖ =
        |p.coord z 1| * ‖chartCoeff p.R (p.inlet 1) pt‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    linarith
  have hw := mul_le_mul_of_nonneg_left htri hw0
  have hsplitw : Real.sqrt pt.1 * transWeight mZ pt *
      (‖chartCoeff p.R p.raw pt‖ + |p.coord z 0| * ‖chartCoeff p.R (p.inlet 0) pt‖
        + |p.coord z 1| * ‖chartCoeff p.R (p.inlet 1) pt‖) =
      Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖
        + |p.coord z 0| * (Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet 0) pt‖)
        + |p.coord z 1| * (Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet 1) pt‖) := by
    ring
  have hterm0 : |p.coord z 0| * (Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet 0) pt‖)
      ≤ (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν) :=
    mul_le_mul hB0 hI0 (mul_nonneg hw0 (norm_nonneg _)) hBnn
  have hterm1 : |p.coord z 1| * (Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet 1) pt‖)
      ≤ (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν) :=
    mul_le_mul hB1' hI1 (mul_nonneg hw0 (norm_nonneg _)) hBnn
  have hfin : Real.exp (-(Dperp + 1) / p.ν) + (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν)
      + (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν) ≤ Real.exp (-Dperp / p.ν) := by
    calc Real.exp (-(Dperp + 1) / p.ν) + (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν)
          + (|C0| * (p.ν ^ k0)⁻¹) * Real.exp (-(Dperp + 1) / p.ν)
        = (1 + 2 * (|C0| * (p.ν ^ k0)⁻¹)) * Real.exp (-(Dperp + 1) / p.ν) := by ring
      _ ≤ Real.exp p.ν⁻¹ * Real.exp (-(Dperp + 1) / p.ν) :=
          mul_le_mul_of_nonneg_right hB1 hE0
      _ = Real.exp (-Dperp / p.ν) := hEv
  have hR2 : Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ +
      Real.sqrt pt.1 * transWeight mZ pt * ‖p.train.v pt.1 pt.2‖ ≤ Real.exp (-(Dperp + 1) / p.ν) := by
    have := hR
    rw [mul_add] at this
    exact this
  rw [mul_add]
  linarith [hw, hsplitw, hR2, hterm0, hterm1, hfin]

end UnforcedLeray.Short.IIIa
