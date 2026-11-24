import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild.ExpJoint

/-!
# Helper for `Spine:SP-CAN` Bridge 3: the Duhamel forms of `V` and `S`

Helper module of `Short/Spine/Proofs/CanonicalBranch/Mild.lean` (task `Spine:SP-CAN`, Bridge 3).
Source: `the November 2 reference manuscript` lines 1094-1150.

The proof works coefficientwise in the eigenbasis `oscBasis` of `D` (B0094). For a strong
solution `V` of `-V' = (L₀ + θ⁻¹D)V` and a mode `n`, the coefficient `c(u) = ⟪e_n, V u⟫` satisfies
`c' = n u⁻¹ c - ⟪e_n, L₀V⟫`, so `u ↦ exp(-n log u) c(u)` has derivative
`-exp(-n log u) ⟪e_n, L₀V(u)⟫`. Integrating gives the coefficient form of the Duhamel identity,
which is the vector identity `V θ = e^{log(θ'/θ)D} V θ' + ∫_θ^{θ'} e^{log(v/θ)D} L₀V(v) dv`.

Main declarations (namespace `UnforcedLeray.Short.Spine.CanonicalMild`):
* `hasDerivAt_coeff`, `inner_deriv_eq`: the coefficient ODE;
* `coeff_duhamel`: the coefficient form of the Duhamel identity for `V`;
* `canonical_duhamel`: the vector Duhamel identity for `V`;
* `S_mild_interval`: the Duhamel form of `S(θ, θ')` with the integral over `θ..θ'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff

namespace UnforcedLeray.Short.Spine.CanonicalMild

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
open UnforcedLeray.Short.PartI UnforcedLeray.Cons.G3b

/-- The coefficient `u ↦ ⟪e_n, V u⟫` is differentiable on `(0, ∞)`. -/
theorem hasDerivAt_coeff {V : ℝ → XG} (hV : IsCanonicalSolution V) (n : ℕ) {v : ℝ}
    (hv : 0 < v) :
    HasDerivAt (fun u => ⟪oscBasis n, V u⟫_ℂ) ⟪oscBasis n, deriv V v⟫_ℂ v := by
  have hdiff : DifferentiableAt ℝ V v :=
    (hV.smooth.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hv)
  have h := ((innerSL ℂ (oscBasis n)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (x := v)
    hdiff.hasDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    innerSL_apply_apply] using h

/-- The coefficient ODE: `⟪e_n, V'(v)⟫ = -⟪e_n, L₀V(v)⟫ + v⁻¹ n ⟪e_n, V(v)⟫`. -/
theorem inner_deriv_eq {V : ℝ → XG} (hV : IsCanonicalSolution V) (n : ℕ) {v : ℝ} (hv : 0 < v) :
    ⟪oscBasis n, deriv V v⟫_ℂ =
      -⟪oscBasis n, B0012.L0 (V v)⟫_ℂ + (v : ℂ)⁻¹ * (n : ℂ) * ⟪oscBasis n, V v⟫_ℂ := by
  have hODE : -(deriv V v) = B0012.L0 (V v) + ((v : ℂ))⁻¹ • D ⟨V v, hV.mem_domain v hv⟩ :=
    hV.equation v hv
  have h := congrArg (fun z => ⟪oscBasis n, z⟫_ℂ) hODE
  simp only [inner_neg_right, inner_add_right, inner_smul_right] at h
  rw [inner_D] at h
  dsimp only at h
  linear_combination -h

/-- `v ↦ e^{(log v - log θ)D}` acts on the `n`-th coefficient as the scalar `expMult`. -/
theorem expMult_log_sub {θ v : ℝ} (hθ : 0 < θ) (hv : θ ≤ v) (n : ℕ) :
    ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) * ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) =
      expMult (Real.log v - Real.log θ) n := by
  have hlog : Real.log θ ≤ Real.log v := Real.log_le_log hθ hv
  unfold expMult
  rw [max_eq_left (sub_nonneg.2 hlog), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- At the base point the weight is `expMult 0 n = 1`. -/
theorem expMult_log_self (θ : ℝ) (n : ℕ) : expMult (Real.log θ - Real.log θ) n = 1 := by
  simp [expMult]

/-- The coefficient form of the Duhamel identity for a canonical solution. -/
theorem coeff_duhamel {V : ℝ → XG} (hV : IsCanonicalSolution V) (n : ℕ) {θ θ' : ℝ}
    (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    ⟪oscBasis n, V θ⟫_ℂ = expMult (Real.log θ' - Real.log θ) n * ⟪oscBasis n, V θ'⟫_ℂ +
      ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ := by
  have hVc : ContinuousOn V (Icc θ θ') :=
    hV.smooth.continuousOn.mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Icc θ θ') := by
    apply ContinuousOn.log continuousOn_id
    intro v hv
    exact (lt_of_lt_of_le hθ hv.1).ne'
  have hexp : ContinuousOn (fun v : ℝ => Real.exp (-(n : ℝ) * Real.log v)) (Icc θ θ') :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)
  have hwc : ContinuousOn (fun v : ℝ => ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ))
      (Icc θ θ') :=
    Complex.continuous_ofReal.comp_continuousOn hexp
  have hℓc : ContinuousOn (fun v : ℝ => ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ) (Icc θ θ') := by
    have h1 : ContinuousOn (fun v : ℝ => B0012.L0 (V v)) (Icc θ θ') :=
      B0012.L0.continuous.comp_continuousOn hVc
    exact (innerSL ℂ (oscBasis n)).continuous.comp_continuousOn h1
  have hgc : ContinuousOn
      (fun v : ℝ => -(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ))
      (Icc θ θ') :=
    (hwc.mul hℓc).neg
  -- the derivative of `G(u) = exp(-n log u) ⟪e_n, V u⟫`
  have hG : ∀ v ∈ uIcc θ θ',
      HasDerivAt (fun u : ℝ => ((Real.exp (-(n : ℝ) * Real.log u) : ℝ) : ℂ) * ⟪oscBasis n, V u⟫_ℂ)
        (-(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ)) v := by
    intro v hv
    rw [uIcc_of_le hθθ'] at hv
    have hvpos : 0 < v := lt_of_lt_of_le hθ hv.1
    have hw : HasDerivAt (fun u : ℝ => Real.exp (-(n : ℝ) * Real.log u))
        (Real.exp (-(n : ℝ) * Real.log v) * (-(n : ℝ) * v⁻¹)) v :=
      ((Real.hasDerivAt_log hvpos.ne').const_mul (-(n : ℝ))).exp
    have hwC := hw.ofReal_comp
    have hc := hasDerivAt_coeff hV n hvpos
    have hprod := hwC.mul hc
    refine hprod.congr_deriv ?_
    rw [inner_deriv_eq hV n hvpos]
    push_cast
    ring
  have hint : IntervalIntegrable
      (fun v : ℝ => -(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ))
      volume θ θ' := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hθθ']
    exact hgc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => ((Real.exp (-(n : ℝ) * Real.log u) : ℝ) : ℂ) * ⟪oscBasis n, V u⟫_ℂ)
    (f' := fun v : ℝ =>
      -(((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ))
    hG hint
  rw [intervalIntegral.integral_neg] at hFTC
  -- `hFTC : -J = G θ' - G θ`, with `J = ∫ w v * ℓ v`
  have hGθ : ((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) * ⟪oscBasis n, V θ⟫_ℂ =
      ((Real.exp (-(n : ℝ) * Real.log θ') : ℝ) : ℂ) * ⟪oscBasis n, V θ'⟫_ℂ +
        ∫ v in θ..θ', ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
          ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ := by
    linear_combination hFTC
  -- the base weights: `E · w(θ) = 1` and `E · w(θ') = expMult (log θ' - log θ)`
  have hE1 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
      ((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) = 1 := by
    have h := expMult_log_sub hθ le_rfl n
    rw [expMult_log_self] at h
    exact h
  have hE2 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
      (((Real.exp (-(n : ℝ) * Real.log θ') : ℝ) : ℂ) * ⟪oscBasis n, V θ'⟫_ℂ) =
      expMult (Real.log θ' - Real.log θ) n * ⟪oscBasis n, V θ'⟫_ℂ := by
    rw [← mul_assoc, expMult_log_sub hθ hθθ' n]
  have hE3 : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
      (∫ v in θ..θ', ((Real.exp (-(n : ℝ) * Real.log v) : ℝ) : ℂ) *
          ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ) =
      ∫ v in θ..θ', expMult (Real.log v - Real.log θ) n * ⟪oscBasis n, B0012.L0 (V v)⟫_ℂ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hθθ'] at hv
    dsimp only
    rw [← expMult_log_sub hθ hv.1 n]
    ring
  have hself : ((Real.exp ((n : ℝ) * Real.log θ) : ℝ) : ℂ) *
      (((Real.exp (-(n : ℝ) * Real.log θ) : ℝ) : ℂ) * ⟪oscBasis n, V θ⟫_ℂ) =
      ⟪oscBasis n, V θ⟫_ℂ := by
    rw [← mul_assoc, hE1, one_mul]
  rw [← hself, hGθ, mul_add, hE2, hE3]

/-- The vector Duhamel identity for a canonical solution (`Spine:SP-CAN`, Bridge 3). -/
theorem canonical_duhamel {V : ℝ → XG} (hV : IsCanonicalSolution V) {θ θ' : ℝ}
    (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    V θ = expD (Real.log θ' - Real.log θ) (V θ') +
      ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (V v)) := by
  have hVc : ContinuousOn V (Icc θ θ') :=
    hV.smooth.continuousOn.mono (fun v hv => lt_of_lt_of_le hθ hv.1)
  have hF : ContinuousOn (fun v : ℝ => B0012.L0 (V v)) (Icc θ θ') :=
    B0012.L0.continuous.comp_continuousOn hVc
  have hint := intervalIntegrable_expD_log hθ hθθ' hF
  apply ext_inner_basis oscBasis
  intro n
  have hinner : ⟪oscBasis n, ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (V v))⟫_ℂ =
      ∫ v in θ..θ', ⟪oscBasis n, expD (Real.log v - Real.log θ) (B0012.L0 (V v))⟫_ℂ := by
    have h := (innerSL ℂ (oscBasis n)).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    exact h.symm
  rw [inner_add_right, hinner, inner_expD]
  simp only [inner_expD]
  exact coeff_duhamel hV n hθ hθθ'

/-- The Duhamel form of `S(θ, θ')` with the integral over `θ..θ'` (`S_mild` after the change of
variables `u = -v`). -/
theorem S_mild_interval {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (x : XG) :
    S θ θ' x = expD (Real.log θ' - Real.log θ) x +
      ∫ v in θ..θ', expD (Real.log v - Real.log θ) (B0012.L0 (S v θ' x)) := by
  rw [S_mild hθ hθθ' x]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := θ) (b := θ')
    (f := fun u : ℝ => freeU (-θ) u (B0012.L0 (S (-u) θ' x)))
  simp only [neg_neg] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v _
  simp only [freeU, neg_neg]

end UnforcedLeray.Short.Spine.CanonicalMild
