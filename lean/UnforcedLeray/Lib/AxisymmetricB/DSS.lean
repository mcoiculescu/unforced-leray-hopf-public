import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# AX08 (rest): periodicity of the ring lift and discrete self-similarity


§5 Layer 3, target AX08 (`Axi/DSS.lean`): `Nv_dss` and `physical_dss` (critic correction 3
moved them to Wave 2J since they need AX04's `Nv`; `phase_shift` is in Wave 1,
`Lib/Axisymmetric/RingChart.lean`). Blueprint units served: B0190 (`unlabeled:2916`,
tex 2916–2917: "The field and its pressure obey the DSS scaling with physical ratio `e^{c/R}`.
In similarity time `τ = log t`, the period is `2c/R`"), B0687 (`background:eq:2.8`,
tex 5123–5870: `a(e^{P/2} x) = e^{−P/2} a(x)`), B0186 (tex 2076: phase period `P = 2εc`).

* `Nv_dss`: for a profile `c`-periodic in `ξ`, the lift `N_v b` is `P`-periodic in `τ`,
  `P = 2c/R`.
* `selfSim k U x t = t^{-k/2} U(log t, x/√t)`: the physical field of a similarity profile
  (`k = 1` for velocities, `k = 2` for pressures); `selfSim_dss`: a `P`-periodic profile gives
  `u(λx, λ²t) = λ^{-k} u(x, t)` with `λ = e^{P/2}`.
* `physical_dss`: the physical velocity `u = t^{-1/2} N_v b(log t, x/√t)` and the physical
  pressure `p = t^{-1} (s Π)(log t, x/√t)` satisfy `u(λx, λ²t) = λ⁻¹ u(x,t)`,
  `p(λx, λ²t) = λ⁻² p(x,t)`, `λ = e^{c/R}` (B0190).
* `physNv_eq`: in physical variables `u = (R/r)(b_r e_r + b_z e_z)` at the physical chart point
  `((R/r)² t, R log(r/R), (R/r) z)` (tex 2851–2856, B0185: `u_r = a_r v₁`, `u_z = a_r(v₂+εH)`).

Junk values. `selfSim` is used only for `t > 0`: Lean's `√t = 0` and `log t = log |t|` for
`t ≤ 0` would give a junk field there, and every statement assumes `0 < t`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- **AX08 `Nv_dss`.** For a profile `c`-periodic in `ξ`, the ring lift is periodic in the
similarity time with period `P = 2c/R` (tex 2076, 2916–2917). -/
theorem Nv_dss {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) {b : ℝ × (ℝ × ℝ) → Merid}
    (hper : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) (τ : ℝ) :
    Nv R b (τ + P) = Nv R b τ := by
  funext y
  rw [Nv, Nv, chart_add_period hR hP, hper]
  rfl

/-- The scalar ring lift `s Π` of a raw pressure profile `Π` (tex 2081: "raw pressure `sp`"). -/
def Np (R : ℝ) (pr : ℝ × (ℝ × ℝ) → ℝ) (τ : ℝ) (y : Space) : ℝ := age R y * pr (chart R τ y)

theorem Np_dss {R c P : ℝ} (hR : R ≠ 0) (hP : P = 2 * c / R) {pr : ℝ × (ℝ × ℝ) → ℝ}
    (hper : ∀ s ξ η, pr (s, (ξ + c, η)) = pr (s, (ξ, η))) (τ : ℝ) :
    Np R pr (τ + P) = Np R pr τ := by
  funext y
  rw [Np, Np, chart_add_period hR hP, hper]
  rfl

/-! ### Self-similar fields -/

section SelfSim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical field of a similarity profile `U(τ, y)`:
`u(x, t) = t^{-k/2} U(log t, x/√t)` (similarity variables `y = x/√t`, `τ = log t`). -/
def selfSim (k : ℕ) (U : ℝ → Space → E) (x : Space) (t : ℝ) : E :=
  ((√t) ^ k)⁻¹ • U (Real.log t) ((√t)⁻¹ • x)

/-- **Discrete self-similarity of a periodic profile.** If `U` is `P`-periodic in `τ` and
`λ = e^{P/2}`, then `u(λx, λ²t) = λ^{-k} u(x, t)` for `t > 0`. -/
theorem selfSim_dss (k : ℕ) {U : ℝ → Space → E} {P : ℝ} (hU : ∀ τ, U (τ + P) = U τ)
    (x : Space) {t : ℝ} (ht : 0 < t) :
    selfSim k U (Real.exp (P / 2) • x) (Real.exp (P / 2) ^ 2 * t) =
      (Real.exp (P / 2) ^ k)⁻¹ • selfSim k U x t := by
  set l := Real.exp (P / 2) with hl
  have hl0 : 0 < l := Real.exp_pos _
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hsq : √(l ^ 2 * t) = l * √t := by
    rw [Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl0.le]
  have hlog : Real.log (l ^ 2 * t) = Real.log t + P := by
    rw [Real.log_mul (pow_ne_zero 2 hl0.ne') ht.ne', Real.log_pow, hl, Real.log_exp]
    push_cast
    ring
  have hx : (l * √t)⁻¹ • (l • x) = (√t)⁻¹ • x := by
    rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hl0.ne', mul_one]
  rw [selfSim, selfSim, hsq, hlog, hU, hx, smul_smul, mul_pow, mul_inv_rev, mul_comm]

end SelfSim

/-- The physical velocity `u(x, t) = t^{-1/2} N_v b(log t, x/√t)` of a profile `b`. -/
def physNv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (x : Space) (t : ℝ) : Space :=
  selfSim 1 (Nv R b) x t

/-- The physical pressure `p(x, t) = t^{-1} (s Π)(log t, x/√t)` of a raw pressure profile. -/
def physNp (R : ℝ) (pr : ℝ × (ℝ × ℝ) → ℝ) (x : Space) (t : ℝ) : ℝ :=
  selfSim 2 (Np R pr) x t

/-- **AX08 `physical_dss`** (B0190, tex 2916–2917). For profiles `c`-periodic in `ξ`, the
physical velocity and pressure obey the DSS scaling with ratio `λ = e^{c/R}`:
`u(λx, λ²t) = λ⁻¹ u(x, t)` and `p(λx, λ²t) = λ⁻² p(x, t)` for `t > 0`. -/
theorem physical_dss {R c : ℝ} (hR : R ≠ 0) {b : ℝ × (ℝ × ℝ) → Merid}
    {pr : ℝ × (ℝ × ℝ) → ℝ}
    (hb : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η)))
    (hpr : ∀ s ξ η, pr (s, (ξ + c, η)) = pr (s, (ξ, η))) (x : Space) {t : ℝ} (ht : 0 < t) :
    physNv R b (Real.exp (c / R) • x) (Real.exp (c / R) ^ 2 * t) =
        (Real.exp (c / R))⁻¹ • physNv R b x t ∧
      physNp R pr (Real.exp (c / R) • x) (Real.exp (c / R) ^ 2 * t) =
        (Real.exp (c / R) ^ 2)⁻¹ * physNp R pr x t := by
  have hP : (2 * c / R) / 2 = c / R := by ring
  constructor
  · have h := selfSim_dss 1 (U := Nv R b) (P := 2 * c / R) (Nv_dss hR rfl hb) x ht
    rw [hP, pow_one] at h
    exact h
  · have h := selfSim_dss 2 (U := Np R pr) (P := 2 * c / R) (Np_dss hR rfl hpr) x ht
    rw [hP, smul_eq_mul] at h
    exact h

/-! ### The physical form of the lift (B0185) -/

theorem hor_smul (k : ℝ) (x : Space) : hor (k • x) = k • hor x := by
  ext i
  fin_cases i <;> simp [hor]

theorem eR_smul {k : ℝ} (hk : 0 < k) (x : Space) : eR (k • x) = eR x := by
  rw [eR, eR, hor_smul, ϱ_smul, abs_of_pos hk, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hk.ne', mul_one]

theorem frameL_smul {k : ℝ} (hk : 0 < k) (x : Space) : frameL (k • x) = frameL x := by
  ext v : 1
  rw [frameL_apply, frameL_apply, eR_smul hk]

/-- **Physical form of the lift** (B0185, tex 2851–2856). For `R, t > 0` and `x` off the axis,
`u(x, t) = (R/r) (b_r e_r + b_z e_z)` at the physical chart point
`(s, ξ, η) = ((R/r)² t, R log(r/R), (R/r) z)`, `r = ϱ(x)`, `z = x₃`. -/
theorem physNv_eq {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (b : ℝ × (ℝ × ℝ) → Merid) {x : Space}
    (hx : x ∉ axis) :
    physNv R b x t = (R / ϱ x) • frameL x (b (RingLift.ageCoordinate R (ϱ x) t,
      (RingLift.logRadius R (ϱ x), RingLift.transverseCoordinate R (ϱ x) (x 2)))) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hρ := ϱ_pos hx
  have hch := chart_similarity hR ht hx
  have hage : age R ((√t)⁻¹ • x) = (R / ϱ x) ^ 2 * t := congrArg Prod.fst hch
  have hsa : √(age R ((√t)⁻¹ • x)) = R / ϱ x * √t := by
    rw [hage, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hR hρ).le]
  rw [physNv, selfSim, Nv, hch, hsa, frameL_smul (inv_pos.2 hst), pow_one, smul_smul]
  congr 1
  field_simp

end UnforcedLeray.Axi
