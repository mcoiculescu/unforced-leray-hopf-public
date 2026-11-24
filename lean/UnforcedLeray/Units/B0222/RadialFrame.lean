import UnforcedLeray.Units.B0221
import UnforcedLeray.Units.B0222.Product

/-!
# B0222 helper: the radial frame vector and the cylindrical vector Laplacian

Blueprint unit B0222 (label `eq:st18-t00115`), `paper/main.tex` lines 3327–3339; infrastructure
INF23 (cylindrical vector Laplacian for no-swirl fields).

The manuscript (tex lines 3333–3334) attributes the radial term `-ε²` of `A_ε^vec` to "the
vector-basis contribution `-r⁻²` in the cylindrical vector Laplacian". This file proves that
contribution. The Cartesian components `g_j = (e_r)_j` of the radial unit vector
(`B0220.unitR`: `x₀/r`, `x₁/r`, `0`) satisfy, off the axis,

* `(x·∇) g_j = 0` (homogeneous of degree `0`; `euler_unitR`),
* `∇g_j · ∇W = 0` whenever `W` has no angular derivative, `∂_φ W = x₀ ∂₁W - x₁ ∂₀W = 0`
  (`gradDot_unitR`),
* `Δ g_j = -g_j / r²` (`lapFun_unitR`).

With the Leibniz rule of `B0222/Product.lean` this gives, for an axisymmetric `C²` field `W`,

  `Δ(W e_r) = (ΔW - W/r²) e_r`   (`spatialLap_unitR_mul`, `spatialLapVec_noSwirl`),
  `L(W e_r) = (L W - ν ε² W/r²) e_r`   (`outerGen_unitR_mul`),

for the outer operator `L = ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` acting componentwise.

All derivatives of `g_j` are computed along coordinate lines (`B0221.LineCalculus`), where the
cylindrical radius is `R(t) = √(r² + 2βt + t²)` (`B0221.lineR`) and `g_j` is `R'(t)` or
`γ / R(t)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220 UnforcedLeray.B0221

namespace UnforcedLeray.B0222

/-! ### Components of the frame vectors -/

theorem unitR_apply_zero (x : Space) : unitR x 0 = x 0 / radius x := by simp [unitR]

theorem unitR_apply_one (x : Space) : unitR x 1 = x 1 / radius x := by simp [unitR]

theorem unitR_apply_two (x : Space) : unitR x 2 = 0 := by simp [unitR]

theorem unitZ_apply_zero : unitZ 0 = 0 := by simp [unitZ]

theorem unitZ_apply_one : unitZ 1 = 0 := by simp [unitZ]

theorem unitZ_apply_two : unitZ 2 = 1 := by simp [unitZ]

/-- The frame vector `e_r` is `C²` off the axis. -/
theorem contDiffAt_unitR_vec {x : Space} (hx : radius x ≠ 0) : ContDiffAt ℝ 2 unitR x := by
  have hrad := contDiffAt_radius hx
  have h0 : ContDiffAt ℝ 2 (fun y : Space => y 0 / radius y) x :=
    (by fun_prop : ContDiffAt ℝ 2 (fun y : Space => y 0) x).div hrad hx
  have h1 : ContDiffAt ℝ 2 (fun y : Space => y 1 / radius y) x :=
    (by fun_prop : ContDiffAt ℝ 2 (fun y : Space => y 1) x).div hrad hx
  exact (h0.smul contDiffAt_const).add (h1.smul contDiffAt_const)

/-- Each Cartesian component of `e_r` is `C²` off the axis. -/
theorem contDiffAt_unitR (j : Fin 3) {x : Space} (hx : radius x ≠ 0) :
    ContDiffAt ℝ 2 (fun y => unitR y j) x :=
  ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt).comp x
    (contDiffAt_unitR_vec hx)

/-! ### One-variable derivatives along a horizontal line -/

section OneVar

variable {r β γ : ℝ}

theorem eventually_radicand_pos (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < r ^ 2 + 2 * β * t + t ^ 2 := by
  have hcont : Continuous fun t : ℝ => r ^ 2 + 2 * β * t + t ^ 2 := by fun_prop
  have h0 : (0 : ℝ) < r ^ 2 + 2 * β * 0 + 0 ^ 2 := by simp; positivity
  exact (hcont.tendsto 0).eventually_const_lt h0

/-- `R''(t) = (r² - β²)/R(t)³` near `t = 0`. -/
theorem hasDerivAt_lineR'_eventually (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (lineR' r β) ((r ^ 2 - β ^ 2) / lineR r β t ^ 3) t := by
  filter_upwards [eventually_radicand_pos (β := β) hr, hasDerivAt_lineR (β := β) hr]
    with t ht hRt
  have hRpos : 0 < lineR r β t := Real.sqrt_pos.2 ht
  have hsq : lineR r β t ^ 2 = r ^ 2 + 2 * β * t + t ^ 2 := Real.sq_sqrt ht.le
  have h : HasDerivAt (fun t => (β + t) / lineR r β t) _ t :=
    ((hasDerivAt_id' t).const_add β).div hRt hRpos.ne'
  refine h.congr_deriv ?_
  simp only [lineR']
  field_simp
  linear_combination hsq

theorem deriv_lineR' (hr : 0 < r) : deriv (lineR' r β) 0 = (r ^ 2 - β ^ 2) / r ^ 3 :=
  (hasDerivAt_lineR' hr).deriv

/-- `R'''(0) = -3β(r² - β²)/r⁵`. -/
theorem deriv_deriv_lineR' (hr : 0 < r) :
    deriv (deriv (lineR' r β)) 0 = -(3 * β * (r ^ 2 - β ^ 2)) / r ^ 5 := by
  have heq : deriv (lineR' r β) =ᶠ[𝓝 0] fun t => (r ^ 2 - β ^ 2) / lineR r β t ^ 3 :=
    (hasDerivAt_lineR'_eventually hr).mono fun t ht => ht.deriv
  rw [heq.deriv_eq]
  have hR := (hasDerivAt_lineR (β := β) hr).self_of_nhds
  have hR0 := lineR_zero (β := β) hr.le
  have h2 : HasDerivAt (fun t => (r ^ 2 - β ^ 2) / lineR r β t ^ 3) _ 0 :=
    (hasDerivAt_const (0 : ℝ) (r ^ 2 - β ^ 2)).div (hR.pow 3) (by rw [hR0]; positivity)
  rw [h2.deriv, hR0, lineR'_zero hr.le]
  field_simp
  ring

theorem hasDerivAt_const_div_lineR (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => γ / lineR r β t)
      (-(γ * lineR' r β t) / lineR r β t ^ 2) t := by
  filter_upwards [eventually_radicand_pos (β := β) hr, hasDerivAt_lineR (β := β) hr]
    with t ht hRt
  have hRpos : 0 < lineR r β t := Real.sqrt_pos.2 ht
  refine ((hasDerivAt_const t γ).div hRt hRpos.ne').congr_deriv ?_
  ring

theorem deriv_const_div_lineR (hr : 0 < r) :
    deriv (fun t => γ / lineR r β t) 0 = -(γ * β) / r ^ 3 := by
  rw [(hasDerivAt_const_div_lineR hr).self_of_nhds.deriv, lineR_zero hr.le, lineR'_zero hr.le]
  field_simp

theorem deriv_deriv_const_div_lineR (hr : 0 < r) :
    deriv (deriv fun t => γ / lineR r β t) 0 = γ * (3 * β ^ 2 - r ^ 2) / r ^ 5 := by
  have heq : deriv (fun t => γ / lineR r β t) =ᶠ[𝓝 0]
      fun t => -(γ * lineR' r β t) / lineR r β t ^ 2 :=
    (hasDerivAt_const_div_lineR hr).mono fun t ht => ht.deriv
  rw [heq.deriv_eq]
  have hR := (hasDerivAt_lineR (β := β) hr).self_of_nhds
  have hR' := hasDerivAt_lineR' (β := β) hr
  have hR0 := lineR_zero (β := β) hr.le
  have h2 : HasDerivAt (fun t => -(γ * lineR' r β t) / lineR r β t ^ 2) _ 0 :=
    ((hR'.const_mul γ).neg).div (hR.pow 2) (by rw [hR0]; positivity)
  rw [h2.deriv]
  simp only [Pi.neg_apply]
  rw [hR0, lineR'_zero hr.le]
  field_simp
  ring

end OneVar

/-! ### The components of `e_r` along the coordinate lines -/

section Lines

variable (x : Space) (t : ℝ)

theorem unitR0_line0 : unitR (x + t • coordinateVector 0) 0 = lineR' (radius x) (x 0) t := by
  rw [unitR_apply_zero, radius_line0]
  simp [lineR', coordinateVector]

theorem unitR0_line1 : unitR (x + t • coordinateVector 1) 0 = x 0 / lineR (radius x) (x 1) t := by
  rw [unitR_apply_zero, radius_line1]
  simp [coordinateVector]

theorem unitR0_line2 : unitR (x + t • coordinateVector 2) 0 = x 0 / radius x := by
  rw [unitR_apply_zero, radius_line2]
  simp [coordinateVector]

theorem unitR1_line0 : unitR (x + t • coordinateVector 0) 1 = x 1 / lineR (radius x) (x 0) t := by
  rw [unitR_apply_one, radius_line0]
  simp [coordinateVector]

theorem unitR1_line1 : unitR (x + t • coordinateVector 1) 1 = lineR' (radius x) (x 1) t := by
  rw [unitR_apply_one, radius_line1]
  simp [lineR', coordinateVector]

theorem unitR1_line2 : unitR (x + t • coordinateVector 2) 1 = x 1 / radius x := by
  rw [unitR_apply_one, radius_line2]
  simp [coordinateVector]

end Lines

/-! ### First and second partial derivatives of the components of `e_r` -/

section Partials

variable {x : Space}

/-- `∂ᵢ (e_r)_j(x)`. -/
def dUnitR (j i : Fin 3) (x : Space) : ℝ := fderiv ℝ (fun y => unitR y j) x (coordinateVector i)

/-- `∂ᵢ∂ᵢ (e_r)_j(x)`. -/
def ddUnitR (j i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ (fun y' => unitR y' j) y (coordinateVector i)) x
    (coordinateVector i)

theorem dUnitR_eq_deriv (j i : Fin 3) (hx : radius x ≠ 0) :
    dUnitR j i x = deriv (fun t : ℝ => unitR (x + t • coordinateVector i) j) 0 :=
  fderiv_eq_deriv_line ((contDiffAt_unitR j hx).differentiableAt (by norm_num)) _

theorem ddUnitR_eq_deriv (j i : Fin 3) (hx : radius x ≠ 0) :
    ddUnitR j i x = deriv (deriv fun t : ℝ => unitR (x + t • coordinateVector i) j) 0 :=
  secondPartial_eq_deriv_deriv (contDiffAt_unitR j hx) _

theorem dUnitR_00 (hx : radius x ≠ 0) :
    dUnitR 0 0 x = (radius x ^ 2 - x 0 ^ 2) / radius x ^ 3 := by
  rw [dUnitR_eq_deriv 0 0 hx]
  simp only [unitR0_line0]
  exact deriv_lineR' (radius_pos hx)

theorem dUnitR_01 (hx : radius x ≠ 0) : dUnitR 0 1 x = -(x 0 * x 1) / radius x ^ 3 := by
  rw [dUnitR_eq_deriv 0 1 hx]
  simp only [unitR0_line1]
  exact deriv_const_div_lineR (radius_pos hx)

theorem dUnitR_02 (hx : radius x ≠ 0) : dUnitR 0 2 x = 0 := by
  rw [dUnitR_eq_deriv 0 2 hx]
  simp only [unitR0_line2, deriv_const]

theorem dUnitR_10 (hx : radius x ≠ 0) : dUnitR 1 0 x = -(x 1 * x 0) / radius x ^ 3 := by
  rw [dUnitR_eq_deriv 1 0 hx]
  simp only [unitR1_line0]
  exact deriv_const_div_lineR (radius_pos hx)

theorem dUnitR_11 (hx : radius x ≠ 0) :
    dUnitR 1 1 x = (radius x ^ 2 - x 1 ^ 2) / radius x ^ 3 := by
  rw [dUnitR_eq_deriv 1 1 hx]
  simp only [unitR1_line1]
  exact deriv_lineR' (radius_pos hx)

theorem dUnitR_12 (hx : radius x ≠ 0) : dUnitR 1 2 x = 0 := by
  rw [dUnitR_eq_deriv 1 2 hx]
  simp only [unitR1_line2, deriv_const]

theorem ddUnitR_00 (hx : radius x ≠ 0) :
    ddUnitR 0 0 x = -(3 * x 0 * (radius x ^ 2 - x 0 ^ 2)) / radius x ^ 5 := by
  rw [ddUnitR_eq_deriv 0 0 hx]
  simp only [unitR0_line0]
  exact deriv_deriv_lineR' (radius_pos hx)

theorem ddUnitR_01 (hx : radius x ≠ 0) :
    ddUnitR 0 1 x = x 0 * (3 * x 1 ^ 2 - radius x ^ 2) / radius x ^ 5 := by
  rw [ddUnitR_eq_deriv 0 1 hx]
  simp only [unitR0_line1]
  exact deriv_deriv_const_div_lineR (radius_pos hx)

theorem ddUnitR_02 (hx : radius x ≠ 0) : ddUnitR 0 2 x = 0 := by
  rw [ddUnitR_eq_deriv 0 2 hx]
  simp only [unitR0_line2, deriv_const', deriv_const]

theorem ddUnitR_10 (hx : radius x ≠ 0) :
    ddUnitR 1 0 x = x 1 * (3 * x 0 ^ 2 - radius x ^ 2) / radius x ^ 5 := by
  rw [ddUnitR_eq_deriv 1 0 hx]
  simp only [unitR1_line0]
  exact deriv_deriv_const_div_lineR (radius_pos hx)

theorem ddUnitR_11 (hx : radius x ≠ 0) :
    ddUnitR 1 1 x = -(3 * x 1 * (radius x ^ 2 - x 1 ^ 2)) / radius x ^ 5 := by
  rw [ddUnitR_eq_deriv 1 1 hx]
  simp only [unitR1_line1]
  exact deriv_deriv_lineR' (radius_pos hx)

theorem ddUnitR_12 (hx : radius x ≠ 0) : ddUnitR 1 2 x = 0 := by
  rw [ddUnitR_eq_deriv 1 2 hx]
  simp only [unitR1_line2, deriv_const', deriv_const]

theorem unitR_two_fun : (fun y : Space => unitR y 2) = fun _ => 0 :=
  funext unitR_apply_two

theorem dUnitR_2 (i : Fin 3) : dUnitR 2 i x = 0 := by
  simp [dUnitR, unitR_two_fun]

theorem ddUnitR_2 (i : Fin 3) : ddUnitR 2 i x = 0 := by
  simp [ddUnitR, unitR_two_fun]

/-- `(e_r)_j` is homogeneous of degree `0`: `(x·∇)(e_r)_j = 0` off the axis. -/
theorem euler_unitR (j : Fin 3) (hx : radius x ≠ 0) :
    ∑ i : Fin 3, x i * dUnitR j i x = 0 := by
  have hr := radius_pos hx
  have hr2 := radius_sq x
  rw [Fin.sum_univ_three]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [dUnitR_00 hx, dUnitR_01 hx, dUnitR_02 hx]
    field_simp
    linear_combination (-(x 0)) * hr2
  · simp only [Fin.mk_one, Fin.isValue]
    rw [dUnitR_10 hx, dUnitR_11 hx, dUnitR_12 hx]
    field_simp
    linear_combination (-(x 1)) * hr2
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [dUnitR_2, dUnitR_2, dUnitR_2]
    ring

/-- `∇(e_r)_j · w = 0` for every vector `w` with no angular part, `x₀ w₁ - x₁ w₀ = 0`. -/
theorem gradDot_unitR (j : Fin 3) (hx : radius x ≠ 0) (w : Fin 3 → ℝ)
    (hw : x 0 * w 1 - x 1 * w 0 = 0) :
    ∑ i : Fin 3, dUnitR j i x * w i = 0 := by
  have hr := radius_pos hx
  have hr2 := radius_sq x
  rw [Fin.sum_univ_three]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [dUnitR_00 hx, dUnitR_01 hx, dUnitR_02 hx]
    field_simp
    linear_combination (-(w 0)) * hr2 + (-(x 1)) * hw
  · simp only [Fin.mk_one, Fin.isValue]
    rw [dUnitR_10 hx, dUnitR_11 hx, dUnitR_12 hx]
    field_simp
    linear_combination (-(w 1)) * hr2 + (x 0) * hw
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [dUnitR_2, dUnitR_2, dUnitR_2]
    ring

/-- `Δ(e_r)_j = -(e_r)_j / r²` off the axis. -/
theorem lapFun_unitR (j : Fin 3) (hx : radius x ≠ 0) :
    lapFun (fun y => unitR y j) x = -unitR x j / radius x ^ 2 := by
  have hr := radius_pos hx
  have hr2 := radius_sq x
  have h : lapFun (fun y => unitR y j) x = ∑ i : Fin 3, ddUnitR j i x := rfl
  rw [h, Fin.sum_univ_three]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [ddUnitR_00 hx, ddUnitR_01 hx, ddUnitR_02 hx, unitR_apply_zero]
    field_simp
    linear_combination (3 * x 0) * hr2
  · simp only [Fin.mk_one, Fin.isValue]
    rw [ddUnitR_10 hx, ddUnitR_11 hx, ddUnitR_12 hx, unitR_apply_one]
    field_simp
    linear_combination (3 * x 1) * hr2
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [ddUnitR_2, ddUnitR_2, ddUnitR_2, unitR_apply_two]
    ring

end Partials

/-! ### The vector-basis contribution `-r⁻²` -/

/-- The angular derivative `∂_φ W = x₀ ∂₁W - x₁ ∂₀W` of a scalar field. -/
def angularPartial (W : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ :=
  y.1 0 * spatialPartial W 1 y - y.1 1 * spatialPartial W 0 y

/-- **The radial component of the cylindrical vector Laplacian** (tex lines 3333–3334): for a
field `W` of class `C²` in `x` with no angular derivative, off the axis,
`Δ_x(W (e_r)_j) = (e_r)_j (Δ_x W - W/r²)`. -/
theorem spatialLap_unitR_mul (j : Fin 3) {W : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hx : radius x ≠ 0) (hW : ContDiffAt ℝ 2 (fun x' => W (x', τ)) x)
    (hφ : angularPartial W (x, τ) = 0) :
    spatialLap (fun y => unitR y.1 j * W y) (x, τ) =
      unitR x j * (spatialLap W (x, τ) - W (x, τ) / radius x ^ 2) := by
  have hr := radius_pos hx
  rw [spatialLap_mul (contDiffAt_unitR j hx) hW, lapFun_unitR j hx]
  have hg := gradDot_unitR j hx (fun i => spatialPartial W i (x, τ)) hφ
  simp only [dUnitR] at hg
  rw [hg]
  field_simp
  ring

/-- **The outer operator on a radial field** (tex lines 3327–3334): for `W` of class `C²` in `x`
with no angular derivative, off the axis,
`L(W (e_r)_j) = (e_r)_j (L W - ν ε² W/r²)`, with
`L = ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ`. -/
theorem outerGen_unitR_mul (ν ε : ℝ) (j : Fin 3) {W : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hx : radius x ≠ 0) (hW : ContDiffAt ℝ 2 (fun x' => W (x', τ)) x)
    (hφ : angularPartial W (x, τ) = 0) :
    outerGen ν ε (fun y => unitR y.1 j * W y) (x, τ) =
      unitR x j * (outerGen ν ε W (x, τ) - ν * ε ^ 2 * W (x, τ) / radius x ^ 2) := by
  have hr := radius_pos hx
  rw [outerGen_mul ν ε (contDiffAt_unitR j hx) hW, lapFun_unitR j hx]
  have hg := gradDot_unitR j hx (fun i => spatialPartial W i (x, τ)) hφ
  have he := euler_unitR j hx
  simp only [dUnitR] at hg he
  rw [hg, he]
  field_simp
  ring

/-- The componentwise (Cartesian) vector Laplacian `Δ_x V` of a vector field
`V : ℝ³ × ℝ → ℝ³`. -/
def spatialLapVec (V : Space × ℝ → Space) (y : Space × ℝ) : Space :=
  WithLp.toLp 2 fun j => spatialLap (fun y' => V y' j) y

/-- **The cylindrical vector Laplacian of a no-swirl field** (tex lines 3333–3334; INF23): for
`V = W_r e_r + W_z e_z` with `W_r` of class `C²` in `x` and without angular derivative, off the
axis, `Δ_x V = (Δ_x W_r - W_r/r²) e_r + (Δ_x W_z) e_z`. The term `-W_r/r²` is the vector-basis
contribution. -/
theorem spatialLapVec_noSwirl {Wr Wz : Space × ℝ → ℝ} {x : Space} {τ : ℝ} (hx : radius x ≠ 0)
    (hWr : ContDiffAt ℝ 2 (fun x' => Wr (x', τ)) x) (hφ : angularPartial Wr (x, τ) = 0) :
    spatialLapVec (fun y => Wr y • unitR y.1 + Wz y • unitZ) (x, τ) =
      (spatialLap Wr (x, τ) - Wr (x, τ) / radius x ^ 2) • unitR x +
        spatialLap Wz (x, τ) • unitZ := by
  ext j
  simp only [spatialLapVec, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hrad : ∀ j : Fin 3, unitZ j = 0 →
      (fun y' : Space × ℝ => Wr y' * unitR y'.1 j + Wz y' * unitZ j) =
        fun y => unitR y.1 j * Wr y := by
    intro j hj
    funext y'
    rw [hj]
    ring
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [hrad 0 unitZ_apply_zero, spatialLap_unitR_mul 0 hx hWr hφ, unitZ_apply_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [hrad 1 unitZ_apply_one, spatialLap_unitR_mul 1 hx hWr hφ, unitZ_apply_one]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have h2 : (fun y' : Space × ℝ => Wr y' * unitR y'.1 2 + Wz y' * unitZ 2) = Wz := by
      funext y'
      rw [unitR_apply_two, unitZ_apply_two]
      ring
    rw [h2, unitR_apply_two, unitZ_apply_two]
    ring

end UnforcedLeray.B0222
