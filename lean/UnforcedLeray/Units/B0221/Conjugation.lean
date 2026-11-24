import UnforcedLeray.Units.B0221.Generators
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# B0221 helper: the pointwise conjugation identity `L(a b) = a A_ε b`

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346.

For the lift `U(x, τ) = a b(s, q, η)` of `eq:st18-t00113` (B0220, `liftU`), with `a = 1/r`,
`s = r⁻²`, `q = ε⁻¹ log r + τ/(2ε)`, `η = z/(εr)`, and the outer operator
`L = ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` (tex lines 3343–3347, `outerGen`), this file proves

  `L U (x, τ) = a(x) · (A_ε b)(s, q, η)`  at every point `x` off the axis,

for `b` of class `C²` at the chart point (`outerGen_liftU`). This is the statement that `A_ε`
is the conjugate of `L` under the lift (tex lines 3341–3347).

Method (the blueprint's proof outline: chain rule with `∂_r = (εr)⁻¹[∂_q - ε(2S + η∂_η)]`,
`∂_z = (εr)⁻¹ ∂_η`, conjugation by `a` shifting `K` to `K + 1`): every second coordinate
derivative is a second derivative along a coordinate line (`LineCalculus`). Along the line
`x + t e_i` (`i = 0, 1`) the radius is `R(t) = √(r² + 2 x_i t + t²)` (`lineR`), and the field
is `R⁻¹ b(G(R))` with `G(u) = (u⁻², ε⁻¹ log u + τ/(2ε), z/(εu))` (`Gm`). Along `x + t e_2`
only `η` moves. The two horizontal lines give `α + x_i² γ` (`radial_second`); their sum uses
`x₀² + x₁² = r²`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-! ### The chart along the radius -/

/-- The chart point at cylindrical radius `u`, height `z` and phase `τ`:
`G(u) = (u⁻², ε⁻¹ log u + τ/(2ε), z/(εu))` (tex lines 3283–3288). -/
def Gm (ε τ z u : ℝ) : Profile := ((u ^ 2)⁻¹, ε⁻¹ * Real.log u + τ / (2 * ε), z / (ε * u))

/-- `G'(u)`. -/
def Gm' (ε z u : ℝ) : Profile := (-2 / u ^ 3, ε⁻¹ / u, -z / (ε * u ^ 2))

/-- `G''(u)`. -/
def Gm'' (ε z u : ℝ) : Profile := (6 / u ^ 4, -ε⁻¹ / u ^ 2, 2 * z / (ε * u ^ 3))

theorem chart_eq_Gm (ε : ℝ) (x : Space) (τ : ℝ) :
    chart ε (x, τ) = Gm ε τ (x 2) (radius x) := rfl

theorem liftU_eq (ε : ℝ) (b : Profile → ℝ) (x : Space) (τ : ℝ) :
    liftU ε b (x, τ) = (radius x)⁻¹ * b (Gm ε τ (x 2) (radius x)) := rfl

theorem hasDerivAt_Gm {ε τ z u : ℝ} (hε : ε ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (Gm ε τ z) (Gm' ε z u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u ^ 2)⁻¹) (-2 / u ^ 3) u := by
    refine ((hasDerivAt_pow 2 u).inv (pow_ne_zero 2 hu)).congr_deriv ?_
    field_simp
    ring
  have h2 : HasDerivAt (fun u : ℝ => ε⁻¹ * Real.log u + τ / (2 * ε)) (ε⁻¹ / u) u := by
    refine (((Real.hasDerivAt_log hu).const_mul ε⁻¹).add_const (τ / (2 * ε))).congr_deriv ?_
    rw [div_eq_mul_inv]
  have h3 : HasDerivAt (fun u : ℝ => z / (ε * u)) (-z / (ε * u ^ 2)) u := by
    refine ((hasDerivAt_const u z).div ((hasDerivAt_id' u).const_mul ε)
      (mul_ne_zero hε hu)).congr_deriv ?_
    field_simp
    ring
  exact h1.prodMk (h2.prodMk h3)

theorem hasDerivAt_Gm' {ε z u : ℝ} (hε : ε ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (Gm' ε z) (Gm'' ε z u) u := by
  have h1 : HasDerivAt (fun u : ℝ => -2 / u ^ 3) (6 / u ^ 4) u := by
    refine ((hasDerivAt_const u (-2 : ℝ)).div (hasDerivAt_pow 3 u)
      (pow_ne_zero 3 hu)).congr_deriv ?_
    field_simp
    ring
  have h2 : HasDerivAt (fun u : ℝ => ε⁻¹ / u) (-ε⁻¹ / u ^ 2) u := by
    refine ((hasDerivAt_const u ε⁻¹).div (hasDerivAt_id' u) hu).congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (fun u : ℝ => -z / (ε * u ^ 2)) (2 * z / (ε * u ^ 3)) u := by
    refine ((hasDerivAt_const u (-z)).div ((hasDerivAt_pow 2 u).const_mul ε)
      (mul_ne_zero hε (pow_ne_zero 2 hu))).congr_deriv ?_
    field_simp
    ring
  exact h1.prodMk (h2.prodMk h3)

/-! ### The radius along a horizontal coordinate line -/

/-- `R(t) = √(r² + 2βt + t²)`: the cylindrical radius along `x + t e_i`, `β = x_i`, `i = 0, 1`. -/
def lineR (r β t : ℝ) : ℝ := √(r ^ 2 + 2 * β * t + t ^ 2)

/-- `R'(t) = (β + t)/R(t)`. -/
def lineR' (r β t : ℝ) : ℝ := (β + t) / lineR r β t

theorem lineR_zero {r β : ℝ} (hr : 0 ≤ r) : lineR r β 0 = r := by
  simp [lineR, Real.sqrt_sq hr]

theorem lineR'_zero {r β : ℝ} (hr : 0 ≤ r) : lineR' r β 0 = β / r := by
  simp [lineR', lineR_zero hr]

theorem hasDerivAt_lineR {r β : ℝ} (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (lineR r β) (lineR' r β t) t := by
  have hcont : Continuous fun t : ℝ => r ^ 2 + 2 * β * t + t ^ 2 := by fun_prop
  have h0 : (0 : ℝ) < r ^ 2 + 2 * β * 0 + 0 ^ 2 := by simp; positivity
  filter_upwards [(hcont.tendsto 0).eventually_const_lt h0] with t ht
  have h1 : HasDerivAt (fun t : ℝ => r ^ 2 + 2 * β * t + t ^ 2) (2 * β + 2 * t) t := by
    refine ((((hasDerivAt_id' t).const_mul (2 * β)).const_add (r ^ 2)).add
      (hasDerivAt_pow 2 t)).congr_deriv ?_
    simp
  refine (h1.sqrt ht.ne').congr_deriv ?_
  have hs : 0 < √(r ^ 2 + 2 * β * t + t ^ 2) := Real.sqrt_pos.2 ht
  simp only [lineR', lineR]
  field_simp

theorem hasDerivAt_lineR' {r β : ℝ} (hr : 0 < r) :
    HasDerivAt (lineR' r β) ((r ^ 2 - β ^ 2) / r ^ 3) 0 := by
  have hR := (hasDerivAt_lineR (β := β) hr).self_of_nhds
  have hR0 := lineR_zero (β := β) hr.le
  refine (((hasDerivAt_id' (0 : ℝ)).const_add β).div hR
    (by rw [hR0]; exact hr.ne')).congr_deriv ?_
  rw [hR0, lineR'_zero hr.le]
  field_simp
  ring

/-! ### First and second derivatives along the coordinate lines -/

section Lines

variable {b : Profile → ℝ} {r β ε τ z : ℝ}

/-- The `β`-free part of the second derivative along a horizontal line. -/
def radAlpha (b : Profile → ℝ) (ε τ z r : ℝ) : ℝ :=
  -b (Gm ε τ z r) / r ^ 3 + fderiv ℝ b (Gm ε τ z r) (Gm' ε z r) / r ^ 2

/-- The `β²` coefficient of the second derivative along a horizontal line. -/
def radGamma (b : Profile → ℝ) (ε τ z r : ℝ) : ℝ :=
  3 * b (Gm ε τ z r) / r ^ 5 - 3 * fderiv ℝ b (Gm ε τ z r) (Gm' ε z r) / r ^ 4 +
    (fderiv ℝ (fderiv ℝ b) (Gm ε τ z r) (Gm' ε z r) (Gm' ε z r) +
      fderiv ℝ b (Gm ε τ z r) (Gm'' ε z r)) / r ^ 3

/-- First derivative along the horizontal line `x + t e_i`, `β = x_i`. -/
theorem radial_first (hr : 0 < r) (hε : ε ≠ 0) (hb : DifferentiableAt ℝ b (Gm ε τ z r)) :
    deriv (fun t => (lineR r β t)⁻¹ * b (Gm ε τ z (lineR r β t))) 0 =
      β * radAlpha b ε τ z r := by
  have hR := (hasDerivAt_lineR (β := β) hr).self_of_nhds
  have hR0 := lineR_zero (β := β) hr.le
  have hA : HasDerivAt (fun t => (lineR r β t)⁻¹) (-(lineR' r β 0) / (lineR r β 0) ^ 2) 0 :=
    hR.inv (by rw [hR0]; exact hr.ne')
  have hc : HasDerivAt (fun t => Gm ε τ z (lineR r β t)) (lineR' r β 0 • Gm' ε z (lineR r β 0))
      0 := (hasDerivAt_Gm hε (by rw [hR0]; exact hr.ne')).scomp 0 hR
  rw [deriv_mul_comp hA hc (by rw [hR0]; exact hb)]
  rw [hR0, lineR'_zero hr.le, map_smul, smul_eq_mul, radAlpha]
  field_simp

/-- Second derivative along the horizontal line `x + t e_i`, `β = x_i`: `α + β² γ`. -/
theorem radial_second (hr : 0 < r) (hε : ε ≠ 0) (hb : ContDiffAt ℝ 2 b (Gm ε τ z r)) :
    deriv (deriv fun t => (lineR r β t)⁻¹ * b (Gm ε τ z (lineR r β t))) 0 =
      radAlpha b ε τ z r + β ^ 2 * radGamma b ε τ z r := by
  have hR := hasDerivAt_lineR (β := β) hr
  have hR' := hasDerivAt_lineR' (β := β) hr
  have hR0 := lineR_zero (β := β) hr.le
  have hne : ∀ᶠ u in 𝓝 (lineR r β 0), u ≠ 0 := by
    rw [hR0]; exact eventually_ne_nhds hr.ne'
  have hA := hasDerivAt_comp_eventually (h := fun u : ℝ => u⁻¹) (h' := fun u => -(u ^ 2)⁻¹)
    (hne.mono fun u hu => hasDerivAt_inv hu) hR
  have hinv' : HasDerivAt (fun u : ℝ => -(u ^ 2)⁻¹) (2 / r ^ 3) (lineR r β 0) := by
    rw [hR0]
    refine ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne')).neg.congr_deriv ?_
    field_simp
    ring
  have hA' := hasDerivAt_comp_deriv hinv' hR hR'
  have hc := hasDerivAt_comp_eventually (h := Gm ε τ z) (h' := Gm' ε z)
    (hne.mono fun u hu => hasDerivAt_Gm hε hu) hR
  have hGm' : HasDerivAt (Gm' ε z) (Gm'' ε z r) (lineR r β 0) := by
    rw [hR0]; exact hasDerivAt_Gm' hε hr.ne'
  have hc' := hasDerivAt_comp_deriv hGm' hR hR'
  rw [deriv_deriv_mul_comp hA hA' hc hc' (by rw [hR0]; exact hb)]
  simp only [hR0, lineR'_zero hr.le, smul_eq_mul, map_add, map_smul,
    smul_apply, radAlpha, radGamma]
  field_simp
  ring

/-- The vertical direction `(0, 0, 1/(εr))` of the chart. -/
theorem hasDerivAt_Gm_vertical (ε τ z r t : ℝ) :
    HasDerivAt (fun t => Gm ε τ (z + t) r) ((0 : ℝ), (0 : ℝ), 1 / (ε * r)) t := by
  have h3 : HasDerivAt (fun t : ℝ => (z + t) / (ε * r)) (1 / (ε * r)) t :=
    ((hasDerivAt_id' t).const_add z).div_const (ε * r)
  exact (hasDerivAt_const t _).prodMk ((hasDerivAt_const t _).prodMk h3)

/-- First derivative along the vertical line `x + t e_2`. -/
theorem vertical_first (hb : DifferentiableAt ℝ b (Gm ε τ z r)) :
    deriv (fun t => r⁻¹ * b (Gm ε τ (z + t) r)) 0 =
      r⁻¹ * fderiv ℝ b (Gm ε τ z r) ((0 : ℝ), (0 : ℝ), 1 / (ε * r)) := by
  rw [deriv_mul_comp (hasDerivAt_const (0 : ℝ) r⁻¹) (hasDerivAt_Gm_vertical ε τ z r 0)
    (by simpa using hb)]
  simp

/-- Second derivative along the vertical line `x + t e_2`. -/
theorem vertical_second (hb : ContDiffAt ℝ 2 b (Gm ε τ z r)) :
    deriv (deriv fun t => r⁻¹ * b (Gm ε τ (z + t) r)) 0 =
      r⁻¹ * fderiv ℝ (fderiv ℝ b) (Gm ε τ z r) ((0 : ℝ), (0 : ℝ), 1 / (ε * r))
        ((0 : ℝ), (0 : ℝ), 1 / (ε * r)) := by
  rw [deriv_deriv_mul_comp (A' := fun _ => (0 : ℝ)) (A'' := 0)
    (c' := fun _ => ((0 : ℝ), (0 : ℝ), 1 / (ε * r))) (c'' := 0)
    (Eventually.of_forall fun t => hasDerivAt_const t r⁻¹) (hasDerivAt_const 0 0)
    (Eventually.of_forall fun t => hasDerivAt_Gm_vertical ε τ z r t) (hasDerivAt_const 0 _)
    (by simpa using hb)]
  simp

/-- The phase derivative: only `q` moves, at rate `1/(2ε)`. -/
theorem time_first (hb : DifferentiableAt ℝ b (Gm ε τ z r)) :
    deriv (fun σ => r⁻¹ * b (Gm ε σ z r)) τ =
      r⁻¹ * fderiv ℝ b (Gm ε τ z r) ((0 : ℝ), 1 / (2 * ε), (0 : ℝ)) := by
  have h2 : HasDerivAt (fun σ : ℝ => ε⁻¹ * Real.log r + σ / (2 * ε)) (1 / (2 * ε)) τ :=
    ((hasDerivAt_id' τ).div_const (2 * ε)).const_add _
  have hc : HasDerivAt (fun σ => Gm ε σ z r) ((0 : ℝ), 1 / (2 * ε), (0 : ℝ)) τ :=
    (hasDerivAt_const τ _).prodMk (h2.prodMk (hasDerivAt_const τ _))
  rw [deriv_mul_comp (hasDerivAt_const τ r⁻¹) hc hb]
  simp

end Lines

/-! ### The conjugation identity -/

section Identity

variable {b : Profile → ℝ}

theorem radius_pos {x : Space} (hx : radius x ≠ 0) : 0 < radius x :=
  lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)

theorem radius_sq (x : Space) : x 0 ^ 2 + x 1 ^ 2 = radius x ^ 2 := by
  rw [radius, Real.sq_sqrt (by positivity)]

theorem radius_line0 (x : Space) (t : ℝ) :
    radius (x + t • coordinateVector 0) = lineR (radius x) (x 0) t := by
  simp only [radius, lineR, coordinateVector, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  simp
  ring

theorem radius_line1 (x : Space) (t : ℝ) :
    radius (x + t • coordinateVector 1) = lineR (radius x) (x 1) t := by
  simp only [radius, lineR, coordinateVector, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  rw [Real.sq_sqrt (by positivity)]
  congr 1
  simp
  ring

theorem radius_line2 (x : Space) (t : ℝ) : radius (x + t • coordinateVector 2) = radius x := by
  simp [radius, coordinateVector]

/-- The slice `x ↦ U(x, τ)` of the lift is `C²` off the axis. -/
theorem contDiffAt_liftU_slice {ε : ℝ} (hε : ε ≠ 0) {x : Space} {τ : ℝ} (hx : radius x ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    ContDiffAt ℝ 2 (fun y => liftU ε b (y, τ)) x := by
  have hrad : ContDiffAt ℝ 2 radius x := by
    have hin : ContDiff ℝ 2 fun y : Space => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
    have hne : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
      rw [radius_sq]; exact pow_ne_zero 2 hx
    exact hin.contDiffAt.sqrt hne
  have hz : ContDiffAt ℝ 2 (fun y : Space => y 2) x := by fun_prop
  have hG : ContDiffAt ℝ 2 (fun y => Gm ε τ (y 2) (radius y)) x := by
    have h1 : ContDiffAt ℝ 2 (fun y => (radius y ^ 2)⁻¹) x :=
      (hrad.pow 2).inv (pow_ne_zero 2 hx)
    have h2 : ContDiffAt ℝ 2 (fun y => ε⁻¹ * Real.log (radius y) + τ / (2 * ε)) x :=
      (contDiffAt_const.mul (hrad.log hx)).add contDiffAt_const
    have h3 : ContDiffAt ℝ 2 (fun y : Space => y 2 / (ε * radius y)) x :=
      hz.div (contDiffAt_const.mul hrad) (mul_ne_zero hε hx)
    exact h1.prodMk (h2.prodMk h3)
  exact (hrad.inv hx).mul (hb.comp x hG)

/-- **The conjugation identity** (tex lines 3316–3347): for `b` of class `C²` at the chart
point of `(x, τ)`, `x` off the axis,
`(ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ)(a b(s,q,η)) = a (A_ε b)(s,q,η)`. -/
theorem outerGen_liftU {ν ε : ℝ} (hε : ε ≠ 0) {x : Space} {τ : ℝ} (hx : radius x ≠ 0)
    (hb : ContDiffAt ℝ 2 b (chart ε (x, τ))) :
    outerGen ν ε (liftU ε b) (x, τ) = liftA x * Aeps ν ε b (chart ε (x, τ)) := by
  have hU := contDiffAt_liftU_slice hε hx hb
  have hU1 : DifferentiableAt ℝ (fun y => liftU ε b (y, τ)) x :=
    hU.differentiableAt (by norm_num)
  have hr := radius_pos hx
  have hr2 := radius_sq x
  have hb' : ContDiffAt ℝ 2 b (Gm ε τ (x 2) (radius x)) := hb
  have hb1 : DifferentiableAt ℝ b (Gm ε τ (x 2) (radius x)) := hb'.differentiableAt (by norm_num)
  have hl0 : (fun t : ℝ => liftU ε b (x + t • coordinateVector 0, τ)) =
      fun t => (lineR (radius x) (x 0) t)⁻¹ * b (Gm ε τ (x 2) (lineR (radius x) (x 0) t)) := by
    funext t
    rw [liftU_eq, radius_line0]
    simp [coordinateVector]
  have hl1 : (fun t : ℝ => liftU ε b (x + t • coordinateVector 1, τ)) =
      fun t => (lineR (radius x) (x 1) t)⁻¹ * b (Gm ε τ (x 2) (lineR (radius x) (x 1) t)) := by
    funext t
    rw [liftU_eq, radius_line1]
    simp [coordinateVector]
  have hl2 : (fun t : ℝ => liftU ε b (x + t • coordinateVector 2, τ)) =
      fun t => (radius x)⁻¹ * b (Gm ε τ (x 2 + t) (radius x)) := by
    funext t
    rw [liftU_eq, radius_line2]
    simp [coordinateVector]
  have hlap : spatialLap (liftU ε b) (x, τ) =
      2 * radAlpha b ε τ (x 2) (radius x) + radius x ^ 2 * radGamma b ε τ (x 2) (radius x) +
        (radius x)⁻¹ * fderiv ℝ (fderiv ℝ b) (Gm ε τ (x 2) (radius x))
          ((0 : ℝ), (0 : ℝ), 1 / (ε * radius x)) ((0 : ℝ), (0 : ℝ), 1 / (ε * radius x)) := by
    simp only [spatialLap, Fin.sum_univ_three]
    rw [secondPartial_eq_deriv_deriv hU, secondPartial_eq_deriv_deriv hU,
      secondPartial_eq_deriv_deriv hU, hl0, hl1, hl2, radial_second hr hε hb',
      radial_second hr hε hb', vertical_second hb']
    linear_combination radGamma b ε τ (x 2) (radius x) * hr2
  have heul : (∑ i : Fin 3, (x, τ).1 i * spatialPartial (liftU ε b) i (x, τ)) =
      radius x ^ 2 * radAlpha b ε τ (x 2) (radius x) +
        x 2 * ((radius x)⁻¹ * fderiv ℝ b (Gm ε τ (x 2) (radius x))
          ((0 : ℝ), (0 : ℝ), 1 / (ε * radius x))) := by
    simp only [spatialPartial, Fin.sum_univ_three]
    rw [fderiv_eq_deriv_line hU1, fderiv_eq_deriv_line hU1, fderiv_eq_deriv_line hU1,
      hl0, hl1, hl2, radial_first hr hε hb1, radial_first hr hε hb1, vertical_first hb1]
    linear_combination radAlpha b ε τ (x 2) (radius x) * hr2
  have htime : timePartial (liftU ε b) (x, τ) =
      (radius x)⁻¹ * fderiv ℝ b (Gm ε τ (x 2) (radius x)) ((0 : ℝ), 1 / (2 * ε), (0 : ℝ)) :=
    time_first hb1
  have hsym := hb'.isSymmSndFDerivAt (by simp)
  rw [outerGen, hlap, heul, htime, chart_eq_Gm, Aeps_expand ν ε hb', liftU_eq]
  simp only [radAlpha, radGamma, liftA, Gm', Gm'', clm_apply_triple,
    add_apply, smul_apply, smul_eq_mul,
    hsym eQ eS, hsym eEta eS, hsym eEta eQ]
  set p := Gm ε τ (x 2) (radius x) with hp
  have hp1 : p.1 = (radius x ^ 2)⁻¹ := rfl
  have hp3 : p.2.2 = x 2 / (ε * radius x) := rfl
  rw [hp1, hp3]
  set D1 := fderiv ℝ b p
  set D2 := fderiv ℝ (fderiv ℝ b) p
  set r := radius x
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  ring

end Identity

end UnforcedLeray.B0221
