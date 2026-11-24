import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.Defs

/-!
# `PartIII-a:T21/2/2/2/2/3`: the chain rule `dr/dζ = -a²`, `∂_ζ d = d/(2θ)` (SP 2860)

With `z = z_s - ζ` (`z_s = movingZ ν s`), `D = 1 - ν z`, one has `a(r) = 1/D` for `r = revAge ν s ζ`,
`d = c√D`, `θ = D/ν` and `dr/dζ = -(1/D)² = -a²`, `∂_ζ d = cν/(2√D) = d/(2θ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `1 - ν z > 0` at reverse moving time `ζ > 0` (since `z < z_s` and `ν z_s < 1`). -/
theorem reyD_pos {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    0 < 1 - ν * (movingZ ν s - ζ) := by
  have hνs : 0 ≤ ν * s := mul_nonneg hν.le hs
  have h1 : 0 < 1 + ν * s := by linarith
  have hM : ν * (s / (1 + ν * s)) < 1 := by
    rw [← mul_div_assoc, div_lt_one h1]
    linarith
  have e : 1 - ν * (movingZ ν s - ζ) = (1 - ν * (s / (1 + ν * s))) + ν * ζ := by
    unfold movingZ clockA
    ring
  have hp : 0 < ν * ζ := mul_pos hν hζ
  rw [e]
  linarith

/-- `a(r) = 1/(1 - ν z)` at reverse moving time `ζ > 0`. -/
theorem reyClockA_eq {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    clockA ν (revAge ν s ζ) = (1 - ν * (movingZ ν s - ζ))⁻¹ := by
  have hD := (reyD_pos hν hs hζ).ne'
  unfold revAge ageOfZ clockA
  field_simp
  ring

/-- `dr/dζ = -a(r)²` (SP 2860). -/
theorem reyRevAge_hasDeriv {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    HasDerivAt (revAge ν s) (-(clockA ν (revAge ν s ζ)) ^ 2) ζ := by
  have hD := reyD_pos hν hs hζ
  have hg : HasDerivAt (fun x => movingZ ν s - x) (-1) ζ :=
    (hasDerivAt_id' ζ).const_sub (movingZ ν s)
  have hden : HasDerivAt (fun x => 1 - ν * (movingZ ν s - x)) (-(ν * -1)) ζ :=
    (hg.const_mul ν).const_sub 1
  have hq := hg.fun_div hden hD.ne'
  have hfun : revAge ν s = fun x => (movingZ ν s - x) / (1 - ν * (movingZ ν s - x)) := rfl
  rw [reyClockA_eq hν hs hζ, hfun]
  refine HasDerivAt.congr_deriv hq ?_
  field_simp
  ring

/-- `d(ζ) = c√(1 - ν z)` near `ζ`, and `∂_ζ d = d/(2θ)` (SP 2857, 2860). -/
theorem reyRevCell_hasDeriv {ν c s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    HasDerivAt (revCell ν c s) (revCell ν c s ζ / (2 * revTheta ν s ζ)) ζ := by
  have hD := reyD_pos hν hs hζ
  have hg : HasDerivAt (fun x => movingZ ν s - x) (-1) ζ :=
    (hasDerivAt_id' ζ).const_sub (movingZ ν s)
  have hden : HasDerivAt (fun x => 1 - ν * (movingZ ν s - x)) (-(ν * -1)) ζ :=
    (hg.const_mul ν).const_sub 1
  have hsq := (hden.sqrt hD.ne').const_mul c
  have heq : revCell ν c s =ᶠ[𝓝 ζ] fun x => c * Real.sqrt (1 - ν * (movingZ ν s - x)) := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hζ) ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hDx := reyD_pos hν hs hxpos
    unfold revCell cellLen
    rw [reyClockA_eq hν hs hxpos, Real.sqrt_inv, div_inv_eq_mul]
  have hder := hsq.congr_of_eventuallyEq heq
  refine HasDerivAt.congr_deriv hder ?_
  have hDz := reyD_pos hν hs hζ
  have hrc : revCell ν c s ζ = c * Real.sqrt (1 - ν * (movingZ ν s - ζ)) := by
    unfold revCell cellLen
    rw [reyClockA_eq hν hs hζ, Real.sqrt_inv, div_inv_eq_mul]
  have hth : revTheta ν s ζ = (1 - ν * (movingZ ν s - ζ)) / ν := by
    unfold revTheta clockTheta
    rw [reyClockA_eq hν hs hζ]
    field_simp
  rw [hrc, hth]
  have hsqD := Real.sq_sqrt hDz.le
  set q := Real.sqrt (1 - ν * (movingZ ν s - ζ)) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hDz
  rw [← hsqD]
  field_simp

/-- **R3: chain rule** (SP 2860): `dr/dζ = -a(r)²` and `∂_ζ d = d/(2θ)`, for `ζ ∈ (0, Δz)`. -/
theorem reyChain : ReyChain := by
  intro ν hν t s ht hts ζ hζ
  have hs : 0 ≤ s := by linarith
  have hζ0 : 0 < ζ := hζ.1
  exact ⟨reyRevAge_hasDeriv hν hs hζ0, reyRevCell_hasDeriv hν hs hζ0⟩

end UnforcedLeray.Short.IIIa.E0
