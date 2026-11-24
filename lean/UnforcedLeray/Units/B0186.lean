import UnforcedLeray.Units.B0185
import UnforcedLeray.Lib.Axisymmetric.PhysicalChart
import UnforcedLeray.Lib.Axisymmetric.Tensor
import UnforcedLeray.Lib.AxisymmetricB.DSS
import UnforcedLeray.Lib.AxisymmetricB.Range

/-!
# B0186 `eq:m3-ring-lift`: the similarity chart and the complete solenoidal raw lift `U_raw`

Blueprint unit B0186, label `eq:m3-ring-lift`, `paper/main.tex` lines 2070–2098
(Section `sec:train`, "Actual train, raw lift, and coefficient tails").

Statement in words (tex lines 2070–2081, 2094–2095). With `R = ε⁻¹`, the physical chart is
`s = (R/r)² t`, `ξ = R log(r/R)`, `η = R x₃/r`. In similarity variables `y = x/√t`,
`τ = log t`, with cylindrical radius `ϱ = ϱ(y)`, the chart and the complete solenoidal lift are
`s = R²/ϱ²`, `ξ = Rτ/2 − (R/2) log s`, `η = R y₃/ϱ`, `K_age = η∂_η + 2s∂_s`,
`H = (1 − K_age)ψ`, `U_raw = √s [v₁ e_r + (v₂ + εH) e_z]`.
The physical stream is `ϱψ`, the raw pressure is `s p`, and the period is `P = 2εc`.
Passing to the order `(r, ϑ, z)` permutes vectors, tensors and derivatives together, as in
`eq:stress-setup:3.2b`. Here `v = ∇^⊥_z ψ = (−ψ_η, ψ_ξ)` is the train velocity with its
decaying stream `ψ` (tex lines 2049–2051, unit B0140), `p` its pressure, and the train is
`c`-periodic in `ξ` (tex line 2051).
Proof outline (blueprint): definitions; `√t u` is the similarity velocity and
`√t a_r = R/r_y = √s`.

Reuse. The similarity chart is the library's `Axi.chart R τ y = (s, (ξ, η))`
(`Lib/Axisymmetric/RingChart.lean`, profile variables in the order `(s, (ξ, η))`, the order
used by every consumer of `Axi.Nv`); the lift `U_raw` is the library ring lift
`Axi.Nv R b = √s (b_r e_r + b_z e_z)` of the profile `b = (v₁, v₂ + εH)`; the raw pressure
`s p` is `Axi.Np R p`; `ε = ringEps R = R⁻¹` is B0184's. The physical lift of B0185
(`B0185.liftVelocity`, `B0185.physicalStream`, `B0185.liftPressure`) uses B0184's profile
order `(q, (η, s))`, `q = ξ`; `toProfile` is the reordering, a continuous linear
equivalence, so derivatives transfer without any differentiability hypothesis.

Contents.
* Definitions: `physChart` (physical chart in the order `(s, (ξ, η))`), `toProfile`,
  `ageOp` (`K_age`), `ageDefect` (`H`), `perpGrad` (`∇^⊥ψ`), `rawProfile` (`(v₁, v₂ + εH)`),
  `Uraw`, `period` (`P = 2εc`), `IsCellPeriodic`, `simAgeDomain` (`{s > 0}`), `toRThetaZ`.
* Charts: `physChart_eq`, `chart_eq` (the formulas of tex 2070–2075),
  `chart_similarity_eq_physChart` (the similarity chart at `y = x/√t`, `τ = log t` is the
  physical chart), `sqrt_mul_radialScale` (`√t a_r = R/r_y = √s`).
* The lift: `Uraw_apply`, `Uraw_eq_streamLift` (the Stokes stream of `U_raw` is `ϱψ`),
  `divergence_Uraw_eq_zero` (complete solenoidal lift), `similarity_velocity`
  (`√t u(x, t) = U_raw(log t, x/√t)` for B0185's physical lift `u`),
  `physicalStream_similarity` (`𝒫/√t = ϱψ`), `rawPressure_similarity` (`t p_raw = s p`).
* Period: `period_eq`, `chart_add_period`, `Uraw_add_period`, `Np_add_period`.
* The order `(r, ϑ, z)`: `Uraw_eq_frame_sum`, `inner_Uraw_eΦ` (no `e_ϑ` component),
  `isAxisymmetricNoSwirl_Uraw`.
* `m3_ring_lift`: the unit in one statement.

Hypotheses. `R > 0` (the manuscript has `R = ε⁻¹` with `ε > 0` small; `R ≥ 2` in
tex line 2838 is stronger). The stream `ψ` is assumed of class `C²` on the open age domain
`{s > 0}` only where derivatives of the lift are taken (divergence), and differentiable there
for the stream identity; the manuscript's train is smooth for `s ≥ 0`. The velocity `v` enters
only through `v = ∇^⊥ψ` on `{s > 0}` (B0140, tex line 2051). Periodicity is assumed only on
`{s > 0}`, the image of the chart off the axis.

Junk values. On the axis `ϱ = 0`, Lean gives `age R y = R²/0 = 0` and `√0 = 0`, so `U_raw`
and `s p` are `0` there; every chart identity is stated off the axis (`x ∉ Axi.axis`) and for
`t > 0` (`√t = 0` and `log t = log |t|` for `t ≤ 0` would be junk). `fderiv` is `0` at
non-differentiable points; the stream identity and the divergence assume differentiability.

Not covered here (other units). The body residual `eq:m3-ring-residual` (tex 2082–2093) is
unit B0189; the permutation `P_swap` of `eq:stress-setup:3.2b` (tex 8765–8770) is unit B0732,
a removed forward reference: here the order `(r, ϑ, z)` is the library frame
`Axi.frame = (e_r, e_ϑ, e_z)` (`Lib/Axisymmetric/Tensor.lean`) and the vector statement is
`Uraw_eq_frame_sum`. The period-average measure `dξ/c` (tex 2096) is notation used by B0219
and B0417 (`Lib/AxisymmetricB/Lift.lean`, `ageμ`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0186

open Set Filter Topology
open UnforcedLeray.RingLift UnforcedLeray.B0184

/-! ## Profile variables and the reordering to B0184's order -/

/-- Similarity profile variables `(s, (ξ, η))`, the order of `Axi.chart` (tex 2073–2075). -/
abbrev SimPoint := ℝ × (ℝ × ℝ)

/-- The open age domain `{s > 0}` of similarity profile space: the image of the chart off the
axis (`Axi.age_pos`). -/
def simAgeDomain : Set SimPoint := {m | 0 < m.1}

theorem isOpen_simAgeDomain : IsOpen simAgeDomain :=
  isOpen_lt continuous_const continuous_fst

/-- The reordering `(s, (ξ, η)) ↦ (ξ, (η, s))` from the similarity order to B0184's profile
order `(q, (η, s))` (with `q = ξ`, tex lines 2070 and 2842). -/
def toProfile : SimPoint ≃L[ℝ] ProfilePoint :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ (ℝ × ℝ)).trans (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ)

@[simp] theorem toProfile_apply (m : SimPoint) : toProfile m = (m.2.1, (m.2.2, m.1)) := rfl

@[simp] theorem toProfile_symm_apply (x : ProfilePoint) :
    toProfile.symm x = (x.2.2, (x.1, x.2.1)) := rfl

/-! ## The charts (tex 2070–2075) -/

/-- The physical chart `(r, z, t) ↦ (s, (ξ, η)) = ((R/r)² t, (R log(r/R), R z/r))`
(tex lines 2070–2071), in the similarity order; it is B0184's `profileChart` reordered. -/
def physChart (R r z t : ℝ) : SimPoint :=
  (ageCoordinate R r t, (logRadius R r, transverseCoordinate R r z))

/-- The physical chart has the manuscript's formulas `s = (R/r)² t`, `ξ = R log(r/R)`,
`η = R x₃/r` (tex lines 2070–2071). -/
theorem physChart_eq (R r z t : ℝ) :
    physChart R r z t = ((R / r) ^ 2 * t, (R * Real.log (r / R), R * z / r)) := by
  simp only [physChart, ageCoordinate, logRadius, transverseCoordinate, radialScale,
    Prod.mk.injEq, true_and]
  ring

theorem toProfile_physChart (R r z t : ℝ) : toProfile (physChart R r z t) = profileChart R r z t :=
  rfl

theorem toProfile_symm_profileChart (R r z t : ℝ) :
    toProfile.symm (profileChart R r z t) = physChart R r z t := rfl

/-- The similarity chart has the manuscript's formulas `s = R²/ϱ²`, `ξ = Rτ/2 − (R/2) log s`,
`η = R y₃/ϱ` (`eq:m3-ring-lift`, tex lines 2073–2076). -/
theorem chart_eq (R τ : ℝ) (y : Space) :
    Axi.chart R τ y = (R ^ 2 / Axi.ϱ y ^ 2,
      (R * τ / 2 - (R / 2) * Real.log (R ^ 2 / Axi.ϱ y ^ 2), R * y 2 / Axi.ϱ y)) := rfl

/-- **The similarity chart is the physical chart** (tex lines 2070–2076). For `R, t > 0` and `x`
off the axis, the similarity chart at `y = x/√t`, `τ = log t` is the physical chart at
`r = ϱ(x)`, `z = x₃`. -/
theorem chart_similarity_eq_physChart {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {x : Space}
    (hx : x ∉ Axi.axis) :
    Axi.chart R (Real.log t) ((√t)⁻¹ • x) = physChart R (Axi.ϱ x) (x 2) t :=
  Axi.chart_similarity hR ht hx

/-- `√t a_r = √s` in physical variables (blueprint proof outline of B0186). -/
theorem sqrt_mul_radialScale {R r t : ℝ} (hR : 0 < R) (hr : 0 < r) :
    √t * radialScale R r = √(ageCoordinate R r t) := by
  rw [ageCoordinate, radialScale, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hR hr).le,
    mul_comm]

/-- `√t a_r = R/r_y = √s` with `r_y = ϱ(x/√t)` (blueprint proof outline of B0186). -/
theorem sqrt_mul_radialScale_eq_sqrt_age {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {x : Space}
    (hx : x ∉ Axi.axis) :
    √t * radialScale R (Axi.ϱ x) = R / Axi.ϱ ((√t)⁻¹ • x) ∧
      √t * radialScale R (Axi.ϱ x) = √(Axi.age R ((√t)⁻¹ • x)) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hρ := Axi.ϱ_pos hx
  have hϱ : Axi.ϱ ((√t)⁻¹ • x) = (√t)⁻¹ * Axi.ϱ x := by
    rw [Axi.ϱ_smul, abs_of_pos (inv_pos.2 hst)]
  have hy : (√t)⁻¹ • x ∉ Axi.axis := by
    rw [Axi.mem_axis_iff, hϱ]
    exact (mul_pos (inv_pos.2 hst) hρ).ne'
  have h1 : √t * radialScale R (Axi.ϱ x) = R / Axi.ϱ ((√t)⁻¹ • x) := by
    rw [hϱ, radialScale]
    field_simp
  exact ⟨h1, by rw [h1, Axi.sqrt_age hR hy]⟩

/-! ## Transfer of derivatives through the reordering -/

theorem fderiv_comp_toProfile_symm (ψ : SimPoint → ℝ) (x w : ProfilePoint) :
    fderiv ℝ (ψ ∘ toProfile.symm) x w = fderiv ℝ ψ (toProfile.symm x) (toProfile.symm w) := by
  rw [toProfile.symm.comp_right_fderiv]
  rfl

theorem partialQ_comp (ψ : SimPoint → ℝ) (x : ProfilePoint) :
    partialQ (ψ ∘ toProfile.symm) x = Axi.dQ ψ (toProfile.symm x) := by
  rw [partialQ, fderiv_comp_toProfile_symm]
  rfl

theorem partialEta_comp (ψ : SimPoint → ℝ) (x : ProfilePoint) :
    partialEta (ψ ∘ toProfile.symm) x = Axi.dEta ψ (toProfile.symm x) := by
  rw [partialEta, fderiv_comp_toProfile_symm]
  rfl

theorem partialAge_comp (ψ : SimPoint → ℝ) (x : ProfilePoint) :
    partialAge (ψ ∘ toProfile.symm) x = Axi.dS ψ (toProfile.symm x) := by
  rw [partialAge, fderiv_comp_toProfile_symm]
  rfl

/-! ## `K_age`, `H`, `∇^⊥ψ` and the lift profile (tex 2076–2077) -/

/-- The age operator `K_age = η∂_η + 2s∂_s` at `(s, (ξ, η))` (tex line 2076). -/
def ageOp (ψ : SimPoint → ℝ) (m : SimPoint) : ℝ :=
  m.2.2 * Axi.dEta ψ m + 2 * m.1 * Axi.dS ψ m

/-- `H = (1 − K_age)ψ` (tex line 2077). -/
def ageDefect (ψ : SimPoint → ℝ) (m : SimPoint) : ℝ := ψ m - ageOp ψ m

/-- The planar field `∇^⊥_z ψ = (−ψ_η, ψ_ξ)` of a stream `ψ` (tex line 2049, B0140), as a
meridional vector `(r, z)`. -/
def perpGrad (ψ : SimPoint → ℝ) (m : SimPoint) : Axi.Merid :=
  (-Axi.dEta ψ m) • Axi.m0 + Axi.dQ ψ m • Axi.m1

/-- The normalized profile `(v₁, v₂ + εH)`, `ε = R⁻¹`, of `U_raw` (tex line 2077), in the
meridional order `(r, z)`. -/
def rawProfile (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (m : SimPoint) :
    Axi.Merid :=
  v m 0 • Axi.m0 + (v m 1 + ringEps R * ageDefect ψ m) • Axi.m1

/-- **The raw lift** `U_raw(τ, y) = √s [v₁ e_r + (v₂ + εH) e_z]` at the chart point
`(s, (ξ, η)) = Axi.chart R τ y` (`eq:m3-ring-lift`, tex lines 2073–2077): the library ring lift
`Axi.Nv` of `rawProfile`. -/
def Uraw (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) : ℝ → Space → Space :=
  Axi.Nv R (rawProfile R v ψ)

/-- The similarity period `P = 2εc`, `ε = R⁻¹` (tex line 2079). -/
def period (R c : ℝ) : ℝ := 2 * ringEps R * c

/-- `c`-periodicity in the cylinder variable `ξ` on the age domain `s > 0` (tex line 2051:
"The field is `c`-periodic"). -/
def IsCellPeriodic {E : Type*} (c : ℝ) (f : SimPoint → E) : Prop :=
  ∀ s, 0 < s → ∀ ξ η, f (s, (ξ + c, η)) = f (s, (ξ, η))

/-- Components in the order `(r, ϑ, z)` (tex lines 2094–2095): `(b_r, b_z) ↦ (b_r, 0, b_z)`. -/
def toRThetaZ (b : Axi.Merid) : Fin 3 → ℝ := ![b 0, 0, b 1]

theorem ringEps_inv (ε : ℝ) : ringEps ε⁻¹ = ε := inv_inv ε

@[simp] theorem perpGrad_zero (ψ : SimPoint → ℝ) (m : SimPoint) :
    perpGrad ψ m 0 = -Axi.dEta ψ m := by
  simp [perpGrad]

@[simp] theorem perpGrad_one (ψ : SimPoint → ℝ) (m : SimPoint) :
    perpGrad ψ m 1 = Axi.dQ ψ m := by
  simp [perpGrad]

@[simp] theorem rawProfile_zero (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ)
    (m : SimPoint) : rawProfile R v ψ m 0 = v m 0 := by
  simp [rawProfile]

@[simp] theorem rawProfile_one (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ)
    (m : SimPoint) : rawProfile R v ψ m 1 = v m 1 + ringEps R * ageDefect ψ m := by
  simp [rawProfile]

/-- `(v₁, v₂ + εH) = v + εH e_z`. -/
theorem rawProfile_eq (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (m : SimPoint) :
    rawProfile R v ψ m = v m + (ringEps R * ageDefect ψ m) • Axi.m1 := by
  ext i
  fin_cases i <;> simp [rawProfile]

/-- `H = ψ − ηψ_η − 2sψ_s` unfolded. -/
theorem ageDefect_apply (ψ : SimPoint → ℝ) (m : SimPoint) :
    ageDefect ψ m = ψ m - (m.2.2 * Axi.dEta ψ m + 2 * m.1 * Axi.dS ψ m) := rfl

/-- B0184's `K = η∂_η + 2s∂_s` is `K_age` after reordering. -/
theorem ageOperator_comp (ψ : SimPoint → ℝ) (x : ProfilePoint) :
    ageOperator (ψ ∘ toProfile.symm) x = ageOp ψ (toProfile.symm x) := by
  rw [ageOperator, partialEta_comp, partialAge_comp]
  rfl

/-- B0185's `H = (1 − K)ψ` is this `H` after reordering. -/
theorem ageDefect_comp (ψ : SimPoint → ℝ) (x : ProfilePoint) :
    B0185.ageDefect (ψ ∘ toProfile.symm) x = ageDefect ψ (toProfile.symm x) := by
  rw [B0185.ageDefect, ageOperator_comp]
  rfl

/-- With `v = ∇^⊥ψ`, the profile `(v₁, v₂ + εH)` is the library's ring-stream profile
(`Axi.ringStreamProfile`, B0298). -/
theorem rawProfile_perpGrad (R : ℝ) (ψ : SimPoint → ℝ) :
    rawProfile R (perpGrad ψ) ψ = Axi.ringStreamProfile R ψ := by
  funext m
  rw [rawProfile, Axi.ringStreamProfile, perpGrad_zero, perpGrad_one, ageDefect_apply, ringEps]
  congr 2
  ring

theorem rawProfile_congr {R : ℝ} {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m) {m : SimPoint} (hm : m ∈ simAgeDomain) :
    rawProfile R v ψ m = Axi.ringStreamProfile R ψ m := by
  rw [← rawProfile_perpGrad, rawProfile, rawProfile, hv m hm]

/-! ## The lift -/

theorem frameL_rawProfile (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (m : SimPoint)
    (y : Space) :
    Axi.frameL y (rawProfile R v ψ m) =
      v m 0 • Axi.eR y + (v m 1 + ringEps R * ageDefect ψ m) • Axi.e3 := by
  rw [rawProfile, map_add, map_smul, map_smul, Axi.frameL_m0, Axi.frameL_m1]

/-- `U_raw = √s [v₁ e_r + (v₂ + εH) e_z]` at the chart point (tex line 2077). -/
theorem Uraw_apply (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (τ : ℝ) (y : Space) :
    Uraw R v ψ τ y = √(Axi.age R y) •
      (v (Axi.chart R τ y) 0 • Axi.eR y +
        (v (Axi.chart R τ y) 1 + ringEps R * ageDefect ψ (Axi.chart R τ y)) • Axi.e3) := by
  rw [Uraw, Axi.Nv, frameL_rawProfile]

/-- The lift only sees `v` on `{s > 0}`: there `v = ∇^⊥ψ` gives the lift of `∇^⊥ψ`. -/
theorem Uraw_congr {R : ℝ} {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m) :
    Uraw R v ψ = Uraw R (perpGrad ψ) ψ := by
  funext τ y
  simp only [Uraw, Axi.Nv]
  rcases (Axi.age_nonneg R y).eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_smul, zero_smul]
  · have hm : Axi.chart R τ y ∈ simAgeDomain := hpos
    rw [rawProfile, rawProfile, hv _ hm]

/-- **The physical stream is `ϱψ`** (tex line 2078). If `v = ∇^⊥ψ` on `{s > 0}` and `ψ` is
differentiable there, then `U_raw = curl(Ψ e_ϑ/ϱ) = −ϱ⁻¹Ψ_z e_r + ϱ⁻¹Ψ_ϱ e_z` with the
Stokes stream `Ψ(ϱ, z) = ϱ ψ(chart)` (`Axi.ringStream`), on all of `ℝ³` (both sides are `0` on
the axis). -/
theorem Uraw_eq_streamLift {R : ℝ} (hR : 0 < R) {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hψ : DifferentiableOn ℝ ψ simAgeDomain) (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m)
    (τ : ℝ) :
    Uraw R v ψ τ = Axi.streamLift (Axi.ringStream R τ ψ) := by
  funext y
  by_cases hy : y ∈ Axi.axis
  · have h0 : Axi.ϱ y = 0 := (Axi.mem_axis_iff y).1 hy
    simp [Uraw, Axi.Nv, Axi.age, h0, Axi.streamLift_apply]
  · have hm : Axi.chart R τ y ∈ simAgeDomain := Axi.age_pos hR.ne' hy
    have hφ : DifferentiableAt ℝ ψ (Axi.chart R τ y) :=
      hψ.differentiableAt (isOpen_simAgeDomain.mem_nhds hm)
    rw [Axi.ringStreamLift_components hR hy hφ, Uraw, Axi.Nv, Axi.Nv, rawProfile_congr hv hm]

theorem contDiffOn_merChart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) :
    ContDiffOn ℝ 2 (Axi.merChart R τ) (Ioi 0 ×ˢ univ) := by
  have hne : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (p : ℝ × ℝ).1 ≠ 0 :=
    fun p hp => ne_of_gt hp.1
  have hs : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => R ^ 2 / p.1 ^ 2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.fun_div (contDiffOn_fst.pow 2) fun p hp => pow_ne_zero 2 (hne p hp)
  have hξ : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / p.1 ^ 2)) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.sub (contDiffOn_const.mul (hs.log fun p hp =>
      div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 (hne p hp))))
  have hη : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => R * p.2 / p.1) (Ioi 0 ×ˢ univ) :=
    (contDiffOn_const.mul contDiffOn_snd).fun_div contDiffOn_fst hne
  exact hs.prodMk (hξ.prodMk hη)

theorem mapsTo_merChart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) :
    MapsTo (Axi.merChart R τ) (Ioi 0 ×ˢ univ) simAgeDomain := by
  intro p hp
  have hp1 : (0 : ℝ) < p.1 := hp.1
  show 0 < R ^ 2 / p.1 ^ 2
  exact div_pos (lt_of_le_of_ne (sq_nonneg R) (Ne.symm (pow_ne_zero 2 hR))) (pow_pos hp1 2)

/-- The similarity Stokes stream `ϱ ψ(chart)` is `C²` on `{ϱ > 0}` for `ψ` of class `C²` on
`{s > 0}`. -/
theorem contDiffOn_ringStream {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {ψ : SimPoint → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ simAgeDomain) :
    ContDiffOn ℝ 2 (Axi.ringStream R τ ψ) (Ioi 0 ×ˢ univ) :=
  contDiffOn_fst.mul (hψ.comp (contDiffOn_merChart hR τ) (mapsTo_merChart hR τ))

/-- **`U_raw` is a complete solenoidal lift** (tex line 2072). For `v = ∇^⊥ψ` on `{s > 0}`
with `ψ` of class `C²` there, `div U_raw = 0` at every point off the axis. -/
theorem divergence_Uraw_eq_zero {R : ℝ} (hR : 0 < R) {v : SimPoint → Axi.Merid}
    {ψ : SimPoint → ℝ} (hψ : ContDiffOn ℝ 2 ψ simAgeDomain)
    (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    Axi.divergence (Uraw R v ψ τ) y = 0 := by
  rw [Uraw_eq_streamLift hR (hψ.differentiableOn (by norm_num)) hv]
  exact Axi.div_streamLift_eq_zero (contDiffOn_ringStream hR.ne' τ hψ) hy

/-! ## Similarity variables versus the physical lift of B0185 -/

/-- B0185's physical lift `u = a_r [v₁ e_r + (v₂ + εH) e_z]` (tex lines 2854–2856), for the
reordered stream, is the self-similar field `t^{-1/2} U_raw(log t, x/√t)` of the profile
`(v₁, v₂ + εH)`, `v = ∇^⊥ψ`. -/
theorem liftVelocity_eq_physNv {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (ψ : SimPoint → ℝ)
    {x : Space} (hx : x ∉ Axi.axis) :
    B0185.liftVelocity R (ψ ∘ toProfile.symm) t x =
      Axi.physNv R (rawProfile R (perpGrad ψ) ψ) x t := by
  rw [Axi.physNv_eq hR ht _ hx, B0185.liftVelocity_apply, B0185.liftUr_apply,
    B0185.liftUz_apply]
  rw [show ((ageCoordinate R (Axi.ϱ x) t,
      (logRadius R (Axi.ϱ x), transverseCoordinate R (Axi.ϱ x) (x 2))) : SimPoint) =
      physChart R (Axi.ϱ x) (x 2) t from rfl]
  have h1 : B0185.streamV1 (ψ ∘ toProfile.symm) (profileChart R (Axi.ϱ x) (x 2) t) =
      -Axi.dEta ψ (physChart R (Axi.ϱ x) (x 2) t) := by
    rw [B0185.streamV1, partialEta_comp, toProfile_symm_profileChart]
  have h2 : B0185.axialProfile R (ψ ∘ toProfile.symm) (profileChart R (Axi.ϱ x) (x 2) t) =
      Axi.dQ ψ (physChart R (Axi.ϱ x) (x 2) t) +
        ringEps R * ageDefect ψ (physChart R (Axi.ϱ x) (x 2) t) := by
    rw [B0185.axialProfile, B0185.streamV2, partialQ_comp, ageDefect_comp,
      toProfile_symm_profileChart]
  rw [h1, h2, frameL_rawProfile, perpGrad_zero, perpGrad_one, smul_add, smul_smul, smul_smul]
  rfl

/-- **`U_raw` is the similarity velocity** (blueprint proof outline: "`√t u` is the similarity
velocity"). For `R, t > 0`, `x` off the axis and `v = ∇^⊥ψ` on `{s > 0}`, B0185's physical
lift `u` of the reordered stream satisfies `√t u(x, t) = U_raw(log t, x/√t)`. -/
theorem similarity_velocity {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {v : SimPoint → Axi.Merid}
    {ψ : SimPoint → ℝ} (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m) {x : Space}
    (hx : x ∉ Axi.axis) :
    √t • B0185.liftVelocity R (ψ ∘ toProfile.symm) t x =
      Uraw R v ψ (Real.log t) ((√t)⁻¹ • x) := by
  rw [Uraw_congr hv, liftVelocity_eq_physNv hR ht ψ hx, Axi.physNv, Axi.selfSim, pow_one,
    smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 ht).ne', one_smul]
  rfl

/-- **The physical stream in similarity variables is `ϱψ`** (tex line 2078). B0185's physical
stream `𝒫 = rψ` (tex line 2854) satisfies `𝒫(r, z, t)/√t = ϱ(y) ψ(chart)` at `y = x/√t`,
`τ = log t`, which is the similarity Stokes stream `Axi.ringStream` of `Uraw_eq_streamLift`. -/
theorem physicalStream_similarity {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (ψ : SimPoint → ℝ)
    {x : Space} (hx : x ∉ Axi.axis) :
    (√t)⁻¹ * B0185.physicalStream R (ψ ∘ toProfile.symm) (Axi.ϱ x) (x 2) t =
      Axi.ringStream R (Real.log t) ψ (Axi.mer ((√t)⁻¹ • x)) := by
  have hch := chart_similarity_eq_physChart hR ht hx
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hϱ : (Axi.mer ((√t)⁻¹ • x)).1 = (√t)⁻¹ * Axi.ϱ x := by
    show Axi.ϱ ((√t)⁻¹ • x) = _
    rw [Axi.ϱ_smul, abs_of_pos (inv_pos.2 hst)]
  rw [Axi.ringStream, ← Axi.chart_eq_merChart, hch, hϱ, B0185.physicalStream_apply,
    Function.comp_apply, toProfile_symm_profileChart, mul_assoc]

/-- **The raw pressure is `s p`** (tex line 2078). B0185's raw pressure `p_raw = a_r² p`
(tex line 2857), for the reordered pressure profile, satisfies
`t p_raw(x, t) = (s p)(log t, x/√t)` (`Axi.Np`). -/
theorem rawPressure_similarity {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (p : SimPoint → ℝ)
    {x : Space} (hx : x ∉ Axi.axis) :
    t * B0185.liftPressure R (p ∘ toProfile.symm) t x =
      Axi.Np R p (Real.log t) ((√t)⁻¹ • x) := by
  have hch := chart_similarity_eq_physChart hR ht hx
  have hage : Axi.age R ((√t)⁻¹ • x) = ageCoordinate R (Axi.ϱ x) t := congrArg Prod.fst hch
  rw [Axi.Np, hch, hage, B0185.liftPressure, B0185.rawPressure_apply, Function.comp_apply,
    toProfile_symm_profileChart, ageCoordinate]
  ring

/-! ## The period `P = 2εc` (tex line 2079) -/

theorem period_eq (R c : ℝ) : period R c = 2 * c / R := by
  rw [period, ringEps]
  ring

/-- One period `P = 2εc` in `τ` shifts `ξ` by one cell `c`. -/
theorem chart_add_period {R : ℝ} (hR : R ≠ 0) (c τ : ℝ) (y : Space) :
    Axi.chart R (τ + period R c) y =
      (Axi.age R y, (Axi.phase R τ y + c, Axi.trans R y)) :=
  Axi.chart_add_period hR (period_eq R c) τ y

/-- Derivatives of a `c`-periodic profile are `c`-periodic on `{s > 0}`. -/
theorem fderiv_cellPeriodic {c : ℝ} {ψ : SimPoint → ℝ} (hψ : IsCellPeriodic c ψ) {s : ℝ}
    (hs : 0 < s) (ξ η : ℝ) :
    fderiv ℝ ψ (s, (ξ + c, η)) = fderiv ℝ ψ (s, (ξ, η)) := by
  have hpt : ((s, (ξ + c, η)) : SimPoint) = (s, (ξ, η)) + (0, (c, 0)) := by simp
  have hmem : ((s, (ξ, η)) : SimPoint) ∈ simAgeDomain := hs
  rw [hpt, ← fderiv_comp_add_right]
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [isOpen_simAgeDomain.mem_nhds hmem] with n hn
  rcases n with ⟨a, b, d⟩
  simp only [Prod.mk_add_mk, add_zero]
  exact hψ a hn b d

/-- The lift profile `(v₁, v₂ + εH)` of a `c`-periodic train is `c`-periodic. -/
theorem rawProfile_periodic {R c : ℝ} {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hv : IsCellPeriodic c v) (hψ : IsCellPeriodic c ψ) :
    IsCellPeriodic c (rawProfile R v ψ) := by
  intro s hs ξ η
  have hd := fderiv_cellPeriodic hψ hs ξ η
  simp only [rawProfile, ageDefect, ageOp, Axi.dEta, Axi.dS, hv s hs ξ η, hψ s hs ξ η, hd]

/-- **The period is `P = 2εc`** (tex line 2079): for a `c`-periodic train, `U_raw` is
`P`-periodic in the similarity time `τ`. -/
theorem Uraw_add_period {R c : ℝ} (hR : R ≠ 0) {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hv : IsCellPeriodic c v) (hψ : IsCellPeriodic c ψ) (τ : ℝ) :
    Uraw R v ψ (τ + period R c) = Uraw R v ψ τ := by
  funext y
  simp only [Uraw, Axi.Nv]
  rw [chart_add_period hR c τ y]
  rcases (Axi.age_nonneg R y).eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_smul, zero_smul]
  · rw [rawProfile_periodic hv hψ _ hpos]
    rfl

/-- The raw pressure `s p` of a `c`-periodic pressure is `P`-periodic in `τ`, `P = 2εc`. -/
theorem Np_add_period {R c : ℝ} (hR : R ≠ 0) {p : SimPoint → ℝ} (hp : IsCellPeriodic c p)
    (τ : ℝ) :
    Axi.Np R p (τ + period R c) = Axi.Np R p τ := by
  funext y
  rw [Axi.Np, Axi.Np, chart_add_period hR c τ y]
  rcases (Axi.age_nonneg R y).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · rw [hp _ hpos]
    rfl

/-! ## The order `(r, ϑ, z)` (tex lines 2094–2095) -/

/-- In the order `(r, ϑ, z)` with the frame `(e_r, e_ϑ, e_z)` (`Axi.frame`), `U_raw` has
components `√s (v₁, 0, v₂ + εH)`. -/
theorem Uraw_eq_frame_sum (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (τ : ℝ)
    (y : Space) :
    Uraw R v ψ τ y = √(Axi.age R y) •
      ∑ a : Fin 3, toRThetaZ (rawProfile R v ψ (Axi.chart R τ y)) a • Axi.frame y a := by
  rw [Uraw, Axi.Nv, Axi.frameL_apply, Fin.sum_univ_three]
  simp [toRThetaZ, Axi.frame_zero, Axi.frame_one, Axi.frame_two]

theorem toRThetaZ_rawProfile (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ)
    (m : SimPoint) :
    toRThetaZ (rawProfile R v ψ m) = ![v m 0, 0, v m 1 + ringEps R * ageDefect ψ m] := by
  simp [toRThetaZ]

/-- `U_raw` has no `e_ϑ` component (the no-swirl structure; blueprint note of B0186). -/
theorem inner_Uraw_eΦ (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ) (τ : ℝ)
    (y : Space) :
    inner ℝ (Uraw R v ψ τ y) (Axi.eΦ y) = 0 := by
  rw [Uraw_apply, real_inner_smul_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, Axi.inner_eR_eΦ, Axi.inner_e3_left, Axi.eΦ_apply_two]
  ring

/-- Every slice of `U_raw` is axisymmetric without swirl (`Statement.IsAxisymmetricNoSwirl`). -/
theorem isAxisymmetricNoSwirl_Uraw (R : ℝ) (v : SimPoint → Axi.Merid) (ψ : SimPoint → ℝ)
    (τ : ℝ) : IsAxisymmetricNoSwirl (Uraw R v ψ τ) :=
  Axi.isAxisymmetricNoSwirl_Nv R _ τ

/-! ## The unit -/

/-- **Unit B0186** (`eq:m3-ring-lift`, tex lines 2070–2098). Let `R > 0`, `ε = R⁻¹`, and let
`ψ(s, ξ, η)` be a stream of class `C²` on `{s > 0}` with `v = ∇^⊥ψ` there. Then:
1. the similarity chart `s = R²/ϱ²`, `ξ = Rτ/2 − (R/2) log s`, `η = R y₃/ϱ` at `y = x/√t`,
   `τ = log t` is the physical chart `s = (R/r)² t`, `ξ = R log(r/R)`, `η = R x₃/r`;
2. `U_raw = √s [v₁ e_r + (v₂ + εH) e_z]`, `H = (1 − K_age)ψ`, `K_age = η∂_η + 2s∂_s`, is the
   similarity velocity `√t u` of the physical lift `u` of B0185;
3. its Stokes stream is `ϱψ` (`U_raw = curl(ϱψ e_ϑ/ϱ)`), and `ϱψ = 𝒫/√t` for the physical
   stream `𝒫 = rψ` of B0185;
4. it is solenoidal off the axis (complete solenoidal lift);
5. it has no `e_ϑ` component (order `(r, ϑ, z)`: components `√s (v₁, 0, v₂ + εH)`);
6. the raw pressure is `s p`: `t p_raw = s p` for B0185's `p_raw = a_r² p`;
7. the period is `P = 2εc`: for a `c`-periodic train (`v`, `ψ`, `p` periodic in `ξ` on
   `s > 0`), `U_raw` and `s p` are `P`-periodic in `τ`. -/
theorem m3_ring_lift {R : ℝ} (hR : 0 < R) {v : SimPoint → Axi.Merid} {ψ : SimPoint → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ simAgeDomain) (hv : ∀ m ∈ simAgeDomain, v m = perpGrad ψ m) :
    (∀ t, 0 < t → ∀ x : Space, x ∉ Axi.axis →
      Axi.chart R (Real.log t) ((√t)⁻¹ • x) =
        ((R / Axi.ϱ x) ^ 2 * t, (R * Real.log (Axi.ϱ x / R), R * x 2 / Axi.ϱ x))) ∧
    (∀ τ y, Uraw R v ψ τ y = √(Axi.age R y) •
      (v (Axi.chart R τ y) 0 • Axi.eR y +
        (v (Axi.chart R τ y) 1 + ringEps R * (ψ (Axi.chart R τ y) -
          ageOp ψ (Axi.chart R τ y))) • Axi.e3)) ∧
    (∀ t, 0 < t → ∀ x : Space, x ∉ Axi.axis →
      √t • B0185.liftVelocity R (ψ ∘ toProfile.symm) t x =
        Uraw R v ψ (Real.log t) ((√t)⁻¹ • x)) ∧
    (∀ τ, Uraw R v ψ τ = Axi.streamLift (Axi.ringStream R τ ψ)) ∧
    (∀ t, 0 < t → ∀ x : Space, x ∉ Axi.axis →
      (√t)⁻¹ * B0185.physicalStream R (ψ ∘ toProfile.symm) (Axi.ϱ x) (x 2) t =
        Axi.ringStream R (Real.log t) ψ (Axi.mer ((√t)⁻¹ • x))) ∧
    (∀ τ y, y ∉ Axi.axis → Axi.divergence (Uraw R v ψ τ) y = 0) ∧
    (∀ τ y, inner ℝ (Uraw R v ψ τ y) (Axi.eΦ y) = 0) ∧
    (∀ p : SimPoint → ℝ, ∀ t, 0 < t → ∀ x : Space, x ∉ Axi.axis →
      t * B0185.liftPressure R (p ∘ toProfile.symm) t x =
        Axi.Np R p (Real.log t) ((√t)⁻¹ • x)) ∧
    (∀ (c : ℝ) (p : SimPoint → ℝ), IsCellPeriodic c v → IsCellPeriodic c ψ →
      IsCellPeriodic c p → ∀ τ,
        Uraw R v ψ (τ + 2 * ringEps R * c) = Uraw R v ψ τ ∧
          Axi.Np R p (τ + 2 * ringEps R * c) = Axi.Np R p τ) := by
  refine ⟨fun t ht x hx => ?_, fun τ y => Uraw_apply R v ψ τ y,
    fun t ht x hx => similarity_velocity hR ht hv hx,
    Uraw_eq_streamLift hR (hψ.differentiableOn (by norm_num)) hv,
    fun t ht x hx => physicalStream_similarity hR ht ψ hx,
    fun τ y hy => divergence_Uraw_eq_zero hR hψ hv τ hy,
    fun τ y => inner_Uraw_eΦ R v ψ τ y,
    fun p t ht x hx => rawPressure_similarity hR ht p hx,
    fun c p hvc hψc hpc τ => ⟨Uraw_add_period hR.ne' hvc hψc τ, Np_add_period hR.ne' hpc τ⟩⟩
  rw [chart_similarity_eq_physChart hR ht hx, physChart_eq]

end UnforcedLeray.B0186
