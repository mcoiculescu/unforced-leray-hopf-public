import UnforcedLeray.Short.PartIIIa.StressInputs

/-!
# Part III-a, `PartIII-a:T23/1/org`: the chart coefficient of the raw lift (bridge)

Source of record: `the November 2 reference manuscript`, lines 2666-2668 (the
cylinder chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`), 2685 (the velocity lift
`𝒩_v b = √s b`) and 2711 (`v = s^{-1/2} V`).

The raw field is `U_raw = p.raw = axisExt (𝒩_v b_raw)` with the profile
`b_raw = rawProfile ε v ψ = (v₁, v₂ + εH)`, `H = (1 - η∂_η - 2s∂_s)ψ` the stream completion
(`Cons/L2/BackgroundConcrete/Fields.lean`, `Params.raw`; `Cons/C03Background/RawLift.lean`).
The chart coefficient `v = s^{-1/2} V` of `StressSpaces.lean` (`chartCoeff`) is the inverse of the
lift: at a chart point with `s > 0` it evaluates the field at `y = (R/√s, 0, η/√s)` (off the axis),
phase `τ = 2q/R + log s`, and divides by `√s`.

Proved here (no `sorry`):
* `chartCoeff_Nv`: `chartCoeff R (𝒩_v b) = b` at every chart point with `s > 0` (`R > 0`);
* `chartCoeff_axisExt`: the extension through the axis does not change the chart coefficient;
* `chartCoeff_raw`: `chartCoeff p.R p.raw = rawProfile p.ε p.train.v p.train.ψ` at `s > 0`;
* `norm_rawProfile_le`: `‖b_raw‖ ≤ ‖v‖ + |ε| |H|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete

/-- The inverse chart point `y = (R/√s, 0, η/√s)` used by `chartCoeff`. -/
def chartPoint (R : ℝ) (pt : ℝ × (ℝ × ℝ)) : Space :=
  !₂[R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1]

/-- The inverse chart phase `τ = 2q/R + log s` used by `chartCoeff`. -/
def chartPhase (R : ℝ) (pt : ℝ × (ℝ × ℝ)) : ℝ := 2 * pt.2.1 / R + Real.log pt.1

theorem chartPoint_not_mem_axis {R : ℝ} (hR : 0 < R) {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    chartPoint R pt ∉ axis := by
  intro h
  have h0 : R / Real.sqrt pt.1 = 0 := h.1
  have : 0 < R / Real.sqrt pt.1 := div_pos hR (Real.sqrt_pos.2 hs)
  linarith

theorem ϱ_chartPoint {R : ℝ} (hR : 0 < R) (pt : ℝ × (ℝ × ℝ)) :
    ϱ (chartPoint R pt) = R / Real.sqrt pt.1 := by
  have h0 : 0 ≤ R / Real.sqrt pt.1 := div_nonneg hR.le (Real.sqrt_nonneg _)
  have e0 : chartPoint R pt 0 = R / Real.sqrt pt.1 := by simp [chartPoint]
  have e1 : chartPoint R pt 1 = 0 := by simp [chartPoint]
  rw [ϱ, e0, e1, zero_pow two_ne_zero, add_zero, Real.sqrt_sq h0]

theorem age_chartPoint {R : ℝ} (hR : 0 < R) {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    age R (chartPoint R pt) = pt.1 := by
  rw [age, ϱ_chartPoint hR, div_pow, Real.sq_sqrt hs.le]
  have hR2 : R ^ 2 ≠ 0 := by positivity
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hR2]

theorem chart_chartPoint {R : ℝ} (hR : 0 < R) {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    chart R (chartPhase R pt) (chartPoint R pt) = pt := by
  have hsq : 0 < Real.sqrt pt.1 := Real.sqrt_pos.2 hs
  have hR0 : R ≠ 0 := hR.ne'
  have hsq0 : Real.sqrt pt.1 ≠ 0 := hsq.ne'
  have ha := age_chartPoint hR hs
  have hϱ := ϱ_chartPoint hR pt
  have h1 : Axi.phase R (chartPhase R pt) (chartPoint R pt) = pt.2.1 := by
    rw [Axi.phase, ha, chartPhase]
    have hk : R * (2 * pt.2.1 / R) = 2 * pt.2.1 := by
      rw [mul_div_assoc', mul_comm R, mul_div_assoc, div_self hR0, mul_one]
    calc R * (2 * pt.2.1 / R + Real.log pt.1) / 2 - R / 2 * Real.log pt.1
        = (R * (2 * pt.2.1 / R)) / 2 := by ring
      _ = pt.2.1 := by rw [hk]; ring
  have h3 : (chartPoint R pt) 2 = pt.2.2 / Real.sqrt pt.1 := by
    simp [chartPoint]
  have h2 : Axi.trans R (chartPoint R pt) = pt.2.2 := by
    rw [Axi.trans, hϱ, h3]
    field_simp
  rw [Axi.chart, ha, h1, h2]

theorem eR_chartPoint {R : ℝ} (hR : 0 < R) {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    eR (chartPoint R pt) = !₂[1, 0, 0] := by
  have hpos : 0 < R / Real.sqrt pt.1 := div_pos hR (Real.sqrt_pos.2 hs)
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, eR_apply_zero, ϱ_chartPoint hR]
    simp [chartPoint, hpos.ne']
  · simp only [Fin.mk_one, eR_apply_one]
    simp [chartPoint]
  · simp [chartPoint]

/-- **The chart coefficient inverts the velocity lift** (SP 2685, 2711): for `R > 0` and a chart
point with `s > 0`, `chartCoeff R (𝒩_v b) = b`. -/
theorem chartCoeff_Nv {R : ℝ} (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → Merid)
    {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) : chartCoeff R (Nv R b) pt = b pt := by
  have hsq : 0 < Real.sqrt pt.1 := Real.sqrt_pos.2 hs
  have hNv : Nv R b (chartPhase R pt) (chartPoint R pt) =
      Real.sqrt pt.1 • (b pt 0 • (!₂[1, 0, 0] : Space) + b pt 1 • e3) := by
    rw [Nv, age_chartPoint hR hs, chart_chartPoint hR hs, frameL_apply, eR_chartPoint hR hs]
  have h0 : Nv R b (chartPhase R pt) (chartPoint R pt) 0 = Real.sqrt pt.1 * b pt 0 := by
    rw [hNv]; simp
  have h2 : Nv R b (chartPhase R pt) (chartPoint R pt) 2 = Real.sqrt pt.1 * b pt 1 := by
    rw [hNv]; simp
  have hc : chartCoeff R (Nv R b) pt = (Real.sqrt pt.1)⁻¹ •
      (!₂[Nv R b (chartPhase R pt) (chartPoint R pt) 0,
        Nv R b (chartPhase R pt) (chartPoint R pt) 2] : Merid) := rfl
  rw [hc, h0, h2]
  ext i
  fin_cases i
  · simp [hsq.ne']
  · simp [hsq.ne']

/-- The extension through the axis does not change the chart coefficient (the chart point is off
the axis). -/
theorem chartCoeff_axisExt {R : ℝ} (hR : 0 < R) (F : ℝ → Space → Space)
    {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    chartCoeff R (fun τ => axisExt (F τ)) pt = chartCoeff R F pt := by
  have hax := chartPoint_not_mem_axis hR hs
  show (Real.sqrt pt.1)⁻¹ •
      (!₂[axisExt (F (chartPhase R pt)) (chartPoint R pt) 0,
        axisExt (F (chartPhase R pt)) (chartPoint R pt) 2] : Merid) =
    (Real.sqrt pt.1)⁻¹ •
      (!₂[F (chartPhase R pt) (chartPoint R pt) 0, F (chartPhase R pt) (chartPoint R pt) 2] : Merid)
  rw [axisExt_of_not_mem hax]

/-- **The chart coefficient of the raw lift** (SP 2703-2711): at a chart point with `s > 0`,
`v_raw = s^{-1/2} U_raw = b_raw = (v₁, v₂ + εH)` of the actual train. -/
theorem chartCoeff_raw (p : Params) {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    chartCoeff p.R p.raw pt =
      UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ pt := by
  have h := chartCoeff_axisExt p.R_pos
    (Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)) hs
  have hraw : p.raw =
      fun τ => axisExt (Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) :=
    rfl
  rw [hraw, h, chartCoeff_Nv p.R_pos _ hs]

/-- `‖b_raw‖ ≤ ‖v‖ + |ε| |H|` for `b_raw = v + εH e_z` (SP 2721-2723). -/
theorem norm_rawProfile_le (ε : ℝ) (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec)
    (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (pt : ℝ × (ℝ × ℝ)) :
    ‖UnforcedLeray.Cons.C03.rawProfile ε v ψ pt‖ ≤
      ‖v pt.1 pt.2‖ + |ε| * |UnforcedLeray.Cons.C03.raisedStream ψ pt.1 pt.2.1 pt.2.2| := by
  unfold UnforcedLeray.Cons.C03.rawProfile
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_mul]

end UnforcedLeray.Short.IIIa
