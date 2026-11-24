import UnforcedLeray.Short.PartIIIb.Near

/-!
# Proof of `GainRatioTanh` (source: `the November 2 reference manuscript`)

The gain ratio `(√M-1)/(√M+1)` equals `tanh(log M / 4)` for `M ≥ 1`. In the source this is the
identity `η_δ = γ tanh(3δ/8)` with `M = e^{3δ/2}` (lines 3984-3991); the same statement is
`GainRatioTanh` in `Near.lean`.

Proof: put `x = log M / 4`. Then `e^{2x} = √M`, and with `e = e^x`,
`tanh x = (e - e⁻¹)/(e + e⁻¹) = (e² - 1)/(e² + 1) = (√M - 1)/(√M + 1)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem gainRatioTanh : UnforcedLeray.Short.PartIIIb.GainRatioTanh := by
  intro M hM
  have hMpos : 0 < M := by linarith
  have hsqrt : Real.sqrt M = Real.exp (Real.log M / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hMpos]
    congr 1
    ring
  set x : ℝ := Real.log M / 4 with hxdef
  have h2x : Real.log M / 2 = 2 * x := by
    rw [hxdef]
    ring
  have hexp2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := ne_of_gt hpos
  have hden1 : Real.exp x * Real.exp x + 1 ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsqrt, h2x, hexp2, Real.exp_neg]
  field_simp

end UnforcedLeray.Short.PartIIIb
