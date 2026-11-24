import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3Eq

/-!
# Part II-a, block `B₃`: the leaf `CoeffB3ShiftEq` (task `PartII-a:R02/11/3`)

Target: `coeffB3ShiftEq : CoeffB3ShiftEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`ageShift 3 (coeffB₃ ν g) x = ν * (-3 jet 0 0 0 g x - 4 jet 1 0 0 g x + 2 jet 2 0 0 g x +
4 jet 3 0 0 g x + jet 4 0 0 g x)`.

Source of record: `the November 2 reference manuscript`, lines 1250-1270 (the
`(K+3)` size column; `K` degree `-3`).

Route: `coeffB3Eq` gives `B₃[g] = ν(-g - Kg + K²g + K³g)` on `{s > 0}`; by locality of `K` and
linearity of `K` at points of differentiability, `K B₃[g] x = ν(-Kg - K²g + K³g + K⁴g) x`.
Adding `3 B₃[g] x` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `K` of a four-term linear combination at a point of differentiability. -/
theorem ageOp4_of (f0 f1 f2 f3 : ProfilePoint → ℝ) {x : ProfilePoint}
    (h0 : DifferentiableAt ℝ f0 x) (h1 : DifferentiableAt ℝ f1 x)
    (h2 : DifferentiableAt ℝ f2 x) (h3 : DifferentiableAt ℝ f3 x) (a0 a1 a2 a3 : ℝ) :
    ageOperator (fun y => a0 * f0 y + a1 * f1 y + a2 * f2 y + a3 * f3 y) x =
      a0 * ageOperator f0 x + a1 * ageOperator f1 x + a2 * ageOperator f2 x +
        a3 * ageOperator f3 x := by
  have h01 : DifferentiableAt ℝ (fun y => a0 * f0 y) x := h0.const_mul a0
  have h012 : DifferentiableAt ℝ (fun y => a0 * f0 y + a1 * f1 y) x :=
    h01.add (h1.const_mul a1)
  have h0123 : DifferentiableAt ℝ (fun y => a0 * f0 y + a1 * f1 y + a2 * f2 y) x :=
    h012.add (h2.const_mul a2)
  rw [ageOperator_add_mul h0123 h3 a3, ageOperator_add_mul h012 h2 a2,
    ageOperator_add_mul h01 h1 a1, kx_ageOp_const_mul a0 h0]

/-- **Leaf `CoeffB3ShiftEq`** (source lines 1250-1270): `ageShift 3 (B₃[g]) = ν(-3g - 4Kg + 2K²g +
4K³g + K⁴g)` on `{s > 0}`, from `B₃[g] = ν(-g - Kg + K²g + K³g)` (`coeffB3Eq`). -/
theorem coeffB3ShiftEq : CoeffB3ShiftEq := by
  unfold CoeffB3ShiftEq
  intro ν g hg x hx
  have hd0 : DifferentiableAt ℝ g x := differentiableAt_of_late hg hx
  have hd1 : DifferentiableAt ℝ (ageOperator g) x :=
    differentiableAt_of_late (contDiffOn_ageOperator hg) hx
  have hd2 : DifferentiableAt ℝ (ageOperator (ageOperator g)) x :=
    differentiableAt_of_late (contDiffOn_ageOperator (contDiffOn_ageOperator hg)) hx
  have hd3 : DifferentiableAt ℝ (ageOperator (ageOperator (ageOperator g))) x :=
    differentiableAt_of_late
      (contDiffOn_ageOperator (contDiffOn_ageOperator (contDiffOn_ageOperator hg))) hx
  have hΦ : DifferentiableAt ℝ
      (fun y => -1 * g y + (-1) * ageOperator g y + 1 * ageOperator (ageOperator g) y +
        1 * ageOperator (ageOperator (ageOperator g)) y) x :=
    ((((hd0.const_mul (-1)).add (hd1.const_mul (-1))).add (hd2.const_mul 1)).add
      (hd3.const_mul 1))
  have hev : coeffB₃ ν g =ᶠ[𝓝 x] (fun y => ν * (-1 * g y + (-1) * ageOperator g y +
      1 * ageOperator (ageOperator g) y + 1 * ageOperator (ageOperator (ageOperator g)) y)) :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun y hy => by
      have h : coeffB₃ ν g y = ν * (-g y - ageOperator g y + ageOperator (ageOperator g) y +
          ageOperator (ageOperator (ageOperator g)) y) := coeffB3Eq ν g hg y hy
      rw [h]
      ring)
  have hraw : coeffB₃ ν g x = ν * (-g x - ageOperator g x + ageOperator (ageOperator g) x +
      ageOperator (ageOperator (ageOperator g)) x) := coeffB3Eq ν g hg x hx
  unfold ageShift
  rw [kx_ageOp_congr hev, kx_ageOp_const_mul ν hΦ,
    ageOp4_of g (ageOperator g) (ageOperator (ageOperator g))
      (ageOperator (ageOperator (ageOperator g))) hd0 hd1 hd2 hd3 (-1) (-1) 1 1, hraw]
  show ν * (-1 * ageOperator g x + (-1) * ageOperator (ageOperator g) x +
      1 * ageOperator (ageOperator (ageOperator g)) x +
      1 * ageOperator (ageOperator (ageOperator (ageOperator g))) x) +
    3 * (ν * (-g x - ageOperator g x + ageOperator (ageOperator g) x +
      ageOperator (ageOperator (ageOperator g)) x)) =
    ν * (-3 * g x - 4 * ageOperator g x + 2 * ageOperator (ageOperator g) x +
      4 * ageOperator (ageOperator (ageOperator g)) x +
      ageOperator (ageOperator (ageOperator (ageOperator g))) x)
  ring

end UnforcedLeray.Short.PartIIa.BlockB3
