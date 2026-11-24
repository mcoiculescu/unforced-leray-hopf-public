import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4

/-!
# `PartIII-b:C/rep/2/4/5` : decomposition of `VertYoungPhase`

Source `the November 2 reference manuscript` 3624-3647 (`sep:young`: Young in `y`,
dilation, Minkowski in `λ`, phase translation), 5219-5221 (normalised phase estimate over `P ≤ 1`),
in one dimension with the vertical kernel `vertKern rIn D t = rIn/(2D(D²+t²))`.

Three analytic Props (`VertKernLb`, `Vert1DYoung`, `VertDil`); Minkowski in `λ` and the assembly with
`PeriodicDilationSum` (`periodicDilationSum_proved`) are proved in `Of.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(K) The vertical kernel in `L^{11/3}(ℝ)`** (3624-3631 in one dimension): with `b = 11/3`,
`‖vertKern rIn D‖_{L^b(ℝ)} = (rIn/(2D)) (∫ (D²+t²)^{-b} dt)^{1/b} = c (rIn/D) D^{-2+3/11}`,
`c = ½ (∫ (1+u²)^{-11/3} du)^{3/11}` (substitute `t = D u`; `(1+u²)^{-11/3}` is integrable on `ℝ`). -/
def VertKernLb : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D →
    lqNorm1 (11 / 3) (vertKern rIn D) ≤ ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ))

/-- **(Y) Young's convolution inequality on `ℝ`** for `[0,∞]`-valued data (3631-3645):
`‖K * g‖_{L^q} ≤ ‖K‖_{L^b} ‖g‖_{L^p}`, `1 + 1/q = 1/p + 1/b`, `K` measurable and finite everywhere,
`g` measurable of finite `L^p` norm.  (The group version is `Conv.eLpNorm_convAbs_le_young` in
`Lib/ConvIneq/YoungGroup.lean`; the three-dimensional port is `sky_young_conv` in
`Sub/PartIII-b_C_rep_2_1_2.lean`.) -/
def Vert1DYoung : Prop :=
  ∀ (K g : ℝ → ℝ≥0∞), Measurable K → (∀ x, K x ≠ ⊤) → Measurable g → ∀ b p q : ℝ,
    1 ≤ b → 1 ≤ p → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b → lqNorm1 p g ≠ ⊤ →
      lqNorm1 q (fun y => ∫⁻ x : ℝ, K (y - x) * g x) ≤ lqNorm1 b K * lqNorm1 p g

/-- **(D) Dilation `s ↦ λ s` on `ℝ`** (3631-3645): for `λ > 0`, (i) `∫ S(z - λ s) g(s) ds =
λ⁻¹ ∫ S(z - w) g(w/λ) dw` (substitute `w = λ s`), (ii) `‖g(·/λ)‖_{L^p} = λ^{1/p} ‖g‖_{L^p}`. -/
def VertDil : Prop :=
  ∀ l : ℝ, 0 < l →
    (∀ (S g : ℝ → ℝ≥0∞) (z : ℝ), ∫⁻ s : ℝ, S (z - l * s) * g s =
        ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * g (l⁻¹ * w)) ∧
    (∀ (p : ℝ), 0 < p → ∀ g : ℝ → ℝ≥0∞,
        lqNorm1 p (fun w => g (l⁻¹ * w)) = ENNReal.ofReal (l ^ (1 / p)) * lqNorm1 p g)

end UnforcedLeray.Short.PartIIIb.Concrete
