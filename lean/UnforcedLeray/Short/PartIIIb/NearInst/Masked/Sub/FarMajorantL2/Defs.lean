import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# Chart bookkeeping for `FarMajorantL2` (source 3996-4005, 2666-2668, 2675-2683)

Source of record: `the November 2 reference manuscript`.

`FarMajorantL2` (Sub/PositiveKernel.lean) is the chart form of the source route
"Young's inequality, followed by normalized-phase Minkowski" (4002-4003). Bookkeeping, with
`ρ = R/√s`, `t = η/√s`, `τ = 2q/R + log s`, `P = 2c/R` (the `τ`-period of the cell `q ∈ [-c/2,c/2)`):

* `y = chartY R x = (ρ, 0, t)` lies on the slice `φ = 0` of the similarity space `ℝ³`; everything
  in sight is axisymmetric, so `∫_{ℝ³} dy = 2π ∫ ρ dρ dt`.
* `ρ dρ dt = (R²/2) s^{-5/2} ds dη`, `dτ = (2/R) dq`, so
  `∫_{τ∈[0,P)} ∫_{ρ>R/√sm} ∫_t ρ Θ = R c ∫_{s<sm} s^{-5/2} Θ d(ageμ c 0)` (the weight `-5/2` is the
  `-3/2` of `H` times the `s^{-1}` of the factor `s^{-1/2}` squared).
* the source: `|cartLift| = s |nsSym f|` (orthogonal frame), `ρ dρ dt = (R²/2) s^{-5/2} ds dη`
  gives `∫_{τ∈[0,P)} ∫_{ℝ³} |cartLift|² dz = 2π R c ‖nsSym f‖²_{L²(ageμ c (-1/2))}`.
* Young at fixed `(l, τ)` with kernel `|x|^{-4}1_{|x|≥d}`, `d = (1-e^{-δ/2}) R/√sm`, `L¹` norm
  `C/d = Cε√sm/(1-e^{-δ/2})` (`ε = R⁻¹`); then Minkowski over `l`, the weight
  `l^{2μ+2}·l^{-3/2} = l^{2μ+1/2}` integrable by `DilationMargin`; the `τ`-shift `2 log l` is
  harmless because the `P`-periodic source is shifted inside the window `[0,P)`.

The statement `FarMajorantL2` is TRUE as stated (no `ν`-power needed: `k = 0`; the support
hypothesis `x.1 < e^δ sm` is not used).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The point `(ρ, 0, t)` of `ℝ³` (azimuth `φ = 0`), as `chartY` produces. -/
def ptOf (ρ t : ℝ) : UnforcedLeray.Space := WithLp.toLp 2 ![ρ, 0, t]

/-- The truncated kernel `|x|^{-4} 1_{|x| ≥ d}` (source 3999-4000). -/
def farKern (d : ℝ) (x : UnforcedLeray.Space) : ℝ≥0∞ :=
  if d ≤ ‖x‖ then ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) else 0

/-- The dilated positive kernel integral (source 4001-4002): for a source profile `g(τ, z) ≥ 0`,
`∫_0^1 l^{2μ+2} ∫ farKern d (y - l z) g(τ + 2 log l, z) dz dl`. -/
def dilMaj (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (τ : ℝ) (y : UnforcedLeray.Space) :
    ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
    ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z

/-- The axisymmetric source profile `s |nsSym f|` at the similarity point `(z, τ)` (the norm of
`cartLift R c f τ z` off the axis, source 2675-2683). -/
def gAx (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal ((chartOf R c z τ).1 *
    UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (chartOf R c z τ))))

/-- A profile depending on the similarity point only through `(|z'|, z₃)`. -/
def AxisymProf (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) : Prop :=
  ∀ τ (z z' : UnforcedLeray.Space), hRad z = hRad z' → z 2 = z' 2 → g τ z = g τ z'

/-! ## Pointwise reduction (source 3996-3998) -/

/-- `cartLift` has the norm `s |nsSym f|` off the axis (orthogonal frame `cylFrame`, `s ≥ 0`). -/
def CartLiftNormOffAxis : Prop :=
  ∀ (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : UnforcedLeray.Space), hRad z ≠ 0 →
    UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) τ z = gAx R c f τ z

/-- The axis `{z₀ = z₁ = 0}` is Lebesgue-null in `ℝ³`. -/
def AxisNull : Prop :=
  volume {z : UnforcedLeray.Space | hRad z = 0} = 0

/-- `|nsSym T| ≤ |T|` (`ten3` Euclidean norm): `2((a+b)/2)² ≤ a² + b²`. -/
def NsSymNormLe : Prop :=
  ∀ T : Ten3, UnforcedLeray.Short.IIIa.tensorNorm (nsSym T) ≤ ‖T‖

/-- **Pointwise majorant by the dilated positive kernel** (source 3996-3998): at a chart point of
age `0 < s < sm`, the masked majorant `farMajE` is at most `dilMaj` with the truncation radius
`d = (1 - e^{-δ/2}) R/√sm` (by `FarSeparation`: `|y - l z| ≥ (1-e^{-δ/2})R/√s ≥ d`; and
`srcNorm (cartLift) = gAx` off the axis). -/
def FarMajorantPointwise : Prop :=
  ∀ (R c δ μ sm : ℝ), 0 < R → 0 < δ → 0 < sm → ∀ (f : Chart → Ten3) (x : Chart),
    0 < x.1 → x.1 < sm →
      farMajE R c δ μ f x ≤
        dilMaj μ ((1 - Real.exp (-δ / 2)) * R / Real.sqrt sm) (gAx R c f)
          (chartTau R x) (chartY R x)

/-- `farKern d` has `L¹` norm at most `C/d` (from `TailL1`, source 3999-4000). -/
def FarKernL1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → ∫⁻ x, farKern d x ≤ ENNReal.ofReal (C / d)

/-! ## The `L²` bound of the dilated positive kernel (source 4001-4003) -/

/-- Shift invariance over a period of a periodic measurable function. -/
def PeriodShift : Prop :=
  ∀ (h : ℝ → ℝ≥0∞) (P a σ : ℝ), 0 < P → Measurable h → (∀ τ, h (τ + P) = h τ) →
    ∫⁻ τ in Ico a (a + P), h (τ + σ) = ∫⁻ τ in Ico a (a + P), h τ

/-- Joint measurability of `dilMaj` (and of `farKern`). -/
def DilMajMeasurable : Prop :=
  ∀ (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), Measurable (Function.uncurry g) →
    Measurable (Function.uncurry (dilMaj μ d g))

/-- **Young at a fixed dilation `l ∈ (0,1)`** (source 4001-4002; `YoungDilated` at every `τ`,
then the shift invariance of the periodic source): the `l`-th term of `dilMaj` has `L²([0,P) × ℝ³)`
norm at most `l^{2μ+1/2} A ‖g‖`. -/
def DilMajFixedL : Prop :=
  ∀ (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), Measurable (Function.uncurry g) →
    ∀ P : ℝ, 0 < P → (∀ τ z, g (τ + P) z = g τ z) → ∀ A : ℝ≥0∞, ∫⁻ x, farKern d x ≤ A →
      ∀ l : ℝ, 0 < l →
        (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
            (ENNReal.ofReal (l ^ (2 * μ + 2)) *
              ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z)
                ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Minkowski over `l`** (source 4002): `‖dilMaj‖_{L²([0,P)×ℝ³)} ≤ (∫_0^1 l^{2μ+1/2} dl) A ‖g‖`. -/
def DilMajL2 : Prop :=
  ∀ (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), Measurable (Function.uncurry g) →
    ∀ P : ℝ, 0 < P → (∀ τ z, g (τ + P) z = g τ z) → ∀ A : ℝ≥0∞, ∫⁻ x, farKern d x ≤ A →
      (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space, dilMaj μ d g τ y ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) ≤
        (∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2))) * A *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-! ## Axisymmetry, periodicity, measurability of the source profile -/

/-- Rotations about the vertical axis: if `|y'| = |y'_2|`-radius and heights agree there is a
linear isometry of `ℝ³` fixing `hRad` and the third coordinate (of every point) and carrying `y` to
`y'`. -/
def RotExists : Prop :=
  ∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 →
    ∃ Q : UnforcedLeray.Space ≃ₗᵢ[ℝ] UnforcedLeray.Space, Q y = y' ∧
      ∀ z, hRad (Q z) = hRad z ∧ Q z 2 = z 2

/-- `dilMaj` of an axisymmetric profile is axisymmetric in `y` (rotation invariance of the
Lebesgue measure and of the norm). -/
def DilMajAxisym : Prop :=
  ∀ (μ d : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), AxisymProf g →
    ∀ τ (y y' : UnforcedLeray.Space), hRad y = hRad y' → y 2 = y' 2 →
      dilMaj μ d g τ y = dilMaj μ d g τ y'

/-- `gAx` is axisymmetric (`chartOf` sees `z` only through `|z'|, z₃`), `2c/R`-periodic in `τ`
(`τ ↦ τ + 2c/R` shifts the unreduced `q` by `c`) and jointly measurable for a measurable `f`. -/
def GAxFacts : Prop :=
  ∀ (R c : ℝ) (f : Chart → Ten3), 0 < R → 0 < c → Measurable f →
    AxisymProf (gAx R c f) ∧ (∀ τ z, gAx R c f (τ + 2 * c / R) z = gAx R c f τ z) ∧
      Measurable (Function.uncurry (gAx R c f))

/-! ## Change of variables, chart `(s, q, η)` against `(τ, ρ, t)` (source 2666-2668) -/

/-- Shift of the age exponent: `ageμ c (a+b) = s^b · ageμ c a`. -/
def AgeShift : Prop :=
  ∀ (c a b : ℝ) (F : Chart → ℝ≥0∞), Measurable F →
    ∫⁻ x, F x ∂(ageμ c (a + b)) = ∫⁻ x, ENNReal.ofReal (x.1 ^ b) * F x ∂(ageμ c a)

/-- Reduction of an axisymmetric integral over `ℝ³` to cylindrical coordinates:
`∫_{|y'|>lo} H = 2π ∫_{ρ>lo} ∫_t ρ H(ρ,0,t)`. -/
def PolarReduction : Prop :=
  ∀ (H : UnforcedLeray.Space → ℝ≥0∞), Measurable H →
    (∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 → H y = H y') →
    ∀ lo : ℝ, 0 ≤ lo →
      ∫⁻ y in {y : UnforcedLeray.Space | lo < hRad y}, H y =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * H (ptOf ρ t)

/-- The planar change of variables `(s, η) ↦ (ρ, t) = (R/√s, η/√s)` (source 2666-2668):
`ρ dρ dt = (R²/2) s^{-5/2} ds dη`, the region `ρ > lo` being `s < R²/lo²`. -/
def ChartChangeSE : Prop :=
  ∀ (R lo : ℝ), 0 < R → 0 ≤ lo → ∀ Ψ : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry Ψ) →
    ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * Ψ ρ t =
      ENNReal.ofReal (R ^ 2 / 2) *
        ∫⁻ s in {s : ℝ | 0 < s ∧ lo < R / Real.sqrt s}, ∫⁻ η : ℝ,
          ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Ψ (R / Real.sqrt s) (η / Real.sqrt s)

/-- The phase change `τ = 2q/R + a` over one period (source 2667): for a `2c/R`-periodic
measurable `Ξ` and any `a`, `∫_{[0,2c/R)} Ξ = (2/R) ∫_{q ∈ [-c/2, c/2)} Ξ(2q/R + a) dq`. -/
def ChartChangeTQ : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ Ξ : ℝ → ℝ≥0∞, Measurable Ξ →
    (∀ τ, Ξ (τ + 2 * c / R) = Ξ τ) → ∀ a : ℝ,
      ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), Ξ τ =
        ENNReal.ofReal (2 / R) * ∫⁻ q in Ico (-c / 2) (c / 2), Ξ (2 * q / R + a)

/-- **The chart change of variables** (source 2666-2668): `ρ = R/√s`, `t = η/√s`,
`τ = 2q/R + log s`, `ρ dρ dt = (R²/2) s^{-5/2} ds dη`, `dτ = (2/R) dq`; for `2c/R`-periodic `Θ`,
`∫_{τ∈[0,2c/R)} ∫_{ρ>lo} ∫_t ρ Θ(τ,ρ,t) = R c ∫_{{s>0, ρ>lo}} Θ(chartTau, ρ, t) d(ageμ c (-5/2))`. -/
def ChartChange : Prop :=
  ∀ (R c lo : ℝ), 0 < R → 0 < c → 0 ≤ lo →
    ∀ Θ : ℝ → ℝ → ℝ → ℝ≥0∞, Measurable (fun u : ℝ × ℝ × ℝ => Θ u.1 u.2.1 u.2.2) →
      (∀ τ ρ t, Θ (τ + 2 * c / R) ρ t = Θ τ ρ t) →
      ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ ρ in Ioi lo, ∫⁻ t : ℝ, ENNReal.ofReal ρ * Θ τ ρ t =
        ENNReal.ofReal (R * c) *
          ∫⁻ x in {x : Chart | 0 < x.1 ∧ lo < R / Real.sqrt x.1},
            Θ (chartTau R x) (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1) ∂(ageμ c (-5 / 2))

/-- **The `L²` identity for the majorant on the chart** (assembles `AgeShift`, `PolarReduction`,
`ChartChange`): for a measurable `2c/R`-periodic axisymmetric `M(τ, y)`,
`‖s^{-1/2} M(chartTau, chartY)‖²_{L²(ageBelow sm; ageμ c (-3/2))}
   = (2π c R)⁻¹ ∫_{τ∈[0,2c/R)} ∫_{|y'|>R/√sm} M²`. -/
def ChartL2Majorant : Prop :=
  ∀ (R c sm : ℝ), 0 < R → 0 < c → 0 < sm →
    ∀ M : ℝ → UnforcedLeray.Space → ℝ≥0∞, Measurable (Function.uncurry M) →
      (∀ τ y, M (τ + 2 * c / R) y = M τ y) → AxisymProf M →
      ∫⁻ x in ageBelow sm, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          M (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
        ENNReal.ofReal (1 / (2 * Real.pi * c * R)) *
          ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
            ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y},
              M τ y ^ (2 : ℝ)

/-- **The norm identity of the source tensor** (source 2683, `cartLift = s · nsSym`): for a
measurable `f`, `∫_{[0,2c/R)} ∫_{ℝ³} (s|nsSym f|)² = 2π R c ∫ |nsSym f|² d(ageμ c (-1/2))`
(`ageμ c (-1/2)` is the weight `s^{-1/2}` of `H_T`). -/
def ChartL2Source : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ f : Chart → Ten3, Measurable f →
    ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space, gAx R c f τ z ^ (2 : ℝ) =
      ENNReal.ofReal (2 * Real.pi * R * c) *
        ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ)
          ∂(ageμ c (-1 / 2))

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
