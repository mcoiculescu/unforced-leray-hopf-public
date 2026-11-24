import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# `FullMajL2` decomposed (`PartIII-b:C/near/masked/18/3/2/4`, source 3996-4011, 2683, 2681-2691)

Source: `the November 2 reference manuscript`.

Route (unmasked version of `FarMajorantL2`, `Sub/FarMajorantL2.lean`): the Cartesian-component sum
`gradKNorm` is NOT rotation invariant, so it is first dominated by the radial kernel
`t^{-2}(1+|w|/√t)^{-4}` (`fmKer`, `t = ν(1-l²)`, `L¹` norm `≲ t^{-1/2}`); `fullMaj ≤ K · dilMajG`
pointwise (`FmPointwise`, `FmKerDom`).  `dilMajG` is a measurable axisymmetric `P`-periodic profile,
so the chart identity (`FmChartL2`, the `sm = ∞` form of `ChartL2Majorant`) reduces its weighted
`L²` norm to the `L²([0,P)×ℝ³)` norm, which is bounded by Young + Minkowski + the dilation margin
`∫_0^1 l^{2μ+1/2}(1-l²)^{-1/2} dl < ∞` (`FmDilL2`, decomposed into `FmFixedL`, `FmMargin`,
`FmKerMeasurable`, `FmKerL1`).  The source norm is `ChartL2Source` plus `FmNsSymTv4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The radial kernel `t^{-2}(1+|w|/√t)^{-4}`, `t = ν(1-l²)`, for `l ∈ (0,1)` (and `0` otherwise, so
that it is jointly measurable in `(l, w)`). -/
def fmKer (ν l : ℝ) (w : UnforcedLeray.Space) : ℝ≥0∞ :=
  if l ∈ Ioo (0 : ℝ) 1 then
    ENNReal.ofReal ((ν * (1 - l ^ 2)) ^ (-2 : ℝ) *
      (1 + ‖w‖ / Real.sqrt (ν * (1 - l ^ 2))) ^ (-4 : ℝ))
  else 0

/-- The dilated positive kernel integral with the radial kernel `fmKer` (cf. `dilMaj`). -/
def dilMajG (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (τ : ℝ) (y : UnforcedLeray.Space) :
    ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
    ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z

/-- **Pointwise domination** (source 3996-4011): if `gradKNorm ≤ K · fmKer` then
`fullMaj ≤ K · dilMajG` of the source profile `gAx` (`srcNorm (cartLift) = gAx` off the axis,
`CartLiftNormOffAxis`; the axis is null, `AxisNull`; on `Ioo 0 1` `fmKer` is the radial kernel). -/
def FmPointwise : Prop :=
  ∀ (R c ν μ K : ℝ), (∀ l ∈ Ioo (0 : ℝ) 1, ∀ w : UnforcedLeray.Space,
      gradKNorm (ν * (1 - l ^ 2)) w ≤ ENNReal.ofReal K * fmKer ν l w) →
    ∀ (f : Chart → Ten3) (x : Chart),
      fullMaj R c ν μ f x ≤
        ENNReal.ofReal K * dilMajG ν μ (gAx R c f) (chartTau R x) (chartY R x)

/-- **Radial domination of the heat-Leray gradient** (source 3604-3610): `|∇K_1(w)| ≤ K(1+|w|)^{-4}`
(`gk1_bound` in `.../FullOutLip/GradKL1.lean`) and the heat scaling `gk1_gsum_scale`. -/
def FmKerDom : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℝ, 0 < ν → ∀ l ∈ Ioo (0 : ℝ) 1, ∀ w : UnforcedLeray.Space,
    gradKNorm (ν * (1 - l ^ 2)) w ≤ ENNReal.ofReal K * fmKer ν l w

/-- `L¹` norm of the radial kernel: `∫ t^{-2}(1+|w|/√t)^{-4} dw = t^{-1/2} ∫(1+|u|)^{-4} du`. -/
def FmKerL1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ l ∈ Ioo (0 : ℝ) 1,
    ∫⁻ w : UnforcedLeray.Space, fmKer ν l w ≤
      ENNReal.ofReal C * ENNReal.ofReal ((ν * (1 - l ^ 2)) ^ (-(1 / 2 : ℝ)))

/-- Joint measurability of the kernel in `(l, w)` (continuous on `Ioo 0 1 × ℝ³`, `0` elsewhere). -/
def FmKerMeasurable : Prop :=
  ∀ ν : ℝ, Measurable (fun p : ℝ × UnforcedLeray.Space => fmKer ν p.1 p.2)

/-- **Young at a fixed dilation** (generalizes `DilMajFixedL`, the kernel `fmKer ν l` replacing
`farKern d`; `YoungDilated` and `PeriodShift` apply to any measurable kernel). -/
def FmFixedL : Prop :=
  ∀ (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), Measurable (Function.uncurry g) →
    ∀ P : ℝ, 0 < P → (∀ τ z, g (τ + P) z = g τ z) → ∀ A : ℝ≥0∞, ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫⁻ w, fmKer ν l w ≤ A →
        (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
            (ENNReal.ofReal (l ^ (2 * μ + 2)) *
              ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z)
                ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * A *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Dilation margin** (source 4001, `μ > -1/4`): `∫_0^1 l^{2μ+1/2}(1-l²)^{-1/2} dl < ∞`
(`LinAux.lint_inv_sqrt_lt_top` in `FullOutLip/Lin/Core.lean` handles the `(1-l²)^{-1/2}` part;
`l^{2μ+1/2}` is bounded on `(0,1)`). -/
def FmMargin : Prop :=
  ∀ μ : ℝ, -(1 / 4) < μ →
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
      ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) < ⊤

/-- **`L²([0,P)×ℝ³)` bound of the dilated radial operator** (Young + Minkowski + margin; squared
form): `‖dilMajG‖² ≤ C² ‖g‖²` for measurable `P`-periodic `g`. -/
def FmDilL2 : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → -(1 / 4) < μ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℝ → UnforcedLeray.Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      ∀ P : ℝ, 0 < P → (∀ τ z, g (τ + P) z = g τ z) →
        ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space, dilMajG ν μ g τ y ^ (2 : ℝ) ≤
          ENNReal.ofReal C ^ (2 : ℝ) *
            ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)

/-- Joint measurability of `dilMajG` (cf. `DilMajMeasurable`; uses `FmKerMeasurable`). -/
def FmDilMeasurable : Prop :=
  ∀ (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), Measurable (Function.uncurry g) →
    Measurable (Function.uncurry (dilMajG ν μ g))

/-- `dilMajG` of an axisymmetric profile is axisymmetric in `y` (cf. `DilMajAxisym`, via
`RotExists`; `fmKer` is radial). -/
def FmDilAxisym : Prop :=
  ∀ (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞), AxisymProf g →
    ∀ τ (y y' : UnforcedLeray.Space), hRad y = hRad y' → y 2 = y' 2 →
      dilMajG ν μ g τ y = dilMajG ν μ g τ y'

/-- **Unmasked chart `L²` identity** (the `sm = ∞` form of `ChartL2Majorant`; `AgeShift`,
`PolarReduction` with `lo = 0`, `ChartChange`; the axis is null): for a measurable `2c/R`-periodic
axisymmetric `M`,
`‖s^{-1/2} M(chartTau, chartY)‖²_{L²(ageμ c (-3/2))} = (2π c R)⁻¹ ∫_{[0,2c/R)} ∫_{ℝ³} M²`. -/
def FmChartL2 : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c →
    ∀ M : ℝ → UnforcedLeray.Space → ℝ≥0∞, Measurable (Function.uncurry M) →
      (∀ τ y, M (τ + 2 * c / R) y = M τ y) → AxisymProf M →
      ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          M (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
        ENNReal.ofReal (1 / (2 * Real.pi * c * R)) *
          ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ y : UnforcedLeray.Space, M τ y ^ (2 : ℝ)

/-- `|nsSym T| ≤ C |tv4 T|` (`tv4 T = (T₀₀, symRZ T, T₂₂, T₁₁)`, so `|nsSym T|² = |T₀₀|² + |T₁₁|² +
|T₂₂|² + 2 symRZ² ≤ 2 |tv4 T|²`). -/
def FmNsSymTv4 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Ten3,
    ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym T)) ≤
      ENNReal.ofReal C * ‖tv4 T‖ₑ

theorem fullMajL2_of (h1 : FmPointwise) (hKd : FmKerDom) (h3 : FmDilL2) (h4 : FmDilMeasurable)
    (h5 : FmDilAxisym) (h6 : FmChartL2) (h7 : FmNsSymTv4) (hG : GAxFacts)
    (hCS : ChartL2Source) : FullMajL2 := by
  intro R c ν μ hR hc hν hμ
  obtain ⟨K, hK0, hKd⟩ := hKd
  obtain ⟨C3, hC30, h3b⟩ := h3 ν μ hν hμ
  obtain ⟨C7, hC70, h7b⟩ := h7
  refine ⟨K * C3 * C7, by positivity, fun f hf => ?_⟩
  obtain ⟨hax, hper, hgm⟩ := hG R c f hR hc hf.measurable
  set g := gAx R c f with hg
  set Mf : ℝ → UnforcedLeray.Space → ℝ≥0∞ := dilMajG ν μ g with hMf
  have hMmeas : Measurable (Function.uncurry Mf) := h4 ν μ g hgm
  have hMper : ∀ τ y, Mf (τ + 2 * c / R) y = Mf τ y := by
    intro τ y
    simp only [hMf, dilMajG]
    refine lintegral_congr fun l => ?_
    congr 1
    refine lintegral_congr fun z => ?_
    have : τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R := by ring
    rw [this, hper]
  have hMax : AxisymProf Mf := fun τ y y' e1 e2 => h5 ν μ g hax τ y y' e1 e2
  have hPpos : 0 < 2 * c / R := div_pos (by linarith) hR
  have hp : (0 : ℝ) < 2 := by norm_num
  set E : ℝ≥0∞ := ∫⁻ x, ‖tv4 (f x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) with hE
  set X : ℝ≥0∞ := ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ y : UnforcedLeray.Space,
    Mf τ y ^ (2 : ℝ) with hX
  set G : ℝ≥0∞ := ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
    g τ z ^ (2 : ℝ) with hGdef
  set k : ℝ := 1 / (2 * Real.pi * c * R) with hk
  have hk0 : 0 < k := by positivity
  -- Step 1: pointwise domination
  have step1 : ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal K ^ (2 : ℝ) * ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
        Mf (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    have hd := h1 R c ν μ K (fun l hl w => hKd ν hν l hl w) f x
    calc (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * (ENNReal.ofReal K *
            Mf (chartTau R x) (chartY R x))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hd) hp.le
      _ = (ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
            Mf (chartTau R x) (chartY R x))) ^ (2 : ℝ) := by rw [mul_left_comm]
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hp.le
  -- Step 2: the chart identity
  have step2 := h6 R c hR hc Mf hMmeas hMper hMax
  -- Step 3: Young + Minkowski
  have step3 : X ≤ ENNReal.ofReal C3 ^ (2 : ℝ) * G := h3b g hgm _ hPpos hper
  -- Step 4: the source norm
  have hGE : G ≤ ENNReal.ofReal (2 * Real.pi * R * c) * (ENNReal.ofReal C7 ^ (2 : ℝ) * E) := by
    rw [hGdef, hg, hCS R c hR hc f hf.measurable]
    refine mul_le_mul' le_rfl ?_
    rw [hE, ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    calc ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal C7 * ‖tv4 (f x)‖ₑ) ^ (2 : ℝ) := ENNReal.rpow_le_rpow (h7b _) hp.le
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hp.le
  have hkk : ENNReal.ofReal k * ENNReal.ofReal (2 * Real.pi * R * c) = 1 := by
    rw [← ENNReal.ofReal_mul hk0.le, hk]
    have : 1 / (2 * Real.pi * c * R) * (2 * Real.pi * R * c) = 1 := by
      field_simp
    rw [this, ENNReal.ofReal_one]
  have hcoef : ENNReal.ofReal (K * C3 * C7) ^ (2 : ℝ) =
      ENNReal.ofReal K ^ (2 : ℝ) * ENNReal.ofReal C3 ^ (2 : ℝ) * ENNReal.ofReal C7 ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hK0 hC30), ENNReal.ofReal_mul hK0,
      ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  calc ∫⁻ x, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))
      ≤ ENNReal.ofReal K ^ (2 : ℝ) * (ENNReal.ofReal k * X) := by
        rw [← step2]; exact step1
    _ ≤ ENNReal.ofReal K ^ (2 : ℝ) * (ENNReal.ofReal k * (ENNReal.ofReal C3 ^ (2 : ℝ) *
          (ENNReal.ofReal (2 * Real.pi * R * c) * (ENNReal.ofReal C7 ^ (2 : ℝ) * E)))) := by
        gcongr
        exact step3.trans (mul_le_mul' le_rfl hGE)
    _ = ENNReal.ofReal K ^ (2 : ℝ) * ENNReal.ofReal C3 ^ (2 : ℝ) * ENNReal.ofReal C7 ^ (2 : ℝ) *
          ((ENNReal.ofReal k * ENNReal.ofReal (2 * Real.pi * R * c)) * E) := by ring
    _ = _ := by rw [hkk, one_mul, hcoef]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
