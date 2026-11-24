import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PartIIIb_C_near_masked_22
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Majorant
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutMeas
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3

/-!
# `PartIII-b:C/near/masked/22/2`: `StripNear` from `sep:young` (source 4000-4003)

Source of record: `the November 2 reference manuscript`, lines 4000-4003.

Route.  `fullOut g` is `(√s)⁻¹ merRe(-W)` with `W = sepW (cartLift g)`.  Put `M(τ,y) = |W(y,τ)|₂`
for `|y'| > R/√r` and `0` otherwise (axisymmetric, `2c/R`-periodic, measurable).  Then
`‖1_{band} fullOut g‖² ≤ ‖(√s)⁻¹ M(chartTau,chartY)‖²_{L²(ageBelow r)}`, and `ChartL2Majorant` turns
this into `(2πcR)⁻¹ ∫_{[0,2c/R)}∫_{|y'|>R/√r} M²`.  `sep:young` (`j = 0`, `p = q = 2`, `b = 1`,
`rIn = R/√r`, `rOut = R/√(e^δ l)`, `rIn - rOut ≥ (1 - e^{-δ/4})R/√r`) bounds this by
`C² r/R² ∫_{[0,2c/R)}∫ |cartLift g|²`, and `ChartL2Source` evaluates the latter as
`2πRc ‖g‖²_{H_T}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The Euclidean norm `|W(y,τ)|₂` of `W = sepW (cartLift R c g)`. -/
def nearEN (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal ‖(WithLp.toLp 2 (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ)
    (NearInst.cartLift R c g) y τ) : EuclideanSpace ℂ (Fin 3))‖

/-- The receiver-truncated profile `1_{|y'| > R/√r} |W|₂`. -/
def nearM (ν μ R c r : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : UnforcedLeray.Space) : ℝ≥0∞ :=
  if R / Real.sqrt r < hRad y then nearEN ν μ R c g τ y else 0

/-- **Leaf Q1** (pointwise, 4000): `‖fullOut g x‖ ≤ (√s)⁻¹ |W(chartY x, chartTau x)|₂`
(`‖merRe w‖ ≤ ‖w‖₂`, `‖-w‖ = ‖w‖`, `fullOut = (√s)⁻¹ • merRe(-sepW …)`). -/
def NearPointwise : Prop :=
  ∀ (R c ν μ : ℝ) (g : Chart → Ten3) (x : Chart),
    ‖fullOut R c ν μ g x‖ₑ ≤
      ENNReal.ofReal (Real.sqrt x.1)⁻¹ * nearEN ν μ R c g (chartTau R x) (chartY R x)

/-- **Leaf Q2** (measurability and `2c/R`-periodicity of `nearM`): `cartLift` is jointly measurable
(`T8_1.measurable_cartLift_entry`), hence `sepW` is (`T8_1.measurable_sepW_comp`), the norm and
the `hRad` condition are measurable; periodicity from `sp_chartOf_period`-type periodicity of
`chartOf` in `τ` (period `2c/R`) and the substitution form of `sepW` (`T(τ + P + 2 log l) = T(τ + 2 log l)`). -/
def NearMeasPeriodic : Prop :=
  ∀ (R c ν μ r : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → 0 < ν → IsBoxTensor g →
    Measurable (Function.uncurry (nearM ν μ R c r g)) ∧
      ∀ τ y, nearM ν μ R c r g (τ + 2 * c / R) y = nearM ν μ R c r g τ y

/-- **Leaf Q3** (rotation covariance of the Cartesian lift, 2666-2683): for the vertical-axis
rotation `rotM co si`, `cylFrame (Rz) = R cylFrame z`, `chartOf` and `hRad` are invariant, so
`cartLift (Rz) = R cartLift(z) Rᵀ` (also on the axis, where `s = 0`). -/
def CartLiftRotCov : Prop :=
  ∀ (co si : ℝ), co ^ 2 + si ^ 2 = 1 → ∀ (R c : ℝ) (g : Chart → Ten3) (τ : ℝ)
    (z : UnforcedLeray.Space),
    NearInst.cartLift R c g τ (actM (rotM co si) z) =
      rotM co si * NearInst.cartLift R c g τ z * (rotM co si).transpose

/-- **Leaf Q4** (axisymmetry of `nearM`, 4171-4178): by `sepWEquivariance` (integrability of the
`sepW` integrand at receivers `|y'| > R/√r > R/√(e^δ l)` from `sepIntegrableOfSource_all`, as in
`sp_integrable`), `CartLiftRotCov`, the rotation `RotExists` carrying `y` to `y'` and the
invariance of the Euclidean norm under the real rotation matrix; the truncation is a function of
`hRad y` only. -/
def NearAxisym : Prop :=
  ∀ (R c ν μ δ l r : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → 0 < ν → μ ∈ Ioo (0 : ℝ) (1 / 4) →
    0 < δ → 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → IsBoxTensor g →
    (∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1) → AxisymProf (nearM ν μ R c r g)

/-- **Leaf Q5** (`sep:young`, 4000-4003; `j = 0`, `p = q = 2`, `b = 1`, `K = Kset` cast to `ℂ`,
`2 Re μ + 3/2 ≥ 3/2 > 0`; `IsSepSource (2c/R) (R/√(e^δ l)) (cartLift g)` by `sp_isSepSource_cartLift`;
`rIn = R/√r`, `rOut = R/√(e^δ l)`, `D = rIn - rOut ≥ (1 - e^{-δ/4}) R/√r` since `r ≤ e^{δ/2} l`;
Euclidean norm `≤ √3` sup norm (`youngDerivNorm` is the sup norm of `Fin 3 → ℂ`); conversion of
`ltauLq P 2` to the `Ico 0 P` double integral with `P = 2c/R`, `Ioc`/`Ico` differ by a null set).
The constant is `C² = 3 C_young² /(1 - e^{-δ/4})²`, which may depend on `Kset`, `δ` only. -/
def NearYoung : Prop :=
  UnforcedLeray.Short.IIIa.SepYoung → ∀ (Kset : Set ℝ), IsCompact Kset → Kset ⊆ Ioo (0 : ℝ) (1 / 4) →
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R c ν μ l r : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → 0 < ν → μ ∈ Kset →
        0 < l → l < r → r ≤ Real.exp (δ / 2) * l → IsBoxTensor g →
        (∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1) →
        ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
            ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt r < hRad y},
              nearM ν μ R c r g τ y ^ (2 : ℝ) ≤
          ENNReal.ofReal (C ^ 2 * (r / R ^ 2)) *
            ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
              UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) τ z ^ (2 : ℝ)

/-- **Leaf Q6** (source norm, 2683; `ChartL2Source`, `CartLiftNormOffAxis`, `AxisNull`,
`NsSymNormLe`): `∫_{[0,2c/R)}∫ |cartLift g|² ≤ 2πRc ‖g‖²_{H_T}`. -/
def NearSource : Prop :=
  ∀ (R c : ℝ) (g : Chart → Ten3), 0 < R → 0 < c → IsBoxTensor g →
    ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
        UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) τ z ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.pi * R * c) * eLpNorm g 2 (ageμ c (-1 / 2)) ^ (2 : ℝ)

theorem stripNear_holds_of (h1 : NearPointwise) (h2 : NearMeasPeriodic) (h4 : NearAxisym)
    (h5 : NearYoung) (h6 : NearSource) (hY : UnforcedLeray.Short.IIIa.SepYoung) : StripNear := by
  intro Kset hKc hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨C, hC0, hCb⟩ := h5 hY Kset hKc hKs δ hδ
  refine ⟨C, 0, 1, one_pos, ?_⟩
  intro p d hreg hν μ hμ l r hl hlr hrl hrS g hg hsupp
  have hr : 0 < r := hl.trans hlr
  have hRpos : 0 < p.R := by
    have : p.R = p.ε⁻¹ := by simp [Params.R]
    rw [this]
    exact inv_pos.2 p.ε_pos
  have hμ' : μ ∈ Ioo (0 : ℝ) (1 / 4) := hKs hμ
  have hsupp' : ∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1 := fun x hx => (hsupp x hx).1
  obtain ⟨hMeas, hPer⟩ := h2 p.R p.c p.ν μ r g hRpos p.c_pos p.ν_pos hg
  have hAx := h4 p.R p.c p.ν μ δ l r g hRpos p.c_pos p.ν_pos hμ' hδ hl hlr hrl hg hsupp'
  have hid := chartL2Majorant_of ageShift_holds polarReduction_holds
    (chartChange_of chartChangeSE_holds chartChangeTQ_holds) p.R p.c r hRpos p.c_pos hr
    (nearM p.ν μ p.R p.c r g) hMeas hPer hAx
  have hmeasF : Measurable (fullOut p.R p.c p.ν μ g) :=
    Realization.FullOutMeasAux.fullOut_measurable_aux p.R p.c p.ν μ g hg
  have hmeasI : Measurable ((ageBand l r).indicator (fullOut p.R p.c p.ν μ g)) :=
    hmeasF.indicator (measurableSet_ageBand l r)
  refine ⟨hmeasI.aestronglyMeasurable, ?_⟩
  have h2' : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2']
  have hY5 := hCb p.R p.c p.ν μ l r g hRpos p.c_pos p.ν_pos hμ hl hlr hrl hg hsupp'
  have hS6 := h6 p.R p.c g hRpos p.c_pos hg
  have hpt : ∀ x, ‖(ageBand l r).indicator (fullOut p.R p.c p.ν μ g) x‖ₑ ≤
      (ageBelow r).indicator (fun x => ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
        nearM p.ν μ p.R p.c r g (chartTau p.R x) (chartY p.R x)) x := by
    intro x
    by_cases hx : x ∈ ageBand l r
    · have hx' : l ≤ x.1 ∧ x.1 < r := hx
      have hs : 0 < x.1 := lt_of_lt_of_le hl hx'.1
      have hxB : x ∈ ageBelow r := show x.1 < r from hx'.2
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxB]
      have hrad : p.R / Real.sqrt r < hRad (chartY p.R x) := by
        have : hRad (chartY p.R x) = p.R / Real.sqrt x.1 := by
          unfold hRad chartY
          simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
          rw [show (p.R / Real.sqrt x.1) ^ 2 + (0:ℝ) ^ 2 = (p.R / Real.sqrt x.1) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
        rw [this]
        exact div_lt_div_of_pos_left hRpos (Real.sqrt_pos.2 hs) (Real.sqrt_lt_sqrt hs.le hx'.2)
      unfold nearM
      rw [if_pos hrad]
      exact h1 p.R p.c p.ν μ g x
    · simp [Set.indicator_of_notMem hx]
  have hind : ∫⁻ x, ((ageBelow r).indicator (fun x => ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
        nearM p.ν μ p.R p.c r g (chartTau p.R x) (chartY p.R x)) x) ^ (2 : ℝ)
          ∂(ageμ p.c (-3 / 2)) =
      ∫⁻ x in ageBelow r, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
        nearM p.ν μ p.R p.c r g (chartTau p.R x) (chartY p.R x)) ^ (2 : ℝ)
          ∂(ageμ p.c (-3 / 2)) := by
    have hmeas : MeasurableSet (ageBelow r) := measurableSet_lt measurable_fst measurable_const
    rw [← lintegral_indicator hmeas]
    congr 1
    ext x
    by_cases hx : x ∈ ageBelow r
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have step1 : ∫⁻ x, ‖(ageBand l r).indicator (fullOut p.R p.c p.ν μ g) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2)) ≤
      ENNReal.ofReal (1 / (2 * Real.pi * p.c * p.R)) *
        (ENNReal.ofReal (C ^ 2 * (r / p.R ^ 2)) *
          (ENNReal.ofReal (2 * Real.pi * p.R * p.c) *
            eLpNorm g 2 (ageμ p.c (-1 / 2)) ^ (2 : ℝ))) := by
    calc _ ≤ ∫⁻ x, ((ageBelow r).indicator (fun x => ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          nearM p.ν μ p.R p.c r g (chartTau p.R x) (chartY p.R x)) x) ^ (2 : ℝ)
            ∂(ageμ p.c (-3 / 2)) :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num)
      _ = _ := hind
      _ = _ := hid
      _ ≤ _ := by
          gcongr
          exact hY5.trans (by gcongr)
  have hconst : ENNReal.ofReal (1 / (2 * Real.pi * p.c * p.R)) *
        (ENNReal.ofReal (C ^ 2 * (r / p.R ^ 2)) * ENNReal.ofReal (2 * Real.pi * p.R * p.c)) =
      ENNReal.ofReal ((C * (p.ε * Real.sqrt r)) ^ 2) := by
    have hε : p.ε = p.R⁻¹ := by simp [Params.R]
    have hcp := p.c_pos
    have hpi := Real.pi_pos
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hε, mul_pow, mul_pow, Real.sq_sqrt hr.le]
    have := Real.pi_pos
    have := p.c_pos
    field_simp
  have hK : 0 ≤ C * (p.ε * Real.sqrt r) := by
    have := p.ε_pos
    positivity
  have step2 : ∫⁻ x, ‖(ageBand l r).indicator (fullOut p.R p.c p.ν μ g) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2)) ≤
      ENNReal.ofReal ((C * (p.ε * Real.sqrt r)) ^ 2) * eLpNorm g 2 (ageμ p.c (-1 / 2)) ^ (2 : ℝ) := by
    refine step1.trans (le_of_eq ?_)
    rw [← hconst]
    simp only [mul_assoc]
  calc _ ≤ (ENNReal.ofReal ((C * (p.ε * Real.sqrt r)) ^ 2) *
          eLpNorm g 2 (ageμ p.c (-1 / 2)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step2 (by norm_num)
    _ = ENNReal.ofReal (C * p.ν⁻¹ ^ 0 * (p.ε * Real.sqrt r)) * eLpNorm g 2 (ageμ p.c (-1 / 2)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul hK]
        norm_num

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
