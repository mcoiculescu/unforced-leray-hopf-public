import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg

/-!
# `PartIII-b:C/ward/9/3` (decomposition): the young `Y₂` bound of the stream transitions

Source `the November 2 reference manuscript`
3687-3713 (stream cutoff majorants), 4202-4216 (`ward:cutoff-source`, `transField`), 2683-2689
(chart normalization, lift identity), 3631-3648 (`sep:young`, `p = q = 2`, `b = 1`).

`transField = sepTrans (oldPhys R c g)` (`transField_eq_sepTrans`) is supported on the annulus
`R√ν ≤ ϱ ≤ R√(5ν/4)`; there it is dominated pointwise by the separated-kernel majorant
`transMajA` (as `transMaj` of `PartIII-b_C_rep_5_2_2TransOrg`, but with the genuine weight
`λ^{a}`, `a = 2μ + 2 > 3/2`, in place of `λ^0`: for `p = 2` the dilation integral
`∫₀¹ λ^{a - 3/2} dλ` needs `a > 1/2`, so the crude weight `a = 0` of `transMaj` is not enough).
The chart `L²(s^{-3/2}dς)` norm of the majorant is `≤ C‖g‖_{L²(s^{-1/2}dς)}` by the lift identity
(`oldCutSrc`), `ChartPhysL2`, `IIIa.SepDomYoung` (`p = q = 2`, `b = 1`) and the `L²_τL² → L²_τL²`
bound of the outward primitive majorant.  All constants may depend on `ν, μ, R, c, χ_y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The transition majorant with weight `λ^a` (source 3684-3712, 4181-4192):
`1_ann (sepDom a 0 + L⁻¹ sepDom a 1 + L⁻² outMaj a)`, gap `D = transGap ν R`, `L = transLen ν R`
(`transMaj` is the case `a = 0`). -/
def transMajA (a ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => IIIa.sepDom a 0 (transGap ν R) g τ y +
      ENNReal.ofReal (transLen ν R)⁻¹ * IIIa.sepDom a 1 (transGap ν R) g τ y +
      ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) * outMaj a (transGap ν R) g τ (ϱ y) (y 2)) y

/-- **Sub 1** (pointwise domination of `transField`, source 3684-3712, 4181-4214, 4203-4214; the
proof of `transSepDom` of `Concrete/ReturnRepair/Sub/PartIII-b_C_rep_5_2_2/TransSepDom.lean`
with (i) the weight `2μ + 2` kept instead of weakened to `0` (`sepX0Dom`, `outPrimPointwise_of`
already carry it before the `sepDom_anti_a` steps), and (ii) arbitrary `ν, R > 0` (constants
depending on them) instead of `ν ≤ 1 ≤ R` (in `transCommPoint_of`, `tsd_abstract`); the
separated source of `g` is `oldCutSrc R c (R√(5ν/6)) g`, with the same `sepW` responses as
`oldPhys R c g` (`wardYWYoungL2_proved` step `l2_bridge` in `Sub/PartIII-b_C_ward_9/L2.lean`),
so `transField_eq_sepTrans` and `sepTrans_congr` apply). -/
def WardYTransDomG : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
      ‖transField ν μ R c χy g τ y‖ₑ ≤
        ENNReal.ofReal C * transMajA (2 * μ + 2) ν R
          (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y

/-- **Sub 2** (the outward primitive majorant in `L²_τL² → L²_τL²`, source 4181-4192, 3687-3697;
the `p = 2` analogue of `OutMajAnnulusL2` in `PartIII-b_C_rep_5_2_2TransOrg.lean`, proved in
`rep_5_2_2/OutMajAnnulusL2.lean` for `p = 22/19`): the vertical kernel `(D² + t²)^{-1}` has
`L¹(ℝ)` norm `π/D` (Young `L² * L¹ → L²`), the dilation integral is `∫₀¹ λ^{a-3/2} dλ < ∞` for
`a > 1`, the horizontal variable is Cauchy-Schwarz over the old disk `ϱ ≤ R√(5ν/6)` (area
`π(5ν/6)R²`), and the annulus has area `πνR²/4` (`annulusFubiniL2`); `C` depends on `ν, R, a`
only (the normalized `L²_τ` norm on a period is invariant under the phase shift of the dilation). -/
def OutMajAnnulusL2P2 : Prop :=
  ∀ (ν R a : ℝ), 0 < ν → 0 < R → 1 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ), 0 < P →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
            (fun y => outMaj a (transGap ν R) g τ (ϱ y) (y 2))) ≤
          ENNReal.ofReal C * IIIa.ltauLq P 2 g

/-- **Sub 3** (chart `L²` norm of the majorant, source 2683-2689, 3631-3648 with `p = q = 2`,
`b = 1`, 3651-3656; the `p = 2` analogue of `transMajChart` of
`rep_5_2_2/TransMajChart.lean`): Minkowski on the chart for the three components of `transMajA`,
for each `ChartPhysL2` (`R = ε⁻¹` there, period `2c/R`) and then `IIIa.SepDomYoung`
(`p = q = 2`, `b = 1`, `a = 2μ + 2 ≥ 1 + δ`, `D = transGap ν R = (1 - √(5/6))R√ν`) for the `W` and
`D` parts and `OutMajAnnulusL2P2` (with `a = 2μ + 2 > 3/2`) for the `S` part; the lift identity
`ltauLq (2c/R) 2 (srcNorm (oldCutSrc ..)) ≤ √π R ‖g‖` is `l2_bridge` of
`Sub/PartIII-b_C_ward_9/L2.lean`; `ageμ c (-3/2)`-integral against `ChartPhysL2` as in
`chartYoungTransport` (`T16_SepYoung`). -/
def WardYTransMajChartG : Prop :=
  ∀ (ν μ R c : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      (∫⁻ q, ENNReal.ofReal q.1⁻¹ *
          transMajA (2 * μ + 2) ν R (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))
            (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-- **Sub 4** (measurability, cf. `WardYYoungMeas`, `wardX0_measurable_of_measurable`,
`sepWre_measurable`, `sepX0` smooth off the old disk): the young chart reading of `transField`
is a.e. strongly measurable for `ageμ c (-3/2)` (`transField = sepTrans (oldCutSrc ..)` a.e.-wise
through `sepTrans_congr`; `streamCorr`, `outPrim` and `fderiv` of the jointly measurable
`sepX0` are jointly measurable). -/
def WardYTransMeasG : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      AEStronglyMeasurable (wardYoungRead ν R (transField ν μ R c χy g)) (ageμ c (-3 / 2))

/-- Pointwise: the young chart reading is dominated by `C s^{-1/2} · majorant`. -/
private theorem read_sq_le {ν R : ℝ} (hR : 0 < R) {F : ℝ → Space → Space} {C : ℝ} (hC0 : 0 ≤ C)
    {M : ℝ → Space → ℝ≥0∞}
    (hF : ∀ (τ : ℝ) (y : Space), 0 < ϱ y → ‖F τ y‖ₑ ≤ ENNReal.ofReal C * M τ y) (q : Chart) :
    ‖wardYoungRead ν R F q‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (C ^ 2) *
      (ENNReal.ofReal q.1⁻¹ * M (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) := by
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      simp
    · rw [wyl_youngRead_of_young _ hq]
      have hy : 0 < ϱ (NearInst.chartY R q) := by
        rw [ϱ_chartY hR hs]; positivity
      have h1 := hF (NearInst.chartTau R q) _ hy
      have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hsq.le)
        (norm_nonneg _)), ENNReal.ofReal_mul (inv_nonneg.2 hsq.le), ENNReal.mul_rpow_of_nonneg _ _
        (by norm_num), ofReal_norm]
      have hsc : ENNReal.ofReal (Real.sqrt q.1)⁻¹ ^ (2 : ℝ) = ENNReal.ofReal q.1⁻¹ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hsq.le) (by norm_num)]
        congr 1
        rw [Real.rpow_two, inv_pow, Real.sq_sqrt hs.le]
      rw [hsc]
      have h2 : ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ₑ ^ (2 : ℝ) ≤
          (ENNReal.ofReal C * M (NearInst.chartTau R q) (NearInst.chartY R q)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h2
      have hC : ENNReal.ofReal C ^ (2 : ℝ) = ENNReal.ofReal (C ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC0 (by norm_num), Real.rpow_two]
      rw [hC] at h2
      calc ENNReal.ofReal q.1⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ₑ ^ (2 : ℝ)
          ≤ ENNReal.ofReal q.1⁻¹ * (ENNReal.ofReal (C ^ 2) *
              M (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) := by gcongr
        _ = _ := by ring
  · have : wardYoungRead ν R F q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem (show q ∉ wardYoungSet ν from hq)]
    rw [this]
    simp


/-- The target from the four lemmas. -/
theorem wardYTransYoungL2_of (h1 : WardYTransDomG) (h2 : WardYTransMajChartG)
    (h3 : WardYTransMeasG) : WardYTransYoungL2 := by
  intro ν μ R c χy hχ hν hR hc hμ
  obtain ⟨C1, hC1, hD⟩ := h1 ν μ R c χy hχ hν hR hc hμ
  obtain ⟨C2, hC2, hM⟩ := h2 ν μ R c hν hR hc hμ
  refine ⟨C1 * C2, fun g hg => ⟨(h3 ν μ R c χy hχ hν hR hc hμ g hg), ?_⟩⟩
  have hpt := fun q => read_sq_le (ν := ν) hR hC1
    (M := transMajA (2 * μ + 2) ν R (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)))
    (hD g hg) q
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ q, ‖wardYoungRead ν R (transField ν μ R c χy g) q‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
        (1 / (2 : ℝ))
      ≤ (∫⁻ q, ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal q.1⁻¹ *
          transMajA (2 * μ + 2) ν R
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))
            (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) ∂(ageμ c (-3 / 2))) ^
          (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = ENNReal.ofReal C1 * (∫⁻ q, ENNReal.ofReal q.1⁻¹ *
          transMajA (2 * μ + 2) ν R
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))
            (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
          (1 / (2 : ℝ)) := by
        have hk : ENNReal.ofReal (C1 ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal C1 := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC1]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hk]
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * eLpNorm g 2 (ageμ c (-1 / 2))) := by
        gcongr
        exact hM g hg
    _ = ENNReal.ofReal (C1 * C2) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC1]

end UnforcedLeray.Short.PartIIIb.Concrete
