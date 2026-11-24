import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull

/-!
# `FmChartL2` (source 2666-2668, 3996-4005)

The `sm = ∞` form of `chartL2Majorant_of`: there is no age restriction, so the age shift
(`ageShift_holds`, exponent `-3/2 = -5/2 + 1`), the chart change (`chartChange_of` with `lo = 0`,
`chartChangeSE_holds`, `chartChangeTQ_holds`) and the polar reduction (`polarReduction_holds` with
`lo = 0`, the set `{0 < hRad}` being the whole space up to the null axis `axisNull_holds`) apply
directly.  The constants combine to `1/(2π c R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

private lemma fcl_ptOf_cont : Continuous (fun u : ℝ × ℝ => ptOf u.1 u.2) := by
  unfold ptOf
  have h3 : Continuous (fun u : ℝ × ℝ => (![u.1, 0, u.2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 _).comp h3

private lemma fcl_ptOf_meas : Measurable (fun u : ℝ × ℝ => ptOf u.1 u.2) :=
  fcl_ptOf_cont.measurable

private lemma fcl_sqrt_meas : Measurable (fun s : ℝ => Real.sqrt s) :=
  Real.continuous_sqrt.measurable

/-- `s · (s^{-1/2})² = 1` for `s > 0`, in `ℝ≥0∞`. -/
private lemma fcl_weight (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (s ^ (1 : ℝ)) * (ENNReal.ofReal (Real.sqrt s)⁻¹) ^ (2 : ℝ) = 1 := by
  rw [Real.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg s)) (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul hs.le, Real.rpow_two, inv_pow, Real.sq_sqrt hs.le,
    mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]

theorem fmChartL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmChartL2 := by
  intro R c hR hc M hM hper hax
  have hτm : Measurable (chartTau R) := by
    unfold chartTau
    exact ((measurable_const.mul (measurable_fst.comp measurable_snd)).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hψ : Measurable (fun x : Chart => (R / Real.sqrt x.1, x.2.2 / Real.sqrt x.1)) :=
    (measurable_const.div (fcl_sqrt_meas.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_snd).div (fcl_sqrt_meas.comp measurable_fst))
  have hYm : Measurable (chartY R) := fcl_ptOf_meas.comp hψ
  have hMc : Measurable (fun x : Chart => M (chartTau R x) (chartY R x)) :=
    hM.comp (hτm.prodMk hYm)
  have hGm : Measurable (fun x : Chart =>
      (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ)) :=
    ((ENNReal.measurable_ofReal.comp (fcl_sqrt_meas.comp measurable_fst).inv).mul hMc).pow_const _
  -- Step 1: the age shift `-3/2 = -5/2 + 1`
  have h2 := ageShift_holds c (-5 / 2) 1 _ hGm
  rw [show (-5 / 2 : ℝ) + 1 = -3 / 2 by norm_num] at h2
  rw [h2]
  try dsimp only at h2
  -- Step 2: the chart set `{0 < s, 0 < R/√s}` is `{0 < s}`
  have hSet : MeasurableSet {x : Chart | 0 < x.1 ∧ 0 < R / Real.sqrt x.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_const.div (fcl_sqrt_meas.comp measurable_fst)))
  have hae : ∀ᵐ x ∂(ageμ c (-5 / 2)),
      ENNReal.ofReal (x.1 ^ (1 : ℝ)) * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          M (chartTau R x) (chartY R x)) ^ (2 : ℝ) =
      {x : Chart | 0 < x.1 ∧ 0 < R / Real.sqrt x.1}.indicator
        (fun x : Chart => M (chartTau R x) (ptOf (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) ^
          (2 : ℝ)) x := by
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with x hx
    have hx0 : 0 < x.1 := hx.1.out
    have hmem : x ∈ {x : Chart | 0 < x.1 ∧ 0 < R / Real.sqrt x.1} :=
      ⟨hx0, div_pos hR (Real.sqrt_pos.2 hx0)⟩
    rw [Set.indicator_of_mem hmem]
    show ENNReal.ofReal (x.1 ^ (1 : ℝ)) *
        (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ) =
      M (chartTau R x) (ptOf (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) ^ (2 : ℝ)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
      fcl_weight x.1 hx0, one_mul]
    rfl
  rw [lintegral_congr_ae hae, lintegral_indicator hSet]
  -- Step 3: the change of variables `ChartChange` with `lo = 0`
  have hΘm : Measurable (fun u : ℝ × ℝ × ℝ => M u.1 (ptOf u.2.1 u.2.2) ^ (2 : ℝ)) :=
    (hM.comp (measurable_fst.prodMk (fcl_ptOf_meas.comp measurable_snd))).pow_const _
  have hperΘ : ∀ (τ ρ t : ℝ), M (τ + 2 * c / R) (ptOf ρ t) ^ (2 : ℝ) =
      M τ (ptOf ρ t) ^ (2 : ℝ) := fun τ ρ t => by rw [hper]
  have hCres := chartChange_of chartChangeSE_holds chartChangeTQ_holds R c 0 hR hc le_rfl
    (fun τ ρ t => M τ (ptOf ρ t) ^ (2 : ℝ)) hΘm hperΘ
  beta_reduce at hCres
  -- Step 4: polar reduction of each phase over the whole space
  have hN : volume {z : UnforcedLeray.Space | hRad z = 0} = 0 := axisNull_holds
  have hae0 : ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), hRad y ≠ 0 := by
    rw [ae_iff]
    simpa using hN
  have hsetae : ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
      y ∈ {y : UnforcedLeray.Space | 0 < hRad y} := by
    filter_upwards [hae0] with y hy
    show 0 < hRad y
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hy)
  have hfull : ∀ τ : ℝ, ∫⁻ y in {y : UnforcedLeray.Space | 0 < hRad y}, M τ y ^ (2 : ℝ) =
      ∫⁻ y : UnforcedLeray.Space, M τ y ^ (2 : ℝ) := fun τ => by
    rw [Measure.restrict_eq_self_of_ae_mem hsetae]
  have hinner : ∀ τ : ℝ,
      (∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ t : ℝ, ENNReal.ofReal ρ * M τ (ptOf ρ t) ^ (2 : ℝ)) =
        (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ y : UnforcedLeray.Space, M τ y ^ (2 : ℝ) := by
    intro τ
    have hH : Measurable (fun y : UnforcedLeray.Space => M τ y ^ (2 : ℝ)) :=
      (hM.comp (measurable_const.prodMk measurable_id)).pow_const _
    have hax' : ∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 →
        M τ y ^ (2 : ℝ) = M τ y' ^ (2 : ℝ) := fun y y' h1 h2 => by
      rw [hax τ y y' h1 h2]
    have hpr : ∫⁻ y in {y : UnforcedLeray.Space | 0 < hRad y}, M τ y ^ (2 : ℝ) =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ t : ℝ, ENNReal.ofReal ρ * M τ (ptOf ρ t) ^ (2 : ℝ) :=
      polarReduction_holds (fun y => M τ y ^ (2 : ℝ)) hH hax' 0 le_rfl
    have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have htop : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [hfull τ] at hpr
    rw [hpr, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  -- Step 5: the `τ`-integral
  have hτint : (∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ t : ℝ, ENNReal.ofReal ρ * M τ (ptOf ρ t) ^ (2 : ℝ)) =
      (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ y : UnforcedLeray.Space, M τ y ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2
      (by positivity)).ne')]
    exact lintegral_congr fun τ => hinner τ
  rw [hτint] at hCres
  -- Step 6: the constants
  have hK : ENNReal.ofReal (1 / (2 * Real.pi * c * R)) =
      (ENNReal.ofReal (R * c))⁻¹ * (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < R * c),
      ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (R * c)⁻¹)]
    congr 1
    field_simp
  have hRc0 : ENNReal.ofReal (R * c) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hRctop : ENNReal.ofReal (R * c) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hK, mul_assoc, hCres, ← mul_assoc, ENNReal.inv_mul_cancel hRc0 hRctop, one_mul]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
