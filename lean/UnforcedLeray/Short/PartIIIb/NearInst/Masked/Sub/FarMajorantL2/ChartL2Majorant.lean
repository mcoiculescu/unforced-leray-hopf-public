import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The `L²` identity for the majorant on the chart (source 2666-2668, 3996-4005)

`chartL2Majorant_of`: the age-weight `s^{-3/2}` of `ageBelow sm` is `s^{1}` times the weight
`s^{-5/2}` (`AgeShift`); on `{s < sm}` the factor `s · (s^{-1/2})²` is `1`, and the region
`{s < sm}` is the chart region `{ρ > R/√sm}` (ρ = R/√s). `ChartChange` turns the `(s, η)`-integral
into a `(τ, ρ, t)`-integral, `PolarReduction` turns each `(ρ, t)`-integral into a `ℝ³`-integral over
`{hRad > R/√sm}`, and the constants combine to `1/(2π c R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

private lemma cml_ptOf_cont : Continuous (fun u : ℝ × ℝ => ptOf u.1 u.2) := by
  unfold ptOf
  have h3 : Continuous (fun u : ℝ × ℝ => (![u.1, 0, u.2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 _).comp h3

private lemma cml_ptOf_meas : Measurable (fun u : ℝ × ℝ => ptOf u.1 u.2) :=
  cml_ptOf_cont.measurable

private lemma cml_sqrt_meas : Measurable (fun s : ℝ => Real.sqrt s) :=
  Real.continuous_sqrt.measurable

/-- `s · (s^{-1/2})² = 1` for `s > 0`, in `ℝ≥0∞`. -/
private lemma cml_weight (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (s ^ (1 : ℝ)) * (ENNReal.ofReal (Real.sqrt s)⁻¹) ^ (2 : ℝ) = 1 := by
  rw [Real.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg s)) (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul hs.le, Real.rpow_two, inv_pow, Real.sq_sqrt hs.le,
    mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]

theorem chartL2Majorant_of (hS : AgeShift) (hP : PolarReduction) (hC : ChartChange) :
    ChartL2Majorant := by
  intro R c sm hR hc hsm M hM hper hax
  have hτm : Measurable (chartTau R) := by
    unfold chartTau
    exact ((measurable_const.mul (measurable_fst.comp measurable_snd)).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hψ : Measurable (fun x : Chart => (R / Real.sqrt x.1, x.2.2 / Real.sqrt x.1)) :=
    (measurable_const.div (cml_sqrt_meas.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_snd).div (cml_sqrt_meas.comp measurable_fst))
  have hYm : Measurable (chartY R) := cml_ptOf_meas.comp hψ
  have hMc : Measurable (fun x : Chart => M (chartTau R x) (chartY R x)) :=
    hM.comp (hτm.prodMk hYm)
  have hGm : Measurable (fun x : Chart =>
      (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ)) :=
    ((ENNReal.measurable_ofReal.comp (cml_sqrt_meas.comp measurable_fst).inv).mul hMc).pow_const _
  have hIm : Measurable ((ageBelow sm).indicator (fun x : Chart =>
      (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ))) :=
    hGm.indicator (measurableSet_ageBelow sm)
  -- Step 1: the age shift `-3/2 = -5/2 + 1`
  have h1 : (∫⁻ x in ageBelow sm, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
        M (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) =
      ∫⁻ x, (ageBelow sm).indicator (fun x : Chart =>
        (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ)) x
        ∂(ageμ c (-3 / 2)) :=
    (lintegral_indicator (measurableSet_ageBelow sm) _).symm
  rw [h1]
  have h2 := hS c (-5 / 2) 1 _ hIm
  rw [show (-5 / 2 : ℝ) + 1 = -3 / 2 by norm_num] at h2
  rw [h2]
  -- Step 2: the chart set `{0 < s, R/√sm < R/√s}` is `{s < sm}`
  have hlo : 0 ≤ R / Real.sqrt sm := div_nonneg hR.le (Real.sqrt_nonneg _)
  have hSet : MeasurableSet {x : Chart | 0 < x.1 ∧ R / Real.sqrt sm < R / Real.sqrt x.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_const.div (cml_sqrt_meas.comp measurable_fst)))
  have hmono : ∀ s : ℝ, 0 < s → (R / Real.sqrt sm < R / Real.sqrt s ↔ s < sm) := by
    intro s hs
    rw [div_lt_div_iff_of_pos_left hR (Real.sqrt_pos.2 hsm) (Real.sqrt_pos.2 hs),
      Real.sqrt_lt_sqrt_iff hs.le]
  have hae : ∀ᵐ x ∂(ageμ c (-5 / 2)),
      ENNReal.ofReal (x.1 ^ (1 : ℝ)) * (ageBelow sm).indicator (fun x : Chart =>
        (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ)) x =
      {x : Chart | 0 < x.1 ∧ R / Real.sqrt sm < R / Real.sqrt x.1}.indicator
        (fun x : Chart => M (chartTau R x) (ptOf (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) ^
          (2 : ℝ)) x := by
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with x hx
    have hx0 : 0 < x.1 := hx.1.out
    by_cases hlt : x.1 < sm
    · have hmem : x ∈ {x : Chart | 0 < x.1 ∧ R / Real.sqrt sm < R / Real.sqrt x.1} :=
        ⟨hx0, (hmono x.1 hx0).2 hlt⟩
      rw [Set.indicator_of_mem (show x ∈ ageBelow sm from hlt), Set.indicator_of_mem hmem]
      show ENNReal.ofReal (x.1 ^ (1 : ℝ)) *
          (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * M (chartTau R x) (chartY R x)) ^ (2 : ℝ) =
        M (chartTau R x) (chartY R x) ^ (2 : ℝ)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
        cml_weight x.1 hx0, one_mul]
    · have hnmem : x ∉ {x : Chart | 0 < x.1 ∧ R / Real.sqrt sm < R / Real.sqrt x.1} :=
        fun h => hlt ((hmono x.1 hx0).1 h.2)
      rw [Set.indicator_of_notMem (show x ∉ ageBelow sm from hlt),
        Set.indicator_of_notMem hnmem, mul_zero]
  rw [lintegral_congr_ae hae, lintegral_indicator hSet]
  -- Step 3: the change of variables `ChartChange` with `Θ τ ρ t = M τ (ptOf ρ t)²`
  have hΘm : Measurable (fun u : ℝ × ℝ × ℝ => M u.1 (ptOf u.2.1 u.2.2) ^ (2 : ℝ)) :=
    (hM.comp (measurable_fst.prodMk (cml_ptOf_meas.comp measurable_snd))).pow_const _
  have hperΘ : ∀ (τ ρ t : ℝ), M (τ + 2 * c / R) (ptOf ρ t) ^ (2 : ℝ) =
      M τ (ptOf ρ t) ^ (2 : ℝ) := fun τ ρ t => by rw [hper]
  have hCres := hC R c (R / Real.sqrt sm) hR hc hlo
    (fun τ ρ t => M τ (ptOf ρ t) ^ (2 : ℝ)) hΘm hperΘ
  beta_reduce at hCres
  -- Step 4: polar reduction of each phase
  have hinner : ∀ τ : ℝ,
      (∫⁻ ρ in Ioi (R / Real.sqrt sm), ∫⁻ t : ℝ, ENNReal.ofReal ρ * M τ (ptOf ρ t) ^ (2 : ℝ)) =
        (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y}, M τ y ^ (2 : ℝ) := by
    intro τ
    have hH : Measurable (fun y : UnforcedLeray.Space => M τ y ^ (2 : ℝ)) :=
      (hM.comp (measurable_const.prodMk measurable_id)).pow_const _
    have hax' : ∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 →
        M τ y ^ (2 : ℝ) = M τ y' ^ (2 : ℝ) := fun y y' h1 h2 => by
      rw [hax τ y y' h1 h2]
    have hpr := hP (fun y => M τ y ^ (2 : ℝ)) hH hax' (R / Real.sqrt sm) hlo
    have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have htop : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [hpr, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  -- Step 5: the `τ`-integral
  have hτint : (∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ ρ in Ioi (R / Real.sqrt sm), ∫⁻ t : ℝ, ENNReal.ofReal ρ * M τ (ptOf ρ t) ^ (2 : ℝ)) =
      (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
          ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y}, M τ y ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2
      (by positivity)).ne')]
    exact lintegral_congr fun τ => hinner τ
  rw [hτint] at hCres
  -- Step 6: the constants
  have hmain : (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
          ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y}, M τ y ^ (2 : ℝ) =
      ENNReal.ofReal (R * c) * ∫⁻ x in {x : Chart | 0 < x.1 ∧ R / Real.sqrt sm < R / Real.sqrt x.1},
        (fun x : Chart => M (chartTau R x) (ptOf (R / Real.sqrt x.1) (x.2.2 / Real.sqrt x.1)) ^
          (2 : ℝ)) x ∂(ageμ c (-5 / 2)) := hCres
  have hK : ENNReal.ofReal (1 / (2 * Real.pi * c * R)) =
      (ENNReal.ofReal (R * c))⁻¹ * (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < R * c),
      ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (R * c)⁻¹)]
    congr 1
    field_simp
  have hRc0 : ENNReal.ofReal (R * c) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hRctop : ENNReal.ofReal (R * c) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hK, mul_assoc, hmain, ← mul_assoc, ENNReal.inv_mul_cancel hRc0 hRctop, one_mul]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
