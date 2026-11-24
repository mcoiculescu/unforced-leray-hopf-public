import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# Part II-b, task `PartII-b:T07`: the norm identity for the complex ring lift (conditional)

Source of record: `the November 2 reference manuscript`, lines 1902-1906
("the lift `Mb = √s b` and the norm factor `(πR²)^{1/r}` cancel"), `‖N_v b‖_{Y_r} =
(πR²)^{1/r}‖b‖_{H_r}` for the complex lift `N_v b = N_v(Re b) + i N_v(Im b)`.



The original target had only `hper : QPeriodic c b` (almost-everywhere periodicity) and no
measurability hypothesis. `phaseLpNorm` and `hNorm` are built from the lower Lebesgue integral
`∫⁻`, which for a non-measurable `b` is not controlled by the change of variables used here, and
the library lemmas `Axi.lintegral_Nv_rpow` / `Axi.lintegral_ageμ` need `Measurable b` and
everywhere periodicity. Every consumer has `b ∈ H_r` (`InHr`, which contains periodicity and
`AEStronglyMeasurable b (hMeas c r)`), so the target is amended to

`phaseLpNorm_NvC (hc) (hr) (hε) (b) (hper : QPeriodic c b)
  (hmeas : AEStronglyMeasurable b (hMeas c r))`,

i.e. exactly the `periodic` and `meas` fields of `InHr` (finiteness is not needed).

## Proof structure

* `NvCNormSq`, `CMeridNormSq`, `NvCPointwise`: the pointwise identity
  `‖N_v b(τ, y)‖ₑ^q = age^{q/2} ‖b(chart)‖ₑ^q` for the complex lift;
* `NvCPhaseIntegral`: the copy of `Axi.lintegral_Nv_rpow` for the complex lift (measurable,
  everywhere periodic profile);
* `PeriodicRepresentative`: a measurable everywhere-periodic representative `b'` of an a.e.
  periodic `b ∈ AEStronglyMeasurable (hMeas c r)`, differing from `b` on `s > 0` only inside a
  measurable `q`-periodic null set `M`;
* `ChartNullPullback`: the ring chart pulls a periodic Lebesgue-null set back to a null set of
  `(τ, y)` (almost every phase slice).

Proved here: `phaseLpNorm_NvC_of` (the amended target from `NvCPhaseIntegral`,
`PeriodicRepresentative`, `ChartNullPullback`; no sorry).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- SP 1902-1906, step 1: for `u, v ∈ ℝ³`, `‖u + i v‖² = ‖u‖² + ‖v‖²` in `ℂ³`
(`B0412.realC` is the coordinatewise inclusion `ℝ³ → ℂ³`). -/
def NvCNormSq : Prop :=
  ∀ u v : Space, ‖B0412.realC u + Complex.I • B0412.realC v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2

/-- SP 1902-1906, step 2: `‖v‖² = ‖Re v‖² + ‖Im v‖²` for `v ∈ ℂ²`. -/
def CMeridNormSq : Prop :=
  ∀ v : CMerid, ‖v‖ ^ 2 = ‖reM v‖ ^ 2 + ‖imM v‖ ^ 2

/-- SP 1902-1906, step 3 (pointwise form of `Axi.enorm_Nv_rpow` for the complex lift): off the
axis, `‖N_v b(τ, y)‖ₑ^q = age^{q/2} ‖b(chart R τ y)‖ₑ^q`, `q ≥ 0`. -/
def NvCPointwise : Prop :=
  ∀ (R : ℝ) (b : CProf) (τ : ℝ) (y : Space), y ∉ Axi.axis → ∀ q : ℝ, 0 ≤ q →
    ‖NvC R b (τ, y)‖ₑ ^ q =
      ENNReal.ofReal (Axi.age R y ^ (q / 2)) * ‖b (Axi.chart R τ y)‖ₑ ^ q

/-- SP 1902-1906, step 4 (the complex copy of `Axi.lintegral_Nv_rpow`, `Lib/AxisymmetricB/Lift.lean`):
for a measurable profile `b`, `c`-periodic in `q`, `P = 2c/R`, `q > 0`,
`P⁻¹ ∫_{(0,P]} ∫_{ℝ³} ‖N_v b‖ₑ^q dy dτ = π R² ∫ ‖b‖ₑ^q d(ageμ c (q/2 - 5/2))`. -/
def NvCPhaseIntegral : Prop :=
  ∀ (R c P q : ℝ), 0 < R → 0 < c → P = 2 * c / R → 0 < q → ∀ b : CProf, Measurable b →
    (∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) →
    (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖NvC R b (τ, y)‖ₑ ^ q =
      ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖b p‖ₑ ^ q ∂Axi.ageμ c (q / 2 - 5 / 2)

/-- A measurable, everywhere `q`-periodic representative of an a.e. periodic, a.e.-strongly
measurable profile of `H_r`: there are such `b'` and a measurable, `q`-periodic, Lebesgue-null set
`M` (in the chart space `(s, (q, η))`) with `b = b'` on `{s > 0} \ M`. -/
def PeriodicRepresentative : Prop :=
  ∀ (c r : ℝ), 0 < c → ∀ b : CProf, QPeriodic c b → AEStronglyMeasurable b (hMeas c r) →
    ∃ (b' : CProf) (M : Set Coord), Measurable b' ∧
      (∀ s ξ η, b' (s, (ξ + c, η)) = b' (s, (ξ, η))) ∧
      MeasurableSet M ∧ volume M = 0 ∧
      (∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) ∧
      ∀ x : Coord, 0 < x.1 → x ∉ M → b x = b' x

/-- The ring chart pulls a periodic null set back to a null set: for a measurable `q`-periodic
Lebesgue-null `M ⊆ ℝ × (ℝ × ℝ)`, for a.e. phase `τ ∈ (0, P]` and a.e. `y ∈ ℝ³`, the chart point
`(s, ξ, η)(τ, y)` lies outside `M` (from `phaseAvg_ringChart` with `G = 1_M`). -/
def ChartNullPullback : Prop :=
  ∀ (R c P : ℝ), 0 < R → 0 < c → P = 2 * c / R → ∀ M : Set Coord, MeasurableSet M →
    volume M = 0 → (∀ s ξ η, (s, (ξ + c, η)) ∈ M ↔ (s, (ξ, η)) ∈ M) →
    ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ y : Space, Axi.chart R τ y ∉ M

/-- A Lebesgue-null measurable set is `ageμ`-null. -/
theorem ageμ_null_of_volume_null {c a : ℝ} (hc : 0 < c) {M : Set Coord} (hM : MeasurableSet M)
    (hM0 : volume M = 0) : Axi.ageμ c a M = 0 := by
  have h := Axi.lintegral_ageμ hc a (f := M.indicator 1) (measurable_one.indicator hM)
  rw [lintegral_indicator_one hM] at h
  rw [h]
  have hae : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)), p ∉ M :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hM0)
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  · filter_upwards [hae] with p hp
    simp [Set.indicator_of_notMem hp]

/-- **`PartII-b:T07`, conditional form (amended target).** -/
theorem phaseLpNorm_NvC_of (hPhase : NvCPhaseIntegral) (hRep : PeriodicRepresentative)
    (hNull : ChartNullPullback) {c r ε : ℝ} (hc : 0 < c) (hr : 0 < r) (hε : 0 < ε) (b : CProf)
    (hper : QPeriodic c b) (hmeas : AEStronglyMeasurable b (hMeas c r)) :
    phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b) =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r b := by
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hbb'⟩ := hRep c r hc b hper hmeas
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP0 : 0 < 2 * ε * c := by positivity
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    field_simp
  -- the two phase integrals agree
  have hnull := hNull ε⁻¹ c (2 * ε * c) hR hc hP M hMm hM0 hMper
  have hstep : ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ‖NvC ε⁻¹ b (τ, y)‖ₑ ^ r =
      ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ‖NvC ε⁻¹ b' (τ, y)‖ₑ ^ r := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with τ hτ
    refine lintegral_congr_ae ?_
    filter_upwards [hτ, Axi.ae_not_mem_axis] with y hy hax
    have hpos : 0 < (Axi.chart ε⁻¹ τ y).1 := Axi.age_pos hR.ne' hax
    have key : b (Axi.chart ε⁻¹ τ y) = b' (Axi.chart ε⁻¹ τ y) := hbb' _ hpos hy
    simp only [NvC, Axi.Nv, key]
  -- the profile norms agree
  have hae : b' =ᵐ[hMeas c r] b := by
    have hn : Axi.ageμ c (r / 2 - 5 / 2) M = 0 := ageμ_null_of_volume_null hc hMm hM0
    filter_upwards [Axi.ae_ageμ_mem hc (r / 2 - 5 / 2),
      measure_eq_zero_iff_ae_notMem.1 hn] with p hp hpM
    exact (hbb' p hp.1 hpM).symm
  have hI : ∫⁻ p, ‖b' p‖ₑ ^ r ∂Axi.ageμ c (r / 2 - 5 / 2) =
      ∫⁻ p, ‖b p‖ₑ ^ r ∂Axi.ageμ c (r / 2 - 5 / 2) :=
    lintegral_congr_ae (hae.mono fun p hp => by simp only [hp])
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hNb : hNorm c r b = (∫⁻ p, ‖b p‖ₑ ^ r ∂Axi.ageμ c (r / 2 - 5 / 2)) ^ (1 / r) := by
    unfold hNorm hMeas
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr.le]
  have hmain := hPhase ε⁻¹ c (2 * ε * c) r hR hc hP hr b' hb'm hb'per
  unfold phaseLpNorm
  rw [hstep, ENNReal.ofReal_inv_of_pos hP0, hmain, hNb, ← hI,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

end UnforcedLeray.Short.IIb
