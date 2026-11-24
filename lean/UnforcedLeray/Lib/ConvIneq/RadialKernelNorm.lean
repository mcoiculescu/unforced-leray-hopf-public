import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Radial kernel norms outside a gap (INF22 A5)

Blueprint infrastructure target **INF22 A5** of the scoping note

On `Space = ℝ³`, the radial majorant
`gapMajorant C α D x = C ‖x‖^{-α}` for `‖x‖ ≥ D` (and `0` inside the gap) has the exact norm
`‖gapMajorant C α D‖_{L^b} = C (4π/(αb-3))^{1/b} D^{-α+3/b}` whenever `αb > 3`
(`eLpNorm_gapMajorant`). This is the off-diagonal kernel norm used with Young's inequality
(`YoungGroup.lean`, INF22 A1) in the manuscript units (scoping note §2.1):

* `(α,b) = (4,1)`: `D^{-1}`, the partial-strip kernel (`paper/main.tex` 10214–10242, B0619);
* `(4,2)`: `D^{-5/2}`;
* `(4,11/7)`: `D^{-23/11}` (`paper/main.tex` 10381–10399, 11509–11518; B0761, B0975);
* `(4,11/3)`: `D^{-35/11}` (`paper/main.tex` 10560–10567; B0959);
* `(5,11/3)`: `D^{-46/11}` (`paper/main.tex` 8968–8975, 11467–11484; B0559, B0795);
* `(5,22/3)`: `D^{-101/22}` (`paper/main.tex` 11409–11420; B0974);
* `(4,22/3)`: `D^{-79/22}` (`paper/main.tex` 8960–8967, 10538–10558; B0561, B0958).

The polar-coordinate integral is Mathlib's `integral_fun_norm_addHaar` with
`volume (ball 0 1) = 4π/3` (`EuclideanSpace.volume_ball_fin_three`); the radial integral is
`integral_Ioi_rpow_of_lt`. The method follows the private `radialProfile_integrable` of the
compiled `lean/UnforcedLeray/Analysis/Pressure/NewtonKernel.lean` (not imported, as it is
private).

**Conventions.** `‖x‖` is the Euclidean norm of `EuclideanSpace ℝ (Fin 3)`. Inside the gap the
majorant is `0`, so `‖x‖ ^ (-α)` is never evaluated at `x = 0`. Norms are `eLpNorm`, valued in
`[0,∞]`; the hypotheses `0 ≤ C`, `0 < D`, `1 ≤ b`, `3 < αb` are exactly those under which the
manuscript's formula is finite and correct.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Conv

/-! ### Polar coordinates on `ℝ³` -/

/-- `dim ℝ³ = 3`. -/
theorem finrank_space : Module.finrank ℝ Space = 3 := by
  rw [finrank_euclideanSpace, Fintype.card_fin]

/-- The unit ball of `ℝ³` has volume `4π/3`. -/
theorem measureReal_ball_one_space :
    (volume : Measure Space).real (Metric.ball 0 1) = 4 * Real.pi / 3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The radial profile `1_{[D,∞)}(r) r^{-β}`. -/
def gapProfile (β D r : ℝ) : ℝ := if D ≤ r then r ^ (-β) else 0

theorem gapProfile_nonneg (β : ℝ) {D : ℝ} (hD : 0 < D) (r : ℝ) : 0 ≤ gapProfile β D r := by
  unfold gapProfile
  split_ifs with h
  · exact Real.rpow_nonneg (hD.le.trans h) _
  · exact le_rfl

private theorem radial_eq {β D : ℝ} {y : ℝ} (hy : 0 < y) :
    y ^ (Module.finrank ℝ Space - 1) • gapProfile β D y =
      (Ici D).indicator (fun r => r ^ (2 - β)) y := by
  rw [finrank_space, smul_eq_mul, gapProfile]
  by_cases h : D ≤ y
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_mem (show y ∈ Ici D from h),
      show (3 - 1 : ℕ) = 2 from rfl, sub_eq_add_neg, Real.rpow_add hy, Real.rpow_two]
  · simp only [h, ↓reduceIte]
    rw [Set.indicator_of_notMem (show y ∉ Ici D from h), mul_zero]

private theorem integrableOn_radial {β D : ℝ} (hβ : 3 < β) (hD : 0 < D) :
    IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • gapProfile β D y) (Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => r ^ (2 - β)) (Ici D) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_rpow_of_lt (by linarith) hD)
  have h2 : IntegrableOn ((Ici D).indicator (fun r : ℝ => r ^ (2 - β))) (Ioi 0) :=
    (h1.integrable_indicator measurableSet_Ici).integrableOn
  exact h2.congr_fun (fun y hy => (radial_eq hy).symm) measurableSet_Ioi

/-- `x ↦ 1_{‖x‖ ≥ D} ‖x‖^{-β}` is integrable on `ℝ³` for `β > 3`, `D > 0`. -/
theorem integrable_gapProfile_norm {β D : ℝ} (hβ : 3 < β) (hD : 0 < D) :
    Integrable (fun x : Space => gapProfile β D ‖x‖) :=
  (integrable_fun_norm_addHaar (volume : Measure Space) (f := gapProfile β D)).2
    (integrableOn_radial hβ hD)

/-- `∫_{‖x‖ ≥ D} ‖x‖^{-β} dx = 4π D^{3-β}/(β-3)` on `ℝ³`, for `β > 3`, `D > 0`. -/
theorem integral_gapProfile_norm {β D : ℝ} (hβ : 3 < β) (hD : 0 < D) :
    ∫ x : Space, gapProfile β D ‖x‖ = 4 * Real.pi * D ^ (3 - β) / (β - 3) := by
  have hcongr : ∫ y in Ioi (0:ℝ), y ^ (Module.finrank ℝ Space - 1) • gapProfile β D y =
      ∫ y in Ioi (0:ℝ), (Ici D).indicator (fun r => r ^ (2 - β)) y :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => radial_eq hy)
  rw [integral_fun_norm_addHaar (volume : Measure Space) (gapProfile β D),
    measureReal_ball_one_space, hcongr, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, inter_eq_left.2 (Ici_subset_Ioi.2 hD),
    integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hD, finrank_space,
    show 2 - β + 1 = 3 - β by ring, neg_div, ← div_neg, neg_sub, nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- Lower-integral form: `∫⁻ 1_{‖x‖ ≥ D} ‖x‖^{-β} dx = 4π D^{3-β}/(β-3)` for `β > 3`, `D > 0`. -/
theorem lintegral_gapProfile_norm {β D : ℝ} (hβ : 3 < β) (hD : 0 < D) :
    ∫⁻ x : Space, ENNReal.ofReal (gapProfile β D ‖x‖) =
      ENNReal.ofReal (4 * Real.pi * D ^ (3 - β) / (β - 3)) := by
  rw [← integral_gapProfile_norm hβ hD, ofReal_integral_eq_lintegral_ofReal
    (integrable_gapProfile_norm hβ hD) (Eventually.of_forall fun x => gapProfile_nonneg β hD _)]

/-! ### The gap majorant -/

/-- The radial kernel majorant outside a gap (INF22 A5):
`gapMajorant C α D x = C ‖x‖^{-α}` if `‖x‖ ≥ D`, and `0` otherwise. -/
def gapMajorant (C α D : ℝ) (x : Space) : ℝ := if D ≤ ‖x‖ then C * ‖x‖ ^ (-α) else 0

theorem gapMajorant_nonneg {C α D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (x : Space) :
    0 ≤ gapMajorant C α D x := by
  unfold gapMajorant
  split_ifs with h
  · exact mul_nonneg hC (Real.rpow_nonneg (hD.le.trans h) _)
  · exact le_rfl

theorem measurable_gapMajorant (C α D : ℝ) : Measurable (gapMajorant C α D) := by
  unfold gapMajorant
  exact Measurable.ite (measurableSet_le measurable_const measurable_norm) (by fun_prop)
    measurable_const

theorem gapMajorant_rpow {C α D : ℝ} (hC : 0 ≤ C) {b : ℝ} (hb : 0 < b) (x : Space) :
    gapMajorant C α D x ^ b = C ^ b * gapProfile (α * b) D ‖x‖ := by
  unfold gapMajorant gapProfile
  split_ifs with h
  · have hx : 0 ≤ ‖x‖ := norm_nonneg _
    rw [Real.mul_rpow hC (Real.rpow_nonneg hx _), ← Real.rpow_mul hx, neg_mul]
  · rw [Real.zero_rpow hb.ne', mul_zero]

/-- **The exact `L^b` norm of the gap majorant** (INF22 A5): for `C ≥ 0`, `D > 0`, `b ≥ 1` and
`αb > 3`,
`‖gapMajorant C α D‖_{L^b(ℝ³)} = C (4π/(αb-3))^{1/b} D^{-α+3/b}`. -/
theorem eLpNorm_gapMajorant {C α b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hb : 1 ≤ b)
    (hαb : 3 < α * b) :
    eLpNorm (gapMajorant C α D) (ENNReal.ofReal b) volume =
      ENNReal.ofReal (C * (4 * Real.pi / (α * b - 3)) ^ (1 / b) * D ^ (-α + 3 / b)) := by
  have hb0 : 0 < b := by linarith
  have hαb' : 0 < α * b - 3 := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hb0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hb0.le]
  have h1 : ∀ x : Space, ‖gapMajorant C α D x‖ₑ ^ b =
      ENNReal.ofReal (C ^ b) * ENNReal.ofReal (gapProfile (α * b) D ‖x‖) := by
    intro x
    rw [Real.enorm_eq_ofReal (gapMajorant_nonneg hC hD x),
      ENNReal.ofReal_rpow_of_nonneg (gapMajorant_nonneg hC hD x) hb0.le, gapMajorant_rpow hC hb0,
      ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
  simp_rw [h1]
  have hk : 0 ≤ 4 * Real.pi / (α * b - 3) := div_nonneg (by positivity) hαb'.le
  have hDp : 0 ≤ D ^ (3 - α * b) := Real.rpow_nonneg hD.le _
  have hnn : 0 ≤ C ^ b * (4 * Real.pi * D ^ (3 - α * b) / (α * b - 3)) :=
    mul_nonneg (Real.rpow_nonneg hC _) (div_nonneg (mul_nonneg (by positivity) hDp) hαb'.le)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gapProfile_norm hαb hD,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _),
    ENNReal.ofReal_rpow_of_nonneg hnn (div_nonneg zero_le_one hb0.le)]
  congr 1
  have hexp : (3 - α * b) * (1 / b) = -α + 3 / b := by
    rw [mul_one_div, sub_div, mul_div_assoc, div_self hb0.ne', mul_one]
    ring
  rw [show 4 * Real.pi * D ^ (3 - α * b) / (α * b - 3) =
      4 * Real.pi / (α * b - 3) * D ^ (3 - α * b) by ring,
    Real.mul_rpow (Real.rpow_nonneg hC _) (mul_nonneg hk hDp),
    Real.mul_rpow hk hDp,
    ← Real.rpow_mul hC, ← Real.rpow_mul hD.le, mul_one_div_cancel hb0.ne', Real.rpow_one, hexp]
  ring

/-- Domination: a kernel with `‖K x‖ ≤ gapMajorant C α D x` everywhere has
`‖K‖_{L^b} ≤ C (4π/(αb-3))^{1/b} D^{-α+3/b}`. -/
theorem eLpNorm_le_of_le_gapMajorant {E : Type*} [NormedAddCommGroup E] {K : Space → E}
    {C α b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hb : 1 ≤ b) (hαb : 3 < α * b)
    (hK : ∀ x, ‖K x‖ ≤ gapMajorant C α D x) :
    eLpNorm K (ENNReal.ofReal b) volume ≤
      ENNReal.ofReal (C * (4 * Real.pi / (α * b - 3)) ^ (1 / b) * D ^ (-α + 3 / b)) := by
  rw [← eLpNorm_gapMajorant hC hD hb hαb]
  exact eLpNorm_mono_real hK

/-- A kernel bounded by `C ‖x‖^{-α}` on `‖x‖ ≥ D`, cut off to that region, has
`L^b` norm at most `C (4π/(αb-3))^{1/b} D^{-α+3/b}` (`b ≥ 1`, `αb > 3`). -/
theorem eLpNorm_indicator_gap_le {E : Type*} [NormedAddCommGroup E] {K : Space → E}
    {C α b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hb : 1 ≤ b) (hαb : 3 < α * b)
    (hK : ∀ x : Space, D ≤ ‖x‖ → ‖K x‖ ≤ C * ‖x‖ ^ (-α)) :
    eLpNorm ({x : Space | D ≤ ‖x‖}.indicator K) (ENNReal.ofReal b) volume ≤
      ENNReal.ofReal (C * (4 * Real.pi / (α * b - 3)) ^ (1 / b) * D ^ (-α + 3 / b)) := by
  refine eLpNorm_le_of_le_gapMajorant hC hD hb hαb fun x => ?_
  by_cases h : D ≤ ‖x‖
  · rw [Set.indicator_of_mem (show x ∈ {x : Space | D ≤ ‖x‖} from h), gapMajorant]
    simp only [h, ↓reduceIte]
    exact hK x h
  · rw [Set.indicator_of_notMem (show x ∉ {x : Space | D ≤ ‖x‖} from h), norm_zero]
    exact gapMajorant_nonneg hC hD x

/-! ### The manuscript's exponent pairs -/

private theorem eLpNorm_gapMajorant_of_eq {C α b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hb : 1 ≤ b)
    (hαb : 3 < α * b) {k e f : ℝ} (hk : 4 * Real.pi / (α * b - 3) = k) (he : 1 / b = e)
    (hf : -α + 3 / b = f) :
    eLpNorm (gapMajorant C α D) (ENNReal.ofReal b) volume = ENNReal.ofReal (C * k ^ e * D ^ f) := by
  rw [eLpNorm_gapMajorant hC hD hb hαb, hk, he, hf]

/-- `(α,b) = (4,1)`: `‖gapMajorant C 4 D‖_{L¹} = 4π C D^{-1}` (`paper/main.tex` 10214–10242,
B0619: `∫_{|x|>D} |x|^{-4} dx = C/D`). -/
theorem eLpNorm_gapMajorant_four_one {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 4 D) 1 volume =
      ENNReal.ofReal (C * (4 * Real.pi) ^ (1 : ℝ) * D ^ (-1 : ℝ)) := by
  rw [← ENNReal.ofReal_one]
  exact eLpNorm_gapMajorant_of_eq hC hD le_rfl (by norm_num) (by ring) (by norm_num)
    (by norm_num)

/-- `(α,b) = (4,2)`: `‖gapMajorant C 4 D‖_{L²} = C (4π/5)^{1/2} D^{-5/2}`. -/
theorem eLpNorm_gapMajorant_four_two {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 4 D) 2 volume =
      ENNReal.ofReal (C * (4 * Real.pi / 5) ^ (1 / 2 : ℝ) * D ^ (-(5 / 2) : ℝ)) := by
  have h := eLpNorm_gapMajorant_of_eq (C := C) (α := 4) (b := 2) (D := D)
    (k := 4 * Real.pi / 5) (e := 1 / 2) (f := -(5 / 2)) hC hD (by norm_num) (by norm_num)
    (by ring) (by norm_num) (by norm_num)
  rwa [ENNReal.ofReal_ofNat] at h

/-- `(α,b) = (4,11/7)`: `‖gapMajorant C 4 D‖_{L^{11/7}} = C (28π/23)^{7/11} D^{-23/11}`
(`paper/main.tex` 10381–10399 and 11509–11518, B0761, B0975). -/
theorem eLpNorm_gapMajorant_four_eleven_sevenths {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 4 D) (ENNReal.ofReal (11 / 7)) volume =
      ENNReal.ofReal (C * (28 * Real.pi / 23) ^ (7 / 11 : ℝ) * D ^ (-(23 / 11) : ℝ)) :=
  eLpNorm_gapMajorant_of_eq hC hD (by norm_num) (by norm_num) (by ring) (by norm_num)
    (by norm_num)

/-- `(α,b) = (4,11/3)`: `‖gapMajorant C 4 D‖_{L^{11/3}} = C (12π/35)^{3/11} D^{-35/11}`
(`paper/main.tex` 10560–10567, B0959). -/
theorem eLpNorm_gapMajorant_four_eleven_thirds {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 4 D) (ENNReal.ofReal (11 / 3)) volume =
      ENNReal.ofReal (C * (12 * Real.pi / 35) ^ (3 / 11 : ℝ) * D ^ (-(35 / 11) : ℝ)) :=
  eLpNorm_gapMajorant_of_eq hC hD (by norm_num) (by norm_num) (by ring) (by norm_num)
    (by norm_num)

/-- `(α,b) = (5,11/3)`: `‖gapMajorant C 5 D‖_{L^{11/3}} = C (6π/23)^{3/11} D^{-46/11}`
(`paper/main.tex` 8968–8975 and 11467–11484, B0559, B0795). -/
theorem eLpNorm_gapMajorant_five_eleven_thirds {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 5 D) (ENNReal.ofReal (11 / 3)) volume =
      ENNReal.ofReal (C * (6 * Real.pi / 23) ^ (3 / 11 : ℝ) * D ^ (-(46 / 11) : ℝ)) :=
  eLpNorm_gapMajorant_of_eq hC hD (by norm_num) (by norm_num) (by ring) (by norm_num)
    (by norm_num)

/-- `(α,b) = (5,22/3)`: `‖gapMajorant C 5 D‖_{L^{22/3}} = C (12π/101)^{3/22} D^{-101/22}`
(`paper/main.tex` 11409–11420, B0974). -/
theorem eLpNorm_gapMajorant_five_twentytwo_thirds {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 5 D) (ENNReal.ofReal (22 / 3)) volume =
      ENNReal.ofReal (C * (12 * Real.pi / 101) ^ (3 / 22 : ℝ) * D ^ (-(101 / 22) : ℝ)) :=
  eLpNorm_gapMajorant_of_eq hC hD (by norm_num) (by norm_num) (by ring) (by norm_num)
    (by norm_num)

/-- `(α,b) = (4,22/3)`: `‖gapMajorant C 4 D‖_{L^{22/3}} = C (12π/79)^{3/22} D^{-79/22}`
(`paper/main.tex` 8960–8967 and 10538–10558, B0561, B0958). -/
theorem eLpNorm_gapMajorant_four_twentytwo_thirds {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) :
    eLpNorm (gapMajorant C 4 D) (ENNReal.ofReal (22 / 3)) volume =
      ENNReal.ofReal (C * (12 * Real.pi / 79) ^ (3 / 22 : ℝ) * D ^ (-(79 / 22) : ℝ)) :=
  eLpNorm_gapMajorant_of_eq hC hD (by norm_num) (by norm_num) (by ring) (by norm_num)
    (by norm_num)

end UnforcedLeray.Conv
