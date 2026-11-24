import UnforcedLeray.Short.PartI.Sub.T02_3_11

/-!
# Part I, task `PartI:T02/3/11` (leaf): `CcPressureEstimate`

Source of record: `the November 2 reference manuscript`, lines 276-288 (the pressure
term of the energy identity for the difference of two classical solutions, `T_pres = 2 ∫ φ' π w_η`).
Target: `ccPressureEstimate : CcPressureEstimate` (`Short/PartI/Sub/T02_3_11.lean`, line 259), from the
hypotheses `EtaCutoffFacts`, `CellIntegrableOfSupport`, `CcSliceSmooth` and `CcDiffEnergyBound`.

Route. Let `w = ccDiffV v v' s`, `π = ccDiffP p p' s`, `φ' = deriv (etaCutoff R)`, `C₀` from
`EtaCutoffFacts` (`|φ'| ≤ (C₀/R)√φ`, `0 ≤ φ ≤ 1`), `M` from `ClassicalBoundedBy`.

1. Pointwise bounds on every point: `|φ'| ≤ C₀/R`, `|π| ≤ 2M`, `|w₁| ≤ |w|`. So the integrand
   `g = φ' π w₁` of `ccPressureRhs / 2` satisfies `|g| ≤ (2MC₀/R)|w|`.
2. `φ' = 0` for `2R ≤ |η|` (`φ` is nonnegative and vanishes there, a local minimum), so `g`
   vanishes off the strip `Q = [-c/2, c/2) × [-2R, 2R]` of volume `4cR`, and `∫_cell g = ∫_Q g`.
3. The Young-type bound `x ≤ (b/2)x² + 1/(2b)` with `b = √R` replaces Cauchy-Schwarz:
   `|w| ≤ (√R/2)|w|² + 1/(2√R)`. Integrating over `Q` and using `∫_cell |w|² ≤ 4M`
   (`CcDiffEnergyBound`) gives `∫_Q g ≤ (2MC₀/R)(2M√R + 2c√R) = 4MC₀(M+c)/√R`.
4. `ccPressureRhs = 2 ∫_cell g ≤ K/√R` with `K = 8MC₀(M+c) ≥ 0`.

The route and the constant follow the proved train leaf `pressureEstimate`
(`Tasks/TrainCutoffEnergyProof/PressureEstimate.lean`). The statement `CcPressureEstimate` asks only
for some `K ≥ 0`, so the constant `8MC₀(M+c)` is used in place of the `4C₀M√(8cM)` of the source
comment.

Helpers are prefixed `ccPE_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Elementary inequalities -/

/-- AM-GM with a free positive parameter: `x ≤ (b/2) x² + 1/(2b)` for `b > 0`. -/
theorem ccPE_amgm (b x : ℝ) (hb : 0 < b) : x ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
  have hb' : b ≠ 0 := hb.ne'
  have h2b : 0 < 2 * b := by linarith
  have key : b / 2 * x ^ 2 + 1 / (2 * b) - x = (b * x - 1) ^ 2 / (2 * b) := by
    field_simp
    ring
  have hnn : 0 ≤ (b * x - 1) ^ 2 / (2 * b) := div_nonneg (sq_nonneg _) h2b.le
  linarith

/-- The constant algebra: with `R = b * b`, `(2MC/R)(b/2 · 4M + 1/(2b) · (c · 4R)) = 4MC(M+c)/b`. -/
theorem ccPE_alg (M C c R b : ℝ) (hb : 0 < b) (hR : R = b * b) :
    2 * M * C / R * (b / 2 * (4 * M) + 1 / (2 * b) * (c * (4 * R))) =
      4 * M * C * (M + c) / b := by
  have hb' : b ≠ 0 := hb.ne'
  subst hR
  field_simp

/-! ### The target -/

/-- **`PartI:T02/3/11` leaf, target `CcPressureEstimate`.** The pressure term is bounded by
`|φ'| ≤ C₀/R` on the strip `|η| < 2R`, `|π| ≤ 2M`, and the square-root Young bound together with
`∫_cell |w|² ≤ 4M`. -/
theorem ccPressureEstimate (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hS : CcSliceSmooth) (hE : CcDiffEnergyBound) : CcPressureEstimate := by
  unfold CcPressureEstimate
  intro ν c T M v v' p p' h
  unfold EtaCutoffFacts at hη
  unfold CellIntegrableOfSupport at hI
  unfold CcSliceSmooth at hS
  unfold CcDiffEnergyBound at hE
  obtain ⟨C₀, hC₀, hcut⟩ := hη
  have hc1 : 1 ≤ c := h.c_ge
  have hcpos : 0 < c := by linarith
  have hM : 0 ≤ M := le_trans (norm_nonneg _) ((h.bb 0 ⟨le_refl 0, h.T_pos.le⟩).1 0)
  refine ⟨8 * M * C₀ * (M + c), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hC₀) (by linarith)
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  have hb0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs0 : 0 ≤ s := hs.1
  obtain ⟨hsm, hφ01, -, hφz, hφd⟩ := hcut R hR
  -- smoothness of the cutoff; its derivative vanishes for `2R ≤ |η|`
  have hsm1 : ContDiff ℝ 1 (etaCutoff R) := hsm.of_le (by simp)
  have hdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    hsm1.continuous_deriv_one.comp continuous_snd
  have hdz : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    apply IsLocalMin.deriv_eq_zero
    show ∀ᶠ y in nhds η, etaCutoff R η ≤ etaCutoff R y
    refine Filter.Eventually.of_forall (fun y => ?_)
    show etaCutoff R η ≤ etaCutoff R y
    rw [hφz η hη]
    exact (hφ01 y).1
  -- continuity of the slices of the difference and of its pressure
  have hw1 : ContDiff ℝ ∞ (ccDiffV v v' s) :=
    (hS ν c T v p h.cl s hs).1.sub (hS ν c T v' p' h.cl' s hs).1
  have hp1 : ContDiff ℝ ∞ (ccDiffP p p' s) :=
    (hS ν c T v p h.cl s hs).2.sub (hS ν c T v' p' h.cl' s hs).2
  have hwc : Continuous (ccDiffV v v' s) := hw1.continuous
  have hpc : Continuous (ccDiffP p p' s) := hp1.continuous
  have hw1c : Continuous (fun z : Plane => ccDiffV v v' s z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hwc
  -- the integrand `g = φ' π w₁` of `ccPressureRhs / 2`
  have hG0 : ∀ z : Plane, 2 * R ≤ |z.2| →
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 = 0 := by
    intro z hz
    rw [hdz z.2 hz, zero_mul, zero_mul]
  have hGc : Continuous (fun z : Plane =>
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) :=
    (hdc.mul hpc).mul hw1c
  have hGi : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) (Cyl.cell c) :=
    hI c R hcpos hR0 _ hGc hG0
  -- the strip `Q = [-c/2, c/2) × [-2R, 2R]` carries the whole integral
  set Q : Set Plane := Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hQdef
  have hQmeas : MeasurableSet Q := measurableSet_Ico.prod measurableSet_Icc
  have hQc : Q ⊆ Cyl.cell c := by
    rw [hQdef, Cyl.cell]
    exact Set.prod_mono subset_rfl (Set.subset_univ _)
  have hQfin : (volume : Measure Plane) Q ≠ ⊤ := by
    rw [hQdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hQre : ((volume : Measure Plane) Q).toReal = c * (4 * R) := by
    rw [hQdef, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
    · ring
    all_goals linarith
  have hoff : ∀ x ∈ Cyl.cell c \ Q,
      deriv (etaCutoff R) x.2 * ccDiffP p p' s x * ccDiffV v v' s x 1 = 0 := by
    intro x hx
    apply hG0 x
    by_contra hlt
    apply hx.2
    rw [hQdef]
    exact ⟨hx.1.1, abs_le.1 (not_le.1 hlt).le⟩
  have hcellQ : ∫ z in Cyl.cell c,
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 =
        ∫ z in Q, deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Cyl.measurableSet_cell c) hQc hoff
  have hGQ : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1) Q :=
    hGi.mono_set hQc
  -- the energy of the difference on the strip
  obtain ⟨hEI, hEb⟩ := hE ν c T M v v' p p' h s hs
  have hwQ : IntegrableOn (fun z : Plane => ‖ccDiffV v v' s z‖ ^ 2) Q := hEI.mono_set hQc
  have hI2 : ∫ z in Q, ‖ccDiffV v v' s z‖ ^ 2 ≤ 4 * M :=
    le_trans (setIntegral_mono_set hEI (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hQc hx)) hEb
  have hconstQ : IntegrableOn (fun _ : Plane => 1 / (2 * Real.sqrt R)) Q :=
    integrableOn_const hQfin
  have hfQ : IntegrableOn (fun z : Plane => (2 * M * C₀ / R) *
      (Real.sqrt R / 2 * ‖ccDiffV v v' s z‖ ^ 2 + 1 / (2 * Real.sqrt R))) Q :=
    Integrable.const_mul (Integrable.add (Integrable.const_mul hwQ (Real.sqrt R / 2)) hconstQ) _
  -- pointwise bound: `|g| ≤ (2MC₀/R)|w| ≤ (2MC₀/R)((√R/2)|w|² + 1/(2√R))`
  have hbound : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 ≤
        (2 * M * C₀ / R) * (Real.sqrt R / 2 * ‖ccDiffV v v' s z‖ ^ 2 + 1 / (2 * Real.sqrt R)) := by
    intro z
    have hA : |deriv (etaCutoff R) z.2| ≤ C₀ / R := by
      have hsq : Real.sqrt (etaCutoff R z.2) ≤ 1 := by
        have h' := Real.sqrt_le_sqrt (hφ01 z.2).2
        rwa [Real.sqrt_one] at h'
      have h1 := hφd z.2
      have h2 : C₀ / R * Real.sqrt (etaCutoff R z.2) ≤ C₀ / R :=
        mul_le_of_le_one_right (div_nonneg hC₀ hR0.le) hsq
      linarith
    have hB : |ccDiffP p p' s z| ≤ 2 * M := by
      have h1 := abs_le.1 ((h.bb s hs).2.1 z)
      have h2 := abs_le.1 ((h.bb' s hs).2.1 z)
      show |p s z - p' s z| ≤ 2 * M
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hC : |ccDiffV v v' s z 1| ≤ ‖ccDiffV v v' s z‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ 1
    have hGabs : |deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1| ≤
        C₀ / R * (2 * M) * ‖ccDiffV v v' s z‖ := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hA hB (abs_nonneg _) (div_nonneg hC₀ hR0.le)) hC
        (abs_nonneg _) (mul_nonneg (div_nonneg hC₀ hR0.le) (by linarith))
    have hx := ccPE_amgm (Real.sqrt R) ‖ccDiffV v v' s z‖ hb0
    have hK1 : 0 ≤ 2 * M * C₀ / R :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hC₀) hR0.le
    calc deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1
        ≤ |deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1| := le_abs_self _
      _ ≤ C₀ / R * (2 * M) * ‖ccDiffV v v' s z‖ := hGabs
      _ = (2 * M * C₀ / R) * ‖ccDiffV v v' s z‖ := by ring
      _ ≤ (2 * M * C₀ / R) * (Real.sqrt R / 2 * ‖ccDiffV v v' s z‖ ^ 2 + 1 / (2 * Real.sqrt R)) :=
          mul_le_mul_of_nonneg_left hx hK1
  -- the integral of the bound over the strip
  have hgval : ∫ z in Q, (2 * M * C₀ / R) *
      (Real.sqrt R / 2 * ‖ccDiffV v v' s z‖ ^ 2 + 1 / (2 * Real.sqrt R)) =
      (2 * M * C₀ / R) * (Real.sqrt R / 2 * (∫ z in Q, ‖ccDiffV v v' s z‖ ^ 2) +
        1 / (2 * Real.sqrt R) * ((volume : Measure Plane) Q).toReal) := by
    rw [integral_const_mul, integral_add (Integrable.const_mul hwQ (Real.sqrt R / 2)) hconstQ,
      integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def]
    ring
  have hkey : ∫ z in Cyl.cell c,
      deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1 ≤
        (2 * M * C₀ / R) *
          (Real.sqrt R / 2 * (4 * M) + 1 / (2 * Real.sqrt R) * (c * (4 * R))) := by
    rw [hcellQ]
    have hK1 : 0 ≤ 2 * M * C₀ / R :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hC₀) hR0.le
    calc ∫ z in Q, deriv (etaCutoff R) z.2 * ccDiffP p p' s z * ccDiffV v v' s z 1
        ≤ ∫ z in Q, (2 * M * C₀ / R) *
            (Real.sqrt R / 2 * ‖ccDiffV v v' s z‖ ^ 2 + 1 / (2 * Real.sqrt R)) :=
          setIntegral_mono_on hGQ hfQ hQmeas (fun z _ => hbound z)
      _ = (2 * M * C₀ / R) * (Real.sqrt R / 2 * (∫ z in Q, ‖ccDiffV v v' s z‖ ^ 2) +
            1 / (2 * Real.sqrt R) * ((volume : Measure Plane) Q).toReal) := hgval
      _ ≤ (2 * M * C₀ / R) *
          (Real.sqrt R / 2 * (4 * M) + 1 / (2 * Real.sqrt R) * (c * (4 * R))) := by
          rw [hQre]
          refine mul_le_mul_of_nonneg_left ?_ hK1
          have h3 : Real.sqrt R / 2 * (∫ z in Q, ‖ccDiffV v v' s z‖ ^ 2) ≤
              Real.sqrt R / 2 * (4 * M) :=
            mul_le_mul_of_nonneg_left hI2 (by linarith)
          linarith
  -- conclusion
  have halg := ccPE_alg M C₀ c R (Real.sqrt R) hb0 (Real.mul_self_sqrt hR0.le).symm
  unfold ccPressureRhs
  have h2 := mul_le_mul_of_nonneg_left hkey (by norm_num : (0 : ℝ) ≤ 2)
  rw [halg] at h2
  calc _ ≤ 2 * (4 * M * C₀ * (M + c) / Real.sqrt R) := h2
    _ = 8 * M * C₀ * (M + c) / Real.sqrt R := by ring

end UnforcedLeray.Short.PartI
