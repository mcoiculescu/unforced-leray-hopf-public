import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_3
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound

/-!
# Part I, task `PartI:T04/5/1/3/4`: pressure term of the cutoff energy identity

Target: `apEnergyPressureEstimate : APEnergyPressureEstimate` (`Short/PartI/Sub/PartI_T04_5_1_3.lean`).
Source of record: `the November 2 reference manuscript`, lines 278-286.

Route. `|p| ≤ M_p` on `[0,T]` (`classicalPressureBound_of`), `|χ_R'| ≤ C₀/R`, `|v_η| ≤ |v|`, and
`χ_R' = 0` for `|η| ≥ 2R`.  With `S = ℝ × [-2R, 2R]` and `b = √R`, the integrand satisfies the
pointwise bound `|χ' p v_η| ≤ (C₀M_p/R)(b/2 |v|² + 1_S/(2b))` (Young, `x ≤ b x²/2 + 1/(2b)`).
Integrating over the cell, `jet_l2` at `j = 0` bounds `∫|v|²` by `|K₀|`, and
`vol(cell ∩ S) = 4cR`, so the bound is `C₀M_p(|K₀|/2 + 2c)/√R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- AM-GM with a free parameter: `x ≤ (b/2) x² + 1/(2b)` for `b > 0`. -/
theorem apEP_amgm (b x : ℝ) (hb : 0 < b) : x ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
  have hb' : b ≠ 0 := hb.ne'
  have h2b : 0 < 2 * b := by linarith
  have key : b / 2 * x ^ 2 + 1 / (2 * b) - x = (b * x - 1) ^ 2 / (2 * b) := by
    field_simp
    ring
  have hnn : 0 ≤ (b * x - 1) ^ 2 / (2 * b) := div_nonneg (sq_nonneg _) h2b.le
  linarith

/-- The constant algebra with `R = b * b`. -/
theorem apEP_alg (C0 Mp K c R b : ℝ) (hb : 0 < b) (hR : R = b * b) :
    C0 * Mp / R * (b / 2 * K + c * (4 * R) * (1 / (2 * b))) =
      C0 * Mp * (K / 2 + 2 * c) / b := by
  have hb' : b ≠ 0 := hb.ne'
  subst hR
  field_simp
  ring

/-- **Leaf 4 (pressure term)**: `|∫ χ_R' p v_η| ≤ C/√R`. -/
theorem apEnergyPressureEstimate : APEnergyPressureEstimate := by
  intro ν c T v p hν hc hcls
  have hF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hF
  obtain ⟨C0, hC0, hcut⟩ := hF
  obtain ⟨Mp, hMp⟩ := classicalPressureBound_of slicePoisson velocityDecayOfEnergy
    cylinderPoissonBound ν c T v p hν hc hcls.pos hcls.classical hcls.bounded hcls.pressure_decay
  have hMp0 : 0 ≤ Mp := le_trans (abs_nonneg _) (hMp 0 ⟨le_refl 0, hcls.pos.le⟩ 0)
  obtain ⟨K0, hK0⟩ := hcls.jet_l2 0
  refine ⟨C0 * Mp * (|K0| / 2 + 2 * c),
    mul_nonneg (mul_nonneg hC0 hMp0) (by linarith [abs_nonneg K0]), ?_⟩
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨-, hbd, -, hz, hd⟩ := hcut R hR
  -- `|χ_R'| ≤ C₀ / R` everywhere, and `χ_R' = 0` for `2R ≤ |η|`
  have hdbd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C0 / R := by
    intro η
    have h1 := hd η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 :=
      (Real.sqrt_le_sqrt (hbd η).2).trans_eq Real.sqrt_one
    have hk : 0 ≤ C0 / R := div_nonneg hC0 hR0.le
    calc |deriv (etaCutoff R) η| ≤ C0 / R * Real.sqrt (etaCutoff R η) := h1
      _ ≤ C0 / R * 1 := mul_le_mul_of_nonneg_left hs1 hk
      _ = C0 / R := mul_one _
  have hdz : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h1 := hd η
    rw [hz η hη, Real.sqrt_zero, mul_zero] at h1
    exact abs_nonpos_iff.mp h1
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR0.le
  have hK : 0 ≤ C0 * Mp / R := div_nonneg (mul_nonneg hC0 hMp0) hR0.le
  -- the `jet_l2` bound at `j = 0`, written with the norm of the velocity
  obtain ⟨hI0, hV0⟩ := hK0 s (Ioo_subset_Icc_self hs)
  have hV0' : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 ≤ K0 := hV0
  simp only [norm_iteratedFDeriv_zero] at hV0'
  have hI0' : IntegrableOn (fun z : Plane => ‖v s z‖ ^ 2) (Cyl.cell c) := by
    simpa only [norm_iteratedFDeriv_zero] using hI0
  -- the strip `S = ℝ × [-2R, 2R]`
  set S : Set Plane := univ ×ˢ Icc (-(2 * R)) (2 * R) with hSdef
  have hSmeas : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hmemS : ∀ z : Plane, z ∈ S ↔ |z.2| ≤ 2 * R := by
    intro z
    simp only [hSdef, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc, abs_le]
  have hcellS : S ∩ Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) := by
    ext ⟨a, e⟩
    simp only [hSdef, Cyl.cell, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Icc, Set.mem_Ico]
    tauto
  have hμS : (volume.restrict (Cyl.cell c)) S =
      ENNReal.ofReal (c / 2 - -c / 2) * ENNReal.ofReal (2 * R - -(2 * R)) := by
    rw [Measure.restrict_apply hSmeas, hcellS, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ico, Real.volume_Icc]
  have hfinS : (volume.restrict (Cyl.cell c)) S ≠ ⊤ := by
    rw [hμS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hreal : ((volume.restrict (Cyl.cell c)) S).toReal = c * (4 * R) := by
    rw [hμS, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    ring
  -- the integral of the indicator of the strip
  have hIind : IntegrableOn (S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)))
      (Cyl.cell c) := by
    rw [IntegrableOn, integrable_indicator_iff hSmeas]
    exact integrableOn_const hfinS
  have hind : ∫ z in Cyl.cell c, S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z =
      c * (4 * R) * (1 / (2 * Real.sqrt R)) := by
    rw [integral_indicator_const _ hSmeas, smul_eq_mul]
    show ((volume.restrict (Cyl.cell c)) S).toReal * _ = _
    rw [hreal]
  -- pointwise majorant `(C₀M_p/R)(b/2 |v|² + 1_S/(2b))`, with `b = √R`
  have hpt : ∀ z : Plane,
      ‖deriv (etaCutoff R) z.2 * p s z * v s z 1‖ ≤
        C0 * Mp / R * (Real.sqrt R / 2 * ‖v s z‖ ^ 2 +
          S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z) := by
    intro z
    have hsq2 : 0 ≤ Real.sqrt R / 2 * ‖v s z‖ ^ 2 := by positivity
    by_cases hin : |z.2| ≤ 2 * R
    · have hmem : z ∈ S := (hmemS z).2 hin
      rw [Set.indicator_of_mem hmem]
      have hD : ‖deriv (etaCutoff R) z.2‖ ≤ C0 / R := by
        rw [Real.norm_eq_abs]
        exact hdbd z.2
      have hP : ‖p s z‖ ≤ Mp := by
        rw [Real.norm_eq_abs]
        exact hMp s (Ioo_subset_Icc_self hs) z
      have hV : ‖v s z 1‖ ≤ ‖v s z‖ := PiLp.norm_apply_le _ _
      have hnorm : ‖deriv (etaCutoff R) z.2 * p s z * v s z 1‖ =
          ‖deriv (etaCutoff R) z.2‖ * ‖p s z‖ * ‖v s z 1‖ := by
        simp [norm_mul]
      have hA : ‖deriv (etaCutoff R) z.2‖ * ‖p s z‖ * ‖v s z 1‖ ≤
          C0 / R * Mp * ‖v s z‖ :=
        mul_le_mul (mul_le_mul hD hP (norm_nonneg _) (div_nonneg hC0 hR0.le)) hV
          (norm_nonneg _) (mul_nonneg (div_nonneg hC0 hR0.le) hMp0)
      have hAM := apEP_amgm (Real.sqrt R) ‖v s z‖ hsR
      rw [hnorm]
      calc ‖deriv (etaCutoff R) z.2‖ * ‖p s z‖ * ‖v s z 1‖ ≤ C0 / R * Mp * ‖v s z‖ := hA
        _ = C0 * Mp / R * ‖v s z‖ := by ring
        _ ≤ C0 * Mp / R * (Real.sqrt R / 2 * ‖v s z‖ ^ 2 + 1 / (2 * Real.sqrt R)) :=
            mul_le_mul_of_nonneg_left hAM hK
    · have hmem : z ∉ S := fun h => hin ((hmemS z).1 h)
      rw [Set.indicator_of_notMem hmem, add_zero]
      have hz0 : deriv (etaCutoff R) z.2 = 0 := hdz z.2 (le_of_lt (not_le.1 hin))
      rw [hz0, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg hK hsq2
  -- integrate the majorant over the cell
  have hh : IntegrableOn (fun z : Plane => C0 * Mp / R * (Real.sqrt R / 2 * ‖v s z‖ ^ 2 +
      S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z)) (Cyl.cell c) :=
    ((hI0'.const_mul _).add hIind).const_mul _
  have hint : ∫ z in Cyl.cell c, ‖deriv (etaCutoff R) z.2 * p s z * v s z 1‖ ≤
      ∫ z in Cyl.cell c, C0 * Mp / R * (Real.sqrt R / 2 * ‖v s z‖ ^ 2 +
        S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hh
      (Filter.Eventually.of_forall hpt)
  have hsplit : ∫ z in Cyl.cell c, C0 * Mp / R * (Real.sqrt R / 2 * ‖v s z‖ ^ 2 +
        S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z) =
      C0 * Mp / R * (Real.sqrt R / 2 * (∫ z in Cyl.cell c, ‖v s z‖ ^ 2) +
        ∫ z in Cyl.cell c, S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z) := by
    rw [integral_const_mul, integral_add (hI0'.const_mul _) hIind, integral_const_mul]
  have hI' : ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 ≤ |K0| := le_trans hV0' (le_abs_self K0)
  have hstep : C0 * Mp / R * (Real.sqrt R / 2 * (∫ z in Cyl.cell c, ‖v s z‖ ^ 2) +
        ∫ z in Cyl.cell c, S.indicator (fun _ : Plane => 1 / (2 * Real.sqrt R)) z) ≤
      C0 * Mp / R * (Real.sqrt R / 2 * |K0| +
        c * (4 * R) * (1 / (2 * Real.sqrt R))) := by
    rw [hind]
    apply mul_le_mul_of_nonneg_left _ hK
    exact add_le_add (mul_le_mul_of_nonneg_left hI' (by positivity)) le_rfl
  calc |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1|
      = ‖∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z in Cyl.cell c, ‖deriv (etaCutoff R) z.2 * p s z * v s z 1‖ :=
        norm_integral_le_integral_norm _
    _ ≤ _ := hint
    _ = _ := hsplit
    _ ≤ _ := hstep
    _ = C0 * Mp * (|K0| / 2 + 2 * c) / Real.sqrt R :=
        apEP_alg C0 Mp |K0| c R (Real.sqrt R) hsR hsq.symm

end UnforcedLeray.Short.PartI
