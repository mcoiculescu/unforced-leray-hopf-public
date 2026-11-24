import UnforcedLeray.Short.PartIIIa.StressSpaces

/-!
# Part III-a, task `PartIII-a:T23/8`: linearity of the chart coefficient and of `etaL2QSup`

Source of record: `the November 2 reference manuscript`, lines 2664-2745
(the chart coefficient `chartCoeff` and the norm `etaL2QSup`, SP 2706 and 2717).

Proved here: `chartCoeff_add`, `chartCoeff_smul`, `chartCoeff_sum2` (pointwise linearity of the
chart coefficient), and `etaL2QSup_smul_le` (homogeneity bound for the `L²_η L^∞_q` norm).

`etaL2QSup_add_le` is reduced to the `L²_η` Minkowski inequality, which needs the `η`-profiles
`η ↦ essSup_q (W ‖f‖)` to be a.e. measurable. The unconditional statement is NOT proved here
(see `needed`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Additivity of the chart coefficient in the field (SP 2706). -/
theorem chartCoeff_add (R : ℝ) (A B : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    chartCoeff R (fun t y => A t y + B t y) = fun pt => chartCoeff R A pt + chartCoeff R B pt := by
  funext pt
  ext i
  fin_cases i <;> simp [chartCoeff, smul_add] <;> ring

/-- Homogeneity of the chart coefficient in the field (SP 2706). -/
theorem chartCoeff_smul (R a : ℝ) (A : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    chartCoeff R (fun t y => a • A t y) = fun pt => a • chartCoeff R A pt := by
  funext pt
  ext i
  fin_cases i <;> simp [chartCoeff] <;> ring

/-- Pointwise linear combination of the chart coefficient (SP 2706). -/
theorem chartCoeff_sum2 (R a0 a1 : ℝ) (A B C : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (pt : ℝ × (ℝ × ℝ)) :
    chartCoeff R (fun t y => A t y + a0 • B t y + a1 • C t y) pt =
      chartCoeff R A pt + a0 • chartCoeff R B pt + a1 • chartCoeff R C pt := by
  ext i
  fin_cases i <;> simp [chartCoeff] <;> ring

/-- Homogeneity bound for the `L²_η L^∞_q` norm (SP 2717). -/
theorem etaL2QSup_smul_le (c mZ a : ℝ) (f : ℝ × (ℝ × ℝ) → Merid) (s : ℝ) :
    etaL2QSup c mZ (fun pt => a • f pt) s ≤ ENNReal.ofReal |a| * etaL2QSup c mZ f s := by
  unfold etaL2QSup
  have hpt : ∀ pt : ℝ × (ℝ × ℝ),
      ENNReal.ofReal (transWeight mZ pt) * ‖a • f pt‖ₑ =
        ENNReal.ofReal |a| * (ENNReal.ofReal (transWeight mZ pt) * ‖f pt‖ₑ) := by
    intro pt
    rw [enorm_smul, Real.enorm_eq_ofReal_abs]
    ring
  simp_rw [hpt]
  simp_rw [ENNReal.essSup_const_mul]
  have hint : ∀ η : ℝ,
      (ENNReal.ofReal |a| * essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
          ‖f (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) =
        (ENNReal.ofReal |a|) ^ (2 : ℝ) *
          (essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
            ‖f (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ) :=
    fun η => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp_rw [hint]
  rw [lintegral_const_mul' _ _ (by simp)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hc : ((ENNReal.ofReal |a|) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ENNReal.ofReal |a| := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hc]

/-- `L²_η` Minkowski step for `etaL2QSup`, assuming the `η`-profiles are a.e. measurable.
This is the reduction used for `etaL2QSup_add_le`. -/
theorem etaL2QSup_add_le_of_aemeasurable (c mZ : ℝ) (f g : ℝ × (ℝ × ℝ) → Merid) (s : ℝ)
    (hF : AEMeasurable (fun η : ℝ => essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖f (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) volume)
    (hG : AEMeasurable (fun η : ℝ => essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖g (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) volume) :
    etaL2QSup c mZ (fun pt => f pt + g pt) s ≤ etaL2QSup c mZ f s + etaL2QSup c mZ g s := by
  unfold etaL2QSup
  set X : ℝ → ℝ≥0∞ := fun η => essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖f (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2))) with hXdef
  set Y : ℝ → ℝ≥0∞ := fun η => essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖g (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2))) with hYdef
  have hpt : ∀ η : ℝ, essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖(f + g) (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2))) ≤ X η + Y η := by
    intro η
    have hle : (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖(f (s, (q, η)) + g (s, (q, η)))‖ₑ) ≤ᵐ[volume.restrict (Ico (-(c / 2)) (c / 2))]
        ((fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) * ‖f (s, (q, η))‖ₑ) +
          (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) * ‖g (s, (q, η))‖ₑ)) := by
      refine Filter.Eventually.of_forall (fun q => ?_)
      simp only [Pi.add_apply]
      rw [← mul_add]
      exact mul_le_mul_right (enorm_add_le _ _) _
    exact (essSup_mono_ae hle).trans (ENNReal.essSup_add_le _ _)
  have hmono : (∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖(fun pt => f pt + g pt) (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ))
      ≤ ∫⁻ η : ℝ, (X η + Y η) ^ (2 : ℝ) := by
    apply lintegral_mono
    intro η
    exact ENNReal.rpow_le_rpow (hpt η) (by norm_num)
  calc (∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
        ‖(fun pt => f pt + g pt) (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ η : ℝ, (X η + Y η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmono (by norm_num)
    _ = (∫⁻ η : ℝ, (X + Y) η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := rfl
    _ ≤ (∫⁻ η : ℝ, X η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) + (∫⁻ η : ℝ, Y η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_Lp_add_le hF hG (by norm_num)

end UnforcedLeray.Short.IIIa

end
