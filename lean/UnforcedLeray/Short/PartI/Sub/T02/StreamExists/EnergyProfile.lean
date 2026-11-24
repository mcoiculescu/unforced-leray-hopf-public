import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`, lemma `SliceEnergyProfile`

Source of record: `the November 2 reference manuscript`, lines 261-288.

The energy profile `G(η) = ∫₀^c |w(q, η)|² dq` of a slice is integrable (Fubini on the cell and
`c`-periodicity in `q`) and Lipschitz with constant `2 M₀ M₁ |c|`, where `M₀` bounds `|w|` and `M₁`
bounds `‖Dw‖` (mean value inequality in the `η` direction).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`SliceEnergyProfile`** (source lines 261-288): the energy profile of a slice is integrable
and Lipschitz in `η`. -/
theorem sliceEnergyProfile : SliceEnergyProfile := by
  intro c w hs
  have hc : 0 < c := hs.pos
  have hd : Differentiable ℝ w := hs.smooth.differentiable (by simp)
  obtain ⟨M0, hM0⟩ := hs.bdd 0
  obtain ⟨M1, hM1⟩ := hs.bdd 1
  have hw0 : ∀ z : Plane, ‖w z‖ ≤ M0 := fun z => by
    have h := hM0 z
    rwa [norm_iteratedFDeriv_zero] at h
  have hw1 : ∀ z : Plane, ‖fderiv ℝ w z‖ ≤ M1 := fun z => by
    have h := hM1 z
    rwa [norm_iteratedFDeriv_one] at h
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hw1 0)
  -- The `q`-integral over `[0, c]` equals the one over the centred cell `[-c/2, c/2)`.
  have hper : ∀ η : ℝ, sliceEnergy c w η = ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2 := by
    intro η
    have hp : Function.Periodic (fun q : ℝ => ‖w (q, η)‖ ^ 2) c := by
      intro q
      have h : w (q + c, η) = w (q, η) := hs.periodic (q, η)
      show ‖w (q + c, η)‖ ^ 2 = ‖w (q, η)‖ ^ 2
      rw [h]
    have hA : ∫ q in (-c / 2)..(-c / 2 + c), ‖w (q, η)‖ ^ 2
        = ∫ q in (0 : ℝ)..c, ‖w (q, η)‖ ^ 2 := by
      have h := hp.intervalIntegral_add_eq (-c / 2) 0
      rw [zero_add] at h
      exact h
    have hB : -c / 2 + c = c / 2 := by ring
    rw [hB] at hA
    unfold sliceEnergy
    rw [← hA, intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith),
      integral_Ico_eq_integral_Ioc]
  -- Integrability: Fubini on the cell gives integrability of the iterated `q`-integral.
  have hI : Integrable (fun η : ℝ => ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2) := by
    have h1 : Integrable (fun z : Plane => ‖w z‖ ^ 2)
        ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
      rw [← Cyl.volume_restrict_cell c]
      exact hs.energy
    exact h1.integral_prod_right
  have hint : Integrable (sliceEnergy c w) := by
    have hfun : sliceEnergy c w = fun η : ℝ => ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2 :=
      funext hper
    rw [hfun]
    exact hI
  -- Lipschitz in `η` for fixed `q`: mean value inequality on the whole plane.
  have hlip : ∀ q η η' : ℝ, ‖w (q, η) - w (q, η')‖ ≤ M1 * |η - η'| := by
    intro q η η'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := w) (s := Set.univ)
      (fun x _ => hd x) (fun x _ => hw1 x) convex_univ
      (Set.mem_univ ((q, η') : Plane)) (Set.mem_univ ((q, η) : Plane))
    have hnorm : ‖((q, η) : Plane) - ((q, η') : Plane)‖ ≤ |η - η'| := by
      have hsub : ((q, η) : Plane) - ((q, η') : Plane) = (0, η - η') := by
        ext <;> simp
      rw [hsub, Prod.norm_def]
      simp [Real.norm_eq_abs]
    calc ‖w (q, η) - w (q, η')‖ ≤ M1 * ‖((q, η) : Plane) - ((q, η') : Plane)‖ := h
      _ ≤ M1 * |η - η'| := mul_le_mul_of_nonneg_left hnorm hM1nn
  -- Pointwise: `| |w(q,η)|² - |w(q,η')|² | ≤ 2 M₀ M₁ |η - η'|`.
  have hpt : ∀ q η η' : ℝ,
      |‖w (q, η)‖ ^ 2 - ‖w (q, η')‖ ^ 2| ≤ 2 * M0 * M1 * |η - η'| := by
    intro q η η'
    have hab : |‖w (q, η)‖ - ‖w (q, η')‖| ≤ M1 * |η - η'| :=
      (abs_norm_sub_norm_le _ _).trans (hlip q η η')
    have hfac : ‖w (q, η)‖ ^ 2 - ‖w (q, η')‖ ^ 2
        = (‖w (q, η)‖ - ‖w (q, η')‖) * (‖w (q, η)‖ + ‖w (q, η')‖) := by ring
    have hsum : ‖w (q, η)‖ + ‖w (q, η')‖ ≤ 2 * M0 := by
      linarith [hw0 (q, η), hw0 (q, η')]
    have hsum0 : 0 ≤ ‖w (q, η)‖ + ‖w (q, η')‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [hfac, abs_mul, abs_of_nonneg hsum0]
    calc |‖w (q, η)‖ - ‖w (q, η')‖| * (‖w (q, η)‖ + ‖w (q, η')‖)
        ≤ (M1 * |η - η'|) * (2 * M0) :=
          mul_le_mul hab hsum hsum0 (mul_nonneg hM1nn (abs_nonneg _))
      _ = 2 * M0 * M1 * |η - η'| := by ring
  -- Splitting the difference of two energy profiles.
  have hcont : ∀ η : ℝ, Continuous (fun q : ℝ => ‖w (q, η)‖ ^ 2) := fun η => by
    have hw : Continuous w := hd.continuous
    have hq : Continuous (fun q : ℝ => w (q, η)) := by fun_prop
    exact hq.norm.pow 2
  have hdiff : ∀ η η' : ℝ, sliceEnergy c w η - sliceEnergy c w η'
      = ∫ q in (0 : ℝ)..c, (‖w (q, η)‖ ^ 2 - ‖w (q, η')‖ ^ 2) := by
    intro η η'
    unfold sliceEnergy
    rw [intervalIntegral.integral_sub ((hcont η).intervalIntegrable 0 c)
      ((hcont η').intervalIntegrable 0 c)]
  refine ⟨hint, 2 * M0 * M1 * |c|, fun η η' => ?_⟩
  rw [hdiff η η']
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := c)
    (C := 2 * M0 * M1 * |η - η'|)
    (f := fun q : ℝ => ‖w (q, η)‖ ^ 2 - ‖w (q, η')‖ ^ 2)
    (fun q _ => by simpa only [Real.norm_eq_abs] using hpt q η η')
  rw [Real.norm_eq_abs] at hbd
  refine hbd.trans (le_of_eq ?_)
  rw [sub_zero]
  ring

end UnforcedLeray.Short.PartI
