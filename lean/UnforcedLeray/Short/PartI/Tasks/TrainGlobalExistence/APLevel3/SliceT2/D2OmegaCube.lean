import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2

/-!
# Part I, `PartI:T04/10/2/2/1`: `SliceD2OmegaCube`, the cube bound on `D²ω`

Source of record: `the November 2 reference manuscript`, lines 285-288.
Route: the first half of `sliceT1Bound` (`cylGN_proof` with `m = 3`, `l = 2`): `D²ω ∈ L³(cell)`
with `‖D²ω‖_{L³} ≤ Cm A^{1/3} (∫|D³ω|²)^{1/3}`, and then `∫|D²ω|³ ≤ Cm³ A ∫|D³ω|²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Target `sliceD2OmegaCube`** (lines 285-288). -/
theorem sliceD2OmegaCube : SliceD2OmegaCube := by
  intro A
  obtain ⟨Cm, hCm, hGN⟩ := cylGN_proof 3 (by norm_num)
  refine ⟨Cm ^ 3 * |A|, mul_nonneg (pow_nonneg hCm 3) (abs_nonneg A), ?_⟩
  intro c u hc hS hA0 hW0 hW1 hsup
  obtain ⟨hu, hper, hdiv, hbdd, hL⟩ := hS
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (hsup 0)
  rw [abs_of_nonneg hA]
  -- the vorticity and its jets
  have hf : ContDiff ℝ ∞ (Cyl.curl u) := APEllipticCaux.curl_contDiff hu
  have hfper : Cyl.IsPeriodic c (Cyl.curl u) := apL2s_curl_isPeriodic hper
  have hfL : ∀ j : ℕ, MemLp (Train.jet j (Cyl.curl u)) 2 (Cyl.cellμ c) := fun j =>
    apL2s_memLp_jet hf j (apL2s_curl_integrableOn hu hL j)
  have hsupE : (⨆ z, ‖Cyl.curl u z‖ₑ) ≤ ENNReal.ofReal A := sl_sup_le hsup
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 3 (Cyl.curl u) z‖ ^ 2 :=
    ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact integral_nonneg fun z => sq_nonneg _
  have hI : ∫ z, ‖Train.jet 3 (Cyl.curl u) z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) = Y := by
    rw [hYdef]
    simp only [Real.rpow_two]
    rfl
  have hYc : Train.cellL2 c (Train.jet 3 (Cyl.curl u)) = ENNReal.ofReal (Y ^ (1/2:ℝ)) := by
    have hm := (hfL 3).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [ENNReal.toReal_ofNat] at hm
    unfold Train.cellL2
    rw [hm, hI]
    norm_num
  -- Gagliardo-Nirenberg bound for `l = 2` (L³)
  have hG2 : eLpNorm (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) ≤
      ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) *
        Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ (2/3:ℝ) := by
    have h := hGN c hc (Cyl.curl u) hf hfper hfL 2 (by norm_num) (by norm_num)
    convert h using 3 <;> norm_num
  -- the sup factor and the cell factor, as real bounds
  have hsup3 : (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) ≤ ENNReal.ofReal (A ^ (1/3:ℝ)) :=
    calc (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) ≤ (ENNReal.ofReal A) ^ (1/3:ℝ) :=
          ENNReal.rpow_le_rpow hsupE (by norm_num)
      _ = ENNReal.ofReal (A ^ (1/3:ℝ)) := ENNReal.ofReal_rpow_of_nonneg hA (by norm_num)
  have hcell : ∀ e : ℝ, 0 ≤ e → Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ e =
      ENNReal.ofReal ((Y ^ (1/2:ℝ)) ^ e) := fun e he => by
    rw [hYc, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hY0 _) he]
  have hX2 : eLpNorm (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) ≤
      ENNReal.ofReal (Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) := by
    calc _ ≤ ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) *
          Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ (2/3:ℝ) := hG2
      _ ≤ ENNReal.ofReal Cm * ENNReal.ofReal (A ^ (1/3:ℝ)) *
          ENNReal.ofReal ((Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) := by
          rw [hcell _ (by norm_num)]
          gcongr
      _ = ENNReal.ofReal (Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCm (Real.rpow_nonneg hA _)),
            ENNReal.ofReal_mul hCm]
  -- membership
  have hmem2 : MemLp (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) :=
    sl_memLp_jet hf 2 hX2
  -- the cube of the bound
  have hpow3 : (Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) ^ (3:ℝ) = Cm ^ 3 * A * Y := by
    rw [Real.mul_rpow (mul_nonneg hCm (Real.rpow_nonneg hA _))
        (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _),
      Real.mul_rpow hCm (Real.rpow_nonneg hA _), sl_cube_third A hA, sl_rpow_cube Y hY0,
      sl_rpow_three]
  have hP : ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) ≤ Cm ^ 3 * A * Y := by
    have h := sl_int_pow_le (μ := Cyl.cellμ c) (f := Train.jet 2 (Cyl.curl u)) (p := 3)
      (X := Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) (by norm_num)
      (mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg hA _))
        (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _))
      (by simpa using hmem2) hX2
    rw [hpow3] at h
    exact h
  rw [← hYdef]
  exact ⟨hmem2, hP⟩

end UnforcedLeray.Short.PartI
