import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT1.Holder

/-!
# Part I, `PartI:T04/10/2/1`: `sliceT1Bound`, the first slice-level commutator leaf

Source of record: `the November 2 reference manuscript`, lines 285-288.
Route: Hölder `(3, 3/2)` then `(4/3, 4)` on `∫ |D²ω| |D²u| |Dω|`; `cylGN_proof` (`m = 3`) for
`l = 2` (`L³`) and `l = 1` (`L⁶`); `apElliptic` (`j = 1`) for `∫|D²u|² ≤ K₁ A`.
The cubed bound gives `T² ≤ L Y` with `Y = ∫|D³ω|²`, and AM-GM closes it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

theorem sl_rpow_three (x : ℝ) : x ^ (3:ℝ) = x ^ 3 := by
  exact_mod_cast Real.rpow_natCast x 3

theorem sl_memLp_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ} {g : Plane → E}
    (hg : ContDiff ℝ ∞ g) (j : ℕ) {p : ℝ≥0∞} {X : ℝ}
    (h : eLpNorm (Train.jet j g) p (Cyl.cellμ c) ≤ ENNReal.ofReal X) :
    MemLp (Train.jet j g) p (Cyl.cellμ c) :=
  ⟨(hg.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).aestronglyMeasurable,
    lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩

/-- The sup-norm enclosure `⨆ ‖f z‖ₑ ≤ A` from the pointwise bound. -/
theorem sl_sup_le {f : Plane → ℝ} {A : ℝ} (hsup : ∀ z, |f z| ≤ A) :
    (⨆ z, ‖f z‖ₑ) ≤ ENNReal.ofReal A :=
  iSup_le fun z => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hsup z)

/-- `T ≤ S` cubed-root style step used to close the AM-GM: `T² ≤ L Y`. -/
theorem sl_sq_le_of_pow {T L Y : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (h : (T ^ 2) ^ 3 ≤ (L * Y) ^ 3) : T ^ 2 ≤ L * Y :=
  (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hL hY) (by norm_num)).1 h

/-- **Target `sliceT1Bound`** (lines 285-288). -/
theorem sliceT1Bound : SliceT1Bound := by
  intro ν A hν
  obtain ⟨Cm, hCm, hGN⟩ := cylGN_proof 3 (by norm_num)
  obtain ⟨K1, hK1, hE⟩ := apElliptic 1
  refine ⟨4 * (Cm ^ 4 * K1 * |A| ^ 3 / ν), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (div_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hCm 4) hK1) (pow_nonneg (abs_nonneg A) 3)) hν.le)
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
  -- Gagliardo-Nirenberg bounds for `l = 2` (L³) and `l = 1` (L⁶), in `eLpNorm` form
  have hG2 : eLpNorm (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) ≤
      ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) *
        Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ (2/3:ℝ) := by
    have h := hGN c hc (Cyl.curl u) hf hfper hfL 2 (by norm_num) (by norm_num)
    convert h using 3 <;> norm_num
  have hG1 : eLpNorm (Train.jet 1 (Cyl.curl u)) (ENNReal.ofReal 6) (Cyl.cellμ c) ≤
      ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (2/3:ℝ) *
        Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ (1/3:ℝ) := by
    have h := hGN c hc (Cyl.curl u) hf hfper hfL 1 (by norm_num) (by norm_num)
    convert h using 3 <;> norm_num
  -- the sup factor and the cell factor, as real bounds
  have hsup3 : (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) ≤ ENNReal.ofReal (A ^ (1/3:ℝ)) :=
    calc (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (1/3:ℝ) ≤ (ENNReal.ofReal A) ^ (1/3:ℝ) :=
          ENNReal.rpow_le_rpow hsupE (by norm_num)
      _ = ENNReal.ofReal (A ^ (1/3:ℝ)) := ENNReal.ofReal_rpow_of_nonneg hA (by norm_num)
  have hsup2 : (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (2/3:ℝ) ≤ ENNReal.ofReal (A ^ (2/3:ℝ)) :=
    calc (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (2/3:ℝ) ≤ (ENNReal.ofReal A) ^ (2/3:ℝ) :=
          ENNReal.rpow_le_rpow hsupE (by norm_num)
      _ = ENNReal.ofReal (A ^ (2/3:ℝ)) := ENNReal.ofReal_rpow_of_nonneg hA (by norm_num)
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
  have hX1 : eLpNorm (Train.jet 1 (Cyl.curl u)) (ENNReal.ofReal 6) (Cyl.cellμ c) ≤
      ENNReal.ofReal (Cm * A ^ (2/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (1/3:ℝ)) := by
    calc _ ≤ ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl u z‖ₑ) ^ (2/3:ℝ) *
          Train.cellL2 c (Train.jet 3 (Cyl.curl u)) ^ (1/3:ℝ) := hG1
      _ ≤ ENNReal.ofReal Cm * ENNReal.ofReal (A ^ (2/3:ℝ)) *
          ENNReal.ofReal ((Y ^ (1/2:ℝ)) ^ (1/3:ℝ)) := by
          rw [hcell _ (by norm_num)]
          gcongr
      _ = ENNReal.ofReal (Cm * A ^ (2/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (1/3:ℝ)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCm (Real.rpow_nonneg hA _)),
            ENNReal.ofReal_mul hCm]
  -- memberships
  have hmem2 : MemLp (Train.jet 2 (Cyl.curl u)) (ENNReal.ofReal 3) (Cyl.cellμ c) :=
    sl_memLp_jet hf 2 hX2
  have hmem1 : MemLp (Train.jet 1 (Cyl.curl u)) (ENNReal.ofReal 6) (Cyl.cellμ c) :=
    sl_memLp_jet hf 1 hX1
  have hmemG : MemLp (Train.jet 2 u) 2 (Cyl.cellμ c) := apL2s_memLp_jet hu 2 (hL 2)
  -- powers of the bounds
  have hpow3 : (Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) ^ (3:ℝ) = Cm ^ 3 * A * Y := by
    rw [Real.mul_rpow (mul_nonneg hCm (Real.rpow_nonneg hA _))
        (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _),
      Real.mul_rpow hCm (Real.rpow_nonneg hA _), sl_cube_third A hA, sl_rpow_cube Y hY0,
      sl_rpow_three]
  have hA46 : (A ^ (2/3:ℝ)) ^ (6:ℝ) = A ^ 4 := by
    rw [← Real.rpow_mul hA]; norm_num
  have hpow6 : (Cm * A ^ (2/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (1/3:ℝ)) ^ (6:ℝ) = Cm ^ 6 * A ^ 4 * Y := by
    rw [Real.mul_rpow (mul_nonneg hCm (Real.rpow_nonneg hA _))
        (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _),
      Real.mul_rpow hCm (Real.rpow_nonneg hA _), hA46, sl_six_power Y hY0, Real.rpow_one]
    rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hP : ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) ≤ Cm ^ 3 * A * Y := by
    have h := sl_int_pow_le (μ := Cyl.cellμ c) (f := Train.jet 2 (Cyl.curl u)) (p := 3)
      (X := Cm * A ^ (1/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (2/3:ℝ)) (by norm_num)
      (mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg hA _)) (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _))
      (by simpa using hmem2) hX2
    rw [hpow3] at h
    exact h
  have hR : ∫ z, ‖Train.jet 1 (Cyl.curl u) z‖ ^ (6:ℝ) ∂(Cyl.cellμ c) ≤ Cm ^ 6 * A ^ 4 * Y := by
    have h := sl_int_pow_le (μ := Cyl.cellμ c) (f := Train.jet 1 (Cyl.curl u)) (p := 6)
      (X := Cm * A ^ (2/3:ℝ) * (Y ^ (1/2:ℝ)) ^ (1/3:ℝ)) (by norm_num)
      (mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg hA _)) (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _))
      (by simpa using hmem1) hX1
    rw [hpow6] at h
    exact h
  have hQ : ∫ z, ‖Train.jet 2 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) ≤ K1 * A := by
    have hEu := hE c hc u hu hper hdiv hbdd hL
    calc ∫ z, ‖Train.jet 2 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c)
        = ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (1 + 1) u z‖ ^ 2 := by
          simp only [Real.rpow_two]; rfl
      _ ≤ K1 * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl u) z‖ ^ 2 := hEu
      _ ≤ K1 * A := mul_le_mul_of_nonneg_left hW1 hK1
  -- the three factors
  have hF0 : ∀ z, 0 ≤ ‖Train.jet 2 (Cyl.curl u) z‖ := fun z => norm_nonneg _
  have hG0 : ∀ z, 0 ≤ ‖Train.jet 2 u z‖ := fun z => norm_nonneg _
  have hH0 : ∀ z, 0 ≤ ‖Train.jet 1 (Cyl.curl u) z‖ := fun z => norm_nonneg _
  have hmF : MemLp (fun z => ‖Train.jet 2 (Cyl.curl u) z‖) (ENNReal.ofReal 3) (Cyl.cellμ c) :=
    hmem2.norm
  have hmG : MemLp (fun z => ‖Train.jet 2 u z‖) (ENNReal.ofReal 2) (Cyl.cellμ c) := by
    have := hmemG.norm
    simpa using this
  have hmH : MemLp (fun z => ‖Train.jet 1 (Cyl.curl u) z‖) (ENNReal.ofReal 6) (Cyl.cellμ c) :=
    hmem1.norm
  have hT := sl_holder_T (μ := Cyl.cellμ c) hF0 hG0 hH0 hmF hmG hmH
  have hS := sl_holder_S (μ := Cyl.cellμ c) hG0 hH0 hmG hmH
  have hTn : 0 ≤ ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ * (‖Train.jet 2 u z‖ * ‖Train.jet 1 (Cyl.curl u) z‖) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => mul_nonneg (hF0 z) (mul_nonneg (hG0 z) (hH0 z))
  have hPn : 0 ≤ ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (hF0 z) _
  have hQn : 0 ≤ ∫ z, ‖Train.jet 2 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (hG0 z) _
  have hRn : 0 ≤ ∫ z, ‖Train.jet 1 (Cyl.curl u) z‖ ^ (6:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (hH0 z) _
  have hSn : 0 ≤ ∫ z, (‖Train.jet 2 u z‖ * ‖Train.jet 1 (Cyl.curl u) z‖) ^ (3/2:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => Real.rpow_nonneg (mul_nonneg (hG0 z) (hH0 z)) _
  have hS4 := sl_fourth_holder hSn hQn hRn hS
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ *
      (‖Train.jet 2 u z‖ * ‖Train.jet 1 (Cyl.curl u) z‖) ∂(Cyl.cellμ c) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∫ z, ‖Train.jet 2 (Cyl.curl u) z‖ ^ (3:ℝ) ∂(Cyl.cellμ c) :=
    ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∫ z, (‖Train.jet 2 u z‖ * ‖Train.jet 1 (Cyl.curl u) z‖) ^ (3/2:ℝ)
      ∂(Cyl.cellμ c) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ∫ z, ‖Train.jet 2 u z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∫ z, ‖Train.jet 1 (Cyl.curl u) z‖ ^ (6:ℝ) ∂(Cyl.cellμ c) :=
    ⟨_, rfl⟩
  have hT' : T ^ 3 ≤ P * S ^ 2 := by rw [hTdef, hPdef, hSdef]; exact hT
  have hS' : S ^ 4 ≤ Q ^ 3 * R := by rw [hSdef, hQdef, hRdef]; exact hS4
  have hPb : P ≤ Cm ^ 3 * A * Y := by rw [hPdef]; exact hP
  have hQb : Q ≤ K1 * A := by rw [hQdef]; exact hQ
  have hRb : R ≤ Cm ^ 6 * A ^ 4 * Y := by rw [hRdef]; exact hR
  have hTn' : 0 ≤ T := by rw [hTdef]; exact hTn
  have hPn' : 0 ≤ P := by rw [hPdef]; exact hPn
  have hQn' : 0 ≤ Q := by rw [hQdef]; exact hQn
  have hRn' : 0 ≤ R := by rw [hRdef]; exact hRn
  have hL0 : 0 ≤ Cm ^ 4 * K1 * A ^ 3 :=
    mul_nonneg (mul_nonneg (pow_nonneg hCm 4) hK1) (pow_nonneg hA 3)
  have hT6 : (T ^ 2) ^ 3 ≤ ((Cm ^ 4 * K1 * A ^ 3) * Y) ^ 3 := by
    have h1 : (T ^ 3) ^ 2 ≤ (P * S ^ 2) ^ 2 := pow_le_pow_left₀ (pow_nonneg hTn' 3) hT' 2
    have h2 : P ^ 2 ≤ (Cm ^ 3 * A * Y) ^ 2 := pow_le_pow_left₀ hPn' hPb 2
    have h3 : Q ^ 3 ≤ (K1 * A) ^ 3 := pow_le_pow_left₀ hQn' hQb 3
    have h4 : P ^ 2 * S ^ 4 ≤ P ^ 2 * (Q ^ 3 * R) := mul_le_mul_of_nonneg_left hS' (sq_nonneg P)
    have h5 : P ^ 2 * (Q ^ 3 * R) ≤ (Cm ^ 3 * A * Y) ^ 2 * ((K1 * A) ^ 3 * (Cm ^ 6 * A ^ 4 * Y)) :=
      mul_le_mul h2 (mul_le_mul h3 hRb hRn' (pow_nonneg (mul_nonneg hK1 hA) 3))
        (mul_nonneg (pow_nonneg hQn' 3) hRn') (sq_nonneg _)
    calc (T ^ 2) ^ 3 = (T ^ 3) ^ 2 := by ring
      _ ≤ (P * S ^ 2) ^ 2 := h1
      _ = P ^ 2 * S ^ 4 := by ring
      _ ≤ P ^ 2 * (Q ^ 3 * R) := h4
      _ ≤ (Cm ^ 3 * A * Y) ^ 2 * ((K1 * A) ^ 3 * (Cm ^ 6 * A ^ 4 * Y)) := h5
      _ = ((Cm ^ 4 * K1 * A ^ 3) * Y) ^ 3 := by ring
  have hT2 : T ^ 2 ≤ (Cm ^ 4 * K1 * A ^ 3) * Y :=
    (pow_le_pow_iff_left₀ (sq_nonneg T) (mul_nonneg hL0 hY0) (by norm_num)).1 hT6
  have hAM := apL2s_amgm hTn' hY0 hL0 hν hT2
  have e16 : 16 * (Cm ^ 4 * K1 * A ^ 3) / ν = 4 * (4 * (Cm ^ 4 * K1 * A ^ 3 / ν)) := by ring
  rw [e16] at hAM
  have hK0 : 0 ≤ Cm ^ 4 * K1 * A ^ 3 / ν := div_nonneg hL0 hν.le
  have hY2 : 0 ≤ ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hcT : (∫ z in Cyl.cell c, commT1 u z) = T := by rw [hTdef]; rfl
  rw [← hYdef]
  refine ⟨?_, ?_⟩
  · have hint : MemLp (fun z => ‖Train.jet 2 (Cyl.curl u) z‖ *
        (‖Train.jet 2 u z‖ * ‖Train.jet 1 (Cyl.curl u) z‖)) 1 (Cyl.cellμ c) := by
      haveI := sl_triple3
      exact MemLp.mul (r := 1) (sl_memLp_GH hmG hmH) hmF
    exact memLp_one_iff_integrable.1 hint
  · rw [hcT]
    nlinarith [hAM, mul_nonneg hK0 hY2, mul_nonneg hν.le hY0]

end UnforcedLeray.Short.PartI
