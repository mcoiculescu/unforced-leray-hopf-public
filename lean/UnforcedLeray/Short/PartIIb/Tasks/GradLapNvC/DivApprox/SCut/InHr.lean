import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2_1

/-!
# Part II-b, task `PartII-b:T09/2/1/2` (`DivSCutInHr`): the cut pieces stay in `H_r`

Source of record: `the November 2 reference manuscript`, lines 1912-1918.
Bounded continuous `q`-invariant multipliers (`DriftSCutHelp.inHr_smul_bdd`): `χ_k ≤ 1`,
`|-2ε s χ_k'| ≤ 2|ε| M/k`, and `√s |-2ε s χ_k'| ≤ e^k 2|ε| M/k` (`χ_k' = 0` for `s > e^{2k}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open DriftSCutHelp in
/-- **`PartII-b:T09/2/1/2`.** -/
theorem divSCutInHr_proof : UnforcedLeray.Short.IIb.DivSCutInHr := by
  intro c r ε k b Qb Eb hc hr hk hd
  obtain ⟨M, hM0, hMb⟩ := sBump_deriv_bound_exists
  have hχc : Continuous (fun y : Coord => sBump k y.1) :=
    (sBump_smooth hk).continuous.comp continuous_fst
  have hbd1 : ∀ x : Coord, ‖sBump k x.1‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sBump_nonneg _ _)]
    exact sBump_le_one _ _
  have eS : ∀ f : CProf, sqrtS (sCutB k f) =
      fun x => ((fun y : Coord => sBump k y.1) x : ℂ) • sqrtS f x := by
    intro f
    funext x
    simp only [sqrtS, sCutB, smul_smul, mul_comm]
  have hC0 : 0 ≤ 2 * |ε| * (M * (1 / k)) :=
    mul_nonneg (mul_nonneg zero_le_two (abs_nonneg ε)) (mul_nonneg hM0 (by positivity))
  have hD : Continuous (fun x : Coord => -2 * ε * (x.1 * deriv (sBump k) x.1)) :=
    continuous_const.mul (sD_continuous hk)
  have hDbd : ∀ x : Coord, ‖-2 * ε * (x.1 * deriv (sBump k) x.1)‖ ≤ 2 * |ε| * (M * (1 / k)) := by
    intro x
    rw [Real.norm_eq_abs]
    calc |-2 * ε * (x.1 * deriv (sBump k) x.1)|
        = 2 * |ε| * |x.1 * deriv (sBump k) x.1| := by
          rw [abs_mul, abs_mul]
          norm_num
      _ ≤ 2 * |ε| * (M * (1 / k)) :=
          mul_le_mul_of_nonneg_left (hMb k hk x.1) (mul_nonneg zero_le_two (abs_nonneg ε))
  have hDs : Continuous (fun x : Coord => Real.sqrt x.1 * (-2 * ε * (x.1 * deriv (sBump k) x.1))) :=
    (Real.continuous_sqrt.comp continuous_fst).mul hD
  have hC1 : 0 ≤ Real.exp k * (2 * |ε| * (M * (1 / k))) := mul_nonneg (Real.exp_pos k).le hC0
  have hDsbd : ∀ x : Coord, ‖Real.sqrt x.1 * (-2 * ε * (x.1 * deriv (sBump k) x.1))‖ ≤
      Real.exp k * (2 * |ε| * (M * (1 / k))) := by
    intro x
    by_cases h : Real.exp (2 * k) < x.1
    · rw [sBump_deriv_zero_of_gt hk h]
      simpa using hC1
    · rw [not_lt] at h
      rw [norm_mul]
      refine mul_le_mul ?_ (hDbd x) (norm_nonneg _) (Real.exp_pos k).le
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt x.1 ≤ Real.sqrt (Real.exp (2 * k)) := Real.sqrt_le_sqrt h
        _ = Real.exp k := by
          rw [show 2 * k = k + k by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos k).le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inHr_smul_bdd (χ := fun y : Coord => sBump k y.1) hχc zero_le_one hbd1
      (fun x => rfl) hd.inHr
  · rw [eS]
    exact inHr_smul_bdd (χ := fun y : Coord => sBump k y.1) hχc zero_le_one hbd1
      (fun x => rfl) hd.inQ
  · rw [eS]
    exact inHr_smul_bdd (χ := fun y : Coord => sBump k y.1) hχc zero_le_one hbd1
      (fun x => rfl) hd.inE
  · exact inHr_smul_bdd (χ := fun x : Coord => -2 * ε * (x.1 * deriv (sBump k) x.1)) hD hC0
      hDbd (fun x => rfl) hd.inHr
  · have e : sqrtS (sCutD ε k b) = fun x =>
        ((fun y : Coord => Real.sqrt y.1 * (-2 * ε * (y.1 * deriv (sBump k) y.1))) x : ℂ) • b x := by
      funext x
      simp only [sqrtS, sCutD, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact inHr_smul_bdd
      (χ := fun y : Coord => Real.sqrt y.1 * (-2 * ε * (y.1 * deriv (sBump k) y.1))) hDs hC1
      hDsbd (fun x => rfl) hd.inHr

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSCutInHr_proof
