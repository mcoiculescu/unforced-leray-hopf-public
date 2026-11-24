import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimInt4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.XKerJoint

/-!
# The scalar kernel `A_h = (xKer h · M)₂`, and `sKer = - primInt`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The third component of the phase-lag kernel. -/
def xKerA (ν μ h : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space) : ℝ := xKer ν μ h x M 2

theorem pdLam_pos (h : ℝ) : 0 < pdLam h := Real.exp_pos _

theorem pdLam_lt_one {h : ℝ} (hh : 0 < h) : pdLam h < 1 := by
  unfold pdLam
  have := Real.exp_lt_exp.2 (show -(h / 2) < 0 by linarith)
  simpa using this

/-- Decay of `xKerA` and its derivatives, from `PDKerBounds`. -/
theorem xKerA_props (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M)
    (ν μ h : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (hh : 0 < h)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ 2 (xKerA ν μ h M) ∧
    (∀ x : Space, x ≠ 0 → |xKerA ν μ h M x| ≤
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (‖x‖ ^ 4)⁻¹) ∧
    (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 1 (xKerA ν μ h M) x‖ ≤
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (‖x‖ ^ 5)⁻¹) ∧
    (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 2 (xKerA ν μ h M) x‖ ≤
        (C * pdLam h ^ (2 * μ + 3) * IIIa.tensorNorm M) * (‖x‖ ^ 6)⁻¹) := by
  obtain ⟨hcd, -, hb⟩ := hC ν μ h hν hμ0 hμ1 hh M
  set L : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3) with hL
  have hLn : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    have := PiLp.norm_apply_le x 2
    simpa [hL] using this)
  have hA : xKerA ν μ h M = L ∘ (fun x' => xKer ν μ h x' M) := rfl
  have hLc : ∀ n : ℕ, n ≤ 2 → ∀ x : Space,
      ‖iteratedFDeriv ℝ n (xKerA ν μ h M) x‖ ≤ ‖iteratedFDeriv ℝ n (fun x' => xKer ν μ h x' M) x‖ := by
    intro n hn x
    rw [hA]
    have := L.norm_iteratedFDeriv_comp_left (hcd.contDiffAt (x := x)) (by exact_mod_cast hn)
    exact this.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ n (fun x' => xKer ν μ h x' M) x)])
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hA]; exact L.contDiff.comp hcd
  · have h1 := (hb x hx).1
    have : |xKerA ν μ h M x| ≤ ‖xKer ν μ h x M‖ := by
      have := PiLp.norm_apply_le (xKer ν μ h x M) 2
      simpa [xKerA, Real.norm_eq_abs] using this
    refine this.trans (h1.trans (le_of_eq ?_))
    ring
  · have h1 := hLc 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h1
    rw [norm_iteratedFDeriv_one]
    refine h1.trans (((hb x hx).2.1).trans (le_of_eq ?_))
    ring
  · refine (hLc 2 le_rfl x).trans (((hb x hx).2.2.1).trans (le_of_eq ?_))
    ring

/-- The Ioi shift: `∫_{ρ>r} g ρ = ∫_{u>0} g (r+u)`. -/
theorem integral_Ioi_shift (g : ℝ → ℝ) (r : ℝ) :
    ∫ ρ in Ioi r, g ρ = ∫ u in Ioi (0 : ℝ), g (r + u) := by
  have h1 : ∫ ρ in Ioi r, g ρ = ∫ ρ, (Ioi r).indicator g ρ := (integral_indicator measurableSet_Ioi).symm
  have h2 : ∫ u in Ioi (0 : ℝ), g (r + u) = ∫ u, (Ioi (0 : ℝ)).indicator (fun u => g (r + u)) u :=
    (integral_indicator measurableSet_Ioi).symm
  rw [h1, h2, ← integral_add_left_eq_self (μ := volume) ((Ioi r).indicator g) r]
  congr 1
  funext u
  by_cases hu : 0 < u
  · simp [indicator, hu, show r < r + u by linarith]
  · simp [indicator, hu, show ¬ r < r + u by intro h; exact hu (by linarith)]

theorem sKer_eq_primInt (ν μ h r y3 : ℝ) (z : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    sKer ν μ h r y3 z M =
      -primInt (xKerA ν μ h M) (pdLam h • z) !₂[r, 0, y3] := by
  unfold sKer primInt primF xKerA
  congr 1
  rw [integral_Ioi_shift (fun ρ => ρ * xKer ν μ h (!₂[ρ, 0, y3] - pdLam h • z) M 2) r]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have e : (!₂[r, 0, y3] : Space) + (u • primE0 - pdLam h • z) = !₂[r + u, 0, y3] - pdLam h • z := by
    ext i; fin_cases i <;> simp [primE0] <;> ring
  simp only [e]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
