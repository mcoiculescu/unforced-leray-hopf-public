import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The bump `1` on the ball of radius `1`, `0` outside the ball of radius `2`, on `Coord`. -/
def mollExistsBump : ContDiffBump (0 : Coord) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The normalized bump `ρ₀`. -/
def mollExistsRho : Coord → ℝ := mollExistsBump.normed volume

theorem mollExists_finrank : Module.finrank ℝ Coord = 3 := by
  simp [Coord]

theorem mollExists_molN_integral (ρ : Coord → ℝ) (hρ : ∫ x, ρ x = 1) (n : ℕ) :
    ∫ x, molN ρ n x = 1 := by
  unfold molN
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_smul, hρ, mollExists_finrank]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 := by positivity
  rw [abs_of_nonneg (inv_nonneg.2 h3.le), smul_eq_mul]
  field_simp

theorem mollExists_molN_isMollifier (ρ : Coord → ℝ) (hρ : IsMollifier ρ) (n : ℕ) :
    IsMollifier (molN ρ n) := by
  obtain ⟨⟨hsm, hcs⟩, hnn, hint⟩ := hρ
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨⟨?_, ?_⟩, ?_, mollExists_molN_integral ρ hint n⟩
  · unfold molN
    exact contDiff_const.mul (hsm.comp (contDiff_const_smul _))
  · unfold molN
    exact (hcs.comp_smul hpos.ne').mul_left
  · intro x
    unfold molN
    exact mul_nonneg (by positivity) (hnn _)

theorem mollExists_base_isMollifier : IsMollifier mollExistsRho := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact mollExistsBump.contDiff_normed
  · exact mollExistsBump.hasCompactSupport_normed
  · intro x
    exact mollExistsBump.nonneg_normed x
  · exact mollExistsBump.integral_normed

/-- **Mollifier family** (`MollExists`). -/
theorem mollExists_proof : UnforcedLeray.Short.IIb.MollExists :=
  ⟨mollExistsRho, mollExists_base_isMollifier,
    fun n => mollExists_molN_isMollifier _ mollExists_base_isMollifier n⟩

end UnforcedLeray.Short.IIb
