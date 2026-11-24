import UnforcedLeray.Lib.Cylinder.CellModes
import UnforcedLeray.Lib.CylinderB.ModePairing
import UnforcedLeray.Units.B0581.Coeff

/-! Compare the two existing normalized horizontal-mode definitions on the centered cell. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Complex AddCircle
open scoped ComplexConjugate

namespace UnforcedLeray.Cons.L2.SolAudit

theorem cyl_fourier_eq_eMode {c : ℝ} (_hc : 0 < c) (k : ℤ) (q : ℝ) :
    fourier (-k) (q : AddCircle (c / 2 - -c / 2)) =
      conj (UnforcedLeray.B0581.eMode c k q) := by
  rw [fourier_neg, fourier_coe_apply, UnforcedLeray.Cyl.half_sub_neg_half]
  congr 1
  unfold UnforcedLeray.B0581.eMode
  congr 1
  push_cast
  ring

theorem cyl_qMode_eq_b0581_modeCoeff {c : ℝ} (hc : 0 < c) (k : ℤ)
    (f : UnforcedLeray.Cyl.Plane → ℂ) (η : ℝ) :
    UnforcedLeray.Cyl.qMode c hc k f η = UnforcedLeray.B0581.modeCoeff c k f η := by
  rw [UnforcedLeray.Cyl.qMode_eq_setIntegral hc k f η]
  unfold UnforcedLeray.B0581.modeCoeff UnforcedLeray.B0581.qInt
  simp_rw [cyl_fourier_eq_eMode hc k]
  simp only [smul_eq_mul]
  simp only [neg_div]
  norm_cast

#print axioms cyl_qMode_eq_b0581_modeCoeff

/-- Existing CY04 Parseval uniqueness, expressed for B0581's explicit coefficients. -/
theorem b0581_ae_eq_zero_of_modeCoeff {c : ℝ} (hc : 0 < c)
    {f : UnforcedLeray.Cyl.Plane → ℂ}
    (hf : MeasureTheory.MemLp f 2 (UnforcedLeray.Cyl.cellμ c))
    (h : ∀ k : ℤ, UnforcedLeray.B0581.modeCoeff c k f =ᵐ[MeasureTheory.volume] 0) :
    f =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := by
  apply UnforcedLeray.Cyl.ae_eq_zero_of_qMode hc hf
  intro k
  simpa only [funext (cyl_qMode_eq_b0581_modeCoeff hc k f)] using h k

#print axioms b0581_ae_eq_zero_of_modeCoeff

/-- The B0581 mode analysis map has zero kernel, via existing cell Parseval. -/
theorem b0581_modes_eq_zero_iff {c : ℝ} [Fact (0 < c)]
    (f : Lp ℂ 2 (UnforcedLeray.B0581.cellVol c)) :
    UnforcedLeray.B0581.modes c f = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    have hf : MeasureTheory.MemLp (f : UnforcedLeray.Cyl.Plane → ℂ) 2
        (UnforcedLeray.Cyl.cellμ c) := by
      simpa only [UnforcedLeray.B0581.cellVol, UnforcedLeray.B0579.cell,
        UnforcedLeray.Cyl.cellμ, UnforcedLeray.Cyl.cell, neg_div]
        using (Lp.memLp f)
    have hcoeff : ∀ k : ℤ,
        UnforcedLeray.B0581.modeCoeff c k (f : UnforcedLeray.Cyl.Plane → ℂ) =ᵐ[volume] 0 := by
      intro k
      have hm := UnforcedLeray.B0581.modes_apply_ae c k f
      rw [hzero] at hm
      have hsqrt : (((Real.sqrt c : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (Fact.out : 0 < c))
      filter_upwards [hm] with η hη
      have hz : (((0 : UnforcedLeray.B0581.ModeSeq ℂ) k : Lp ℂ 2 volume) : ℝ → ℂ) η = 0 := by
        simp
      rw [hz] at hη
      exact (smul_eq_zero.mp hη.symm).resolve_left hsqrt
    have hae := b0581_ae_eq_zero_of_modeCoeff (Fact.out : 0 < c) hf hcoeff
    apply Lp.ext
    have hae' : (f : UnforcedLeray.B0579.Plane → ℂ) =ᵐ[UnforcedLeray.B0581.cellVol c] 0 := by
      simpa only [UnforcedLeray.B0581.cellVol, UnforcedLeray.B0579.cell,
        UnforcedLeray.Cyl.cellμ, UnforcedLeray.Cyl.cell, neg_div] using hae
    exact hae'.trans (Lp.coeFn_zero ℂ 2 (UnforcedLeray.B0581.cellVol c)).symm
  · rintro rfl
    exact map_zero _

#print axioms b0581_modes_eq_zero_iff

/-- The B0581 synthesis map reconstructs every complex scalar L² field on the cell. -/
theorem b0581_synth_modes {c : ℝ} [Fact (0 < c)]
    (f : Lp ℂ 2 (UnforcedLeray.B0581.cellVol c)) :
    UnforcedLeray.B0581.synth c (UnforcedLeray.B0581.modes c f) = f := by
  have hker : UnforcedLeray.B0581.modes c
      (UnforcedLeray.B0581.synth c (UnforcedLeray.B0581.modes c f) - f) = 0 := by
    rw [map_sub, UnforcedLeray.B0581.modes_synth, sub_self]
  exact sub_eq_zero.mp ((b0581_modes_eq_zero_iff _).mp hker)

#print axioms b0581_synth_modes

end UnforcedLeray.Cons.L2.SolAudit
