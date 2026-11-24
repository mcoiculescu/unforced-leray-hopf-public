import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Loc

/-!
# Fundamental lemma for the slice pairing (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- For one cylinder test `ψ`, the slice pairing vanishes for a.e. `s > 0`. -/
theorem hj3_core {c : ℝ} (hc : 0 < c)
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (hb : b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ x in stripSet c,
        ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
            ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
            ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)) = 0 := by
  set F : ℝ → ℂ := fun s => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      ∫ x in stripSet c,
        ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
            ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
            ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)) with hFdef
  have hloc : LocallyIntegrableOn F (Ioi 0) volume := hj3_loc_int hc b hψ
  have hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioi 0 → ∫ x, χ x • F x = 0 := by
    intro χ hχs hχc hχp
    have hid := hj3_test_identity c hc b hb hχs hχc hχp hψ
    have hout : ∀ x ∉ Ioi (0 : ℝ), χ x • F x = 0 := by
      intro x hx
      have : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp h))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, ← hid]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hFdef, Complex.real_smul]
    ring
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioi hloc hzero
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hae] with s hs hspos
  have h := hs hspos
  have hw : ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < s ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hspos _
    exact_mod_cast this.ne'
  exact (mul_eq_zero.1 h).resolve_left hw

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
