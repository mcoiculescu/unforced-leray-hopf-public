import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- The gradient `cgrad 0 Φ` is `(dQ Φ, dEta Φ)` in coordinates. -/
theorem t0g_cgrad_zero_apply (Φ : Profile → ℝ) (p : Profile) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p =
      !₂[((Axi.dQ Φ p : ℝ) : ℂ), ((Axi.dEta Φ p : ℝ) : ℂ)] := by
  simp [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps]

theorem t0g_cgrad_zero_of_notMem {Φ : Profile → ℝ} {p : Profile} (hp : p ∉ tsupport Φ) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p = 0 := by
  have h := fderiv_of_notMem_tsupport ℝ hp
  rw [t0g_cgrad_zero_apply]
  simp [Axi.dQ, Axi.dEta, h]

theorem t0g_cgrad_zero_continuous {c : ℝ} {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) :
    Continuous (UnforcedLeray.Short.PartIIa.cgrad 0 Φ) := by
  have hfd : Continuous (fderiv ℝ Φ) := hΦ.smooth.continuous_fderiv (by simp)
  have hA : Continuous fun p : Profile => (Axi.dQ Φ p : ℝ) := by
    unfold Axi.dQ
    exact hfd.clm_apply continuous_const
  have hB : Continuous fun p : Profile => (Axi.dEta Φ p : ℝ) := by
    unfold Axi.dEta
    exact hfd.clm_apply continuous_const
  have hfun : UnforcedLeray.Short.PartIIa.cgrad 0 Φ =
      fun p : Profile => !₂[((Axi.dQ Φ p : ℝ) : ℂ), ((Axi.dEta Φ p : ℝ) : ℂ)] :=
    funext (t0g_cgrad_zero_apply Φ)
  rw [hfun]
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_ofReal.comp hA
  · exact Complex.continuous_ofReal.comp hB

theorem t0g_shift_eq (p : Profile) (c : ℝ) :
    p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := by
  ext <;> simp

theorem t0g_cgrad_zero_periodic {c : ℝ} {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) :
    QPeriodic c (UnforcedLeray.Short.PartIIa.cgrad 0 Φ) := by
  intro p
  have hfun : (fun x : Profile => Φ (x + ((0 : ℝ), c, (0 : ℝ)))) = Φ :=
    funext fun x => by rw [t0g_shift_eq]; exact hΦ.periodic x
  have hd : fderiv ℝ Φ (p + ((0 : ℝ), c, (0 : ℝ))) = fderiv ℝ Φ p := by
    rw [← fderiv_comp_add_right, hfun]
  rw [t0g_cgrad_zero_apply, t0g_cgrad_zero_apply]
  have hq : Axi.dQ Φ (p.1, p.2.1 + c, p.2.2) = Axi.dQ Φ p := by
    rw [← t0g_shift_eq]
    unfold Axi.dQ
    rw [hd]
  have he : Axi.dEta Φ (p.1, p.2.1 + c, p.2.2) = Axi.dEta Φ p := by
    rw [← t0g_shift_eq]
    unfold Axi.dEta
    rw [hd]
  rw [hq, he]

theorem t0gCgradBand_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gCgradBand := by
  unfold T0gCgradBand
  intro c Φ hΦ
  refine ⟨t0g_cgrad_zero_continuous hΦ, t0g_cgrad_zero_periodic hΦ, ?_⟩
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
  have hmem : p ∈ tsupport Φ := by
    by_contra h
    exact hp (t0g_cgrad_zero_of_notMem h)
  exact UnforcedLeray.B0226.tsupport_subset_band hb hmem

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
