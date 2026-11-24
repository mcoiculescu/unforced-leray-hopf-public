import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_9
import UnforcedLeray.Lib.BochnerTime.Periodic

/-!
# `PhaseNormShiftInv`: translation invariance of the phase norm `‖·‖_{Y_2}`

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The shift in `y` is Lebesgue invariance; the shift in `τ` uses that the slice function
`G(t) = ∫ ‖F(t,y)‖²` is only a.e. `P`-periodic (Fubini slice of the a.e. periodicity), so the
cell integral is translation invariant by replacing `G` with the exactly periodic
`G ∘ toIocMod`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- For `G` a.e. `P`-periodic, `G (t - k P) = G t` a.e., for every integer `k`. -/
theorem ae_periodic_zsmul {P : ℝ} {G : ℝ → ℝ≥0∞} (hper : ∀ᵐ t : ℝ, G (t + P) = G t) (k : ℤ) :
    ∀ᵐ t : ℝ, G (t - k • P) = G t := by
  have hper' : ∀ᵐ t : ℝ, G t = G (t - P) := by
    have := (measurePreserving_sub_right (volume : Measure ℝ) P).quasiMeasurePreserving.ae hper
    filter_upwards [this] with t ht
    simpa using ht
  induction k using Int.induction_on with
  | zero => exact Filter.Eventually.of_forall fun t => by simp
  | succ k ih =>
    have h1 := (measurePreserving_sub_right (volume : Measure ℝ) P).quasiMeasurePreserving.ae ih
    filter_upwards [h1, hper'] with t ht1 ht2
    have e : t - (((k : ℤ) + 1) • P) = (t - P) - (k : ℤ) • P := by
      simp only [zsmul_eq_mul]; push_cast; ring
    rw [e, ht1, ← ht2]
  | pred k ih =>
    have h1 := (measurePreserving_add_right (volume : Measure ℝ) P).quasiMeasurePreserving.ae ih
    filter_upwards [h1, hper] with t ht1 ht2
    have e : t - ((-(k : ℤ) - 1) • P) = (t + P) - (-(k:ℤ)) • P := by
      simp only [zsmul_eq_mul]; push_cast; ring
    rw [e, ht1, ht2]

/-- Cell translation for an a.e. periodic function (no measurability needed). -/
theorem lintegral_Ioc_comp_add_of_ae_periodic {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞}
    (hper : ∀ᵐ t : ℝ, G (t + P) = G t) (s : ℝ) :
    ∫⁻ t in Ioc 0 P, G (t + s) = ∫⁻ t in Ioc 0 P, G t := by
  set G' : ℝ → ℝ≥0∞ := fun t => G (toIocMod hP 0 t) with hG'
  have hper' : Function.Periodic G' P := fun t => by
    simp [hG', toIocMod_add_right]
  have hae : ∀ᵐ t : ℝ, G t = G' t := by
    have hall : ∀ᵐ t : ℝ, ∀ k : ℤ, G (t - k • P) = G t := ae_all_iff.2 (ae_periodic_zsmul hper)
    filter_upwards [hall] with t ht
    simp only [hG']
    rw [← self_sub_toIocDiv_zsmul hP 0 t]
    exact (ht _).symm
  have hae2 : ∀ᵐ t : ℝ, G (t + s) = G' (t + s) :=
    (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae hae
  rw [lintegral_congr_ae (ae_restrict_of_ae hae2),
    UnforcedLeray.BochnerTime.lintegral_Ioc_comp_add_right hP hper' s]
  exact lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun _ h => h.symm))

/-- (M1) Translation invariance of the phase norm for `F ∈ Y_2`. -/
theorem phaseNormShiftInv : PhaseNormShiftInv := by
  intro P hP F hF z
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  congr 2
  set G : ℝ → ℝ≥0∞ := fun t => ∫⁻ y, ‖F (t, y)‖ₑ ^ (2 : ℝ) with hG
  have hGper : ∀ᵐ t : ℝ, G (t + P) = G t := by
    have h := hF.periodic
    rw [Measure.volume_eq_prod] at h
    have h2 := Measure.ae_ae_of_ae_prod h
    filter_upwards [h2] with t ht
    simp only [hG]
    exact lintegral_congr_ae (by filter_upwards [ht] with y hy; simp [hy])
  have hy : ∀ t : ℝ, ∫⁻ y, ‖F ((t, y) - z)‖ₑ ^ (2 : ℝ) = G (t + (-z.1)) := by
    intro t
    simp only [hG]
    have : ∀ y, F ((t, y) - z) = F (t + -z.1, y - z.2) := fun y => by
      show F (t - z.1, y - z.2) = F (t + -z.1, y - z.2)
      rw [sub_eq_add_neg t]
    simp_rw [this]
    exact lintegral_sub_right_eq_self (μ := volume)
      (fun y => ‖F (t + -z.1, y)‖ₑ ^ (2 : ℝ)) z.2
  simp_rw [hy]
  exact lintegral_Ioc_comp_add_of_ae_periodic hP hGper (-z.1)

end UnforcedLeray.Short.PartIIIb.Concrete
