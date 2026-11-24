import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg

/-!
# `PartIII-b:C/rep/5/2/2/3` : both stream transitions vanish off the annulus

Source `the November 2 reference manuscript` 5312-5316 (both stream transitions
are supported on `0.8/ν < s < 1/ν`), 4164-4167 (`χ_y = 1` for `s ≤ 0.8/ν`, `= 0` for `s ≥ 1/ν`).
Pure calculus: off the axis, near a point where `ν·age < 4/5` the stream cutoff is identically one
(so the correction `𝒞_y - χ_y` and the commutator vanish), and near a point where `ν·age > 1` it is
identically zero.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tvo_deriv_of_lt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : t < 4 / 5) :
    deriv χ t = 0 := by
  have hev : χ =ᶠ[nhds t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with u hu using hχ.one u (le_of_lt hu)
  rw [hev.deriv_eq]
  simp

theorem tvo_zero_of_gt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : 1 < t) :
    χ t = 0 ∧ deriv χ t = 0 := by
  refine ⟨hχ.zero t ht.le, ?_⟩
  have hev : χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using hχ.zero u (le_of_lt hu)
  rw [hev.deriv_eq]
  simp

/-- `TransVanishOff` (source 5312-5316). -/
theorem transVanishOff : TransVanishOff := by
  intro ν μ R χy hχ hν hR T τ y hy hcase
  have hcont : ContinuousAt (fun y' => ν * age R y') y := by
    unfold age
    have hϱ : ContinuousAt ϱ y := continuous_ϱ.continuousAt
    have h2 : ContinuousAt (fun y' => ϱ y' ^ 2) y := hϱ.pow 2
    exact continuousAt_const.mul (continuousAt_const.div h2 (pow_ne_zero 2 hy.ne'))
  rcases hcase with hlt | hgt
  · -- the cutoff is identically one near `y`
    have hev : ∀ᶠ y' in nhds y, ν * age R y' < 4 / 5 :=
      hcont.eventually_lt continuousAt_const hlt
    have hc1 : deriv χy (ν * age R y) = 0 := tvo_deriv_of_lt hχ hlt
    have hz : ∀ t, sepWX ν μ R χy T t =ᶠ[nhds y] sepX0 ν μ T t := by
      intro t
      filter_upwards [hev] with y' hy'
      have h1 : χy (ν * age R y') = 1 := hχ.one _ hy'.le
      have h2 : deriv χy (ν * age R y') = 0 := tvo_deriv_of_lt hχ hy'
      unfold sepWX wardStreamCut
      rw [h1, h2]
      simp
    have hcorr : streamCorr ν R χy (sepWre ν μ T) τ y = 0 := by
      unfold streamCorr
      rw [hc1]
      simp
    have hcomm : physDmu ν (μ + 1) (sepWX ν μ R χy T) τ y =
        physDmu ν (μ + 1) (sepX0 ν μ T) τ y := physDmu_congr_nhds hz τ
    have hwc : wardStreamCut ν R χy (physDmu ν (μ + 1) (sepX0 ν μ T)) τ y =
        physDmu ν (μ + 1) (sepX0 ν μ T) τ y := by
      unfold wardStreamCut
      rw [hχ.one _ hlt.le, hc1]
      simp
    unfold sepTrans sepComm
    rw [hcorr, hcomm, hwc]
    simp
  · -- the cutoff is identically zero near `y`
    have hev : ∀ᶠ y' in nhds y, 1 < ν * age R y' :=
      continuousAt_const.eventually_lt hcont hgt
    have hc0 := tvo_zero_of_gt hχ hgt
    have hz : ∀ t, sepWX ν μ R χy T t =ᶠ[nhds y] (fun _ _ => (0 : Space)) t := by
      intro t
      filter_upwards [hev] with y' hy'
      obtain ⟨h1, h2⟩ := tvo_zero_of_gt hχ hy'
      unfold sepWX wardStreamCut
      rw [h1, h2]
      simp
    have hcomm : physDmu ν (μ + 1) (sepWX ν μ R χy T) τ y = 0 := by
      rw [physDmu_congr_nhds hz τ]
      simp [physDmu, physLap, physPd2, physPd]
    have hwc : wardStreamCut ν R χy (physDmu ν (μ + 1) (sepX0 ν μ T)) τ y = 0 := by
      unfold wardStreamCut
      rw [hc0.1, hc0.2]
      simp
    have hcorr : streamCorr ν R χy (sepWre ν μ T) τ y = 0 := by
      unfold streamCorr
      rw [hc0.2]
      simp
    unfold sepTrans sepComm
    rw [hcorr, hcomm, hwc]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
