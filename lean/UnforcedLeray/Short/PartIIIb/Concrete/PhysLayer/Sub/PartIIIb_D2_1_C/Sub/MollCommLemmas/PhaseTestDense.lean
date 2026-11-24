import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Dense
import UnforcedLeray.Short.PartIIb.Bridge.Rep

/-!
# `PhaseTestDense`: phase tests are dense in `Y_2` (source lines 1351-1362, 1556-1583)

Route: `Φ ∈ Y_2` has an element `F : Y_2` with slices `Φ(τ, ·)` (`exists_hasRepY_q`); phase tests are
dense in `Y_2` (`phaseTestsDenseY2`); the difference `Φ - Ψ` has slices of `F - testElem Ψ`, so its
`phaseLpNorm` is the `Y_2`-norm of `F - testElem Ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.PhaseTrace

/-- The phase `L²` norm of a field whose slices are those of `G ∈ Y_2` is `‖G‖ₑ`. -/
theorem phaseLpNorm_eq_enorm_of_slice {P : ℝ} [Fact (0 < P)] (G : Yq P 2)
    (W : ℝ × Space → CVec3)
    (hs : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (G (τ : AddCircle P) : Space → CVec3)) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 W = ‖G‖ₑ := by
  have hq : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hI : ∫⁻ t in Ioc (0:ℝ) P, ‖G (t : AddCircle P)‖ₑ ^ (2 : ℝ≥0∞).toReal
      = ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (t, y)‖ₑ ^ (2 : ℝ≥0∞).toReal := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hs] with t ht
    rw [← lintegral_enorm_rpow_Lp (G (t : AddCircle P)) hq]
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  have hmain : ‖G‖ₑ ^ (2 : ℝ≥0∞).toReal
      = ENNReal.ofReal P⁻¹ *
        ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (t, y)‖ₑ ^ (2 : ℝ≥0∞).toReal := by
    rw [B0411.enorm_rpow_Yq G hq, hI]
  rw [hp] at hmain
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  rw [← hmain, one_div]
  exact ENNReal.rpow_rpow_inv (by norm_num) _

/-- Slices of a phase test are those of its test element. -/
theorem phaseTest_slice_ae {P : ℝ} [Fact (0 < P)] {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) :
    ∀ᵐ τ : ℝ, (fun y => Ψ (τ, y)) =ᵐ[volume]
      ((testElem P 2 Ψ) (τ : AddCircle P) : Space → CVec3) := by
  have hs : IsSliceTest P 2 Ψ := hΨ.isSliceTest 2
  have h1 : ⇑(testElem P 2 Ψ) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hs) := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp _ _
  filter_upwards [ae_comp_mk h1] with t ht
  have ht' : testElem P 2 Ψ (t : AddCircle P) = sliceMap hs.2 t := ht.trans (circleSlice_coe hs t)
  rw [ht']
  exact (MemLp.coeFn_toLp _).symm

theorem phaseTestDense : PhaseTestDense := by
  intro P hP Φ hΦ η hη
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨F, hF, -⟩ := UnforcedLeray.Short.IIb.exists_hasRepY_q P 2 (by norm_num)
    (q := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) Φ hΦ
  obtain ⟨G, hG, hlim⟩ := UnforcedLeray.Short.PartIIa.phaseTestsDenseY2 P F
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.1 hlim η hη).and (Filter.eventually_ge_atTop 0)).exists
  have hn1 : dist (testElem P 2 (G n)) F < η := hn.1
  set Ψ := G n with hΨdef
  have hΨ : IsPhaseTest P Ψ := hG n
  set T := testElem P 2 Ψ
  -- slices of the difference
  have hsl : ∀ᵐ τ : ℝ, (fun y => Φ (τ, y) - Ψ (τ, y)) =ᵐ[volume]
      ((F - T) (τ : AddCircle P) : Space → CVec3) := by
    have h0 : ⇑(F - T) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑F - ⇑T := Lp.coeFn_sub F T
    filter_upwards [hF.slice, phaseTest_slice_ae hΨ, ae_comp_mk h0] with τ h1 h2 h3
    have h4 : (((F - T) (τ : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) :
        Space → CVec3) =ᵐ[volume]
        (fun y => (F (τ : AddCircle P) : Space → CVec3) y - (T (τ : AddCircle P) : Space → CVec3) y) := by
      rw [h3]
      exact Lp.coeFn_sub _ _
    refine (h1.sub h2).trans h4.symm
  have hnorm := phaseLpNorm_eq_enorm_of_slice (F - T) (fun x => Φ x - Ψ x) hsl
  refine ⟨Ψ, hΨ, ⟨?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [hΦ.periodic] with x hx
    simp only [hx]
    rw [(hΨ.isSliceTest 2).1 x.1 x.2]
  · exact hΦ.meas.sub hΨ.continuous.aestronglyMeasurable
  · rw [hnorm]; exact enorm_lt_top
  · rw [hnorm, ← ofReal_norm]
    refine ENNReal.ofReal_lt_ofReal_iff'.2 ⟨?_, hη⟩
    rw [← dist_eq_norm, dist_comm]
    exact hn1
end UnforcedLeray.Short.PartIIIb.Concrete
