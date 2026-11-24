import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection

/-!
# `truncSplit`: additivity of the pairing in the second slot

Proves `TruncSplit` (defined in `Sub/PartIII-b_IIIb-D2_1_3_1_2_1_13.lean`):
`⟪Ψ, χₙ g + ∇χₙ × w + (E_Hardy - ∇χₙ × w + E_Bdd)⟫ = ⟪Ψ, χₙ g + ∇χₙ × w⟫ + ⟪Ψ, E_Hardy - ∇χₙ × w + E_Bdd⟫`.

Route: `pairF_add_right_of_integrable`, with integrability of each summand against the phase
test `Ψ` (bounded `y`-support), from local integrability of `g, w, ψ, Φ, ∂Φ, ∂ψ` (the Hardy
fields `|y|⁻¹ w, |y|⁻¹ ψ ∈ Y_2` and `Y_2` membership) and continuity of the coefficients.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

set_option maxHeartbeats 1000000 in
/-- Local integrability of a continuous-coefficient cross product `a(x) × f(x)`. -/
theorem tsg_loc_cr {a : ℝ × Space → CVec3} (ha : Continuous a) {f : ℝ × Space → CVec3}
    (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => crossC (a x) (f x)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ha.continuousOn
  have hfK : IntegrableOn (fun x => ‖f x‖) K volume := (hf.integrableOn_isCompact hK).norm
  have hKm : MeasurableSet K := hK.measurableSet
  refine Integrable.mono' (hfK.const_mul (6 * max M 0)) ?_ ?_
  · have hpair : AEStronglyMeasurable (fun x : ℝ × Space => (a x, f x)) (volume.restrict K) :=
      ha.aestronglyMeasurable.prodMk (hf.integrableOn_isCompact hK).aestronglyMeasurable
    exact continuous_crossC.comp_aestronglyMeasurable hpair
  · filter_upwards [ae_restrict_mem hKm] with x hx
    calc ‖crossC (a x) (f x)‖ ≤ 6 * ‖a x‖ * ‖f x‖ := crossC_norm_le _ _
      _ ≤ 6 * max M 0 * ‖f x‖ := by
          gcongr
          exact (hM x hx).trans (le_max_left _ _)

theorem truncSplit : TruncSplit := by
  intro _hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨ
  haveI : Fact (0 < P) := ⟨hP⟩
  obtain ⟨RΨ, hRΨ⟩ := hΨ.bounded_support
  have hΨc : Continuous Ψ := hΨ.smooth.continuous
  have hχ : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  -- continuity of the coefficients
  have hg0 : Continuous (fun x : ℝ × Space => gradC (cutχ n) x.2) :=
    (continuous_gradC' fun j => (contDiff_sd hχ j).continuous).comp continuous_snd
  have hg1 : Continuous (fun x : ℝ × Space => gradC (radS (cutχ n)) x.2) :=
    (continuous_gradC' fun j => (contDiff_sd (contDiff_radS' hχ) j).continuous).comp continuous_snd
  have hg2 : Continuous (fun x : ℝ × Space => gradC (lapS (cutχ n)) x.2) :=
    (continuous_gradC' fun j => (contDiff_sd (contDiff_lapS' hχ) j).continuous).comp continuous_snd
  have hgk : ∀ k : Fin 3, Continuous (fun x : ℝ × Space => gradC (sd k (cutχ n)) x.2) :=
    fun k => (continuous_gradC' fun j => (contDiff_sd (contDiff_sd hχ k) j).continuous).comp
      continuous_snd
  have hR0 : Continuous (fun x : ℝ × Space => radS (cutχ n) x.2) :=
    ((contDiff_radS' hχ).continuous).comp continuous_snd
  have hL0 : Continuous (fun x : ℝ × Space => lapS (cutχ n) x.2) :=
    ((contDiff_lapS' hχ).continuous).comp continuous_snd
  have hsk : ∀ k : Fin 3, Continuous (fun x : ℝ × Space => sd k (cutχ n) x.2) :=
    fun k => ((contDiff_sd hχ k).continuous).comp continuous_snd
  have hcoef : Continuous (fun x : ℝ × Space =>
      (1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) :=
    (continuous_const.mul hR0).sub (continuous_const.mul hL0)
  -- local integrability of the data
  have hψloc : LocallyIntegrable D.ψ volume := tsg_locInt_of_hardy hP hD.spΦ.hardy
  have hwloc : LocallyIntegrable D.w volume := tsg_locInt_of_hardy hP hD.spg.hardy
  have hΦloc : LocallyIntegrable D.Φ volume := locInt_of_isInYr hP hD.dom.mem
  have hgloc : LocallyIntegrable D.g volume := locInt_of_isInYr hP hD.dom.mem_g
  have hDΦloc : ∀ k : Fin 3, LocallyIntegrable (D.DΦ k) volume :=
    fun k => locInt_of_isInYr hP (hD.dΦ k).1
  have hDψloc : ∀ k : Fin 3, LocallyIntegrable (D.Dψ k) volume :=
    fun k => locInt_of_isInYr hP (hD.spΦ.grad k).1
  -- the pieces of `EHardy - ∇χₙ × w + EBdd`
  have hcr0 : LocallyIntegrable (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x))
      volume := tsg_loc_cr hg0 hwloc
  have hcr1 : LocallyIntegrable (fun x : ℝ × Space =>
      crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)) volume := tsg_loc_cr hg1 hψloc
  have hcr2 : LocallyIntegrable (fun x : ℝ × Space =>
      crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)) volume := tsg_loc_cr hg2 hψloc
  have hh1 : LocallyIntegrable (fun x : ℝ × Space =>
      (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)) volume :=
    LocallyIntegrable.continuous_smul continuous_const hcr1
  have hnu2 : LocallyIntegrable (fun x : ℝ × Space =>
      ν • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)) volume :=
    LocallyIntegrable.continuous_smul continuous_const hcr2
  have hsPhi : LocallyIntegrable (fun x : ℝ × Space =>
      ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.Φ x) volume :=
    LocallyIntegrable.continuous_smul hcoef hΦloc
  have hS1sum : LocallyIntegrable (fun x : ℝ × Space =>
      ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) volume := by
    simp only [Fin.sum_univ_three]
    exact LocallyIntegrable.add
      (LocallyIntegrable.add (LocallyIntegrable.continuous_smul (hsk 0) (hDΦloc 0))
        (LocallyIntegrable.continuous_smul (hsk 1) (hDΦloc 1)))
      (LocallyIntegrable.continuous_smul (hsk 2) (hDΦloc 2))
  have hS1 : LocallyIntegrable (fun x : ℝ × Space =>
      (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) volume :=
    LocallyIntegrable.continuous_smul continuous_const hS1sum
  have hS2sum : LocallyIntegrable (fun x : ℝ × Space =>
      ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) volume := by
    simp only [Fin.sum_univ_three]
    exact LocallyIntegrable.add
      (LocallyIntegrable.add (tsg_loc_cr (hgk 0) (hDψloc 0)) (tsg_loc_cr (hgk 1) (hDψloc 1)))
      (tsg_loc_cr (hgk 2) (hDψloc 2))
  have hS2 : LocallyIntegrable (fun x : ℝ × Space =>
      (2 * ν) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) volume :=
    LocallyIntegrable.continuous_smul continuous_const hS2sum
  -- the remainder `EHardy - ∇χₙ × w + EBdd` is locally integrable
  have hBloc : LocallyIntegrable (fun x : ℝ × Space =>
      (EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x) volume := by
    unfold EHardy EBdd
    exact LocallyIntegrable.add
      (LocallyIntegrable.sub (LocallyIntegrable.sub (LocallyIntegrable.add hcr0 hh1) hnu2) hcr0)
      (LocallyIntegrable.sub (LocallyIntegrable.sub hsPhi hS1) hS2)
  -- the first summand `χₙ g + ∇χₙ × w`
  have hAloc : LocallyIntegrable (fun x : ℝ × Space =>
      cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)) volume :=
    LocallyIntegrable.add
      (LocallyIntegrable.continuous_smul ((contDiff_cutχ n).continuous.comp continuous_snd)
        hgloc)
      hcr0
  -- integrability against the phase test `Ψ`
  have hIA := tsg_integrable_dotL (P := P) (H := Ψ) hΨc hRΨ hAloc
  have hIB := tsg_integrable_dotL (P := P) (H := Ψ) hΨc hRΨ hBloc
  have hIAB := tsg_integrable_dotL (P := P) (H := Ψ) hΨc hRΨ (LocallyIntegrable.add hAloc hBloc)
  exact UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable hIA hIB hIAB

end UnforcedLeray.Short.PartIIIb.Concrete
