import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CellIntegrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC

/-!
# Part I, `PartI:T04/10/1/2/1/14`: `ClassCommIntegrable`

Source of record: `the November 2 reference manuscript`, lines 285-288 (`jet_l2`).
The commutator density `commDensity (v r)` is integrable on the cell for `r ∈ [0,T]`.

Route: `commDensity` is continuous; pointwise, with `‖D^k v(r)‖ ≤ M_k` (`hcls.bounded`),
`commDensity ≤ M₂/2 (‖D²ω‖² + ‖Dω‖²) + 2M₁ ‖D²ω‖²`, where `ω = curl (v r)`; the majorant is
integrable by `cellVortJetIntegrable_proof`; `Integrable.mono'`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Target** `classCommIntegrable_proof`: the commutator density is integrable on the cell
(`ClassCommIntegrable`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem classCommIntegrable_proof : ClassCommIntegrable := by
  intro ν c T v p hν hc hcls r hr
  have hu : ContDiff ℝ ∞ (v r) := hcls.classical.contDiff_slice hr
  have hw : ContDiff ℝ ∞ (Cyl.curl (v r)) := APEllipticCaux.curl_contDiff hu
  obtain ⟨M1, hM1⟩ := hcls.bounded 1
  obtain ⟨M2, hM2⟩ := hcls.bounded 2
  have hI1 : IntegrableOn (fun z => ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2) (Cyl.cell c) :=
    cellVortJetIntegrable_proof ν c T v p hν hc hcls r hr 1
  have hI2 : IntegrableOn (fun z => ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2) (Cyl.cell c) :=
    cellVortJetIntegrable_proof ν c T v p hν hc hcls r hr 2
  -- continuity of the density
  have hcont : Continuous (fun z => commDensity (v r) z) := by
    have hD : ∀ k : ℕ, Continuous (fun z => iteratedFDeriv ℝ k (Cyl.curl (v r)) z) :=
      fun k => hw.continuous_iteratedFDeriv (m := k) (by simp)
    have hU : ∀ k : ℕ, Continuous (fun z => iteratedFDeriv ℝ k (v r) z) :=
      fun k => hu.continuous_iteratedFDeriv (m := k) (by simp)
    unfold commDensity
    exact (hD 2).norm.mul (((hU 2).norm.mul (hD 1).norm).add
      (((hU 1).norm.mul (hD 2).norm).const_mul 2))
  -- pointwise majorant
  have hbound : ∀ z, commDensity (v r) z ≤
      M2 / 2 * (‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2 +
        ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2) +
      2 * M1 * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2 := by
    intro z
    have hX : ‖iteratedFDeriv ℝ 2 (v r) z‖ ≤ M2 := hM2 r hr z
    have hY : ‖iteratedFDeriv ℝ 1 (v r) z‖ ≤ M1 := hM1 r hr z
    have hX0 : 0 ≤ ‖iteratedFDeriv ℝ 2 (v r) z‖ := norm_nonneg _
    have hM2' : 0 ≤ M2 := le_trans hX0 hX
    have ha0 : 0 ≤ ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ := norm_nonneg _
    have he0 : 0 ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ := norm_nonneg _
    unfold commDensity
    nlinarith [mul_le_mul_of_nonneg_right hX (mul_nonneg ha0 he0),
      mul_le_mul_of_nonneg_right hY (mul_nonneg ha0 ha0),
      mul_nonneg hM2' (sq_nonneg (‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ -
        ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖))]
  -- integrability of the majorant
  have hgint : IntegrableOn (fun z => M2 / 2 * (‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2 +
        ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2) +
      2 * M1 * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2) (Cyl.cell c) :=
    ((hI2.add hI1).const_mul (M2 / 2)).add (hI2.const_mul (2 * M1))
  refine Integrable.mono' hgint hcont.aestronglyMeasurable ?_
  refine ae_of_all _ (fun z => ?_)
  rw [Real.norm_of_nonneg (commDensity_nonneg _ z)]
  exact hbound z

end UnforcedLeray.Short.PartI
