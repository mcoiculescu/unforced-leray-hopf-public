import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Units.B0238.Moments

/-!
# Part I, task `PartI:T08/2/2/1` (`trainDatumWordL2_proof`): the datum is in `L²` for every word

Source of record: `the November 2 reference manuscript`, lines 262-268 (the datum
belongs to `BUC ∩ H^k` for every `k`). The Prop is `TrainDatumWordL2` in `Sub/PartI_T08_2_2.lean`.

Route: `B0238.integrableOn_weight_jet_trainDatum` with weight exponent `0` and `p = 2` gives
`∫_cell ‖D^{|w|} trainDatum‖² < ∞`. The pointwise bound `|∂_w f_k| ≤ ‖D^{|w|} f‖`
(`cylJetWord_proof`, `‖EuclideanSpace.proj k‖ ≤ 1`, as in `vjl_wordBoundedOn`) and
`memLp_two_iff_integrable_sq` finish the proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`TrainDatumWordL2`** (proved). -/
theorem trainDatumWordL2_proof : UnforcedLeray.Short.PartI.TrainDatumWordL2 := by
  intro c hc w k
  have hc0 : c ≠ 0 := hc.ne'
  -- the weighted jet integral of the datum, with weight exponent `0`
  have hint := B0238.integrableOn_weight_jet_trainDatum hc w.length 0 (p := 2) (by norm_num)
  have h2 : IntegrableOn (fun z : Plane => ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ ^ 2)
      (Cyl.cell c) := by
    simpa only [Real.rpow_zero, one_mul] using hint
  -- smoothness of the coordinate and of its word derivatives
  have hv : ContDiff ℝ ∞ (B0140.trainDatum c) := B0238.contDiff_trainDatum hc0
  have hg : ContDiff ℝ ∞ (fun x => B0140.trainDatum c x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hcont : Continuous (wordComp w (B0140.trainDatum c) k) :=
    (B0151.contDiff_derivWord hg w).continuous
  -- pointwise bound `|∂_w f_k| ≤ ‖D^{|w|} f‖`
  have hproj : ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x k)
  have hj : ((w.length : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hpt : ∀ z : Plane,
      |wordComp w (B0140.trainDatum c) k z| ≤ ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ := by
    intro z
    have hw := (cylJetWord_proof (fun x => B0140.trainDatum c x k) hg w.length z).1 w rfl
    have hcomp : ‖iteratedFDeriv ℝ w.length (fun x => B0140.trainDatum c x k) z‖ ≤
        ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ := by
      have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
        (f := B0140.trainDatum c) (x := z) (n := w.length) hv.contDiffAt hj
      calc ‖iteratedFDeriv ℝ w.length (fun x => B0140.trainDatum c x k) z‖
          = ‖iteratedFDeriv ℝ w.length
              ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ B0140.trainDatum c) z‖ :=
            rfl
        _ ≤ ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
              ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ := h
        _ ≤ 1 * ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ :=
              mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ w.length (B0140.trainDatum c) z‖ := one_mul _
    show |B0151.derivWord w (fun x => B0140.trainDatum c x k) z| ≤ _
    calc |B0151.derivWord w (fun x => B0140.trainDatum c x k) z|
        ≤ ‖Train.jet w.length (fun x => B0140.trainDatum c x k) z‖ := hw
      _ = ‖iteratedFDeriv ℝ w.length (fun x => B0140.trainDatum c x k) z‖ := rfl
      _ ≤ _ := hcomp
  -- conclude `MemLp` from `L²` of the square
  show MemLp (wordComp w (B0140.trainDatum c) k) 2 (Cyl.cellμ c)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine Integrable.mono' h2 (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hpt z) 2
  rw [sq_abs] at h1
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact h1

end UnforcedLeray.Short.PartI
