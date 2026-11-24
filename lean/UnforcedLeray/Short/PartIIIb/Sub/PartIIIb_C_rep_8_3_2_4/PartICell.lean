import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_4

/-!
# `PartIII-b:C/rep/8/3/2/4/1`: `TrainPartICell` from Part I `sct:fixed-band`

Source `the November 2 reference manuscript` 468-478 and 5484-5492.
`PartI.TrainFixedBand` at `ρ = 2`, `Sg = 11/10`, `m = 0`, `L = 0`, `k = 2`, transported from the
period `trainPeriod 2 ν = (ν²)⁻¹` to `cOf ν = (ν²)⁻¹` and read as the three cell `L²` norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `cOf ν = trainPeriod 2 ν` (`ν > 0`). -/
theorem pI_cOf_eq_trainPeriod {ν : ℝ} (hν : 0 < ν) :
    cOf ν = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
  unfold cOf UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- At age-scale `ν`, the slow-age jet of order `0` is the ordinary jet at age `s`. -/
theorem pI_sigmaJet_zero_eq {ν : ℝ} (hν : 0 < ν) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (j : ℕ) :
    UnforcedLeray.Short.PartI.sigmaJet ν 0 j F s = UnforcedLeray.Train.jet j (F s) := by
  have hfun : (fun z => iteratedDeriv 0 (fun σ => F (σ / ν) z) (ν * s)) = F s := by
    funext z
    simp [iteratedDeriv_zero, mul_div_cancel_left₀ s hν.ne']
  unfold UnforcedLeray.Short.PartI.sigmaJet
  rw [hfun]

/-- The weighted cell norm of a jet of order `j` (weight `⟨η⟩^0 = 1`) is the cell `L²` norm of
its norm. -/
theorem pI_wCellL2_jet (c : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : UnforcedLeray.Cyl.Plane → E) :
    UnforcedLeray.Train.wCellL2 c 0 (UnforcedLeray.Train.jet j f) =
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2 (UnforcedLeray.Cyl.cellμ c) := by
  unfold UnforcedLeray.Train.wCellL2
  apply eLpNorm_congr_norm_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp [UnforcedLeray.Train.jap, UnforcedLeray.Train.jet]

/-- Order-zero slow-age jet, zeroth derivative. -/
theorem pI_L0 (c ν s : ℝ) (hν : 0 < ν) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → UnforcedLeray.Cyl.Plane → E) :
    UnforcedLeray.Train.wCellL2 c 0 (UnforcedLeray.Short.PartI.sigmaJet ν 0 0 F s) =
      eLpNorm (fun z => ‖F s z‖) 2 (UnforcedLeray.Cyl.cellμ c) := by
  rw [pI_sigmaJet_zero_eq hν F s 0, pI_wCellL2_jet]
  simp only [norm_iteratedFDeriv_zero]

/-- Order-two slow-age jet. -/
theorem pI_L2 (c ν s : ℝ) (hν : 0 < ν) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → UnforcedLeray.Cyl.Plane → E) :
    UnforcedLeray.Train.wCellL2 c 0 (UnforcedLeray.Short.PartI.sigmaJet ν 0 2 F s) =
      eLpNorm (fun z => ‖iteratedFDeriv ℝ 2 (F s) z‖) 2 (UnforcedLeray.Cyl.cellμ c) := by
  rw [pI_sigmaJet_zero_eq hν F s 2, pI_wCellL2_jet]

theorem pI_six_le (a b c d e f : ℝ≥0∞) : a + e ≤ a + b + c + d + e + f := by
  have h : a + b + c + d + e + f = (a + e) + (b + c + d + f) := by ring
  rw [h]
  exact le_self_add

theorem pI_one_le (a b c d e f : ℝ≥0∞) : a ≤ a + b + c + d + e + f := by
  have h : a + b + c + d + e + f = a + (b + c + d + e + f) := by ring
  rw [h]
  exact le_self_add

theorem pI_absorb (A B C G0 G1 G2 : ℝ≥0∞) (h1 : A + C ≤ G0) (h2 : B ≤ G2) :
    A + B + C ≤ G0 + G1 + G2 := by
  calc A + B + C = (A + C) + B := by ring
    _ ≤ G0 + G2 := add_le_add h1 h2
    _ ≤ G0 + G1 + G2 := by
      have h : G0 + G1 + G2 = (G0 + G2) + G1 := by ring
      rw [h]
      exact le_self_add

/-- **Leaf 1** (`TrainPartICell` from `TrainFixedBand`). -/
theorem trainPartICell_of (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : TrainPartICell := by
  obtain ⟨C, N, CS, bS, ν0, hC, hb, hν0, H⟩ := hF 2 (by norm_num) (11 / 10) (by norm_num) 0 0 2
  refine ⟨C, N, CS, bS, ν0, hC, hb, hν0, ?_⟩
  intro L hL hνL s hs hsS
  have hνpos : 0 < L.ν := L.ν_pos
  have key : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol L.ν c),
      c = UnforcedLeray.Short.PartI.trainPeriod 2 L.ν →
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      eLpNorm (fun x => ‖tr.v s x - UnforcedLeray.Train.Vc L.ν c s x‖) 2
          (UnforcedLeray.Cyl.cellμ c) +
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2
            (fun z => tr.v s z - UnforcedLeray.Train.Vc L.ν c s z) x‖) 2
          (UnforcedLeray.Cyl.cellμ c) +
        eLpNorm (fun x => ‖UnforcedLeray.Train.gradS
            (fun w => tr.p s w - UnforcedLeray.Train.pc L.ν c s w) x‖) 2
          (UnforcedLeray.Cyl.cellμ c) ≤
        ENNReal.ofReal (C * (1 + c + L.ν⁻¹) ^ N * Real.exp (CS / L.ν - bS * c ^ 2)) := by
    intro c tr hc' hb'
    subst hc'
    have hH := H L.ν hνpos hνL tr hb' s hs hsS
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hH
    unfold UnforcedLeray.Short.PartI.polyP at hH
    rw [← pI_L0 _ L.ν s hνpos (fun r z => tr.v r z - UnforcedLeray.Train.Vc L.ν
        (UnforcedLeray.Short.PartI.trainPeriod 2 L.ν) r z)]
    rw [← pI_L2 _ L.ν s hνpos (fun r z => tr.v r z - UnforcedLeray.Train.Vc L.ν
        (UnforcedLeray.Short.PartI.trainPeriod 2 L.ν) r z)]
    rw [← pI_L0 _ L.ν s hνpos (fun r w => UnforcedLeray.Train.gradS
        (fun y => tr.p r y - UnforcedLeray.Train.pc L.ν
          (UnforcedLeray.Short.PartI.trainPeriod 2 L.ν) r y) w)]
    exact le_trans (pI_absorb _ _ _ _ _ _ (pI_six_le _ _ _ _ _ _) (pI_one_le _ _ _ _ _ _)) hH
  exact key (cOf L.ν) L.train (pI_cOf_eq_trainPeriod hνpos) hL

end UnforcedLeray.Short.PartIIIb.Concrete

end
