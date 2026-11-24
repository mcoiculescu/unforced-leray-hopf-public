import UnforcedLeray.Lib.TrainB.InitialDatumDerivativeSolenoidal
import UnforcedLeray.Lib.Kernels.IterApply

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.Cyl (Plane)

private def datumListDirections (vs : List Plane) : Fin vs.length → Plane := fun i => vs.get i

private theorem datum_iterD_eq_jet_apply (c : ℝ) (hc : c ≠ 0) (vs : List Plane) :
    Sob.iterD vs (Train.datum c) = fun z =>
      iteratedFDeriv ℝ vs.length (Train.datum c) z (datumListDirections vs) := by
  induction vs with
  | nil =>
      funext z
      simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
      funext z
      change fderiv ℝ (Sob.iterD vs (Train.datum c)) z v =
        iteratedFDeriv ℝ (vs.length + 1) (Train.datum c) z (datumListDirections (v :: vs))
      have hm : datumListDirections (v :: vs) = Fin.cons v (datumListDirections vs) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hm, iteratedFDeriv_succ_apply_left]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ vs.length (Train.datum c)) :=
        (Train.datum_contDiff hc).iteratedFDeriv_right
          (m := ∞) (i := vs.length) UnforcedLeray.Kernels.infty_add_nat_le
      have hdiff : DifferentiableAt ℝ
          (iteratedFDeriv ℝ vs.length (Train.datum c)) z :=
        (contDiff_iff_contDiffAt.mp hD z).differentiableAt (by simp)
      exact fderiv_continuousMultilinear_apply_const_apply hdiff
        (datumListDirections vs) v

private theorem datum_jet_norm_bound (c : ℝ) (hc : 2 ≤ c) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ n (Train.datum c) z‖ ≤ C := by
  obtain ⟨C, hC, hbounds⟩ := Train.datum_bounds n 0
  refine ⟨C, hC, fun z => ?_⟩
  have h := (hbounds c hc).1 z
  simpa [Train.jet, Train.jap] using h

/-- Every fixed ordered directional derivative of the actual periodized Gaussian datum is
globally bounded. Its bound is obtained from the Fréchet-jet estimate, with the product of the
listed direction norms made explicit. -/
theorem datum_iterD_global_bound {c : ℝ} (hc : 2 ≤ c) (vs : List Plane) :
    ∃ M : ℝ, ∀ z, ‖Sob.iterD vs (Train.datum c) z‖ ≤ M := by
  obtain ⟨C, hC, hjet⟩ := datum_jet_norm_bound c hc vs.length
  refine ⟨C * ∏ i : Fin vs.length, ‖datumListDirections vs i‖, fun z => ?_⟩
  rw [datum_iterD_eq_jet_apply c (by linarith) vs]
  calc
    ‖iteratedFDeriv ℝ vs.length (Train.datum c) z (datumListDirections vs)‖
        ≤ ‖iteratedFDeriv ℝ vs.length (Train.datum c) z‖ *
            ∏ i : Fin vs.length, ‖datumListDirections vs i‖ :=
          (iteratedFDeriv ℝ vs.length (Train.datum c) z).le_opNorm _
    _ ≤ C * ∏ i : Fin vs.length, ‖datumListDirections vs i‖ :=
          mul_le_mul_of_nonneg_right (hjet z) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- The Fréchet derivative of any ordered derivative field of the datum is globally bounded.
This is the operator-norm estimate required to differentiate its actual Gaussian convolution. -/
theorem datum_fderiv_iterD_global_bound {c : ℝ} (hc : 2 ≤ c) (vs : List Plane) :
    ∃ M : ℝ, ∀ z, ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z‖ ≤ M := by
  obtain ⟨Mq, hq⟩ := datum_iterD_global_bound hc ((1, 0) :: vs)
  obtain ⟨Me, he⟩ := datum_iterD_global_bound hc ((0, 1) :: vs)
  have hMq : 0 ≤ Mq := (norm_nonneg _).trans (hq 0)
  have hMe : 0 ≤ Me := (norm_nonneg _).trans (he 0)
  refine ⟨Mq + Me, fun z => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hMq hMe)
  intro w
  have hw : w = w.1 • ((1, 0) : Plane) + w.2 • ((0, 1) : Plane) := by
    ext <;> simp
  have hqz : ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z (1, 0)‖ ≤ Mq := by
    change ‖Sob.iterD ((1, 0) :: vs) (Train.datum c) z‖ ≤ Mq
    exact hq z
  have hez : ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z (0, 1)‖ ≤ Me := by
    change ‖Sob.iterD ((0, 1) :: vs) (Train.datum c) z‖ ≤ Me
    exact he z
  calc
    ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z w‖ =
        ‖w.1 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (1, 0) +
          w.2 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (0, 1)‖ := by
          apply congrArg norm
          calc
            (fderiv ℝ (Sob.iterD vs (Train.datum c)) z) w =
                (fderiv ℝ (Sob.iterD vs (Train.datum c)) z)
                  (w.1 • ((1, 0) : Plane) + w.2 • ((0, 1) : Plane)) :=
                    congrArg (fderiv ℝ (Sob.iterD vs (Train.datum c)) z) hw
            _ = w.1 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (1, 0) +
                w.2 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (0, 1) := by
                  rw [map_add, map_smul, map_smul]
    _ ≤ ‖w.1 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (1, 0)‖ +
        ‖w.2 • fderiv ℝ (Sob.iterD vs (Train.datum c)) z (0, 1)‖ := norm_add_le _ _
    _ = ‖w.1‖ * ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z (1, 0)‖ +
        ‖w.2‖ * ‖fderiv ℝ (Sob.iterD vs (Train.datum c)) z (0, 1)‖ := by
          rw [norm_smul, norm_smul]
    _ ≤ ‖w‖ * Mq + ‖w‖ * Me := by
          exact add_le_add
            ((mul_le_mul_of_nonneg_right (norm_fst_le w) (norm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hqz (norm_nonneg _)))
            ((mul_le_mul_of_nonneg_right (norm_snd_le w) (norm_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hez (norm_nonneg _)))
    _ = (Mq + Me) * ‖w‖ := by ring

#print axioms UnforcedLeray.TrainB.datum_iterD_global_bound
#print axioms UnforcedLeray.TrainB.datum_fderiv_iterD_global_bound

end UnforcedLeray.TrainB
