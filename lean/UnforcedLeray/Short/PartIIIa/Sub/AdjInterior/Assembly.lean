import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1

/-!
# `PartIII-a:T21/2/7/2/1/1`: `AdjointInteriorSmooth` from its leaves

Source: `the November 2 reference manuscript` (SP) lines 3060-3061 (the
reverse-time adjoint, smooth coefficients, the energies `E_j`), 3062-3071 (the energy
inequalities), 3052-3058 (the nonlocal term of order `-1`), 270-288 and 2866-2870 (the train).

* `adjointInteriorSmoothJets_of` (the analytic core): with the weighted jets of the train, from the
  differentiated weak equation (`AdjTestedDerivOf`), the bootstrap step (`AdjHkStep`, by induction
  on `k` from `adjHkOn_zero_of_weak`), the time jets (`AdjTimeJetsOf`), and the Sobolev embedding
  with its bookkeeping (`TimeJetsSTSobolev`, `STSobolevSmoothRep`, `STRepSliceAe`);
* `adjointInteriorSmoothBUC_of`: for `BUC` trains, with `TrainSTJetsOfBUC`;
* `adjointInteriorSmooth_of`: the statement of `Sub/PartIII-a_T21_2_7_2_1.lean` (the trains of
  `PartI.IsBUCTrain` with the bounds `LadTrainBdd`, `PartIII-a:T21/2/7/2/1/1/1/org`) is the `BUC`
  one (the identity).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Interior smoothing with the weighted jets of the train, from its leaves.** -/
theorem adjointInteriorSmoothJets_of (m : ℝ) (h1 : AdjTestedDerivOf m) (h2 : AdjHkStep m)
    (h3 : AdjTimeJetsOf m) (h4 : TimeJetsSTSobolev) (h5 : STSobolevSmoothRep)
    (h6 : STRepSliceAe) : AdjointInteriorSmoothJets m := by
  intro ν hν hν1 tr hB hJ t s ht hts G _ φ hφ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hD : AdjTestedDeriv tr t s φ := h1 ν hν hν1 tr hB t s ht hts _ φ hφ
  have hk : ∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ioo t s) φ := by
    intro k
    induction k with
    | zero => exact adjHkOn_zero_of_weak hφ
    | succ k ih => exact h2 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD k ih
  obtain ⟨Φ, hΦ0, hΦ⟩ := h3 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD hk
  obtain ⟨F, hFsl, hFS⟩ := h4 _ m t s Φ hc hts hΦ
  obtain ⟨F', hF', hF'ae⟩ := h5 _ _ F hFS
  have hsl := h6 _ m t s (Φ 0) F F' hc hts (hΦ.1 0 0) hFsl hF'.continuousOn hF'ae
  refine ⟨fun r x => F' (r, x), fun r hr => ?_, hF'⟩
  have h := hsl r hr
  rwa [hΦ0] at h

/-- **Interior smoothing for `BUC` trains**: the jets of the train from `TrainSTJetsOfBUC`. -/
theorem adjointInteriorSmoothBUC_of (m : ℝ) (h0 : TrainSTJetsOfBUC m)
    (h1 : AdjointInteriorSmoothJets m) : AdjointInteriorSmoothBUC m := by
  intro ν hν hν1 tr hbuc hB t s ht hts G hG φ hφ
  exact h1 ν hν hν1 tr hB (h0 ν hν hν1 tr hbuc hB) t s ht hts G hG φ hφ

/-- **`AdjointInteriorSmooth` is the `BUC` statement** (both are for the trains of
`PartI.IsBUCTrain` with the bounds `LadTrainBdd`). -/
theorem adjointInteriorSmooth_of (m : ℝ) (h1 : AdjointInteriorSmoothBUC m) :
    AdjointInteriorSmooth m := by
  intro ν hν hν1 tr htr hB t s ht hts G hG φ hφ
  exact h1 ν hν hν1 tr htr hB t s ht hts G hG φ hφ

end UnforcedLeray.Short.IIIa
