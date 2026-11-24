import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainErrLaplacianL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainStressDivL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureLap

/-!
# Part I, task `PartI:T08/4/2` (`TrainJetPairSplit`): the error equation inside the pairing

Source `the November 2 reference manuscript` lines 326-329 and 341-348. The error
equation (`train_error_equation`) gives pointwise
`∂_s e = ν Δe - (v·∇v - V_c·∇V_c) - ∇π - div Q_c`; the pairing `⟨D^j e, D^j ·⟩` is linear in its
second slot on fields with `L²` word derivatives, so it splits term by term.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- Pointwise: word derivatives of a difference of smooth fields. -/
theorem pairSplit_wordComp_sub {g h : Plane → Vec} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (fun y => g y - h y) k z = wordComp w g k z - wordComp w h k z := by
  have hgk : ContDiff ℝ ∞ (fun x => g x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hg
  have hhk : ContDiff ℝ ∞ (fun x => h x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hh
  exact derivWord_sub_smooth hgk hhk w z

/-- Pointwise: word derivatives commute with a real scalar. -/
theorem pairSplit_wordComp_smul (r : ℝ) (g : Plane → Vec) (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (fun y => r • g y) k z = r * wordComp w g k z := by
  have := congrFun (TrainErrLapL2.derivWord_const_mul r w (fun x => g x k)) z
  exact this

/-- Smoothness and `L²` word derivatives are preserved by differences. -/
theorem pairSplit_smoothJetL2_sub {c : ℝ} {g h : Plane → Vec} (hg : SmoothJetL2 c g)
    (hh : SmoothJetL2 c h) : SmoothJetL2 c (fun y => g y - h y) := by
  refine ⟨hg.1.sub hh.1, fun w k => ?_⟩
  have e : wordComp w (fun y => g y - h y) k =
      fun z => wordComp w g k z - wordComp w h k z :=
    funext fun z => pairSplit_wordComp_sub hg.1 hh.1 w k z
  rw [e]
  exact (hg.2 w k).sub (hh.2 w k)

/-- The pairing is additive in its second slot on fields with `L²` word derivatives. -/
theorem pairSplit_jetPair_sub {c : ℝ} (j : ℕ) {f g h : Plane → Vec}
    (hf : ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w f k) 2 (Cyl.cellμ c))
    (hg : SmoothJetL2 c g) (hh : SmoothJetL2 c h) :
    jetPair c j f (fun y => g y - h y) = jetPair c j f g - jetPair c j f h := by
  unfold jetPair
  have i1 : Integrable (fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      wordComp w f k z * wordComp w g k z) (Cyl.cellμ c) :=
    integrable_finsetSum _ fun w _ => integrable_finsetSum _ fun k _ =>
      (hf w k).integrable_mul (hg.2 w k)
  have i2 : Integrable (fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      wordComp w f k z * wordComp w h k z) (Cyl.cellμ c) :=
    integrable_finsetSum _ fun w _ => integrable_finsetSum _ fun k _ =>
      (hf w k).integrable_mul (hh.2 w k)
  rw [← integral_sub]
  swap
  · exact i1
  swap
  · exact i2
  congr 1
  funext z
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pairSplit_wordComp_sub hg.1 hh.1 w k z]
  ring

/-- The pairing with a scalar multiple. -/
theorem pairSplit_jetPair_smul {c : ℝ} (j : ℕ) (r : ℝ) (f g : Plane → Vec) :
    jetPair c j f (fun y => r • g y) = r * jetPair c j f g := by
  unfold jetPair
  rw [← integral_const_mul]
  congr 1
  funext z
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pairSplit_wordComp_smul]
  ring

theorem trainJetPairSplit_proof : UnforcedLeray.Short.PartI.TrainJetPairSplit := by
  intro ν c hν hc tr htr s hs hac j
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hL2 := trainErrJetL2_proof ν c hν hc tr htr s hs hac
  have hLap : SmoothJetL2 c (fun y => ν • Train.vecLaplacian (trainErr tr s) y) :=
    trainErrLaplacianL2_proof ν c hν hc tr htr s hs hac
  have hAdv : SmoothJetL2 c (advDiff tr s) :=
    trainAdvDiffL2_proof ν c hν hc tr htr s hs hac
  have hPR := trainPressureRegular_proof ν c hν hc tr htr s hs hac
  have hSt : SmoothJetL2 c (Train.matDiv (Qc ν c s)) :=
    trainStressDivL2_proof ν c hν hc tr htr s hs hac
  have hπs : ContDiff ℝ ∞ (errPressure tr s) := hPR.1
  have hG : SmoothJetL2 c (Train.gradS (errPressure tr s)) :=
    ⟨UnforcedLeray.Short.PartI.ErrPressureLapAux.gradS_contDiff hπs, hPR.2.2.2⟩
  -- the error equation, pointwise in `y`
  have hpt : (fun y => deriv (fun t => trainErr tr t y) s) =
      fun y => ((fun y => ν • Train.vecLaplacian (trainErr tr s) y) y - advDiff tr s y)
        - Train.gradS (errPressure tr s) y - Train.matDiv (Qc ν c s) y := by
    funext y
    have h := TrainErrorEquation.train_error_equation tr hν hc0 s hs y
    unfold trainErr advDiff errPressure
    linear_combination (norm := module) h
  rw [hpt]
  rw [pairSplit_jetPair_sub j hL2 (pairSplit_smoothJetL2_sub
      (pairSplit_smoothJetL2_sub hLap hAdv) hG) hSt]
  rw [pairSplit_jetPair_sub j hL2 (pairSplit_smoothJetL2_sub hLap hAdv) hG]
  rw [pairSplit_jetPair_sub j hL2 hLap hAdv]
  rw [pairSplit_jetPair_smul]

end UnforcedLeray.Short.PartI
