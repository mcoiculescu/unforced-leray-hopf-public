import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_6
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradWordLapL2

/-!
# Part I, task `PartI:T08/4/1/1/6/3` (`pressureGradWordLapId_proof`): pointwise word identity

Source of record: `the November 2 reference manuscript`, lines 326-336.
The Prop is `PressureGradWordLapId` in `Sub/PartI_T08_4_1_1_6.lean`.

Route. As `pressureGradWordLapL2_proof`, but pointwise: word derivatives commute with `Δ`
(`JetViscIBP.derivWord_lap`), and `Δπ = -(∂_q F₀ + ∂_η F₁)` holds everywhere, so
`Δ ∂_w ∂_k π = -(∂_{u0} F₀ + ∂_{u1} F₁)` with `u0, u1` the words `w ++ [k-letter] ++ [q-letter]`
and `w ++ [k-letter] ++ [η-letter]` (head of the word applied last). The helpers `pg3_app`,
`pg3_neg` come from the imported module.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`PressureGradWordLapId`** (pointwise Laplacian identity for word jets of `∇π`). -/
theorem pressureGradWordLapId_proof : UnforcedLeray.Short.PartI.PressureGradWordLapId := by
  intro w k
  fin_cases k
  · refine ⟨(w ++ [true]) ++ [true], (w ++ [true]) ++ [false], ?_⟩
    intro π F hπ hF hlap z
    have hF0s : ContDiff ℝ ∞ (fun z : Plane => F z 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF
    have hF1s : ContDiff ℝ ∞ (fun z : Plane => F z 1) :=
      (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF
    have hpi1 : ContDiff ℝ ∞ (Cyl.partialQ π) := ForcingIBP.cd_partialQ hπ
    have hpi2 : ContDiff ℝ ∞ (Cyl.partialEta π) := ForcingIBP.cd_partialEta hπ
    have hlapπ : (fun z => Train.lapS π z) = fun z =>
        -(Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z) := by
      funext z
      have := hlap z
      linarith
    have hA0 : Differentiable ℝ (Cyl.partialQ (fun z : Plane => F z 0)) :=
      (ForcingIBP.cd_partialQ hF0s).differentiable (by simp)
    have hB1 : Differentiable ℝ (Cyl.partialEta (fun z : Plane => F z 1)) :=
      (ForcingIBP.cd_partialEta hF1s).differentiable (by simp)
    have hΦ : Cyl.partialQ (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
        = fun z => Cyl.partialQ (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialQ (Cyl.partialEta (fun w => F w 1)) z := by
      funext z
      exact ForcingIBP.partialQ_add_pt hA0 hB1 z
    have hΦe : Cyl.partialEta (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
        = fun z => Cyl.partialEta (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialEta (Cyl.partialEta (fun w => F w 1)) z := by
      funext z
      exact ForcingIBP.partialEta_add_pt hA0 hB1 z
    show Train.lapS (B0151.derivWord w (Cyl.partialQ π)) z = -(B0151.derivWord ((w ++ [true]) ++ [true]) (fun z => F z 0) z + B0151.derivWord ((w ++ [true]) ++ [false]) (fun z => F z 1) z)
    have step1 : (fun z => Train.lapS (B0151.derivWord w (Cyl.partialQ π)) z)
        = B0151.derivWord w (fun z => Train.lapS (Cyl.partialQ π) z) :=
      (JetViscIBP.derivWord_lap w _ hpi1).symm
    have hlapq : (fun z => Train.lapS (Cyl.partialQ π) z) = fun z =>
        -(Cyl.partialQ (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialQ (Cyl.partialEta (fun w => F w 1)) z) := by
      have s2 : (fun z => Train.lapS (Cyl.partialQ π) z)
          = Cyl.partialQ (fun z => Train.lapS π z) := (JetViscIBP.partialQ_lap hπ).symm
      rw [s2, hlapπ]
      have s3 := pg3_neg [true] (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
      have s3' : Cyl.partialQ (fun z => -(Cyl.partialQ (fun w => F w 0) z +
          Cyl.partialEta (fun w => F w 1) z))
          = fun z => -(Cyl.partialQ (fun z => Cyl.partialQ (fun w => F w 0) z +
            Cyl.partialEta (fun w => F w 1) z) z) := s3
      rw [s3', hΦ]
    have hAs : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ (fun z : Plane => F z 0))) :=
      ForcingIBP.cd_partialQ (ForcingIBP.cd_partialQ hF0s)
    have hBs : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialEta (fun z : Plane => F z 1))) :=
      ForcingIBP.cd_partialQ (ForcingIBP.cd_partialEta hF1s)
    have q1 : B0151.derivWord w (Cyl.partialQ (Cyl.partialQ (fun z : Plane => F z 0)))
        = B0151.derivWord ((w ++ [true]) ++ [true]) (fun z => F z 0) := by
      rw [pg3_app true (fun z : Plane => F z 0) (w ++ [true]),
        pg3_app true (B0151.derivWord [true] (fun z : Plane => F z 0)) w]
      rfl
    have q2 : B0151.derivWord w (Cyl.partialQ (Cyl.partialEta (fun z : Plane => F z 1)))
        = B0151.derivWord ((w ++ [true]) ++ [false]) (fun z => F z 1) := by
      rw [pg3_app false (fun z : Plane => F z 1) (w ++ [true]),
        pg3_app true (B0151.derivWord [false] (fun z : Plane => F z 1)) w]
      rfl
    have hfin : (fun z => Train.lapS (B0151.derivWord w (Cyl.partialQ π)) z) = fun z =>
        -(B0151.derivWord ((w ++ [true]) ++ [true]) (fun z => F z 0) z +
          B0151.derivWord ((w ++ [true]) ++ [false]) (fun z => F z 1) z) := by
      rw [step1, hlapq, pg3_neg w (fun z => Cyl.partialQ (Cyl.partialQ (fun w => F w 0)) z +
        Cyl.partialQ (Cyl.partialEta (fun w => F w 1)) z),
        ForcingIBP.derivWord_add_smooth w _ _ hAs hBs, q1, q2]
    exact congrFun hfin z
  · refine ⟨(w ++ [false]) ++ [true], (w ++ [false]) ++ [false], ?_⟩
    intro π F hπ hF hlap z
    have hF0s : ContDiff ℝ ∞ (fun z : Plane => F z 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF
    have hF1s : ContDiff ℝ ∞ (fun z : Plane => F z 1) :=
      (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF
    have hpi1 : ContDiff ℝ ∞ (Cyl.partialQ π) := ForcingIBP.cd_partialQ hπ
    have hpi2 : ContDiff ℝ ∞ (Cyl.partialEta π) := ForcingIBP.cd_partialEta hπ
    have hlapπ : (fun z => Train.lapS π z) = fun z =>
        -(Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z) := by
      funext z
      have := hlap z
      linarith
    have hA0 : Differentiable ℝ (Cyl.partialQ (fun z : Plane => F z 0)) :=
      (ForcingIBP.cd_partialQ hF0s).differentiable (by simp)
    have hB1 : Differentiable ℝ (Cyl.partialEta (fun z : Plane => F z 1)) :=
      (ForcingIBP.cd_partialEta hF1s).differentiable (by simp)
    have hΦ : Cyl.partialQ (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
        = fun z => Cyl.partialQ (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialQ (Cyl.partialEta (fun w => F w 1)) z := by
      funext z
      exact ForcingIBP.partialQ_add_pt hA0 hB1 z
    have hΦe : Cyl.partialEta (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
        = fun z => Cyl.partialEta (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialEta (Cyl.partialEta (fun w => F w 1)) z := by
      funext z
      exact ForcingIBP.partialEta_add_pt hA0 hB1 z
    show Train.lapS (B0151.derivWord w (Cyl.partialEta π)) z = -(B0151.derivWord ((w ++ [false]) ++ [true]) (fun z => F z 0) z + B0151.derivWord ((w ++ [false]) ++ [false]) (fun z => F z 1) z)
    have step1 : (fun z => Train.lapS (B0151.derivWord w (Cyl.partialEta π)) z)
        = B0151.derivWord w (fun z => Train.lapS (Cyl.partialEta π) z) :=
      (JetViscIBP.derivWord_lap w _ hpi2).symm
    have hlape : (fun z => Train.lapS (Cyl.partialEta π) z) = fun z =>
        -(Cyl.partialEta (Cyl.partialQ (fun w => F w 0)) z +
          Cyl.partialEta (Cyl.partialEta (fun w => F w 1)) z) := by
      have s2 : (fun z => Train.lapS (Cyl.partialEta π) z)
          = Cyl.partialEta (fun z => Train.lapS π z) := (JetViscIBP.partialEta_lap hπ).symm
      rw [s2, hlapπ]
      have s3 := pg3_neg [false] (fun z => Cyl.partialQ (fun w => F w 0) z +
        Cyl.partialEta (fun w => F w 1) z)
      have s3' : Cyl.partialEta (fun z => -(Cyl.partialQ (fun w => F w 0) z +
          Cyl.partialEta (fun w => F w 1) z))
          = fun z => -(Cyl.partialEta (fun z => Cyl.partialQ (fun w => F w 0) z +
            Cyl.partialEta (fun w => F w 1) z) z) := s3
      rw [s3', hΦe]
    have hAs : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialQ (fun z : Plane => F z 0))) :=
      ForcingIBP.cd_partialEta (ForcingIBP.cd_partialQ hF0s)
    have hBs : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta (fun z : Plane => F z 1))) :=
      ForcingIBP.cd_partialEta (ForcingIBP.cd_partialEta hF1s)
    have q1 : B0151.derivWord w (Cyl.partialEta (Cyl.partialQ (fun z : Plane => F z 0)))
        = B0151.derivWord ((w ++ [false]) ++ [true]) (fun z => F z 0) := by
      rw [pg3_app true (fun z : Plane => F z 0) (w ++ [false]),
        pg3_app false (B0151.derivWord [true] (fun z : Plane => F z 0)) w]
      rfl
    have q2 : B0151.derivWord w (Cyl.partialEta (Cyl.partialEta (fun z : Plane => F z 1)))
        = B0151.derivWord ((w ++ [false]) ++ [false]) (fun z => F z 1) := by
      rw [pg3_app false (fun z : Plane => F z 1) (w ++ [false]),
        pg3_app false (B0151.derivWord [false] (fun z : Plane => F z 1)) w]
      rfl
    have hfin : (fun z => Train.lapS (B0151.derivWord w (Cyl.partialEta π)) z) = fun z =>
        -(B0151.derivWord ((w ++ [false]) ++ [true]) (fun z => F z 0) z +
          B0151.derivWord ((w ++ [false]) ++ [false]) (fun z => F z 1) z) := by
      rw [step1, hlape, pg3_neg w (fun z => Cyl.partialEta (Cyl.partialQ (fun w => F w 0)) z +
        Cyl.partialEta (Cyl.partialEta (fun w => F w 1)) z),
        ForcingIBP.derivWord_add_smooth w _ _ hAs hBs, q1, q2]
    exact congrFun hfin z

end UnforcedLeray.Short.PartI
