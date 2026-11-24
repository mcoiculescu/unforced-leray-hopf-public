import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP

/-!
# Part I, task `PartI:T08/3/3/1/3` (`pressureGradWordLapL2_proof`): `Δ` of word derivatives of `∇π`

Source of record: `the November 2 reference manuscript`, lines 326-336.
The Prop is `PressureGradWordLapL2` in `Sub/PartI_T08_3_3_1.lean`.

Route. Write `h = derivWord w (∂_k π)`. Word derivatives commute with `Δ` (`JetViscIBP.derivWord_lap`)
and with `∂_q`, `∂_η` on `π` (`JetViscIBP.partialQ_lap`, `partialEta_lap`). Since `Δπ = -(∂_q F₀ + ∂_η F₁)`,
`Δh = -derivWord w (∂_k ∂_q F₀ + ∂_k ∂_η F₁)`, which is a finite sum of word jets of `F` of
length `|w| + 2`, each in `L²(cell)` by `SmoothJetL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Word derivatives split at the end: `derivWord (u ++ [b]) h = derivWord u (derivWord [b] h)`. -/
theorem pg3_app (b : Bool) (h : Plane → ℝ) : ∀ u : List Bool,
    B0151.derivWord (u ++ [b]) h = B0151.derivWord u (B0151.derivWord [b] h)
  | [] => rfl
  | true :: u => by
      show Cyl.partialQ (B0151.derivWord (u ++ [b]) h)
        = Cyl.partialQ (B0151.derivWord u (B0151.derivWord [b] h))
      rw [pg3_app b h u]
  | false :: u => by
      show Cyl.partialEta (B0151.derivWord (u ++ [b]) h)
        = Cyl.partialEta (B0151.derivWord u (B0151.derivWord [b] h))
      rw [pg3_app b h u]

/-- Word derivatives commute with negation. -/
theorem pg3_neg (u : List Bool) : ∀ f : Plane → ℝ,
    B0151.derivWord u (fun z => -f z) = fun z => -(B0151.derivWord u f z) := by
  induction u with
  | nil => intro f; rfl
  | cons b u ih =>
    intro f
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord u (fun z => -f z))
        = fun z => -(Cyl.partialEta (B0151.derivWord u f) z)
      rw [ih f]
      funext z
      simp only [Cyl.partialEta]
      exact deriv.neg
    | true =>
      show Cyl.partialQ (B0151.derivWord u (fun z => -f z))
        = fun z => -(Cyl.partialQ (B0151.derivWord u f) z)
      rw [ih f]
      funext z
      simp only [Cyl.partialQ]
      exact deriv.neg

/-- **`PressureGradWordLapL2`** (Laplacian of word derivatives of `∇π` is in `L²`). -/
theorem pressureGradWordLapL2_proof : UnforcedLeray.Short.PartI.PressureGradWordLapL2 := by
  intro c hc π F hπ hF hlap w k
  have hF0s : ContDiff ℝ ∞ (fun z : Plane => F z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF.1
  have hF1s : ContDiff ℝ ∞ (fun z : Plane => F z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hF.1
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
  fin_cases k
  · -- the `q`-derivative
    show MemLp (fun z => Train.lapS (B0151.derivWord w (Cyl.partialQ π)) z) 2 (Cyl.cellμ c)
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
    rw [hfin]
    exact ((hF.2 ((w ++ [true]) ++ [true]) 0).add (hF.2 ((w ++ [true]) ++ [false]) 1)).neg
  · -- the `η`-derivative
    show MemLp (fun z => Train.lapS (B0151.derivWord w (Cyl.partialEta π)) z) 2 (Cyl.cellμ c)
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
    rw [hfin]
    exact ((hF.2 ((w ++ [false]) ++ [true]) 0).add (hF.2 ((w ++ [false]) ++ [false]) 1)).neg

end UnforcedLeray.Short.PartI
