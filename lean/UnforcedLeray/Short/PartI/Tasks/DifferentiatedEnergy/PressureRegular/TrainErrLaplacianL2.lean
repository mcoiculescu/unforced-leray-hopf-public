import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# Part I, task `PartI:T08/3/5` (`trainErrLaplacianL2_proof`): the viscous term

Source: `the November 2 reference manuscript` lines 261-288, 344.

Component `k` of `ν Δe` is `ν (∂_q² g + ∂_η² g)` with `g = e_k`. A word derivative of
`∂_q ∂_q g` is the word derivative `(true :: true :: w)` of `g` (commutation,
`ForcingIBP.derivWord_comm`), so every word derivative of `ν Δe` is a constant multiple of a sum
of two word derivatives of `e` of order `|w| + 2`, which are in `L²(cell)` by
`trainErrJetL2_proof`. Smoothness comes from `trainErrBasic_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

namespace TrainErrLapL2

theorem pQ_const_mul (k : ℝ) (f : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (fun w => k * f w) z = k * Cyl.partialQ f z := by
  show deriv (fun x : ℝ => k * f (x, z.2)) z.1 = k * deriv (fun x : ℝ => f (x, z.2)) z.1
  rw [deriv_const_mul_field']

theorem pEta_const_mul (k : ℝ) (f : Plane → ℝ) (z : Plane) :
    Cyl.partialEta (fun w => k * f w) z = k * Cyl.partialEta f z := by
  show deriv (fun x : ℝ => k * f (z.1, x)) z.2 = k * deriv (fun x : ℝ => f (z.1, x)) z.2
  rw [deriv_const_mul_field']

/-- Word derivatives commute with a constant factor (no smoothness needed). -/
theorem derivWord_const_mul (k : ℝ) (w : List Bool) :
    ∀ F : Plane → ℝ, B0151.derivWord w (fun z => k * F z) =
      fun z => k * B0151.derivWord w F z := by
  induction w with
  | nil => intro F; rfl
  | cons b w ih =>
    intro F
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => k * F z)) =
        fun z => k * Cyl.partialEta (B0151.derivWord w F) z
      rw [ih F]
      funext z
      exact pEta_const_mul k _ z
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => k * F z)) =
        fun z => k * Cyl.partialQ (B0151.derivWord w F) z
      rw [ih F]
      funext z
      exact pQ_const_mul k _ z

/-- `∂_w ∂_q² g = ∂_{(q,q,w)} g` on smooth `g`. -/
theorem derivWord_pQQ (w : List Bool) (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) :
    B0151.derivWord w (Cyl.partialQ (Cyl.partialQ g)) = B0151.derivWord (true :: true :: w) g := by
  have h1 := (ForcingIBP.derivWord_comm w (Cyl.partialQ g) (ForcingIBP.cd_partialQ hg)).1
  have h2 := (ForcingIBP.derivWord_comm w g hg).1
  exact h1.trans (congrArg Cyl.partialQ h2)

/-- `∂_w ∂_η² g = ∂_{(η,η,w)} g` on smooth `g`. -/
theorem derivWord_pEE (w : List Bool) (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) :
    B0151.derivWord w (Cyl.partialEta (Cyl.partialEta g)) =
      B0151.derivWord (false :: false :: w) g := by
  have h1 := (ForcingIBP.derivWord_comm w (Cyl.partialEta g) (ForcingIBP.cd_partialEta hg)).2
  have h2 := (ForcingIBP.derivWord_comm w g hg).2
  exact h1.trans (congrArg Cyl.partialEta h2)

theorem vecLap_apply (u : Plane → Vec) (z : Plane) (k : Fin 2) :
    Train.vecLaplacian u z k = Train.lapS (fun x => u x k) z := by
  fin_cases k <;> rfl

end TrainErrLapL2

open TrainErrLapL2 in
theorem trainErrLaplacianL2_proof : UnforcedLeray.Short.PartI.TrainErrLaplacianL2 := by
  intro ν c hν hc tr htr s hs hac
  have he : ContDiff ℝ ∞ (trainErr tr s) := (trainErrBasic_proof ν c hν hc tr htr s hs hac).1
  have hJ := trainErrJetL2_proof ν c hν hc tr htr s hs hac
  have hg : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => trainErr tr s x k) := fun k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp he
  have hcomp : ∀ k : Fin 2, (fun x => (ν • Train.vecLaplacian (trainErr tr s)) x k) =
      fun x => ν * (Cyl.partialQ (Cyl.partialQ (fun y => trainErr tr s y k)) x +
        Cyl.partialEta (Cyl.partialEta (fun y => trainErr tr s y k)) x) := by
    intro k
    funext x
    rw [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, vecLap_apply]
    rfl
  refine ⟨?_, ?_⟩
  · refine (contDiff_piLp _).2 fun k => ?_
    rw [hcomp k]
    exact contDiff_const.mul ((ForcingIBP.cd_partialQ (ForcingIBP.cd_partialQ (hg k))).add
      (ForcingIBP.cd_partialEta (ForcingIBP.cd_partialEta (hg k))))
  · intro w k
    have step : wordComp w (ν • Train.vecLaplacian (trainErr tr s)) k =
        fun z => ν * (B0151.derivWord (true :: true :: w) (fun y => trainErr tr s y k) z +
          B0151.derivWord (false :: false :: w) (fun y => trainErr tr s y k) z) := by
      unfold wordComp
      rw [hcomp k, derivWord_const_mul ν w _,
        ForcingIBP.derivWord_add_smooth w _ _ (ForcingIBP.cd_partialQ (ForcingIBP.cd_partialQ (hg k)))
          (ForcingIBP.cd_partialEta (ForcingIBP.cd_partialEta (hg k))),
        derivWord_pQQ w _ (hg k), derivWord_pEE w _ (hg k)]
    rw [step]
    exact ((hJ (true :: true :: w) k).add (hJ (false :: false :: w) k)).const_mul ν

end UnforcedLeray.Short.PartI
