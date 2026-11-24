import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ConsAppend
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.DerivWordLapComm

/-!
# Part I, task `PartI:T08/2/2/5`: `TrainVelocityWordLap` (Laplacian of velocity words)

Target: `theorem trainVelocityWordLap_proof : UnforcedLeray.Short.PartI.TrainVelocityWordLap`.

Source of record: `the November 2 reference manuscript`, line 261 (`v = ∇^⊥ψ`) and
line 266 (`div v = 0`); the leaf statement is in `Sub/PartI_T08_2_2.lean`.

Route. Write `f_0 = v_q`, `f_1 = v_η` (slices of `tr.v s`), `vom = curl v = ∂_q f_1 - ∂_η f_0`.
* `div v = 0` gives `∂_q f_0 = -∂_η f_1` and `∂_η f_1 = -∂_q f_0`.
* Using that spatial word derivatives commute with `Δ` on smooth fields and that the
  two letters commute, `Δ f_0 = -∂_η vom` and `Δ f_1 = ∂_q vom` (`vwl_lap_pair`).
* A word `w` is moved through: `Δ ∂_w f_k = ∂_w Δ f_k`, and `∂_w ∂_β vom = ∂_{β :: w} vom` on smooth
  fields (`vwl_cons_false`, `vwl_cons_true`, built from `derivWordConsAppend_proof` and
  `vjl_derivWord_append`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- `∂_η` commutes with negation (partial derivatives of `-h`). -/
theorem vwl_partialX_neg (h : Plane → ℝ) :
    GaussianVortex.partialX (fun z => -h z) = fun z => -GaussianVortex.partialX h z := by
  funext z
  show deriv (-(fun x : ℝ => h (x, z.2))) z.1 = -deriv (fun x : ℝ => h (x, z.2)) z.1
  exact deriv.neg

theorem vwl_partialY_neg (h : Plane → ℝ) :
    GaussianVortex.partialY (fun z => -h z) = fun z => -GaussianVortex.partialY h z := by
  funext z
  show deriv (-(fun y : ℝ => h (z.1, y))) z.2 = -deriv (fun y : ℝ => h (z.1, y)) z.2
  exact deriv.neg

/-- Word derivatives commute with negation. -/
theorem vwl_derivWord_neg (g : Plane → ℝ) :
    ∀ w : List Bool, B0151.derivWord w (fun z => -g z) = fun z => -B0151.derivWord w g z
  | [] => rfl
  | true :: w => by
      have ih := vwl_derivWord_neg g w
      show GaussianVortex.partialX (B0151.derivWord w (fun z => -g z)) =
        fun z => -GaussianVortex.partialX (B0151.derivWord w g) z
      rw [ih]
      exact vwl_partialX_neg _
  | false :: w => by
      have ih := vwl_derivWord_neg g w
      show GaussianVortex.partialY (B0151.derivWord w (fun z => -g z)) =
        fun z => -GaussianVortex.partialY (B0151.derivWord w g) z
      rw [ih]
      exact vwl_partialY_neg _

/-- Moving a letter to the front of a word on a smooth field. -/
theorem vwl_cons_false (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) (u : List Bool) :
    B0151.derivWord (false :: u) g = B0151.derivWord u (B0151.derivWord [false] g) :=
  (derivWordConsAppend_proof g hg false u).trans (vjl_derivWord_append false g u)

theorem vwl_cons_true (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) (u : List Bool) :
    B0151.derivWord (true :: u) g = B0151.derivWord u (B0151.derivWord [true] g) :=
  (derivWordConsAppend_proof g hg true u).trans (vjl_derivWord_append true g u)

/-- The Laplacian of the two velocity slices, from `div v = 0` and the commutations. -/
theorem vwl_lap_pair (f0 f1 vom : Plane → ℝ) (h0 : ContDiff ℝ ∞ f0) (h1 : ContDiff ℝ ∞ f1)
    (hvom : vom = fun z => B0151.derivWord [true] f1 z - B0151.derivWord [false] f0 z)
    (hdiv : ∀ z, B0151.derivWord [true] f0 z + B0151.derivWord [false] f1 z = 0) :
    Train.lapS f0 = (fun z => -B0151.derivWord [false] vom z) ∧
      Train.lapS f1 = (fun z => B0151.derivWord [true] vom z) := by
  subst hvom
  have hD1 : ContDiff ℝ ∞ (B0151.derivWord [true] f1) := B0151.contDiff_derivWord h1 [true]
  have hD2 : ContDiff ℝ ∞ (B0151.derivWord [false] f0) := B0151.contDiff_derivWord h0 [false]
  have c1 : B0151.derivWord [true] f0 = fun z => -B0151.derivWord [false] f1 z :=
    funext fun z => by linarith [hdiv z]
  have c2 : B0151.derivWord [false] f1 = fun z => -B0151.derivWord [true] f0 z :=
    funext fun z => by linarith [hdiv z]
  have d1 : B0151.derivWord [true] (B0151.derivWord [true] f0) =
      fun z => -B0151.derivWord [false] (B0151.derivWord [true] f1) z := by
    rw [c1, vwl_derivWord_neg, dwcaSingle_comm h1 true false]
  have d2 : B0151.derivWord [false] (B0151.derivWord [false] f1) =
      fun z => -B0151.derivWord [true] (B0151.derivWord [false] f0) z := by
    rw [c2, vwl_derivWord_neg, dwcaSingle_comm h0 false true]
  have d1z : ∀ z, B0151.derivWord [true] (B0151.derivWord [true] f0) z =
      -B0151.derivWord [false] (B0151.derivWord [true] f1) z := fun z => congrFun d1 z
  have d2z : ∀ z, B0151.derivWord [false] (B0151.derivWord [false] f1) z =
      -B0151.derivWord [true] (B0151.derivWord [false] f0) z := fun z => congrFun d2 z
  have hsub : ∀ w z, B0151.derivWord w
      (fun x => B0151.derivWord [true] f1 x - B0151.derivWord [false] f0 x) z =
      B0151.derivWord w (B0151.derivWord [true] f1) z -
        B0151.derivWord w (B0151.derivWord [false] f0) z :=
    fun w z => derivWord_sub_smooth hD1 hD2 w z
  constructor
  · funext z
    show B0151.derivWord [true] (B0151.derivWord [true] f0) z +
        B0151.derivWord [false] (B0151.derivWord [false] f0) z =
      -B0151.derivWord [false] (fun x => B0151.derivWord [true] f1 x - B0151.derivWord [false] f0 x) z
    rw [hsub [false] z, d1z z]
    ring
  · funext z
    show B0151.derivWord [true] (B0151.derivWord [true] f1) z +
        B0151.derivWord [false] (B0151.derivWord [false] f1) z =
      B0151.derivWord [true] (fun x => B0151.derivWord [true] f1 x - B0151.derivWord [false] f0 x) z
    rw [hsub [true] z, d2z z]
    ring

theorem trainVelocityWordLap_proof : UnforcedLeray.Short.PartI.TrainVelocityWordLap := by
  intro ν c _hc tr s hs w z
  have h0 : ContDiff ℝ ∞ (fun x => tr.v s x 0) := vjl_slice_smooth tr hs 0
  have h1 : ContDiff ℝ ∞ (fun x => tr.v s x 1) := vjl_slice_smooth tr hs 1
  have hdiv : ∀ y, B0151.derivWord [true] (fun x => tr.v s x 0) y +
      B0151.derivWord [false] (fun x => tr.v s x 1) y = 0 :=
    fun y => tr.isTrain.solenoidal s hs y
  have hvom : Cyl.curl (tr.v s) = fun y => B0151.derivWord [true] (fun x => tr.v s x 1) y -
      B0151.derivWord [false] (fun x => tr.v s x 0) y := rfl
  have hvoms : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := vjl_vortWord_contDiff tr hs []
  obtain ⟨hL0, hL1⟩ :=
    vwl_lap_pair (fun x => tr.v s x 0) (fun x => tr.v s x 1) (Cyl.curl (tr.v s)) h0 h1 hvom hdiv
  have hL0' : B0151.derivWord w (Train.lapS (fun x => tr.v s x 0)) =
      fun y => -B0151.derivWord w (B0151.derivWord [false] (Cyl.curl (tr.v s))) y := by
    rw [hL0, vwl_derivWord_neg]
  have hL1' : B0151.derivWord w (Train.lapS (fun x => tr.v s x 1)) =
      fun y => B0151.derivWord w (B0151.derivWord [true] (Cyl.curl (tr.v s))) y := by
    rw [hL1]
  have A1 : Train.lapS (wordComp w (tr.v s) 0) =
      B0151.derivWord w (Train.lapS (fun x => tr.v s x 0)) :=
    (derivWordLapComm_proof (fun x => tr.v s x 0) h0 w).symm
  have A1' : Train.lapS (wordComp w (tr.v s) 1) =
      B0151.derivWord w (Train.lapS (fun x => tr.v s x 1)) :=
    (derivWordLapComm_proof (fun x => tr.v s x 1) h1 w).symm
  have A2 : vortWord tr (false :: w) s =
      B0151.derivWord w (B0151.derivWord [false] (Cyl.curl (tr.v s))) :=
    vwl_cons_false _ hvoms w
  have A2' : vortWord tr (true :: w) s =
      B0151.derivWord w (B0151.derivWord [true] (Cyl.curl (tr.v s))) :=
    vwl_cons_true _ hvoms w
  constructor
  · rw [A1, hL0', A2]
  · rw [A1', hL1', A2']

end UnforcedLeray.Short.PartI
