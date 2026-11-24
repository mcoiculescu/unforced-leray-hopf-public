import UnforcedLeray.Short.PartI.Sub.T08_3

/-!
# Part I, task `PartI:T08/3/3` (`TrainTimeDerivL2`): decomposition

Source: `the November 2 reference manuscript` lines 261-288 (the train: BUC and
`H^k` data, finite-energy solution) and 326-336 (error equation, `A`, `Q_c`, `π = p - p_c^p`).

## Why the time derivative cannot be reached through `∇π` by the error equation

By `train_error_equation`, `∂_s e = νΔe - A - ∇π - div Q_c`, and `Δe`, `A`, `div Q_c` have smooth
`L²` word jets (siblings `T08/3/5`, `/4`, `/6`).  So `∂_s e` has smooth `L²` jets iff `∇π` does;
`trainTimeDerivL2_of` below proves exactly this reduction.  The gradient of the pressure error
therefore needs an independent argument (it cannot be read off from `∂_s e`).

## The independent argument (pressure Poisson equation, no decay of `p` or bounds on `∂_w p`)

Taking the divergence of the error equation (`div e = 0`, `div Δe = 0`, so `div ∂_s e = 0`):
`Δπ = -div F`, `F = A + div Q_c`.  `F` has smooth `L²` jets and `π` is smooth, periodic and
bounded (`PcSmoothDecay`, `PeriodicDecayBounded` as in `trainPressureRegular_of`).  Then:

* order `0`: with a transverse cutoff `φ = φ_R(η)` (`|φ'| ≤ C/R`, supported in `|η| ≤ 2R`),
  `∫ φ²|∇π|² = -∫ φ² π Δπ - 2∫ φ π ∇φ·∇π` and `-∫ φ² π Δπ = ∫ φ² π div F =
  -∫ φ² ∇π·F - 2∫ φ π ∇φ·F`.  Cauchy-Schwarz and `|π| ≤ M` give
  `∫ φ²|∇π|² ≤ 4 ∫ |F|² + (strip terms)`, where the strip terms are `O(M² R^{-1/2})`
  (strip area `2Rc`, `|∇φ| ≤ C/R`, `F ∈ L²`); the bound is uniform in `R`, and monotone
  convergence gives `∇π ∈ L²(cell)`.
* order `j + 1`: `h = ∂_w ∂_k π` (`|w| = j`) is smooth with `h ∈ L²` (previous order) and
  `Δh = -∂_w ∂_k div F ∈ L²`; the cutoff integration by parts
  `∫ φ² |∇h|² ≤ 2 ∫ φ² |h||Δh| + 4 ∫ h² |∇φ|²` gives `∇h ∈ L²`.

## Leaves

1. `PressureGradJetL2OfDivForm` (general analysis on the cell, the argument above).
2. `ErrPressureLap` (the identity `Δπ + div F = 0`; from the momentum equation and
   `div ∂_s v = 0`, and the algebraic identity `∇p_c^p = -V_c·∇V_c + div Q_c` of unit B0146).
3. `ErrPressureGradJetL2` (assembly: `π` smooth, periodic, bounded; `F = A + div Q_c` smooth,
   periodic with `L²` jets from `TrainAdvDiffL2`, `TrainStressDivL2`).

`trainTimeDerivL2_of` (proved here) derives `TrainTimeDerivL2` from `PcSmoothDecay`,
`TrainErrLaplacianL2`, `TrainAdvDiffL2`, `TrainStressDivL2` and `ErrPressureGradJetL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf 1 (general analysis).** A smooth, periodic, bounded scalar `π` on the cylinder whose
Laplacian is minus the divergence of a smooth periodic field `F` with `L²` word jets has
gradient with every word derivative in `L²(cell)`. -/
def PressureGradJetL2OfDivForm : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (π : Plane → ℝ) (F : Plane → Vec),
    ContDiff ℝ ∞ π → Cyl.IsPeriodic c π → (∃ M : ℝ, ∀ z, |π z| ≤ M) →
    SmoothJetL2 c F → Cyl.IsPeriodic c F →
    (∀ z, Train.lapS π z + (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z)
      = 0) →
    ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Train.gradS π) k) 2 (Cyl.cellμ c)

/-- **Leaf 2 (the pressure Poisson identity).** `Δπ + div(A + div Q_c) = 0` for the pressure
error of a train at every age `s > 0` (momentum equation, `div ∂_s v = 0` from joint smoothness,
`∇p_c^p = -V_c·∇V_c + div Q_c` from `B0146.periodicVelocity_residual`). -/
def ErrPressureLap : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s → ∀ z : Plane,
    Train.lapS (errPressure tr s) z +
      (Cyl.partialQ (fun w => (advDiff tr s w + Train.matDiv (Qc ν c s) w) 0) z +
        Cyl.partialEta (fun w => (advDiff tr s w + Train.matDiv (Qc ν c s) w) 1) z) = 0

/-- **Leaf 3 (the pressure-error gradient).** The last conjunct of `TrainPressureRegular`, to be
proved from leaves 1, 2 without using `∂_s e`. -/
def ErrPressureGradJetL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (Train.gradS (errPressure tr s)) k) 2 (Cyl.cellμ c)

theorem trainTimeDerivL2_of (h1 : PcSmoothDecay) (hX : TrainErrLaplacianL2)
    (hA : TrainAdvDiffL2) (hM : TrainStressDivL2) (hG : ErrPressureGradJetL2) :
    TrainTimeDerivL2 := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  obtain ⟨hpcs, -⟩ := h1 ν c s hν hc hs.le
  have hps : ContDiff ℝ ∞ (tr.p s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hs.le
  have hπs : ContDiff ℝ ∞ (errPressure tr s) := hps.sub hpcs
  have hX' := hX ν c hν hc tr htr s hs hac
  have hA' := hA ν c hν hc tr htr s hs hac
  have hM' := hM ν c hν hc tr htr s hs hac
  have hG' := hG ν c hν hc tr htr s hs hac
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have hgrad : ContDiff ℝ ∞ (Train.gradS (errPressure tr s)) :=
    Train.toVecL.contDiff.comp
      ((ForcingIBP.cd_partialQ hπs).prodMk (ForcingIBP.cd_partialEta hπs))
  have key : (fun z => deriv (fun t => trainErr tr t z) s) = fun z =>
      ((ν • Train.vecLaplacian (trainErr tr s) z - advDiff tr s z) -
        Train.gradS (errPressure tr s) z) - Train.matDiv (Qc ν c s) z := by
    funext z
    have h := TrainErrorEquation.train_error_equation tr hν hc0.ne' s hs z
    show deriv (fun t => tr.v t z - Vc ν c t z) s = _
    simp only [advDiff]
    change deriv (fun t => tr.v t z - Vc ν c t z) s = ν • Train.vecLaplacian
        (fun w => tr.v s w - Vc ν c s w) z -
        (Train.advection (tr.v s) z - Train.advection (Vc ν c s) z) -
        Train.gradS (fun w => tr.p s w - pc ν c s w) z - Train.matDiv (Qc ν c s) z
    linear_combination (norm := module) h
  refine ⟨?_, ?_⟩
  · rw [key]
    exact ((hX'.1.sub hA'.1).sub hgrad).sub hM'.1
  · intro w k
    have e : wordComp w (fun z => deriv (fun t => trainErr tr t z) s) k =
        B0151.derivWord w (fun z => ((ν • Train.vecLaplacian (trainErr tr s) z k -
          advDiff tr s z k) - Train.gradS (errPressure tr s) z k) - Train.matDiv (Qc ν c s) z k) := by
      unfold wordComp
      rw [key]
      rfl
    rw [e]
    have cX := comp hX'.1
    have cA := comp hA'.1
    have cG := comp hgrad
    have cM := comp hM'.1
    have l1 : ∀ w : List Bool, MemLp (B0151.derivWord w (fun z =>
        (ν • Train.vecLaplacian (trainErr tr s) z k - advDiff tr s z k) -
          Train.gradS (errPressure tr s) z k)) 2 (Cyl.cellμ c) :=
      fun w => wordL2_sub ((cX k).sub (cA k)) (cG k)
        (fun w => wordL2_sub (cX k) (cA k) (fun w => hX'.2 w k) (fun w => hA'.2 w k) w)
        (fun w => hG' w k) w
    exact wordL2_sub (((cX k).sub (cA k)).sub (cG k)) (cM k) l1 (fun w => hM'.2 w k) w

end UnforcedLeray.Short.PartI
