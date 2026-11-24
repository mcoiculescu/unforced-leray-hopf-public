import UnforcedLeray.Lib.TrainB.P0CompactNonlinearDuhamel
import UnforcedLeray.Lib.TrainB.P0H3Operator
import UnforcedLeray.Lib.CylinderB.Leray

/-!
# Weak centered-cell pairing of the actual mild equation

The fixed point is an H³-valued Bochner equation with the Navier–Stokes minus sign. This leaf
transfers it through the genuine zero-order centered-cell L² map and removes the actual Leray
projection against every weakly divergence-free L² test. No pointwise PDE or pressure is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.TrainB

open UnforcedLeray.Cyl
open UnforcedLeray.HeatCylinder

/-- The continuous row-tensor stress of a compact-time H³ path, extended by its actual constant
endpoint extension used in the mild map. -/
def compactMildStressPath {c T : ℝ} (hc1 : 1 ≤ c) (hT : 0 ≤ T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) :
    ContinuousMap ℝ (TensorH3 c) :=
  tensorH3StressPath hc1 (extendCompactPath hT u)

/-- The zero-order centered-cell value of the unprojected Gaussian heat-divergence stress orbit
in the compact-time mild equation. -/
def compactMildStressOrbit {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hT : 0 ≤ T) (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (t r : ℝ) : L2v c :=
  vecH3CellDerivCLM Sob.Idx.zero
    (actualHeatDivH3Orbit hc (compactMildStressPath hc1 hT u r) (ν * (t - r)))

/-- The actual H³ Leray projection disappears in a centered-cell pairing with a weakly
divergence-free test. -/
theorem inner_vecH3P0_eq_of_divFree {c : ℝ} (hc : 0 < c)
    (x : VectorH3 c) {φ : L2v c} (hφ : φ ∈ divFree c) :
    inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (P0H3CLM hc x)) φ =
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero x) φ := by
  rw [P0H3CLM_apply_component]
  calc
    inner ℝ (P0 c (vecH3CellDerivCLM Sob.Idx.zero x)) φ =
        inner ℝ (vecH3CellDerivCLM Sob.Idx.zero x) (P0 c φ) :=
          inner_P0_comm _ _
    _ = inner ℝ (vecH3CellDerivCLM Sob.Idx.zero x) φ := by
      rw [P0_eq_self hφ]

/-- A genuine centered-cell weak pairing of the corrected local Navier–Stokes fixed-point equation.
The nonlinear term is the negative literal Bochner integral of the projected Gaussian response;
this equality removes its projection only because the test belongs to the actual `divFree` subspace. -/
theorem inner_vecH3_mild_fixedPoint_eq {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (g u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u)
    (t : Icc (0 : ℝ) T) {φ : L2v c} (hφ : φ ∈ divFree c) :
    inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (u t)) φ =
      inner ℝ (vecH3CellDerivCLM Sob.Idx.zero (g t)) φ +
        -∫ r in Ioo (0 : ℝ) (t : ℝ),
          inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u (t : ℝ) r) φ := by
  let vCLM := vecH3CellDerivCLM (c := c) Sob.Idx.zero
  have hpoint : u t = g t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t :=
    congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f t) hfix
  rw [hpoint]
  rw [map_add, inner_add_left]
  by_cases ht0 : (t : ℝ) = 0
  · have hset : Ioo (0 : ℝ) (t : ℝ) = ∅ := by rw [ht0]; simp
    rw [projectedNonlinearDuhamelCompactMap_apply,
      projectedHeatNonlinearityIntegral, hset]
    simp
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
    rw [projectedNonlinearDuhamelCompactMap_apply,
      projectedHeatNonlinearityIntegral]
    let F : ContinuousMap ℝ (TensorH3 c) := compactMildStressPath hc1 hT.le u
    have hFbound : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), ‖F r‖ ≤ 1536 * ‖u‖ ^ 2 := by
      intro r hr
      exact norm_tensorH3StressPath_extendCompactPath_le hc1 hT.le u r
    have hInt : Integrable
        (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F)
        (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
      integrableOn_projectedHeatDuhamelOrbit hc hν htpos F hFbound
    have hpair : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (t : ℝ)),
        inner ℝ (vCLM (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r)) φ =
          inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u (t : ℝ) r) φ := by
      filter_upwards with r
      change inner ℝ (vCLM (P0H3CLM hc
          (actualHeatDivH3Orbit hc (F r) (ν * ((t : ℝ) - r)))) ) φ = _
      exact inner_vecH3P0_eq_of_divFree hc _ hφ
    have hpairIntegral :
        inner ℝ (vCLM (∫ r in Ioo (0 : ℝ) (t : ℝ),
          projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r)) φ =
          ∫ r in Ioo (0 : ℝ) (t : ℝ),
            inner ℝ (vCLM (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r)) φ := by
      rw [real_inner_comm]
      change ((innerSL ℝ φ).comp vCLM)
          (∫ r in Ioo (0 : ℝ) (t : ℝ),
            projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r) = _
      rw [← ((innerSL ℝ φ).comp vCLM).integral_comp_comm hInt]
      apply integral_congr_ae
      filter_upwards with r
      rw [real_inner_comm]
      rfl
    have hmap :
        inner ℝ (vCLM (-∫ r in Ioo (0 : ℝ) (t : ℝ),
          projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r)) φ =
          -∫ r in Ioo (0 : ℝ) (t : ℝ),
            inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u (t : ℝ) r) φ := by
      rw [map_neg, inner_neg_left, hpairIntegral]
      congr 1
      exact integral_congr_ae hpair
    have hmap' :
        inner ℝ (vCLM (-∫ r in Ioo (0 : ℝ) (t : ℝ),
          projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
            (tensorH3StressPath hc1 (extendCompactPath hT.le u)) r)) φ =
          -∫ r in Ioo (0 : ℝ) (t : ℝ),
            inner ℝ (compactMildStressOrbit (ν := ν) hc hc1 hT.le u (t : ℝ) r) φ := by
      simpa [F, compactMildStressPath] using hmap
    exact congrArg (fun z : ℝ => inner ℝ (vCLM (g t)) φ + z) hmap'

#print axioms UnforcedLeray.TrainB.inner_vecH3P0_eq_of_divFree
#print axioms UnforcedLeray.TrainB.inner_vecH3_mild_fixedPoint_eq

end UnforcedLeray.TrainB
