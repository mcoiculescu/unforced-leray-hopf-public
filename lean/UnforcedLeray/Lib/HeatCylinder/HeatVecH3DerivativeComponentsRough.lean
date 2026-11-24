import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeSmoothHeat
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Ordered derivative components of rough H³ Gaussian heat

The smooth derivative identities extend to every centered H³ class by the actual dense smooth
sequence and the continuity of the two actual quotient-valued operators.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- Every ordered weak derivative of the actual H³ Gaussian heat extension is the actual
normalized-cell L² Gaussian heat of the corresponding derivative component of the input. -/
theorem vectorH3DerivativeNormalizedValue_actualHeatVecH3 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    vectorH3DerivativeNormalizedValue hc α (actualHeatVecH3 hc hθ x) =
      heatVecL2CLM hc θ (vectorH3DerivativeNormalizedValue hc α x) := by
  obtain ⟨y, T, hT, hyrep, hyLim⟩ := exists_smoothVectorH3_sequence hc x
  have hheat (n : ℕ) : actualHeatVecH3 hc hθ (y n) =
      heatVecH3 hc hθ (hT n) := by
    apply vectorH3NormalizedValue_injective hc
    calc
      vectorH3NormalizedValue hc (actualHeatVecH3 hc hθ (y n)) =
          heatVecL2CLM hc θ (vectorH3NormalizedValue hc (y n)) :=
        vectorH3NormalizedValue_actualHeatVecH3 hc hθ (y n)
      _ = heatVecL2CLM hc θ (vectorH3NormalizedValue hc
          (UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc (T n) (hT n))) := by rw [hyrep n]
      _ = vectorH3NormalizedValue hc (heatVecH3 hc hθ (hT n)) :=
        (vectorH3NormalizedValue_heatVecH3 hc hθ (hT n)).symm
  let out : ℕ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
    fun n => actualHeatVecH3 hc hθ (y n)
  have hout : Tendsto out atTop (𝓝 (actualHeatVecH3 hc hθ x)) := by
    change Tendsto (fun n => actualHeatVecH3CLM hc hθ (y n)) atTop _
    exact (actualHeatVecH3CLM hc hθ).continuous.tendsto _ |>.comp hyLim
  let lhs : ℕ → Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
    fun n => vectorH3DerivativeNormalizedValue hc α (out n)
  have hlhs : Tendsto lhs atTop
      (𝓝 (vectorH3DerivativeNormalizedValue hc α (actualHeatVecH3 hc hθ x))) := by
    change Tendsto (fun n => vectorH3DerivativeNormalizedValue hc α (out n)) atTop _
    exact (vectorH3DerivativeNormalizedValue hc α).continuous.tendsto _ |>.comp hout
  let rhs : ℕ → Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
    fun n => heatVecL2CLM hc θ (vectorH3DerivativeNormalizedValue hc α (y n))
  have hrhs : Tendsto rhs atTop
      (𝓝 (heatVecL2CLM hc θ (vectorH3DerivativeNormalizedValue hc α x))) := by
    change Tendsto (fun n =>
      (heatVecL2CLM hc θ).comp (vectorH3DerivativeNormalizedValue hc α) (y n)) atTop _
    exact ((heatVecL2CLM hc θ).comp (vectorH3DerivativeNormalizedValue hc α)).continuous.tendsto _ |>.comp hyLim
  have hseq : lhs = rhs := by
    funext n
    change vectorH3DerivativeNormalizedValue hc α (actualHeatVecH3 hc hθ (y n)) =
      heatVecL2CLM hc θ (vectorH3DerivativeNormalizedValue hc α (y n))
    rw [hheat n, hyrep n,
      vectorH3DerivativeNormalizedValue_ofCylSmooth hc (hT n) α]
    exact vectorH3DerivativeNormalizedValue_heatVecH3 hc hθ (hT n) α
  exact tendsto_nhds_unique (by simpa only [hseq] using hlhs) hrhs

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3DerivativeNormalizedValue_actualHeatVecH3
