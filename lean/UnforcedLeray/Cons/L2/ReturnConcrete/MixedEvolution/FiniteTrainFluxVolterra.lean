import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPath
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatStripSupplier
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Finite-age actual train coefficient path for Volterra

Only coefficient bounds on the physical interval [0,T] are required. The actual train
coefficients are extended by clamping age to that interval, providing the globally defined
bounded operator path used by Infra.VolterraEvolution. On [0,T] the clamp is the identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Set
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane
open UnforcedLeray.Infra.VolterraEvolution (ae_ne_real)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Clamp a real age to the finite physical interval [0,T]. -/
def actualTrainAgeClamp (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : Icc (0 : ℝ) T :=
  ⟨max 0 (min T t), ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩⟩

/-- Actual B0238 train coefficients on a finite age interval, with a clamped extension. The
remaining analytic inputs are bounds on the actual velocity and weighted curl on [0,T], plus
strong continuity of the resulting physical flux operators. -/
structure ActualTrainFluxPathOn {c m ν T : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (hT : 0 ≤ T) where
  Cv : ℝ
  CE : ℝ
  hCv : 0 ≤ Cv
  hCE : 0 ≤ CE
  velocity_bound : ∀ s : Icc (0 : ℝ) T, ∀ x i,
    |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv
  weighted_curl_bound : ∀ s : Icc (0 : ℝ) T, ∀ x ∈ cell c,
    |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE
  continuous_flux_apply : ∀ w : ActualVorticity (c := c) (m := m) hm,
    Continuous (fun t => actualTrainFluxAtNonneg
      (s := (actualTrainAgeClamp T hT t).1) hm tr
      (actualTrainAgeClamp T hT t).property.1 hCv hCE
      (velocity_bound (actualTrainAgeClamp T hT t))
      (weighted_curl_bound (actualTrainAgeClamp T hT t)) w)

/-- The globally defined bounded coefficient operator, using the actual train at clamped age. -/
def actualTrainFluxBOn {c m ν T : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (t : ℝ) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualFlux (c := c) (m := m) :=
  actualTrainFluxAtNonneg (s := (actualTrainAgeClamp T hT t).1) hm tr
    (actualTrainAgeClamp T hT t).property.1 P.hCv P.hCE
    (P.velocity_bound (actualTrainAgeClamp T hT t))
    (P.weighted_curl_bound (actualTrainAgeClamp T hT t))

/-- On the physical age interval the clamp is the identity, so the extension is exactly the
physical flux of the actual train coefficients. -/
theorem actualTrainFluxBOn_eq_actual {c m ν T s : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (hs : s ∈ Icc (0 : ℝ) T) :
    actualTrainFluxBOn hm P s =
      actualTrainFluxAtNonneg (s := s) hm tr hs.1 P.hCv P.hCE
        (P.velocity_bound ⟨s, hs⟩) (P.weighted_curl_bound ⟨s, hs⟩) := by
  have hclamp : actualTrainAgeClamp T hT s = ⟨s, hs⟩ := by
    apply Subtype.ext
    simp [actualTrainAgeClamp, max_eq_right hs.1, min_eq_right hs.2]
  apply ContinuousLinearMap.ext
  intro w
  change actualTrainFluxAtNonneg
      (s := (actualTrainAgeClamp T hT s).1) hm tr
      (actualTrainAgeClamp T hT s).property.1 P.hCv P.hCE
      (P.velocity_bound (actualTrainAgeClamp T hT s))
      (P.weighted_curl_bound (actualTrainAgeClamp T hT s)) w = _
  have hval : (actualTrainAgeClamp T hT s).1 = s := congrArg Subtype.val hclamp
  simp only [hval]

/-- The global coefficient path has the explicit fixed-cylinder operator bound. -/
theorem norm_actualTrainFluxBOn_le {c m ν T : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (t : ℝ) :
    ‖actualTrainFluxBOn hm P t‖ ≤ P.Cv + P.CE * (c / (2 * Real.pi) + 2) := by
  exact norm_physicalFluxKernelCLM_le hm _ _ _ _ P.hCv P.hCE
    (P.velocity_bound (actualTrainAgeClamp T hT t))
    (P.weighted_curl_bound (actualTrainAgeClamp T hT t))

theorem continuous_actualTrainFluxBOn_apply {c m ν T : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT)
    (w : ActualVorticity (c := c) (m := m) hm) :
    Continuous (fun t => actualTrainFluxBOn hm P t w) :=
  P.continuous_flux_apply w

/-- Totalize the actual train flux on its physical age interval, using the actual B0238
coefficients there and the clamped coefficient path elsewhere. -/
def actualTrainFluxOnIcc {c m ν T : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn hm tr hT) (r : ℝ) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualFlux (c := c) (m := m) :=
  if hr : r ∈ Icc (0 : ℝ) T then
    actualTrainFluxAtNonneg (s := r) hm tr hr.1 P.hCv P.hCE
      (P.velocity_bound ⟨r, hr⟩) (P.weighted_curl_bound ⟨r, hr⟩)
  else actualTrainFluxBOn hm P r

/-- Volterra data on the finite actual train interval with the constructed physical heat supplier. -/
def actualPhysicalTrainVolterraDataOn {c m ν T : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn hm tr hT) :
    UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (ActualVorticity (c := c) (m := m) hm) (ActualFlux (c := c) (m := m)) where
  S₀ := (actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀
  S := (actualPhysicalWeightedHeatStripSupplier hc1 hm).S
  B := actualTrainFluxBOn hm P
  M₀ := (actualPhysicalWeightedHeatStripSupplier hc1 hm).M₀
  C₀ := (actualPhysicalWeightedHeatStripSupplier hc1 hm).C₀
  β := P.Cv + P.CE * (c / (2 * Real.pi) + 2)
  norm_S₀_le := (actualPhysicalWeightedHeatStripSupplier hc1 hm).norm_S₀_le
  norm_S_le := (actualPhysicalWeightedHeatStripSupplier hc1 hm).norm_S_le
  norm_B_le := norm_actualTrainFluxBOn_le hm P
  continuousOn_S₀ := (actualPhysicalWeightedHeatStripSupplier hc1 hm).continuousOn_S₀
  continuousOn_S := (actualPhysicalWeightedHeatStripSupplier hc1 hm).continuousOn_S
  continuous_B := continuous_actualTrainFluxBOn_apply hm P

/-- Actual physical heat/response compatibility supplies the exact cross law for the finite-age
actual train Volterra data. -/
theorem actualPhysicalTrainVolterraDataOn_compatible {c m ν T : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn hm tr hT) :
    (actualPhysicalTrainVolterraDataOn hc1 hm hT P).Compatible := by
  constructor
  · exact (actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀_comp_S₀
  · exact (actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀_comp_S

/-- The finite-age actual-train evolution obeys the literal weighted physical mild equation.
For `0 ≤ s ≤ t ≤ T`, the forcing integrand is explicitly the actual B0238 train flux on the
whole interval of integration. -/
theorem actualPhysicalTrainEvolutionOn_mild {c m ν T s t : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hT : 0 ≤ T) (P : ActualTrainFluxPathOn hm tr hT)
    (h0s : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ s + 1) (htT : t ≤ T)
    (w : ActualVorticity (c := c) (m := m) hm) :
    let D := actualPhysicalTrainVolterraDataOn hc1 hm hT P
    D.evolution t s w =
      (actualPhysicalWeightedHeatStripSupplier hc1 hm).S₀ (t - s) w +
        ∫ r in s..t,
          (actualPhysicalWeightedHeatStripSupplier hc1 hm).S (t - r)
            (actualTrainFluxOnIcc hm P r (D.evolution r s w)) := by
  dsimp only
  rw [(actualPhysicalTrainVolterraDataOn hc1 hm hT P).evolution_volterra
    (actualPhysicalTrainVolterraDataOn_compatible hc1 hm hT P) ⟨hst, ht⟩ w]
  simp only [actualPhysicalTrainVolterraDataOn]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real t] with r hrt hr
  rw [uIoc_of_le hst] at hr
  have hri : r ∈ Icc (0 : ℝ) T :=
    ⟨le_trans h0s (le_of_lt hr.1), le_trans hr.2 htT⟩
  have hB := actualTrainFluxBOn_eq_actual hm P hri
  rw [hB]
  simp [actualTrainFluxOnIcc, hri]

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualTrainFluxBOn_eq_actual
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalTrainVolterraDataOn
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalTrainEvolutionOn_mild
