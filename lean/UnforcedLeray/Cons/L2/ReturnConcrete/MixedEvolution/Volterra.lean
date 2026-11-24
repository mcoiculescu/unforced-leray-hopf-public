import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.SourceCLM
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Conditional Volterra evolution for the actual train flux

This leaf composes the concrete B0238 train coefficients and the actual B0583 real Biot--Savart
flux with the existing Volterra construction. The weighted heat-divergence family is isolated as
an explicit supplier: the current library does not yet identify a periodic lift of `X_m` data with
B0296's unweighted heat-divergence operator or prove its weighted `t^(-1/2)` estimate. Accordingly,
the evolution theorem below is conditional on that exact heat supplier and on strong continuity of
the actual coefficient path. It does not claim those suppliers are discharged.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.B0579
open UnforcedLeray.Train (Vec)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- State space: the actual real weighted-vorticity class with zero circulation. -/
abbrev ActualVorticity :=
  zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)

/-- Flux space: two actual real weighted-cell flux components. -/
abbrev ActualFlux := Fin 2 → X c m

/-- Circulation is a continuous functional, so its kernel is complete in the inherited `X_m`
norm. This is the Banach space required by the Volterra construction. -/
instance actualVorticityCompleteSpace :
    CompleteSpace (ActualVorticity (c := c) (m := m) hm) :=
  (isClosed_zeroCirculationSubmodule (by linarith : 1 / 2 < m)).completeSpace_coe

/-- A path of spatial train coefficients with their exact age-zero-and-later identification.
The bounds are uniform on nonnegative ages; `max t 0` below extends the path to the whole real
line only to match the global coefficient domain of `Infra.VolterraEvolution`. -/
structure ActualTrainFluxPath (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) where
  Cv : ℝ
  CE : ℝ
  hCv : 0 ≤ Cv
  hCE : 0 ≤ CE
  v : ℝ → Plane → Vec
  E : ℝ → Plane → ℝ
  continuous_v : ∀ t, 0 ≤ t → Continuous (v t)
  continuous_E : ∀ t, 0 ≤ t → Continuous (E t)
  velocity_eq : ∀ t, 0 ≤ t → v t = UnforcedLeray.B0238.Vc tr t
  curl_eq : ∀ t, 0 ≤ t → E t = UnforcedLeray.B0238.Ec tr t
  velocity_bound : ∀ t, 0 ≤ t → ∀ x i, |v t x i| ≤ Cv
  weighted_curl_bound : ∀ t, 0 ≤ t → ∀ x ∈ cell c,
    |bracket x ^ m * E t x| ≤ CE
  /-- Strong continuity of the actual flux operators. For a genuine train this must follow from
  joint continuity of `Vc`, `Ec` and the uniform centered-cell bounds by dominated convergence. -/
  continuous_flux_apply : ∀ w : ActualVorticity (c := c) (m := m) hm,
    Continuous (fun t =>
      physicalFluxKernelCLM hm (v (max t 0)) (E (max t 0))
        (continuous_v _ (le_max_right _ _)) (continuous_E _ (le_max_right _ _))
        hCv hCE
        (velocity_bound _ (le_max_right _ _))
        (weighted_curl_bound _ (le_max_right _ _)) w)

/-- The age-dependent bounded coefficient `B(t):X₀→Y` is formed from the actual train flux.
Negative times are clamped to the actual initial coefficient, solely to provide the global domain
required by the abstract strip construction. -/
def actualTrainFluxB {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) (t : ℝ) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualFlux (c := c) (m := m) :=
  physicalFluxKernelCLM hm (P.v (max t 0)) (P.E (max t 0))
    (P.continuous_v _ (le_max_right _ _)) (P.continuous_E _ (le_max_right _ _))
    P.hCv P.hCE (P.velocity_bound _ (le_max_right _ _))
    (P.weighted_curl_bound _ (le_max_right _ _))

theorem norm_actualTrainFluxB_le {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) (t : ℝ) :
    ‖actualTrainFluxB hm P t‖ ≤ P.Cv + P.CE * (c / (2 * Real.pi) + 2) := by
  exact norm_physicalFluxKernelCLM_le hm _ _ _ _ P.hCv P.hCE
    (P.velocity_bound _ (le_max_right _ _))
    (P.weighted_curl_bound _ (le_max_right _ _))

theorem continuous_actualTrainFluxB_apply {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (w : ActualVorticity (c := c) (m := m) hm) :
    Continuous (fun t => actualTrainFluxB hm P t w) :=
  P.continuous_flux_apply w

/-- On nonnegative ages the path coefficient is exactly the physical flux of B0238's actual
`Vc` and `Ec` and B0583's real `K_c`; this prevents an unrelated abstract coefficient map from
being substituted into the Volterra theorem. -/
theorem actualTrainFluxB_eq_trainFlux {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) {t : ℝ} (ht : 0 ≤ t)
    (w : ActualVorticity (c := c) (m := m) hm) :
    actualTrainFluxB hm P t w =
      physicalFluxKernelCLM hm (UnforcedLeray.B0238.Vc tr t)
        (UnforcedLeray.B0238.Ec tr t)
        (UnforcedLeray.B0238.contDiff_Vc tr ht).continuous
        (by
          unfold UnforcedLeray.B0238.Ec
          exact UnforcedLeray.B0238.continuous_curl
            ((UnforcedLeray.B0238.contDiff_Vc tr ht).of_le (by norm_num)))
        P.hCv P.hCE (by rw [← P.velocity_eq t ht]; exact P.velocity_bound t ht)
        (by rw [← P.curl_eq t ht]; exact P.weighted_curl_bound t ht) w := by
  simp only [actualTrainFluxB, max_eq_left ht, P.velocity_eq t ht, P.curl_eq t ht]

/-- Conditional strip-family data for the zero-circulation state and physical flux spaces. The
semigroup law, cross-compatibility and identity at zero are included because a physical
initial-value mild evolution needs them. This record is not itself a construction of the weighted
heat family: one must identify `S₀` with the actual weighted heat operator on `X_m`, identify `S`
with its heat-divergence response on actual periodic lifts of `X_m²` flux, prove zero-circulation
preservation, and establish the stated weighted bounds and strong continuity. -/
structure WeightedHeatStripSupplier where
  S₀ : ℝ → ActualVorticity (c := c) (m := m) hm →L[ℝ]
    ActualVorticity (c := c) (m := m) hm
  S : ℝ → ActualFlux (c := c) (m := m) →L[ℝ]
    ActualVorticity (c := c) (m := m) hm
  M₀ : ℝ
  C₀ : ℝ
  S₀_zero : S₀ 0 = ContinuousLinearMap.id ℝ
    (ActualVorticity (c := c) (m := m) hm)
  norm_S₀_le : ∀ t, 0 ≤ t → t ≤ 1 → ‖S₀ t‖ ≤ M₀
  norm_S_le : ∀ t, 0 < t → t ≤ 1 → ‖S t‖ ≤ C₀ * t ^ (-(1 / 2 : ℝ))
  continuousOn_S₀ : ∀ x, ContinuousOn (fun t => S₀ t x) (Set.Icc 0 1)
  continuousOn_S : ∀ y, ContinuousOn (fun t => S t y) (Set.Ioc 0 1)
  S₀_comp_S₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 →
    (S₀ a).comp (S₀ b) = S₀ (a + b)
  S₀_comp_S : ∀ a b : ℝ, 0 ≤ a → 0 < b → a + b ≤ 1 →
    (S₀ a).comp (S b) = S (a + b)

/-- The actual conditional Volterra data for the train, with `B` supplied by its concrete flux
path and the weighted heat family supplied separately. -/
def actualTrainVolterraData {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (ActualVorticity (c := c) (m := m) hm) (ActualFlux (c := c) (m := m)) where
  S₀ := H.S₀
  S := H.S
  B := actualTrainFluxB hm P
  M₀ := H.M₀
  C₀ := H.C₀
  β := P.Cv + P.CE * (c / (2 * Real.pi) + 2)
  norm_S₀_le := H.norm_S₀_le
  norm_S_le := H.norm_S_le
  norm_B_le := norm_actualTrainFluxB_le hm P
  continuousOn_S₀ := H.continuousOn_S₀
  continuousOn_S := H.continuousOn_S
  continuous_B := continuous_actualTrainFluxB_apply hm P

/-- The heat supplier's two composition identities provide the compatibility required by the
Volterra cocycle. -/
theorem actualTrainVolterra_compatible {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm) :
    (actualTrainVolterraData hm P H).Compatible where
  S₀_comp_S₀ := H.S₀_comp_S₀
  S₀_comp_S := H.S₀_comp_S

/-- The resulting evolution satisfies the unit-strip Volterra equation with the actual train-flux
coefficient and the supplied heat family. Identifying that heat family with the weighted B0296
Gaussian heat-divergence map is a separate unresolved bridge, so this theorem alone does not assert
the physical train mild equation. -/
theorem actualTrainEvolution_mild {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ s + 1)
    (w : ActualVorticity (c := c) (m := m) hm) :
    let D := actualTrainVolterraData hm P H
    D.evolution t s w =
      H.S₀ (t - s) w + ∫ r in s..t,
        H.S (t - r) (actualTrainFluxB hm P r (D.evolution r s w)) := by
  dsimp
  exact (actualTrainVolterraData hm P H).evolution_volterra
    (actualTrainVolterra_compatible hm P H) ⟨hst, ht⟩ w

/-- The conditional Volterra family has the correct diagonal trace once its supplied free
family is required to start at the identity. This is initial-trace algebra only; the physical heat
supplier remains a separate obligation. -/
theorem actualTrainEvolution_initial {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm)
    (s : ℝ) (w : ActualVorticity (c := c) (m := m) hm) :
    (actualTrainVolterraData hm P H).evolution s s w = w := by
  have h := actualTrainEvolution_mild (c := c) (m := m) hm P H
    (s := s) (t := s) le_rfl (by linarith : s ≤ s + 1) w
  simpa [H.S₀_zero] using h

/-- Fixed-parameter exponential evolution estimate. Its exponent contains the supplied `β`, so
when `CE` grows with the cylinder it is not the uniform mixed-return bound from manuscript A13. -/
theorem actualTrainEvolution_bound {ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (H : WeightedHeatStripSupplier (c := c) (m := m) hm)
    {s t : ℝ} (hst : s ≤ t) :
    ‖(actualTrainVolterraData hm P H).evolution t s‖ ≤
      (actualTrainVolterraData hm P H).evolutionBound *
        Real.exp (Real.log (actualTrainVolterraData hm P H).evolutionBound * (t - s)) :=
  (actualTrainVolterraData hm P H).norm_evolution_le hst

#print axioms actualTrainFluxB_eq_trainFlux
#print axioms actualTrainVolterra_compatible
#print axioms actualTrainEvolution_mild
#print axioms actualTrainEvolution_initial
#print axioms actualTrainEvolution_bound

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
