import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_1
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Spatial mollification converges in `L^p` on `(0,P] x B(0,R)` (decomposition)

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.
The localisation to the cell is proved here from the global statement `SpatMolGlobalLp`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

/-- Approximate identity in `y`: smooth, compactly supported, nonneg, integral one, support in the
ball of radius `1/(n+1)`. -/
def IsApproxId (ρ : ℕ → UnforcedLeray.Space → ℝ) : Prop :=
  ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧ (∀ y, 0 ≤ ρ n y) ∧ ∫ y, ρ n y = 1 ∧
    tsupport (ρ n) ⊆ Metric.closedBall 0 (1 / ((n : ℝ) + 1))

/-- Contraction: `‖spatMol ρ g‖_p ≤ ‖g‖_p` on `ℝ × ℝ³` for `ρ ≥ 0`, `∫ρ = 1`, `ρ` smooth with
compact support, `1 ≤ p < ∞` (Minkowski's integral inequality in `y'`; source 2562-2564). -/
def SpatMolContract : Prop :=
  ∀ (p : ENNReal), 1 ≤ p → p ≠ ⊤ → ∀ (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ →
    HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 →
    ∀ g : ℝ × UnforcedLeray.Space → ℂ, MemLp g p volume →
      eLpNorm (spatMol ρ g) p volume ≤ eLpNorm g p volume

/-- Convergence for continuous compactly supported `g` (uniform continuity: `spatMol (ρ n) g → g`
uniformly with supports in a fixed compact set). -/
def SpatMolContCompact : Prop :=
  ∀ (p : ENNReal), 1 ≤ p → p ≠ ⊤ → ∀ (ρ : ℕ → UnforcedLeray.Space → ℝ), IsApproxId ρ →
    ∀ g : ℝ × UnforcedLeray.Space → ℂ, Continuous g → HasCompactSupport g →
      Tendsto (fun n => eLpNorm (spatMol (ρ n) g - g) p volume) atTop (𝓝 0)

/-- Global `L^p` convergence of the `y`-mollification (density of `C_c` in `L^p`, `SpatMolContract`,
`SpatMolContCompact`, `ε/3` argument). -/
def SpatMolGlobalLp : Prop :=
  ∀ (p : ENNReal), 1 ≤ p → p ≠ ⊤ → ∀ (ρ : ℕ → UnforcedLeray.Space → ℝ), IsApproxId ρ →
    ∀ g : ℝ × UnforcedLeray.Space → ℂ, MemLp g p volume →
      Tendsto (fun n => eLpNorm (spatMol (ρ n) g - g) p volume) atTop (𝓝 0)

/-- Localisation: global convergence gives convergence on `(0,P] × B(0,R)`. -/
theorem spatMol_tendsto_lp_of (hG : SpatMolGlobalLp) (P : ℝ) [Fact (0 < P)] (R : ℝ) (p : ENNReal)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (f : ℝ × UnforcedLeray.Space → ℂ) (hf : MemLpLoc P f p)
    (ρ : ℕ → UnforcedLeray.Space → ℝ) (hρ : IsApproxId ρ) :
    Tendsto (fun n => eLpNorm (spatMol (ρ n) f - f) p
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R))))
      atTop (𝓝 0) := by
  set A : Set (ℝ × UnforcedLeray.Space) := Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 R with hAdef
  set A' : Set (ℝ × UnforcedLeray.Space) := Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 (R + 1) with hA'def
  have hA : MeasurableSet A := measurableSet_Ioc.prod Metric.isClosed_closedBall.measurableSet
  have hA' : MeasurableSet A' := measurableSet_Ioc.prod Metric.isClosed_closedBall.measurableSet
  have hμ : (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R))
      = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict A := by
    rw [hAdef, Measure.volume_eq_prod, Measure.prod_restrict]
  have hμ' : (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 (R + 1)))
      = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict A' := by
    rw [hA'def, Measure.volume_eq_prod, Measure.prod_restrict]
  have hft : MemLp (A'.indicator f) p volume := by
    rw [memLp_indicator_iff_restrict hA']
    rw [← hμ']; exact hf (R + 1)
  have hlim := hG p hp hp' ρ hρ _ hft
  rw [hμ]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    (fun n => ?_)
  refine le_trans (le_of_eq ?_) (eLpNorm_mono_measure (spatMol (ρ n) (A'.indicator f) - A'.indicator f) (Measure.restrict_le_self (s := A)))
  refine eLpNorm_congr_ae ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall ?_))
  rintro ⟨τ, y⟩ hx
  have hτ : τ ∈ Ioc (0 : ℝ) P := hx.1
  have hy : ‖y‖ ≤ R := by simpa using hx.2
  have hmem : (τ, y) ∈ A' := ⟨hτ, by simpa using hy.trans (by linarith)⟩
  have hsm : spatMol (ρ n) f (τ, y) = spatMol (ρ n) (A'.indicator f) (τ, y) := by
    unfold spatMol
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    show (ρ n y' : ℂ) * f (τ, y - y') = (ρ n y' : ℂ) * A'.indicator f (τ, y - y')
    by_cases h0 : ρ n y' = 0
    · simp [h0]
    · have hy' : y' ∈ tsupport (ρ n) := subset_tsupport _ (Function.mem_support.2 h0)
      have hb := (hρ n).2.2.2.2 hy'
      have hn : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have h1 : ‖y'‖ ≤ 1 := by simpa using hb.trans hn
      have h2 : ‖y - y'‖ ≤ R + 1 := (norm_sub_le _ _).trans (by linarith)
      rw [Set.indicator_of_mem (show (τ, y - y') ∈ A' from ⟨hτ, by simpa using h2⟩)]
  have hfi : f (τ, y) = A'.indicator f (τ, y) := (Set.indicator_of_mem hmem f).symm
  simp only [Pi.sub_apply, hsm, ← hfi]

end UnforcedLeray.Short.PartIIIb.Concrete
