import UnforcedLeray.Analysis.Sturm.CompactL2
import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Continuous test pairings and closed weak derivative relations in L²

Pairing an L² equivalence class against an L² function is a continuous
complex-linear functional. Consequently, every distributional derivative
relation defined by smooth compactly supported tests is closed in L² × L².
These statements permit the actual Green equation to pass to L² limits.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace UnforcedLeray.Sturm

open NonUniqueEuler.Sob

/-- Bilinear integral pairing with a fixed L² function, as a continuous
complex-linear functional on the actual Lebesgue L² space. -/
def l2Pairing (φ : ℝ → ℂ) (hφ : MemLp φ 2 (volume : Measure ℝ)) :
    ComplexL2 →L[ℂ] ℂ :=
  innerSL ℂ (hφ.star.toLp (star φ))

theorem integrable_mul_l2 (φ : ℝ → ℂ) (hφ : MemLp φ 2 (volume : Measure ℝ))
    (f : ComplexL2) : Integrable (fun x => f x * φ x) := by
  exact (Lp.memLp f).integrable_mul hφ

theorem l2Pairing_apply (φ : ℝ → ℂ) (hφ : MemLp φ 2 (volume : Measure ℝ))
    (f : ComplexL2) : l2Pairing φ hφ f = ∫ x, f x * φ x := by
  simp only [l2Pairing, innerSL_apply_apply, L2.inner_def, RCLike.inner_apply]
  apply integral_congr_ae
  filter_upwards [hφ.star.coeFn_toLp] with x hx
  simp only [hx, Pi.star_apply, starRingEnd_apply, star_star]

/-- Smooth compactly supported tests, including all their directional
derivatives, belong to L². -/
theorem testFn_memLp {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) :
    MemLp φ 2 (volume : Measure ℝ) :=
  hφ.continuous.memLp_of_hasCompactSupport hφ.compact

def testPairing (φ : ℝ → ℂ) (hφ : IsTestFn univ φ) : ComplexL2 →L[ℂ] ℂ :=
  l2Pairing φ (testFn_memLp hφ)

theorem testPairing_apply (φ : ℝ → ℂ) (hφ : IsTestFn univ φ) (f : ComplexL2) :
    testPairing φ hφ f = ∫ x, f x * φ x :=
  l2Pairing_apply φ (testFn_memLp hφ) f

/-- Any fixed iterated weak derivative relation is closed when both the
function and its derivative converge in L². -/
theorem isClosed_hasWeakDerivOn (vs : List ℝ) :
    IsClosed {p : ComplexL2 × ComplexL2 |
      HasWeakDerivOn univ vs (p.1 : ℝ → ℂ) (p.2 : ℝ → ℂ)} := by
  have heq : {p : ComplexL2 × ComplexL2 |
      HasWeakDerivOn univ vs (p.1 : ℝ → ℂ) (p.2 : ℝ → ℂ)} =
      ⋂ (φ : ℝ → ℂ) (hφ : IsTestFn univ φ),
        {p : ComplexL2 × ComplexL2 |
          testPairing (iterDirDeriv vs φ) (hφ.iterDirDeriv vs) p.1 =
            (-1 : ℂ) ^ vs.length * testPairing φ hφ p.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, HasWeakDerivOn, testPairing_apply]
  rw [heq]
  refine isClosed_iInter fun φ => isClosed_iInter fun hφ => ?_
  exact isClosed_eq
    ((testPairing (iterDirDeriv vs φ) (hφ.iterDirDeriv vs)).continuous.comp continuous_fst)
    (continuous_const.mul ((testPairing φ hφ).continuous.comp continuous_snd))

theorem isClosed_weakDerivative :
    IsClosed {p : ComplexL2 × ComplexL2 |
      HasWeakDerivOn univ (derivList 1) (p.1 : ℝ → ℂ) (p.2 : ℝ → ℂ)} :=
  isClosed_hasWeakDerivOn (derivList 1)

/-- Weak derivative relations between continuous L²-valued maps define a
closed set in their source. -/
theorem isClosed_hasWeakDerivOn_precomp {X : Type*} [TopologicalSpace X]
    (vs : List ℝ) {u v : X → ComplexL2} (hu : Continuous u) (hv : Continuous v) :
    IsClosed {x : X | HasWeakDerivOn univ vs (u x : ℝ → ℂ) (v x : ℝ → ℂ)} :=
  (isClosed_hasWeakDerivOn vs).preimage (hu.prodMk hv)

end UnforcedLeray.Sturm
