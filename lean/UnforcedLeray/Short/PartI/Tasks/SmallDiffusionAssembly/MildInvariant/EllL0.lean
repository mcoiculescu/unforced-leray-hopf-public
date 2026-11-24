import UnforcedLeray.Short.PartI.Sub.PartI_C05_4

/-!
# Target `PartI:C05/4/1`: the left eigenfunctional identity `ℓ(L₀ y) = λ ℓ(y)`

Source of record: `the November 2 reference manuscript`, lines 970-975, 1056-1058.
From `IsSeedXG.proj`, the Riesz projection `P = rankOneProj ℓ q` satisfies `P L₀ = λ P`.
Applying this to `y` and then `ℓ`, with `ℓ q = 1`, gives `ℓ(L₀ y) = λ ℓ y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Infra.Dunford (rankOneProj IsSimpleSpectralProj)

theorem mildEllL0 : MildEllL0 := by
  intro lam q l hI y
  have h := congrArg (fun T : B0010.XG →L[ℂ] B0010.XG => T y) hI.proj.proj_mul
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h
  have h2 := congrArg (fun v : B0010.XG => l v) h
  simp only [Infra.Dunford.rankOneProj_apply, map_smul, hI.ell_q, smul_eq_mul, mul_one] at h2
  exact h2
