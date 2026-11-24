import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartI.Compose

/-!
# Part III-a, task `PartIII-a:T21/c1/a`: planar frame kernels from the Part I seed

Source: `the November 2 reference manuscript`, lines 593-610 (seed, functional
`eq:short-seed-functional`) and 2891-2897 (planar frame kernels).

`planarFrameKernelsExist_of` assembles `PlanarFrameKernelsExist` from the Part I leaves
`SeedModeRegularity`, `SeedFunctional` (open tasks) and four leaf statements below.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (smooth representative with Gaussian decay; lines 593-601).  From the regularity
statement `SeedModeRegularity` and `SeedXGExists`: a growing triple whose profile `h` is itself
smooth (as `seedPlanar h` and as a function on `(0,∞)`) and whose planar mode has the
Gaussian bound of order `k = 0`.  (Replace `h` by the smooth representative `h'`, which agrees
a.e. for `xGMeasure`; `ContDiffOn h (Ioi 0)` follows from smoothness of `seedPlanar h` by
restricting to the positive real axis.) -/
def SeedSmoothRep : Prop :=
  PartI.SeedModeRegularity → PartI.SeedXGExists →
    ∃ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h) ℓ ∧ ContDiff ℝ ∞ (PartI.seedPlanar h) ∧
      ContDiffOn ℝ ∞ h (Ioi 0) ∧
      ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
        ‖PartI.seedPlanar h y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)

/-- **Leaf 2** (polynomial-times-Gaussian is bounded by a Gaussian of half the exponent). -/
def SeedGaussHalf : Prop :=
  ∀ h : ℝ → ℂ, (∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
        ‖PartI.seedPlanar h y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) →
      ∃ C : ℝ, ∀ y : ℝ × ℝ,
        ‖PartI.seedPlanar h (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)

/-- **Leaf 3** (the dual kernel `λ_0 = J_q⁻¹ (h/k)(|y|) e^{-2iϑ}/(2π)`, `λ_1` its conjugate;
lines 601-610, 2891-2897).  Continuous (the quotient `h/k` is smooth with `h = O(r²)` at `0`),
`O(|y|⁻²)` (the `g` of `SeedFunctional`), and representing `ℓ` on the two sectors for smooth
compactly supported `f` by polar coordinates. -/
def SeedDualKernel : Prop :=
  PartI.SeedFunctional →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ → ContDiff ℝ ∞ (PartI.seedPlanar h) →
    ContDiffOn ℝ ∞ h (Ioi 0) →
    ∃ lamP : Fin 2 → ℝ × ℝ → ℂ, (∀ i, Continuous (lamP i)) ∧
      (∃ C : ℝ, ∀ i y, ‖lamP i y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2) ∧
      ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, lamP 0 y * f (planeToC y) =
            PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, lamP 1 y * f (planeToC y) =
            conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))

/-- **Leaf 4** (biorthogonality: extension of the sector identities from compactly supported `f`
to the Gaussian modes `e_0 = q`, `e_1 = \bar q`, using `ℓ f = seedEll h f` on `X_G`
(`SeedFunctional`), `ℓ q = 1`, and orthogonality of the sectors `±2`). -/
def SeedBiorth : Prop :=
  PartI.SeedFunctional →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ → ContDiff ℝ ∞ (PartI.seedPlanar h) →
    (∃ C : ℝ, ∀ y : ℝ × ℝ,
        ‖PartI.seedPlanar h (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
    ∀ lamP : Fin 2 → ℝ × ℝ → ℂ, (∀ i, Continuous (lamP i)) →
      (∃ C : ℝ, ∀ i y, ‖lamP i y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2) →
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, lamP 0 y * f (planeToC y) =
            PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, lamP 1 y * f (planeToC y) =
            conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) →
      ∀ i j : Fin 2, ∫ y, lamP i y * (if j = 0 then PartI.seedPlanar h (planeToC y)
          else conj (PartI.seedPlanar h (planeToC y))) = if i = j then 1 else 0

theorem planarFrameKernelsExist_of (hMR : PartI.SeedModeRegularity) (hSF : PartI.SeedFunctional)
    (l1 : SeedSmoothRep) (l2 : SeedGaussHalf) (l3 : SeedDualKernel) (l4 : SeedBiorth) :
    PlanarFrameKernelsExist := by
  obtain ⟨lam, h, hh, ℓ, hS, hsm, hon, hdec⟩ := l1 hMR PartI.seedXGExists
  obtain ⟨CG, hCG⟩ := l2 h hdec
  obtain ⟨lamP, hc, hd, hcl⟩ := l3 hSF lam h hh ℓ hS hsm hon
  have hb := l4 hSF lam h hh ℓ hS hsm ⟨CG, hCG⟩ lamP hc hd hcl
  let e : Fin 2 → ℝ × ℝ → ℂ := fun j y =>
    if j = 0 then PartI.seedPlanar h (planeToC y) else conj (PartI.seedPlanar h (planeToC y))
  have hcont : Continuous fun y : ℝ × ℝ => PartI.seedPlanar h (planeToC y) := by
    refine hsm.continuous.comp ?_
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_id |>.congr (fun y => rfl)
  refine ⟨⟨e, lamP, ?_, hc, ?_, hd, ?_⟩, lam, h, hh, ℓ, hS, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · simp only [e, hi, if_true]; exact hcont
    · simp only [e, hi, if_false]; exact (Complex.continuous_conj.comp hcont)
  · refine ⟨CG, fun i y => ?_⟩
    by_cases hi : i = 0
    · simp only [e, hi, if_true]; exact hCG y
    · simp only [e, hi, if_false, Complex.norm_conj]; exact hCG y
  · intro i j
    have := hb i j
    simpa [e] using this
  · intro y; rfl
  · intro y; rfl
  · exact hcl

end UnforcedLeray.Short.IIIa
