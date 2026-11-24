import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Tasks.AdjointKernelOneDim

/-!
# Part I, task `PartI:S09` (`SeedFunctional`): decomposition

Source: `the November 2 reference manuscript`
lines 603-609 and 890-912.

* `SeedAdjPairing` (leaf `PartI:S09/1`): the explicit adjoint eigenvector `gd` (lines 890-912,
  `seedAdjEig`, S07) pairs with `f ∈ X_G` as `⟪gd, f⟫ = ∫₀^∞ h f / k r dr`, the integral converging.
* `SeedQuotientSmooth` (leaf `PartI:S09/2`): the smoothness/decay clause (lines 606-609).
* `seedFunctional_of`: Riesz representation + S08 (`adjoint_eigenvector_unique`) + normalization
  `ℓ q = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- Leaf `PartI:S09/1` (lines 890-912, 603-607).  For a seed triple, the adjoint eigenvector `gd`
(`gd = (4π)⁻¹ Ω conj(φ)/(Ω - conj c) e^{2iϑ}`, `φ = greenN 2 h`, `c = iλ/2`, i.e. `seedAdjEig` of
`PartI:S07`) satisfies `⟪gd, f⟫ = ∫₀^∞ h f / k r dr` for every `f ∈ X_G`, the integral converging
absolutely.  Proof: `conj(gd r)·xGDensity r = φ/(Ω - c)·r = h/k·r` a.e. (eigen equation
`(Ω - c) h = k φ`, `k = strainK = radialK`, `xGDensity = (4π Ω⁻¹) r`), then `L2.integrable_inner`
and `B0094.integral_xGMeasure`. -/
def SeedAdjPairing : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ →
      ∃ gd : B0010.XG, ContinuousLinearMap.adjoint Planar.L0 gd = (starRingEnd ℂ) lam • gd ∧
        gd ≠ 0 ∧
        ∀ f : B0010.XG,
          IntegrableOn (fun r : ℝ => h r * (f : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ))
            (Ioi 0) volume ∧
          inner ℂ gd f =
            ∫ r in Ioi (0 : ℝ), h r * (f : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ)

/-- Leaf `PartI:S09/2` (lines 606-609): for smooth `h`, `h/k` extends smoothly across the zero
`r = √8` of `k` and is `O(r⁻²)`.  Proof: `g := φ/(Ω - c)` with `φ = greenN 2 h` smooth on `(0,∞)`
and `Ω - c ≠ 0` since `Im c ≠ 0`; `(Ω - c) h = k φ` a.e. (`adjEig_pointwise`) holds everywhere on
`(0,∞)` by continuity, so `g = h/k` where `k ≠ 0`; decay from `G.far_field`/`|φ| ≤ C r⁻²`. -/
def SeedQuotientSmooth : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ContDiffOn ℝ ∞ h (Ioi 0) →
      ∃ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) ∧
        (∀ r : ℝ, 0 < r → Blueprint.Planar.strainK r ≠ 0 →
          g r = h r / (Blueprint.Planar.strainK r : ℂ)) ∧
        ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖g r‖ ≤ C / r ^ 2

/-- `SeedFunctional` from the two leaves. -/
theorem seedFunctional_of (h1 : SeedAdjPairing) (h2 : SeedQuotientSmooth) : SeedFunctional := by
  intro lam h hh ℓ hI
  obtain ⟨gd, hgd, hgd0, hpair⟩ := h1 lam h hh ℓ hI
  set q : B0010.XG := hh.toLp h with hqdef
  set qd : B0010.XG := (InnerProductSpace.toDual ℂ B0010.XG).symm ℓ with hqd'
  have hqd : ∀ f, ℓ f = inner ℂ qd f := fun f => InnerProductSpace.toDual_symm_apply.symm
  obtain ⟨μ, hμ⟩ := adjoint_eigenvector_unique hI hqd hgd
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hgd0 (by simpa using hμ)
  have hqdμ : qd = μ⁻¹ • gd := by
    rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  set m : ℂ := (starRingEnd ℂ) μ⁻¹ with hm
  have hℓ : ∀ f : B0010.XG, ℓ f = m *
      ∫ r in Ioi (0 : ℝ), h r * (f : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) := by
    intro f
    rw [hqd f, hqdμ, inner_smul_left, (hpair f).2]
  have hq : (⇑q : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hint2 : IntegrableOn
      (fun r : ℝ => h r ^ 2 / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ)) (Ioi 0) volume := by
    refine ((hpair q).1).congr ?_
    filter_upwards [hq] with r hr
    rw [hr]; ring
  have hJ : seedJ h = ∫ r in Ioi (0 : ℝ),
      h r * (q : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) := by
    unfold seedJ
    refine integral_congr_ae ?_
    filter_upwards [hq] with r hr
    rw [hr]; ring
  have hone : m * seedJ h = 1 := by
    rw [hJ, ← hℓ q]; exact hI.ell_q
  have hJ0 : seedJ h ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hone; exact zero_ne_one hone
  have hmJ : m = (seedJ h)⁻¹ := eq_inv_of_mul_eq_one_left hone
  refine ⟨hJ0, hint2, fun f => (hpair f).1, fun f => ?_, h2 lam h hh ℓ hI⟩
  rw [hℓ f, hmJ]; rfl

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.seedFunctional_of
