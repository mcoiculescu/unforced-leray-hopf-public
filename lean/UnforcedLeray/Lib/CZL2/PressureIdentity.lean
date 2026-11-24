import UnforcedLeray.Lib.CZL2.TestProjection

/-!
# The Newton pressure identity `∇p = -(I - 𝔓) f` (INF01 level L0, target T5)

Blueprint: INF01 target T5 (scoping note `INF01-CZ.md` §4.1, §5); decision D6 of
`scoping/README.md` §3; unit B1032 (`paper/main.tex` lines 559–561, outline step 1:
"add ∇p to the projected equation, using `(I - 𝔓)div(u⊗u) = -∇Σ R_iR_k(u_iu_k)`"),
with the pressure convention of lines 107–111 and the pressure of B1031
(lines 552–558) replaced by the compiled Newton pressure
(`PressureAnalysis.velocityPressure`, `Pressure/Spatial.lean:27`), as D6 decides.

For a forcing `F = (F₁, F₂, F₃)` with `Fᵢ ∈ L¹ ∩ L²` and the compiled Newton pressure
`p = Σᵢ ∂ᵢN ∗ Fᵢ`, we prove, for every compact smooth vector test `φ`,

  `∫ p div φ = ⟨(I - 𝔓) F, φ⟩_{L²}`,

where `𝔓` is the compiled orthogonal Leray projection (`LerayProjection/Basic.lean`).
That is, `∇p = -(I - 𝔓)F` in distributions, equivalently `F + ∇p = 𝔓F`.
The specialisation `velocityPressure_pressure_identity` takes `F = (u·∇)u`
(`PressureAnalysis.velocityForcing`), for `u, ∂ᵢu ∈ L²` with `(u·∇)u ∈ L²`.

Proof: Fubini (`integral_newtonComponent_mul_test`) moves the kernel onto the test,
`∫ ∂ᵢN(x - y) div φ(x) dx = -∂ᵢψ(y)` with `ψ = N ∗ div φ`, and the test-level identity
`(I - 𝔓)φ = -∇ψ` (`toL2_sub_projection_vecField`) together with the self-adjointness of
`𝔓` identifies the right side. No Riesz transform, Fourier multiplier or
Calderón–Zygmund estimate is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- The Newton pressure `Σᵢ ∂ᵢN ∗ Fᵢ` of a forcing with components `Fᵢ`
(`velocityPressure u g = newtonPressure (velocityForcing u g)`). -/
def newtonPressure (F : Fin 3 → Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, newtonComponent i (F i) x

theorem velocityPressure_eq_newtonPressure (u : SpatialField) (g : Fin 3 → SpatialField) :
    velocityPressure u g = newtonPressure (velocityForcing u g) := rfl

/-- The L² class of the convective forcing `(u·∇)u` (its components are
`PressureAnalysis.velocityForcing u g i`). Meaningful under `MemLp` of the components. -/
def forcingL2 (u : SpatialField) (g : Fin 3 → SpatialField) : L2Space :=
  toL2 (vecField (velocityForcing u g))

theorem memLp_vecField_of_components {F : Fin 3 → Space → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) : MemLp (vecField F) 2 volume := by
  have he : vecField F = ∑ i : Fin 3, fun x =>
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector i)) (F i x) := by
    funext x; simp [vecField]
  rw [he]
  exact memLp_finsetSum' _ fun i _ => (hF i).continuousLinearMap_comp _

/-- The real inner product of `Σᵢ Fᵢ eᵢ` with `∇ψ`. -/
theorem inner_vecField_gradField (F : Fin 3 → Space → ℝ) (ψ : Space → ℝ) (x : Space) :
    inner ℝ (vecField F x) (gradField ψ x) =
      ∑ i : Fin 3, F i x * spatialTestDerivative i ψ x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecField_apply, gradField_apply, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- **Newton pressure identity** (generic forcing). If `Fᵢ ∈ L¹ ∩ L²`, then for every compact
smooth vector test `φ`,
`∫ (Σᵢ ∂ᵢN ∗ Fᵢ) div φ = ⟨F - 𝔓F, φ⟩`, i.e. `∇p = -(I - 𝔓)F` weakly. -/
theorem newtonPressure_identity {F : Fin 3 → Space → ℝ}
    (hF1 : ∀ i, Integrable (F i) volume) (hF2 : ∀ i, MemLp (F i) 2 volume)
    (φ : Space → Space) (hφ : ∀ j, IsSpatialTest (fun x => φ x j)) :
    ∫ x, newtonPressure F x * (∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x) =
      ∫ x, inner ℝ ((toL2 (vecField F) - Leray.projection (toL2 (vecField F))) x) (φ x) := by
  set f : Fin 3 → Space → ℝ := fun j x => φ x j with hfdef
  have hf : ∀ j, IsSpatialTest (f j) := hφ
  have hh := isSpatialTest_divTest hf
  set ψ := lerayPotential f with hψdef
  have hψ : ContDiff ℝ ∞ ψ := lerayPotential_contDiff hf
  have hφeq : vecField f = φ := vecField_components φ
  have hFv := memLp_vecField_of_components hF2
  have hφm : MemLp φ 2 volume := hφeq ▸ memLp_vecField hf 2
  have hW := memLp_gradField_lerayPotential hf
  -- each `∂ᵢψ` is in L²
  obtain ⟨M, -, hM⟩ := lerayPotential_decay hf
  have hdψ : ∀ i, MemLp (spatialTestDerivative i ψ) 2 volume := fun i =>
    memLp_two_of_norm_le (contDiff_spatialTestDerivative hψ i).continuous.aestronglyMeasurable
      (M := M) fun y => (Real.norm_eq_abs _).trans_le (hM i y)
  have hprod : ∀ i, Integrable (fun x => F i x * spatialTestDerivative i ψ x) volume := fun i =>
    memLp_one_iff_integrable.mp ((hdψ i).mul' (hF2 i))
  -- left side
  have hL : ∫ x, newtonPressure F x * (∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x)
      = -∑ i : Fin 3, ∫ x, F i x * spatialTestDerivative i ψ x := by
    have hint : ∀ i, Integrable (fun x => newtonComponent i (F i) x * divTest f x) volume :=
      fun i => newtonComponent_mul_test_integrable i (hF1 i) hh
    simp only [newtonPressure, Finset.sum_mul]
    change ∫ x, ∑ i : Fin 3, newtonComponent i (F i) x * divTest f x = _
    rw [integral_finsetSum _ fun i _ => hint i, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_newtonComponent_mul_test i (hF1 i) hh, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have h := spatialTestDerivative_lerayPotential hf i y
    change F i y * newtonPair i (divTest f) y = -(F i y * spatialTestDerivative i ψ y)
    rw [h]
    ring
  -- right side
  have hR : ∫ x, inner ℝ ((toL2 (vecField F) - Leray.projection (toL2 (vecField F))) x) (φ x)
      = -∑ i : Fin 3, ∫ x, F i x * spatialTestDerivative i ψ x := by
    set A := toL2 (vecField F)
    have h1 : ∫ x, inner ℝ ((A - Leray.projection A) x) (φ x) =
        inner ℝ (A - Leray.projection A) (toL2 φ) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toL2 hφm] with x hx
      rw [hx]
    have h2 : inner ℝ (A - Leray.projection A) (toL2 φ) =
        inner ℝ A (toL2 φ - Leray.projection (toL2 φ)) := by
      rw [inner_sub_left, inner_sub_right, Leray.projection_selfadjoint]
    have h3 : toL2 φ - Leray.projection (toL2 φ) = -toL2 (gradField ψ) := by
      rw [← hφeq]
      exact toL2_sub_projection_vecField hf
    have h4 : inner ℝ A (toL2 (gradField ψ)) =
        ∑ i : Fin 3, ∫ x, F i x * spatialTestDerivative i ψ x := by
      rw [L2.inner_def, ← integral_finsetSum _ fun i _ => hprod i]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toL2 hFv, coeFn_toL2 hW] with x hx1 hx2
      rw [hx1, hx2, inner_vecField_gradField]
    rw [h1, h2, h3, inner_neg_right, h4]
  rw [hL, hR]

/-- **INF01 T5 (decision D6, input to B1032).** For `u ∈ L²` with `L²` coordinate
derivatives `g` and convective forcing `(u·∇)u ∈ L²` (componentwise), the compiled Newton
pressure `p = velocityPressure u g` satisfies, for every compact smooth vector test `φ`,

  `∫ p div φ = ⟨(u·∇)u - 𝔓((u·∇)u), φ⟩_{L²}`,

i.e. `∇p = -(I - 𝔓)((u·∇)u)` in distributions (`paper/main.tex` lines 107–111, 559–561).
The weak-derivative relation between `u` and `g` is not needed for this identity. -/
theorem velocityPressure_pressure_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hf2 : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (φ : Space → Space) (hφ : ∀ j, IsSpatialTest (fun x => φ x j)) :
    ∫ x, velocityPressure u g x * (∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x) =
      ∫ x, inner ℝ ((forcingL2 u g - Leray.projection (forcingL2 u g)) x) (φ x) :=
  newtonPressure_identity (fun i => memLp_one_iff_integrable.mp (velocityForcing_memLp_one hu hg i))
    hf2 φ hφ

/-- Equivalent form `(u·∇)u + ∇p = 𝔓((u·∇)u)` weakly: for every compact smooth vector test
`φ`, `∫ (u·∇)u · φ - ∫ p div φ = ⟨𝔓((u·∇)u), φ⟩_{L²}`. -/
theorem velocityPressure_projected_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hf2 : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (φ : Space → Space) (hφ : ∀ j, IsSpatialTest (fun x => φ x j)) :
    (∫ x, ∑ i : Fin 3, velocityForcing u g i x * φ x i) -
        ∫ x, velocityPressure u g x * (∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x) =
      ∫ x, inner ℝ ((Leray.projection (forcingL2 u g)) x) (φ x) := by
  have hFv := memLp_vecField_of_components hf2
  have hφm : MemLp φ 2 volume := vecField_components φ ▸ memLp_vecField hφ 2
  rw [velocityPressure_pressure_identity hu hg hf2 φ hφ]
  set A := forcingL2 u g
  have hA : (A : SpatialField) =ᵐ[volume] vecField (velocityForcing u g) := coeFn_toL2 hFv
  have h1 : ∫ x, ∑ i : Fin 3, velocityForcing u g i x * φ x i = inner ℝ A (toL2 φ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA, coeFn_toL2 hφm] with x hx1 hx2
    rw [hx1, hx2, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vecField_apply, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  have h2 : ∀ B : L2Space, ∫ x, inner ℝ (B x) (φ x) = inner ℝ B (toL2 φ) := fun B => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hφm] with x hx
    rw [hx]
  rw [h1, h2, h2, inner_sub_left, sub_sub_cancel]

end UnforcedLeray.RieszLp
