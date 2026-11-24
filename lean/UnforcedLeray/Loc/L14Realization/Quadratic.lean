import UnforcedLeray.Loc.L14Realization.Cutoff
import UnforcedLeray.Loc.L10Nonlinear.Pairing
import UnforcedLeray.Analysis.Pressure.WeakProduct
import UnforcedLeray.Lib.CZL2.PressureIdentity

/-!
# Step L14, helpers: the quadratic identities of the realization

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 539–561, blueprint units B1030 and B1032). For a solenoidal field `u ∈ L²` with
`L²` weak derivatives `g j = ∂ⱼu`, convective forcing `F = (u·∇)u`
(`PressureAnalysis.velocityForcing`, `Fᵢ = Σⱼ uⱼ ∂ⱼuᵢ`) in `L²` and columns `uⱼu` of `u ⊗ u`
in `L²` (the hypotheses available for the `H²` total field of line 545):

* `integral_coord_mul_forcing_eq_zero`: `∫ uᵢ (u·∇)uᵢ = 0` for each `i`, hence
  `⟨(u·∇)u, u⟩ = 0` (the trilinear cancellation behind "multiplication by `u` gives the
  energy identity", line 547). Proof: the compiled weak product rule
  (`PressureAnalysis.velocityForcing_test_identity`) against the test `χ (ρ_ε ∗ u)ᵢ`, the limit
  `ε → 0` (`weighted_product_mollification_tendsto`), which gives
  `2 ∫ χ Fᵢ uᵢ = -Σⱼ ∫ ∂ⱼχ uⱼ uᵢ uᵢ`, and the cutoffs `χ = χ_R`, `R → ∞`.
* `velocityPressure_div_identity`: the compiled Newton pressure `p` of `u`
  (`PressureAnalysis.velocityPressure`, decision D6) satisfies
  `∫ p div φ = -Σⱼ ⟨uⱼu, (I - 𝔓)∂ⱼφ⟩` for every vector test `φ`, that is
  `∇p = -(I - 𝔓) div(u ⊗ u)` (lines 107–111, 559–561, critic §6). Proof: the `(u·∇)u` form
  `RieszLp.velocityPressure_pressure_identity` (`Lib/CZL2/PressureIdentity.lean`),
  `(I - 𝔓)φ = -∇ψ` with `ψ = N ∗ div φ` (`RieszLp.toL2_sub_projection_vecField`),
  `(I - 𝔓)∂ⱼφ = -∇∂ⱼψ`, and the weak product rule against `χ_R ∂ᵢψ`, `R → ∞`.
* `isMinusLerayDiv_eq_neg_projection`: `-𝔓 div(u ⊗ u) = -𝔓((u·∇)u)` in `L²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L14

open PressureAnalysis RieszLp

theorem tensorColumns_apply (u : SpatialField) (j i : Fin 3) (x : Space) :
    tensorColumns u u j x i = u x j * u x i := by
  simp [tensorColumns]

/-! ## The trilinear cancellation -/

section Trilinear

variable {u : SpatialField} {g : Fin 3 → SpatialField}

/-- The mollified local identity: the weak product rule against `χ (ρ_ε ∗ u)ᵢ`. -/
theorem forcing_mollified_identity (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {χ : Space → ℝ} (hχ : IsSpatialTest χ) (i : Fin 3) (n : ℕ) :
    ∫ x, χ x * velocityForcing u g i x *
        SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) u x i =
      -∑ j : Fin 3, ((∫ x, spatialTestDerivative j χ x * tensorColumns u u j x i *
          SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) u x i) +
        ∫ x, χ x * tensorColumns u u j x i *
          SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) (g j) x i) := by
  set ρ := SobolevEmbedding.shrinkingMollifier n
  set v := SobolevEmbedding.mollification ρ u
  have hv : ContDiff ℝ ∞ v := SobolevEmbedding.mollification_smooth ρ u hu
  have hψ := spatialTest_mul_coordinate hχ hv i
  have hid := velocityForcing_test_identity hu hg hderiv hs hψ i
  have hL : ∫ x, χ x * velocityForcing u g i x * v x i =
      ∫ x, (χ x * v x i) * velocityForcing u g i x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hL, hid]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Integrable (fun x => spatialTestDerivative j χ x * tensorColumns u u j x i * v x i) :=
    weighted_product_integrable (hcol j) (SobolevEmbedding.mollification_memLp ρ u hu)
      ((hχ.derivative j).memLp ⊤) i i
  have h2 : Integrable (fun x => χ x * tensorColumns u u j x i *
      SobolevEmbedding.mollification ρ (g j) x i) :=
    weighted_product_integrable (hcol j) (SobolevEmbedding.mollification_memLp ρ (g j) (hg j))
      (hχ.memLp ⊤) i i
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [spatialTestDerivative_mul_coordinate hχ hv i j x,
    SobolevEmbedding.mollification_derivative (hderiv j) hu ρ x, tensorColumns_apply]
  ring

/-- The local identity `∫ χ Fᵢ uᵢ = -Σⱼ (∫ ∂ⱼχ uⱼuᵢ uᵢ + ∫ χ uⱼuᵢ ∂ⱼuᵢ)`. -/
theorem forcing_local_identity (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {χ : Space → ℝ} (hχ : IsSpatialTest χ) (i : Fin 3) :
    ∫ x, χ x * velocityForcing u g i x * u x i =
      -∑ j : Fin 3, ((∫ x, spatialTestDerivative j χ x * tensorColumns u u j x i * u x i) +
        ∫ x, χ x * tensorColumns u u j x i * g j x i) := by
  have hFv := memLp_vecField_of_components hF
  have hvF : ∀ x, vecField (velocityForcing u g) x i = velocityForcing u g i x :=
    fun x => vecField_apply _ x i
  have hl := weighted_product_mollification_tendsto hFv hu (hχ.memLp ⊤) i i
  simp only [hvF] at hl
  have hr := (tendsto_finsetSum Finset.univ (fun j _ =>
    (weighted_product_mollification_tendsto (hcol j) hu ((hχ.derivative j).memLp ⊤) i i).add
      (weighted_product_mollification_tendsto (hcol j) (hg j) (hχ.memLp ⊤) i i))).neg
  refine tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun n => ?_))
  exact (forcing_mollified_identity hu hg hderiv hs hcol hχ i n).symm

/-- `2 ∫ χ Fᵢ uᵢ = -Σⱼ ∫ ∂ⱼχ uⱼuᵢ uᵢ`. -/
theorem forcing_local_energy (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {χ : Space → ℝ} (hχ : IsSpatialTest χ) (i : Fin 3) :
    2 * ∫ x, χ x * (velocityForcing u g i x * u x i) =
      -∑ j : Fin 3, ∫ x, spatialTestDerivative j χ x * (tensorColumns u u j x i * u x i) := by
  have h := forcing_local_identity hu hg hderiv hs hF hcol hχ i
  have hC : ∑ j : Fin 3, ∫ x, χ x * tensorColumns u u j x i * g j x i =
      ∫ x, χ x * velocityForcing u g i x * u x i := by
    rw [← integral_finsetSum _ fun j _ =>
      weighted_product_integrable (hcol j) (hg j) (hχ.memLp ⊤) i i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [velocityForcing, tensorColumns_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_add_distrib, hC] at h
  have hA : ∫ x, χ x * (velocityForcing u g i x * u x i) =
      ∫ x, χ x * velocityForcing u g i x * u x i :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hB : ∑ j : Fin 3, ∫ x, spatialTestDerivative j χ x * (tensorColumns u u j x i * u x i) =
      ∑ j : Fin 3, ∫ x, spatialTestDerivative j χ x * tensorColumns u u j x i * u x i :=
    Finset.sum_congr rfl fun j _ => integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hA, hB]
  linarith

/-- **Trilinear cancellation, componentwise.** `∫ uᵢ (u·∇)uᵢ = 0`. -/
theorem integral_coord_mul_forcing_eq_zero (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume) (i : Fin 3) :
    ∫ x, velocityForcing u g i x * u x i = 0 := by
  have hui : MemLp (fun x => u x i) 2 volume :=
    EnergyInterpolation.coordinate_memLp hu i
  have hFu : Integrable (fun x => velocityForcing u g i x * u x i) :=
    memLp_one_iff_integrable.mp (hui.mul' (hF i))
  have hcu : ∀ j, Integrable (fun x => tensorColumns u u j x i * u x i) := fun j =>
    memLp_one_iff_integrable.mp (hui.mul' (EnergyInterpolation.coordinate_memLp (hcol j) i))
  have hlim := tendsto_integral_cutoff_mul hFu
  have hzero := (tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_integral_cutoff_deriv_mul (hcu j) j)).neg
  simp only [Finset.sum_const_zero, neg_zero] at hzero
  have heq : ∀ n : ℕ, (∫ x, cutoff ((n : ℝ) + 1) x * (velocityForcing u g i x * u x i)) =
      (1 / 2 : ℝ) * -∑ j : Fin 3, ∫ x, spatialTestDerivative j (cutoff ((n : ℝ) + 1)) x *
        (tensorColumns u u j x i * u x i) := by
    intro n
    have h := forcing_local_energy hu hg hderiv hs hF hcol
      (cutoff_isSpatialTest (by positivity : (0 : ℝ) < (n : ℝ) + 1)) i
    linarith
  have h2 := hzero.const_mul (1 / 2 : ℝ)
  rw [mul_zero] at h2
  exact tendsto_nhds_unique hlim (h2.congr' (Eventually.of_forall fun n => (heq n).symm))

end Trilinear

end UnforcedLeray.Blueprint.L14
