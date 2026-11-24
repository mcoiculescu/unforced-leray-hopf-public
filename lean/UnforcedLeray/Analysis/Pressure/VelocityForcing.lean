import UnforcedLeray.Analysis.SobolevEmbedding.H1
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# The actual convective forcing of a weak H¹ velocity

For each component, the function is the sum of the velocity components times
its genuine weak coordinate derivatives. Hölder gives L¹ and L^(3/2)
membership, and the proved homogeneous Sobolev inequality supplies the latter
bound entirely in terms of the L² weak derivatives. No pressure operator or
product rule is assumed here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace UnforcedLeray.PressureAnalysis

/-- The actual component of `(u · ∇)u` from a field and its coordinate derivatives. -/
def velocityForcing (u : SpatialField) (g : Fin 3 → SpatialField) (i : Fin 3) :
    Space → ℝ := fun x => ∑ j : Fin 3, u x j * g j x i

private theorem coordinate_memLp {f : SpatialField} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (i : Fin 3) : MemLp (fun x => f x i) p volume :=
  hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)

private theorem eLpNorm_coordinate_le (f : SpatialField) (p : ℝ≥0∞) (i : Fin 3) :
    eLpNorm (fun x => f x i) p volume ≤ eLpNorm f p volume :=
  eLpNorm_mono (fun x => PiLp.norm_apply_le (f x) i)

/-- Hölder gives actual membership of the finite convective sum. -/
theorem velocityForcing_memLp {u : SpatialField} {g : Fin 3 → SpatialField}
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hu : MemLp u p volume) (hg : ∀ j, MemLp (g j) q volume) (i : Fin 3) :
    MemLp (velocityForcing u g i) r volume := by
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (coordinate_memLp (hg j) i).mul' (coordinate_memLp hu j))

/-- The triangle inequality and Hölder retain constant one for each component. -/
theorem velocityForcing_eLpNorm_le {u : SpatialField} {g : Fin 3 → SpatialField}
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hu : MemLp u p volume) (hg : ∀ j, MemLp (g j) q volume)
    (hr : 1 ≤ r) (i : Fin 3) :
    eLpNorm (velocityForcing u g i) r volume ≤
      eLpNorm u p volume * ∑ j : Fin 3, eLpNorm (g j) q volume := by
  have hterm (j : Fin 3) :
      eLpNorm (fun x => u x j * g j x i) r volume ≤
        eLpNorm u p volume * eLpNorm (g j) q volume := by
    have h := eLpNorm_smul_le_mul_eLpNorm
      (coordinate_memLp (hg j) i).aestronglyMeasurable
      (coordinate_memLp hu j).aestronglyMeasurable (p := p) (q := q) (r := r)
    exact h.trans (mul_le_mul (eLpNorm_coordinate_le u p j)
      (eLpNorm_coordinate_le (g j) q i) zero_le zero_le)
  have hsum := eLpNorm_sum_le
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      ((coordinate_memLp (hg j) i).mul' (coordinate_memLp hu j)
        (r := r)).aestronglyMeasurable) hr
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => u x j * g j x i) r volume := by
      have he : velocityForcing u g i = ∑ j : Fin 3, (fun x => u x j * g j x i) := by
        ext x
        simp [velocityForcing]
      rw [he]
      exact hsum
    _ ≤ ∑ j : Fin 3, eLpNorm u p volume * eLpNorm (g j) q volume :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := (Finset.mul_sum ..).symm

/-- L² velocity and L² coordinate derivatives give genuine L¹ forcing. -/
theorem velocityForcing_memLp_one {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    MemLp (velocityForcing u g i) 1 volume :=
  velocityForcing_memLp hu hg i

/-- The actual forcing is strongly measurable up to a Lebesgue null set. -/
theorem velocityForcing_aestronglyMeasurable {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    AEStronglyMeasurable (velocityForcing u g i) volume :=
  (velocityForcing_memLp_one hu hg i).aestronglyMeasurable

/-- The actual L¹ norm of each convective component is bounded by A D. -/
theorem velocityForcing_norm_one_le {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume) (i : Fin 3) :
    (eLpNorm (velocityForcing u g i) 1 volume).toReal ≤
      l2Norm u * ∑ j : Fin 3, l2Norm (g j) := by
  have hfinite : eLpNorm u 2 volume * ∑ j : Fin 3, eLpNorm (g j) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hu.2.ne (ENNReal.sum_lt_top.mpr (fun j _ => (hg j).2)).ne
  have h := ENNReal.toReal_mono hfinite
    (velocityForcing_eLpNorm_le (r := 1) hu hg le_rfl i)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => (hg j).2.ne),
    l2Norm] using h

/-- The exact Hölder exponents for L⁶ times L². -/
theorem holder_six_two_threeHalves : ENNReal.HolderTriple 6 2 (3 / 2) := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff, ENNReal.toReal_div]

/-- Genuine weak H¹ derivatives yield actual L^(3/2) convective forcing. -/
theorem velocityForcing_memLp_threeHalves {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (i : Fin 3) :
    MemLp (velocityForcing u g i) (3 / 2) volume := by
  let : ENNReal.HolderTriple 6 2 (3 / 2) := holder_six_two_threeHalves
  exact velocityForcing_memLp (SobolevEmbedding.weak_memLp_six hu hg hderiv) hg i

/-- Sobolev and Hölder give the exact bound C_S D² in real finite norms. -/
theorem velocityForcing_norm_threeHalves_le {u : SpatialField}
    {g : Fin 3 → SpatialField} (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (i : Fin 3) :
    (eLpNorm (velocityForcing u g i) (3 / 2) volume).toReal ≤
      (SobolevEmbedding.sobolevConstant : ℝ) * (∑ j : Fin 3, l2Norm (g j)) ^ 2 := by
  let : ENNReal.HolderTriple 6 2 (3 / 2) := holder_six_two_threeHalves
  have hu6 := SobolevEmbedding.weak_memLp_six hu hg hderiv
  have hfinite : eLpNorm u 6 volume * ∑ j : Fin 3, eLpNorm (g j) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hu6.2.ne (ENNReal.sum_lt_top.mpr (fun j _ => (hg j).2)).ne
  have h := ENNReal.toReal_mono hfinite
    (velocityForcing_eLpNorm_le (r := 3 / 2) hu6 hg
      ((ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2 (by norm_num)) i)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => (hg j).2.ne)] at h
  calc
    _ ≤ (eLpNorm u 6 volume).toReal * ∑ j : Fin 3, l2Norm (g j) := h
    _ ≤ ((SobolevEmbedding.sobolevConstant : ℝ) * ∑ j : Fin 3, l2Norm (g j)) *
        (∑ j : Fin 3, l2Norm (g j)) :=
      mul_le_mul_of_nonneg_right (SobolevEmbedding.weak_l6Norm_le_sum hu hg hderiv)
        (Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg))
    _ = _ := by ring

/-- Vanishing velocity or derivative norm makes the actual forcing zero a.e.
The finite L¹ membership rules out the totalized `toReal ∞ = 0` case. -/
theorem velocityForcing_ae_zero_of_energy_norm_zero {u : SpatialField}
    {g : Fin 3 → SpatialField} (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hzero : l2Norm u = 0 ∨ (∑ j : Fin 3, l2Norm (g j)) = 0) (i : Fin 3) :
    velocityForcing u g i =ᵐ[volume] (0 : Space → ℝ) := by
  have hf := velocityForcing_memLp_one hu hg i
  have hbound := velocityForcing_norm_one_le hu hg i
  have hprod : l2Norm u * (∑ j : Fin 3, l2Norm (g j)) = 0 := by
    rcases hzero with hA | hD
    · rw [hA, zero_mul]
    · rw [hD, mul_zero]
  rw [hprod] at hbound
  have hreal : (eLpNorm (velocityForcing u g i) 1 volume).toReal = 0 :=
    le_antisymm hbound ENNReal.toReal_nonneg
  have hnorm : eLpNorm (velocityForcing u g i) 1 volume = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right hf.2.ne
  exact (eLpNorm_eq_zero_iff hf.aestronglyMeasurable (by norm_num)).mp hnorm

/-- The zero-velocity branch of the pressure optimization. -/
theorem velocityForcing_ae_zero_of_l2Norm_eq_zero {u : SpatialField}
    {g : Fin 3 → SpatialField} (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume) (hzero : l2Norm u = 0) (i : Fin 3) :
    velocityForcing u g i =ᵐ[volume] (0 : Space → ℝ) :=
  velocityForcing_ae_zero_of_energy_norm_zero hu hg (Or.inl hzero) i

/-- The zero-derivative branch of the pressure optimization. -/
theorem velocityForcing_ae_zero_of_derivativeNorm_sum_eq_zero {u : SpatialField}
    {g : Fin 3 → SpatialField} (hu : MemLp u 2 volume)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hzero : (∑ j : Fin 3, l2Norm (g j)) = 0) (i : Fin 3) :
    velocityForcing u g i =ᵐ[volume] (0 : Space → ℝ) :=
  velocityForcing_ae_zero_of_energy_norm_zero hu hg (Or.inr hzero) i

end UnforcedLeray.PressureAnalysis
