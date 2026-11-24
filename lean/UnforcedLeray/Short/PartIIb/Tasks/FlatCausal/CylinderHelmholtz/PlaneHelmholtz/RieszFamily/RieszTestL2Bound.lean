import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestSqSum
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Leaf `PartII-b:T12/1/1/2/40`: the test-level Riesz pairs are `L²`-contractions

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f`, `‖S_{ik} f‖₂² ≤ Σ_{a,b} ‖S_{ab} f‖₂² = ‖f‖₂²` (`RieszTestSqSum`), since every
summand is nonnegative.  Hence `‖S_{ik} f‖₂ ≤ ‖f‖₂` in `L²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- For a real `L²` function `g`, `‖g‖₂² = ∫ g²`. -/
theorem norm_toLp_sq_eq_integral_planar {g : Pl → ℝ} (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 := by
  rw [Lp.norm_toLp, hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hI : 0 ≤ ∫ x, ‖g x‖ ^ (ENNReal.toReal 2) := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast,
    ← Real.rpow_mul hI]
  norm_num

/-- **Leaf `PartII-b:T12/1/1/2/40`.**  `‖S_{ik} f‖₂ ≤ ‖f‖₂` for a planar test `f`. -/
theorem rieszTestL2Bound : UnforcedLeray.Short.IIb.PlaneRiesz.RieszTestL2Bound := by
  intro i k f hf h1 h2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_toLp_sq_eq_integral_planar h2, norm_toLp_sq_eq_integral_planar h1,
    ← rieszTestSqSum f hf]
  calc ∫ x, (rieszTest i k f x) ^ 2
      ≤ ∑ k', ∫ x, (rieszTest i k' f x) ^ 2 :=
        Finset.single_le_sum (f := fun k' => ∫ x, (rieszTest i k' f x) ^ 2)
          (fun k' _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', ∫ x, (rieszTest i' k' f x) ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ k', ∫ x, (rieszTest i' k' f x) ^ 2)
          (fun i' _ => Finset.sum_nonneg fun k' _ => integral_nonneg fun x => sq_nonneg _)
          (Finset.mem_univ i)

end UnforcedLeray.Short.IIb.PlaneRiesz
