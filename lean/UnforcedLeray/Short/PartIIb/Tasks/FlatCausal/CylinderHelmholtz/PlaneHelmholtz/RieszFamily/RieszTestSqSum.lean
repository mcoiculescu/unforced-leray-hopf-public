import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PressureIdentityTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestDiag

/-!
# Leaf `PartII-b:T12/1/1/2/34`: the test-level Riesz pairs satisfy `Σ_{i,k} ‖S_{ik} f‖₂² = ‖f‖₂²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` and a column `k`, the field `F_j = δ_{jk} f` has `ψ_i = Σ_j S_{ij} F_j = S_{ik} f`
and `S_{ij} 0 = 0`.  The pressure identity (`PressureIdentityTest`) for this field reads
`∫ f S_{kk} f = Σ_i ∫ (S_{ik} f)²`.  Summing over `k = 0, 1` and using `Σ_k S_{kk} f = f`
(`RieszTestDiag`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The test-level pairs vanish on the zero test. -/
theorem rieszTest_zero_fn (i j : Fin 2) : rieszTest i j (0 : Pl → ℝ) = 0 := by
  have hN : newtonConv (0 : Pl → ℝ) = fun _ => 0 := by
    funext x
    simp [newtonConv]
  have hz : ∀ j : Fin 2, pd j (fun _ : Pl => (0 : ℝ)) = fun _ => 0 := by
    intro j
    funext x
    simp [pd]
  unfold rieszTest
  rw [hN, hz j, hz i]
  rfl

/-- Column identity: for a planar test `f`, `∫ f S_{kk} f = Σ_i ∫ (S_{ik} f)²`. -/
theorem rieszTest_column (k : Fin 2) (f : Pl → ℝ) (hf : IsTest f) :
    ∫ x, f x * rieszTest k k f x = ∑ i, ∫ x, (rieszTest i k f x) ^ 2 := by
  set F : Fin 2 → Pl → ℝ := fun j => if j = k then f else 0 with hFdef
  have hFT : ∀ j, IsTest (F j) := by
    intro j
    by_cases hj : j = k
    · simp only [F, if_pos hj]; exact hf
    · simp only [F, if_neg hj]; exact ⟨contDiff_const, HasCompactSupport.zero⟩
  have hsum : ∀ i x, ∑ j, rieszTest i j (F j) x = rieszTest i k f x := by
    intro i x
    rw [Finset.sum_eq_single k]
    · simp [F]
    · intro j _ hj
      simp [F, hj, rieszTest_zero_fn]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have h := pressureIdentityTest F hFT
  simp only [hsum] at h
  rw [Finset.sum_eq_single k] at h
  · have hFk : F k = f := by simp [F]
    simp only [hFk] at h
    exact h
  · intro i _ hi
    have : ∀ x, F i x * rieszTest i k f x = 0 := fun x => by simp [F, hi]
    simp [this]
  · intro h'
    exact absurd (Finset.mem_univ k) h'

/-- The integrand `f · S_{ik} f` is integrable for a planar test `f`. -/
theorem rieszTest_mul_integrable (i k : Fin 2) (f : Pl → ℝ) (hf : IsTest f) :
    Integrable (fun x => f x * rieszTest i k f x) volume := by
  have hc : Continuous (fun x => f x * rieszTest i k f x) :=
    hf.1.continuous.mul (rieszTestContDiff i k f hf).continuous
  exact hc.integrable_of_hasCompactSupport hf.2.mul_right

/-- **Leaf `PartII-b:T12/1/1/2/34`.**  `Σ_{i,k} ‖S_{ik} f‖₂² = ‖f‖₂²` for a planar test `f`. -/
theorem rieszTestSqSum : UnforcedLeray.Short.IIb.PlaneRiesz.RieszTestSqSum := by
  intro f hf
  have hA0 := rieszTest_column 0 f hf
  have hA1 := rieszTest_column 1 f hf
  have hD : (∫ x, f x * rieszTest 0 0 f x) + (∫ x, f x * rieszTest 1 1 f x) = ∫ x, (f x) ^ 2 := by
    rw [← integral_add (rieszTest_mul_integrable 0 0 f hf) (rieszTest_mul_integrable 1 1 f hf)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hx := rieszTestDiag f hf x
    calc f x * rieszTest 0 0 f x + f x * rieszTest 1 1 f x
        = f x * (rieszTest 0 0 f x + rieszTest 1 1 f x) := by ring
      _ = f x * f x := by rw [hx]
      _ = (f x) ^ 2 := by ring
  rw [hA0, hA1] at hD
  simp only [Fin.sum_univ_two] at hD ⊢
  linarith

end UnforcedLeray.Short.IIb.PlaneRiesz
