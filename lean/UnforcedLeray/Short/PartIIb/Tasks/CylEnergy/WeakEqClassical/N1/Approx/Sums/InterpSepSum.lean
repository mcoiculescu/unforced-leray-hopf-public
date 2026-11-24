import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.CutSliceTest
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.PouProps

/-!

separated sum.

Source: `the November 2 reference manuscript`, lines 2074-2105.
`sepApprox t₀ t₁ K R φ r x = Σ_{k<K} (α_k(r) ψ_k(x) + β_k(r) ψ_{k+1}(x))` with
`ψ_k = θ_R φ(a_k, ·)` (`IsCylTest` by `CutSliceTest`) and `C^1` coefficients `α_k, β_k` (`PouProps`).
The `2K` terms are indexed by `Fin (K + K)` via `Fin.append`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- Coefficient of the left node `a_k` in the age interpolation at age `r` (separated-sum
version). -/
def interpSAlpha (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  pou t₀ t₁ K k r * (1 - (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K)

/-- Coefficient of the right node `a_{k+1}` in the age interpolation at age `r`. -/
def interpSBeta (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  pou t₀ t₁ K k r * ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K)

theorem interpS_sum_identity (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (g : ℝ → ℝ) :
    interp1 t₀ t₁ K g r = ∑ k ∈ Finset.range K,
      (interpSAlpha t₀ t₁ K r k * g (gridPt t₀ t₁ K k) +
        interpSBeta t₀ t₁ K r k * g (gridPt t₀ t₁ K (k + 1))) := by
  unfold interp1 interpSAlpha interpSBeta
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem interpS_gridPt_mem {t₀ t₁ : ℝ} {K k : ℕ} (ht : t₀ ≤ t₁) (hk : k ≤ K) :
    gridPt t₀ t₁ K k ∈ Icc t₀ t₁ := by
  rw [mem_Icc]
  unfold gridPt gridH
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hk0 : k = 0 := by omega
    subst hk0
    simp [ht]
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hD : 0 ≤ (t₁ - t₀) / K := div_nonneg (by linarith) hKr.le
    have hkr : (k : ℝ) ≤ K := by exact_mod_cast hk
    have hKD : (K : ℝ) * ((t₁ - t₀) / K) = t₁ - t₀ := by
      field_simp
    have h1 : (k : ℝ) * ((t₁ - t₀) / K) ≤ K * ((t₁ - t₀) / K) :=
      mul_le_mul_of_nonneg_right hkr hD
    have h2 : (0 : ℝ) ≤ (k : ℝ) * ((t₁ - t₀) / K) := mul_nonneg (Nat.cast_nonneg k) hD
    constructor <;> linarith

theorem interpS_contDiff_alpha (t₀ t₁ : ℝ) (K k : ℕ)
    (hpc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pou t₀ t₁ K k)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r => interpSAlpha t₀ t₁ K r k) := by
  unfold interpSAlpha
  exact hpc.mul (contDiff_const.sub (((contDiff_id.sub contDiff_const).div_const
    (gridH t₀ t₁ K))))

theorem interpS_contDiff_beta (t₀ t₁ : ℝ) (K k : ℕ)
    (hpc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pou t₀ t₁ K k)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r => interpSBeta t₀ t₁ K r k) := by
  unfold interpSBeta
  exact hpc.mul (((contDiff_id.sub contDiff_const).div_const (gridH t₀ t₁ K)))

theorem interpSepSum : UnforcedLeray.Short.IIb.TdSums.InterpSepSum := by
  intro c t₀ t₁ R K φ hR ht hφ
  have hcs : CutSliceTest := cutSliceTest
  obtain ⟨hpc, -, -⟩ := pouProps
  unfold CylSepSum
  refine ⟨K + K,
    Fin.append (fun i : Fin K => fun r => interpSAlpha t₀ t₁ K r (i : ℕ))
      (fun i : Fin K => fun r => interpSBeta t₀ t₁ K r (i : ℕ)),
    Fin.append (fun i : Fin K => cutTest R φ (gridPt t₀ t₁ K (i : ℕ)))
      (fun i : Fin K => cutTest R φ (gridPt t₀ t₁ K ((i : ℕ) + 1))),
    ?_, ?_, ?_⟩
  · intro k
    induction k using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact ((interpS_contDiff_alpha t₀ t₁ K i (hpc t₀ t₁ K i)).of_le (by simp)).contDiffOn
    | right i =>
      simp only [Fin.append_right]
      exact ((interpS_contDiff_beta t₀ t₁ K i (hpc t₀ t₁ K i)).of_le (by simp)).contDiffOn
  · intro k
    induction k using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact hcs c t₀ t₁ R φ hR hφ _ (interpS_gridPt_mem ht (Nat.le_of_lt i.isLt))
    | right i =>
      simp only [Fin.append_right]
      exact hcs c t₀ t₁ R φ hR hφ _ (interpS_gridPt_mem ht (Nat.succ_le_of_lt i.isLt))
  · intro r x
    unfold sepApprox
    rw [interpS_sum_identity, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range
      (fun k => interpSAlpha t₀ t₁ K r k * cutTest R φ (gridPt t₀ t₁ K k) x) K,
      Fin.sum_univ_eq_sum_range
      (fun k => interpSBeta t₀ t₁ K r k * cutTest R φ (gridPt t₀ t₁ K (k + 1)) x) K]
