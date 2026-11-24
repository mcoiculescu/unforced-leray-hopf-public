import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_8
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Compactness.Compact

/-!
# Leaf `PartII-b:T13/1/8/1`: finite window decomposition of a test (SP 1928-1933)

`WglDecomp`: every test `φ` on `s > 0` is a finite sum of tests `ψ_k` with `tsupport ψ_k` inside a
window `winOpen (a_k)`, and the transposes add up. Proof: the `s`-projection of `tsupport φ` is a
compact subset of `(0, ∞)`; finitely many windows `(2s/3, 4s/3)` cover it; a smooth partition of
unity in `s` subordinate to them gives `ψ_k(x) = ρ_k(x.1) φ(x)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Manifold

/-- Finite smooth partition of unity on a compact subset of `(0, ∞)` subordinate to windows
`(A k, 2 A k)`. -/
theorem wgld_partition (K : Set ℝ) (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) :
    ∃ n : ℕ, ∃ A : Fin n → ℝ, ∃ ρ : Fin n → ℝ → ℝ,
      (∀ k, 0 < A k) ∧ (∀ k, ContDiff ℝ ∞ (ρ k)) ∧
      (∀ k, tsupport (ρ k) ⊆ Ioo (A k) (2 * A k)) ∧
      (∀ s ∈ K, ∑ k, ρ k s = 1) := by
  classical
  have hcov : K ⊆ ⋃ s : K, Ioo (2 * (s : ℝ) / 3) (2 * (2 * (s : ℝ) / 3)) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    have hx0 : (0 : ℝ) < x := hKpos hx
    show 2 * x / 3 < x ∧ x < 2 * (2 * x / 3)
    constructor <;> linarith
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun s : K => Ioo (2 * (s : ℝ) / 3) (2 * (2 * (s : ℝ) / 3))) (fun _ => isOpen_Ioo) hcov
  let A₀ : t → ℝ := fun i => 2 * (i.1 : ℝ) / 3
  have hA₀ : ∀ i, 0 < A₀ i := fun i => by
    have h := hKpos (i.1 : K).2
    simp only [mem_Ioi] at h
    exact div_pos (mul_pos two_pos h) three_pos
  have hU : K ⊆ ⋃ i : t, Ioo (A₀ i) (2 * A₀ i) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (s := K) hK.isClosed (fun i : t => Ioo (A₀ i) (2 * A₀ i)) (fun _ => isOpen_Ioo) hU
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun k => A₀ (e k), fun k => ⇑(f (e k)), fun k => hA₀ _, ?_, ?_, ?_⟩
  · intro k
    exact contMDiff_iff_contDiff.mp (f (e k)).contMDiff
  · intro k
    exact hf (e k)
  · intro s hs
    have h1 := f.sum_eq_one hs
    rw [finsum_eq_sum_of_fintype] at h1
    exact (Equiv.sum_comp e (fun i => f i s)).trans h1

/-- Sums of smooth test functions: the transpose is additive. -/
theorem wgld_transpose_sum (v : Coord → Fin 3 → ℝ) (hv : ∀ j, ContDiff ℝ ∞ (fun x => v x j))
    {n : ℕ} (ψ : Fin n → Coord → ℝ) (hψ : ∀ k, ContDiff ℝ ∞ (ψ k)) (x : Coord) :
    coordTranspose v dZero (fun y => ∑ k, ψ k y) x = ∑ k, coordTranspose v dZero (ψ k) x := by
  have hd : ∀ j k, DifferentiableAt ℝ (fun y => v y j * ψ k y) x := fun j k =>
    ((hv j).differentiable (by simp)).differentiableAt.mul
      ((hψ k).differentiable (by simp)).differentiableAt
  have key : ∀ j, cpd j (fun y => v y j * ∑ k, ψ k y) x =
      ∑ k, cpd j (fun y => v y j * ψ k y) x := by
    intro j
    have hfun : (fun y => v y j * ∑ k, ψ k y) = ∑ k, (fun y => v y j * ψ k y) := by
      funext y; rw [Finset.mul_sum, Finset.sum_apply]
    unfold cpd
    rw [hfun, fderiv_sum (fun k _ => hd j k), sum_apply]
  unfold coordTranspose
  simp only [dZero, zero_mul, add_zero, key]
  rw [Finset.sum_comm, Finset.sum_neg_distrib]

theorem wglDecomp : WglDecomp := by
  intro v hv φ hφ
  have hKc : IsCompact (Prod.fst '' tsupport φ) := hφ.compact.isCompact.image continuous_fst
  have hKpos : Prod.fst '' tsupport φ ⊆ Ioi 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hφ.supp hx).1
  obtain ⟨n, A, ρ, hA, hρ, hsupp, hsum⟩ := wgld_partition _ hKc hKpos
  have hψs : ∀ k, ContDiff ℝ ∞ (fun x : Coord => ρ k x.1 * φ x) := fun k =>
    ((hρ k).comp contDiff_fst).mul hφ.smooth
  have hψsub : ∀ k, tsupport (fun x : Coord => ρ k x.1 * φ x) ⊆ winOpen (A k) := by
    intro k
    have h1 : tsupport (fun x : Coord => ρ k x.1) ⊆ Prod.fst ⁻¹' tsupport (ρ k) := by
      refine closure_minimal ?_ ((isClosed_tsupport _).preimage continuous_fst)
      intro x hx
      exact subset_tsupport (ρ k) (Function.mem_support.mpr (Function.mem_support.mp hx))
    intro x hx
    have h2 := h1 (tsupport_mul_subset_left hx)
    exact ⟨hsupp k h2, trivial⟩
  refine ⟨n, A, fun k x => ρ k x.1 * φ x, ?_, ?_, ?_⟩
  · intro k
    refine ⟨hA k, ⟨hψs k, ?_, ?_⟩, ?_⟩
    · exact IsCompact.of_isClosed_subset hφ.compact (isClosed_tsupport _) tsupport_mul_subset_right
    · intro x hx
      have h := hψsub k hx
      exact ⟨lt_trans (hA k) h.1.1, trivial⟩
    · exact hψsub k
  · intro x
    show φ x = ∑ k, ρ k x.1 * φ x
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hxt : x ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hφx)
      have hs := hsum x.1 ⟨x, hxt, rfl⟩
      rw [← Finset.sum_mul, hs, one_mul]
  · intro x
    have hcongr : coordTranspose v dZero φ x =
        coordTranspose v dZero (fun y => ∑ k, ρ k y.1 * φ y) x := by
      congr 1
      funext y
      by_cases hφy : φ y = 0
      · simp [hφy]
      · have hyt : y ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hφy)
        rw [← Finset.sum_mul, hsum y.1 ⟨y, hyt, rfl⟩, one_mul]
    rw [hcongr]
    exact wgld_transpose_sum v hv _ hψs x

end UnforcedLeray.Short.IIb
