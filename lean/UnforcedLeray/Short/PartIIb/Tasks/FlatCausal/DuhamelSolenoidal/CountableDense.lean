import UnforcedLeray.Short.PartIIb.Sub.T12_6
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Part II-b, task `PartII-b:T12/6/4`: countable `C¹`-dense family of planar test functions

Target: `dsolCountableDense : DsolCountableDense` (`Sub/T12_6.lean`, line 120). Source of record:
`the November 2 reference manuscript`, line 1924 (uniformity in the test function
for the slice solenoidality).

Proof. For `n : ℕ` let `Xn n` be the smooth functions vanishing for `‖y‖ > n`. The map
`ψ ↦ (y ↦ (ψ y, Dψ y))` embeds `Xn n` into the separable metric space
`Eb n = C(closedBall 0 n, ℝ × (ℝ²→L[ℝ] ℝ))`, so its image has a countable dense subset `T`
(`IsSeparable.exists_countable_dense_subset`). Pulling `T` back by `Function.invFun` gives a
countable `Dn n ⊆ Xn n`. Put `D := ⋃ n, Dn n`. Given a smooth compactly supported `ψ`, pick `n`
with `tsupport ψ ⊆ closedBall 0 n`, take `R := n`, and approximate `ψ` inside `Xn n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace CountableDenseAux

/-- Smooth planar functions vanishing for `‖y‖ > n`. -/
def Xn (n : ℕ) : Set (ℝ × ℝ → ℝ) :=
  {ψ | ContDiff ℝ ∞ ψ ∧ ∀ y : ℝ × ℝ, (n : ℝ) < ‖y‖ → ψ y = 0}

/-- Target space of the embedding `ψ ↦ (ψ, Dψ)` on the closed ball of radius `n`. -/
abbrev Eb (n : ℕ) : Type :=
  C(Metric.closedBall (0 : ℝ × ℝ) (n : ℝ), ℝ × ((ℝ × ℝ) →L[ℝ] ℝ))

instance instCompactClosedBall (n : ℕ) : CompactSpace (Metric.closedBall (0 : ℝ × ℝ) (n : ℝ)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

theorem Xn_smooth {n : ℕ} {ψ : ℝ × ℝ → ℝ} (h : ψ ∈ Xn n) : ContDiff ℝ ∞ ψ := by
  simp only [Xn, Set.mem_ofPred_eq] at h
  exact h.1

theorem Xn_vanish {n : ℕ} {ψ : ℝ × ℝ → ℝ} (h : ψ ∈ Xn n) (y : ℝ × ℝ) (hy : (n : ℝ) < ‖y‖) :
    ψ y = 0 := by
  simp only [Xn, Set.mem_ofPred_eq] at h
  exact h.2 y hy

theorem Xn_zero_mem (n : ℕ) : (0 : ℝ × ℝ → ℝ) ∈ Xn n := by
  simp only [Xn, Set.mem_ofPred_eq]
  exact ⟨contDiff_const, fun y _ => rfl⟩

instance instNonemptyXn (n : ℕ) : Nonempty (Xn n) := ⟨⟨0, Xn_zero_mem n⟩⟩

theorem Xn_compactSupport {n : ℕ} {ψ : ℝ × ℝ → ℝ} (h : ψ ∈ Xn n) : HasCompactSupport ψ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (n : ℝ)) (fun x hx => ?_)
  apply Xn_vanish h x
  exact not_le.mp (fun h' => hx (mem_closedBall_zero_iff.2 h'))

theorem fderiv_zero_of_vanish {n : ℕ} {ψ : ℝ × ℝ → ℝ} (h : ψ ∈ Xn n) {y : ℝ × ℝ}
    (hy : (n : ℝ) < ‖y‖) : fderiv ℝ ψ y = 0 := by
  have hev : ψ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact Xn_vanish h z hz
  rw [hev.fderiv_eq]
  simp

/-- The embedding `ψ ↦ (ψ, Dψ)` into `C(closedBall 0 n, ℝ × (ℝ²→L[ℝ] ℝ))`. -/
def Fb (n : ℕ) (ψ : Xn n) : Eb n :=
  ⟨fun y => (ψ.1 y.1, fderiv ℝ ψ.1 y.1), by
    have hs : ContDiff ℝ ∞ ψ.1 := Xn_smooth ψ.2
    have h1 : Continuous ψ.1 := hs.continuous
    have h2 : Continuous (fderiv ℝ ψ.1) := hs.continuous_fderiv (by simp)
    exact (h1.prodMk h2).comp continuous_subtype_val⟩

theorem exists_dense (n : ℕ) :
    ∃ T : Set (Eb n), T ⊆ Set.range (Fb n) ∧ T.Countable ∧ Set.range (Fb n) ⊆ closure T := by
  have hsep : TopologicalSpace.IsSeparable (Set.range (Fb n)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  exact hsep.exists_countable_dense_subset

theorem exists_approx (n : ℕ) :
    ∃ Dn : Set (ℝ × ℝ → ℝ), Dn.Countable ∧ (∀ ψ ∈ Dn, ψ ∈ Xn n) ∧
      ∀ ψ : Xn n, ∀ ε : ℝ, 0 < ε → ∃ ψ' : Xn n, ψ'.1 ∈ Dn ∧ dist (Fb n ψ) (Fb n ψ') < ε := by
  obtain ⟨T, hTs, hTc, hTd⟩ := exists_dense n
  refine ⟨(fun g => (Function.invFun (Fb n) g).1) '' T, hTc.image _, ?_, ?_⟩
  · rintro ψ ⟨g, _, rfl⟩
    exact (Function.invFun (Fb n) g).2
  · intro ψ ε hε
    have hcl : Fb n ψ ∈ closure T := hTd ⟨ψ, rfl⟩
    obtain ⟨g, hgT, hdist⟩ := (Metric.mem_closure_iff (α := Eb n)).1 hcl ε hε
    obtain ⟨a, ha⟩ := hTs hgT
    have hinv : Fb n (Function.invFun (Fb n) g) = g := Function.invFun_eq ⟨a, ha⟩
    refine ⟨Function.invFun (Fb n) g, ⟨g, hgT, rfl⟩, ?_⟩
    rw [hinv]
    exact hdist

end CountableDenseAux

open CountableDenseAux in
/-- **Leaf `PartII-b:T12/6/4`** (separability of `C_c^∞(ℝ²)` in the `C¹` topology). -/
theorem dsolCountableDense : DsolCountableDense := by
  unfold DsolCountableDense
  choose Dn hDc hDsub hDapp using exists_approx
  refine ⟨⋃ n, Dn n, countable_iUnion hDc, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hψ
    exact ⟨Xn_smooth (hDsub n ψ hn), Xn_compactSupport (hDsub n ψ hn)⟩
  · intro ψ hψs hψc
    obtain ⟨r, hr⟩ := (hψc.isCompact.isBounded).subset_closedBall (0 : ℝ × ℝ)
    obtain ⟨n, hrn⟩ := exists_nat_ge r
    have hmem : ψ ∈ Xn n := by
      refine (show ContDiff ℝ ∞ ψ ∧ ∀ y : ℝ × ℝ, (n : ℝ) < ‖y‖ → ψ y = 0 from
        ⟨hψs, fun y hy => ?_⟩)
      by_contra hne
      have hyt : y ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hne)
      have h1 := hr hyt
      rw [mem_closedBall_zero_iff] at h1
      linarith
    refine ⟨(n : ℝ), fun ε hε => ?_⟩
    obtain ⟨ψ', hψ'D, hdist⟩ := hDapp n ⟨ψ, hmem⟩ (ε / 2) (half_pos hε)
    refine ⟨ψ'.1, Set.mem_iUnion.2 ⟨n, hψ'D⟩, fun y hy => Xn_vanish ψ'.2 y hy, fun y => ?_⟩
    by_cases hy : y ∈ Metric.closedBall (0 : ℝ × ℝ) (n : ℝ)
    · have hpair : dist (ψ y, fderiv ℝ ψ y) (ψ'.1 y, fderiv ℝ ψ'.1 y) ≤ ε / 2 :=
        le_trans (ContinuousMap.dist_apply_le_dist (f := Fb n ⟨ψ, hmem⟩) (g := Fb n ψ')
          (⟨y, hy⟩ : Metric.closedBall (0 : ℝ × ℝ) (n : ℝ))) hdist.le
      have k1 : dist (ψ y) (ψ'.1 y) ≤ dist (ψ y, fderiv ℝ ψ y) (ψ'.1 y, fderiv ℝ ψ'.1 y) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have k2 : dist (fderiv ℝ ψ y) (fderiv ℝ ψ'.1 y)
          ≤ dist (ψ y, fderiv ℝ ψ y) (ψ'.1 y, fderiv ℝ ψ'.1 y) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      have a1 : dist (ψ y) (ψ'.1 y) ≤ ε / 2 := le_trans k1 hpair
      have a2 : dist (fderiv ℝ ψ y) (fderiv ℝ ψ'.1 y) ≤ ε / 2 := le_trans k2 hpair
      rw [Real.dist_eq] at a1
      rw [dist_eq_norm] at a2
      linarith
    · have hy' : (n : ℝ) < ‖y‖ := not_le.mp (fun h => hy (mem_closedBall_zero_iff.2 h))
      rw [Xn_vanish hmem y hy', fderiv_zero_of_vanish hmem hy',
        Xn_vanish ψ'.2 y hy', fderiv_zero_of_vanish ψ'.2 hy']
      simp [hε.le]

end UnforcedLeray.Short.IIb
