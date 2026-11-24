import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsTestDense

/-!
# A countable dense family of test functions, uniform in `C¹` with a common radius

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).

The family `D = ⋃ₙ bsPick n '' (Tₙ)` of `Fubini/BsTestDense.lean` is used with the radius `n` of
the target: a smooth `φ` vanishing outside `closedBall 0 n` lies in `bsTn n`, its embedding
`(φ, ∇φ)|_{closedBall 0 n}` is approximated by some `q ∈ Tₙ`, and `bsPick n q` is the approximant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem testDense : TestDense := by
  choose T hTsub hTcount hTdense using bsDense_exists
  refine ⟨⋃ n : ℕ, (bsPick n) '' (T n), ?_, ?_, ?_⟩
  · exact Set.countable_iUnion fun n => (hTcount n).image _
  · intro χ hχ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hχ
    obtain ⟨q, _, rfl⟩ := hn
    exact ⟨(bsPick_mem n q).1, bsTn_hasCompactSupport (bsPick_mem n q)⟩
  · intro n φ hφC hφs ε hε
    have hφn : φ ∈ bsTn n := ⟨hφC, hφs⟩
    have hmem : bsEmb n ⟨φ, hφn⟩ ∈ Set.range (bsEmb n) := ⟨⟨φ, hφn⟩, rfl⟩
    have hclose := hTdense n hmem
    rw [Metric.mem_closure_iff] at hclose
    obtain ⟨q, hqT, hqd⟩ := hclose ε hε
    have hqR : q ∈ Set.range (bsEmb n) := hTsub n hqT
    have hχmem : bsPick n q ∈ bsTn n := bsPick_mem n q
    have hemb : bsEmb n ⟨bsPick n q, hχmem⟩ = q := bsPick_emb n q hqR
    have hd : dist (bsEmb n ⟨φ, hφn⟩) (bsEmb n ⟨bsPick n q, hχmem⟩) < ε := by
      rw [hemb]
      exact hqd
    have hball : ∀ y : Space, ‖φ y - bsPick n q y‖ ≤ ε ∧
        ‖bsGradS φ y - bsGradS (bsPick n q) y‖ ≤ ε := by
      intro y
      by_cases hy : (n : ℝ) < ‖y‖
      · rw [hφs y hy, hχmem.2 y hy, bsGradS_eq_zero_of_outside hφn hy,
          bsGradS_eq_zero_of_outside hχmem hy]
        simp [hε.le]
      · push Not at hy
        have hyb : y ∈ Metric.closedBall (0 : Space) n := by
          rw [mem_closedBall_zero_iff]
          exact hy
        have h1 := ContinuousMap.dist_apply_le_dist (f := bsEmb n ⟨φ, hφn⟩)
          (g := bsEmb n ⟨bsPick n q, hχmem⟩) ⟨y, hyb⟩
        have h2 := le_of_lt (lt_of_le_of_lt h1 hd)
        rw [show bsEmb n ⟨φ, hφn⟩ ⟨y, hyb⟩ = (φ y, bsGradS φ y) from rfl,
          show bsEmb n ⟨bsPick n q, hχmem⟩ ⟨y, hyb⟩ = (bsPick n q y, bsGradS (bsPick n q) y) from rfl,
          Prod.dist_eq] at h2
        constructor
        · have h3 := le_trans (le_max_left _ _) h2
          rw [dist_eq_norm] at h3
          exact h3
        · have h3 := le_trans (le_max_right _ _) h2
          rw [dist_eq_norm] at h3
          exact h3
    refine ⟨bsPick n q, Set.mem_iUnion.2 ⟨n, q, hqT, rfl⟩, ?_, ?_, ?_⟩
    · intro y hy
      exact hχmem.2 y hy
    · intro y
      exact (hball y).1
    · intro j y
      have hv := (hball y).2
      have hc := PiLp.norm_apply_le (bsGradS φ y - bsGradS (bsPick n q) y) j
      have heq : (bsGradS φ y - bsGradS (bsPick n q) y) j =
          fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
            fderiv ℝ (bsPick n q) y (EuclideanSpace.single j (1 : ℝ)) := by
        simp [bsGradS]
      rw [heq] at hc
      exact le_trans hc hv

end UnforcedLeray.Short.PartIIIb.Concrete
