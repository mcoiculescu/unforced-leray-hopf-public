import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Countable dense family of test functions (BSTestDense)

Source `the November 2 reference manuscript` lines 1351-1362.
For each radius `n`, the smooth functions supported in `closedBall 0 n`, viewed through
`(χ, ∇χ)` as continuous maps on the compact ball, form a subset of a separable metric space
`C(closedBall 0 n, ℂ × ℂ³)`, hence have a countable dense subset.  Preimages of that subset (chosen
with `Function.invFunOn`) give the countable family.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Smooth functions vanishing outside `closedBall 0 n`. -/
def bsTn (n : ℕ) : Set (Space → ℂ) :=
  {χ | ContDiff ℝ ∞ χ ∧ ∀ y : Space, (n : ℝ) < ‖y‖ → χ y = 0}

theorem bsTn_hasCompactSupport {n : ℕ} {χ : Space → ℂ} (h : χ ∈ bsTn n) :
    HasCompactSupport χ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) n) ?_
  intro y hy
  apply h.2 y
  have : ¬ ‖y‖ ≤ n := by simpa using hy
  exact lt_of_not_ge this

theorem bsGradS_eq_zero_of_outside {n : ℕ} {χ : Space → ℂ} (h : χ ∈ bsTn n) {y : Space}
    (hy : (n : ℝ) < ‖y‖) : bsGradS χ y = 0 := by
  apply bsGradS_eq_zero_of_eventually (c := 0)
  have hopen : IsOpen {x : Space | (n : ℝ) < ‖x‖} := isOpen_lt continuous_const continuous_norm
  exact Filter.eventually_of_mem (hopen.mem_nhds hy) (fun x hx => h.2 x hx)

theorem bsZero_mem (n : ℕ) : (fun _ : Space => (0 : ℂ)) ∈ bsTn n :=
  ⟨contDiff_const, fun _ _ => rfl⟩

instance bsTn_nonempty (n : ℕ) : Nonempty (bsTn n) := ⟨⟨_, bsZero_mem n⟩⟩

theorem bsEmb_continuous {n : ℕ} (χ : Space → ℂ) (h : χ ∈ bsTn n) :
    Continuous (fun y : Metric.closedBall (0 : Space) n => ((χ y.1, bsGradS χ y.1) : ℂ × CVec3)) :=
  (h.1.continuous.comp continuous_subtype_val).prodMk
    ((bsGradS_continuous h.1).comp continuous_subtype_val)

/-- The embedding `χ ↦ (χ, ∇χ)|_{closedBall 0 n}` into continuous maps on the ball. -/
def bsEmb (n : ℕ) (χ : bsTn n) : C(Metric.closedBall (0 : Space) n, ℂ × CVec3) :=
  ⟨fun y => (χ.1 y.1, bsGradS χ.1 y.1), bsEmb_continuous χ.1 χ.2⟩

theorem bsSep (n : ℕ) : TopologicalSpace.SeparableSpace C(Metric.closedBall (0 : Space) n, ℂ × CVec3) := by
  haveI : SecondCountableTopology (Metric.closedBall (0 : Space) n) := inferInstance
  haveI : LocallyCompactSpace (Metric.closedBall (0 : Space) n) := inferInstance
  haveI : SecondCountableTopology (ℂ × CVec3) := inferInstance
  exact inferInstance

theorem bsRange_separable (n : ℕ) : TopologicalSpace.IsSeparable (Set.range (bsEmb n)) := by
  haveI := bsSep n
  exact TopologicalSpace.IsSeparable.of_separableSpace _

theorem bsDense_exists (n : ℕ) : ∃ t : Set C(Metric.closedBall (0 : Space) n, ℂ × CVec3),
    t ⊆ Set.range (bsEmb n) ∧ t.Countable ∧ Set.range (bsEmb n) ⊆ closure t :=
  TopologicalSpace.IsSeparable.exists_countable_dense_subset (bsRange_separable n)

/-- A pick of a preimage of a point in the range of the embedding. -/
def bsPick (n : ℕ) (q : C(Metric.closedBall (0 : Space) n, ℂ × CVec3)) : Space → ℂ :=
  fun y => (Function.invFunOn (bsEmb n) Set.univ q : bsTn n).1 y

theorem bsPick_mem (n : ℕ) (q : C(Metric.closedBall (0 : Space) n, ℂ × CVec3)) :
    bsPick n q ∈ bsTn n :=
  (Function.invFunOn (bsEmb n) Set.univ q).2

theorem bsPick_emb (n : ℕ) (q : C(Metric.closedBall (0 : Space) n, ℂ × CVec3))
    (hq : q ∈ Set.range (bsEmb n)) : bsEmb n ⟨bsPick n q, bsPick_mem n q⟩ = q := by
  obtain ⟨y, hy⟩ := hq
  have h := Function.invFunOn_eq (f := bsEmb n) (s := Set.univ) (b := q)
    ⟨y, Set.mem_univ _, hy⟩
  exact h

/-- The countable family of test functions. -/
theorem bsTestDense : BSTestDense := by
  choose T hTsub hTcount hTdense using bsDense_exists
  refine ⟨⋃ n : ℕ, (bsPick n) '' (T n), ?_, ?_, ?_⟩
  · exact Set.countable_iUnion fun n => (hTcount n).image _
  · intro χ hχ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hχ
    obtain ⟨q, _, rfl⟩ := hn
    exact ⟨(bsPick_mem n q).1, bsTn_hasCompactSupport (bsPick_mem n q)⟩
  · intro χ hχC hχs ε hε
    obtain ⟨r, hr⟩ := hχs.isCompact.isBounded.subset_closedBall (0 : Space)
    set n : ℕ := ⌈r⌉₊ with hn
    have hrn : r ≤ (n : ℝ) := Nat.le_ceil r
    have hχn : χ ∈ bsTn n := by
      refine ⟨hχC, fun y hy => ?_⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hyt
      have h1 := hr hyt
      rw [mem_closedBall_zero_iff] at h1
      linarith
    set χ0 : bsTn n := ⟨χ, hχn⟩ with hχ0
    have hmem : bsEmb n χ0 ∈ Set.range (bsEmb n) := ⟨χ0, rfl⟩
    have hclose := hTdense n hmem
    rw [Metric.mem_closure_iff] at hclose
    obtain ⟨q, hqT, hqd⟩ := hclose ε hε
    have hqR : q ∈ Set.range (bsEmb n) := hTsub n hqT
    have hχ'mem : bsPick n q ∈ bsTn n := bsPick_mem n q
    have hemb : bsEmb n ⟨bsPick n q, hχ'mem⟩ = q := bsPick_emb n q hqR
    have hd : dist (bsEmb n χ0) (bsEmb n ⟨bsPick n q, hχ'mem⟩) < ε := by
      rw [hemb]
      exact hqd
    refine ⟨bsPick n q, Set.mem_iUnion.2 ⟨n, q, hqT, rfl⟩, ?_, ?_, (n : ℝ), fun y hy => hχ'mem.2 y hy⟩
    · intro y
      by_cases hy : (n : ℝ) < ‖y‖
      · rw [hχn.2 y hy, hχ'mem.2 y hy, sub_zero, norm_zero]
        exact hε.le
      · push Not at hy
        have hyb : y ∈ Metric.closedBall (0 : Space) n := by
          rw [mem_closedBall_zero_iff]
          exact hy
        have h1 := ContinuousMap.dist_apply_le_dist (f := bsEmb n χ0) (g := bsEmb n ⟨bsPick n q, hχ'mem⟩) ⟨y, hyb⟩
        have h2 := le_of_lt (lt_of_le_of_lt h1 hd)
        rw [show bsEmb n χ0 ⟨y, hyb⟩ = (χ y, bsGradS χ y) from rfl,
          show bsEmb n ⟨bsPick n q, hχ'mem⟩ ⟨y, hyb⟩ = (bsPick n q y, bsGradS (bsPick n q) y) from rfl,
          Prod.dist_eq] at h2
        have h3 := le_trans (le_max_left _ _) h2
        rw [dist_eq_norm] at h3
        exact h3

    · intro y
      by_cases hy : (n : ℝ) < ‖y‖
      · rw [bsGradS_eq_zero_of_outside hχn hy, bsGradS_eq_zero_of_outside hχ'mem hy, sub_zero, norm_zero]
        exact hε.le
      · push Not at hy
        have hyb : y ∈ Metric.closedBall (0 : Space) n := by
          rw [mem_closedBall_zero_iff]
          exact hy
        have h1 := ContinuousMap.dist_apply_le_dist (f := bsEmb n χ0) (g := bsEmb n ⟨bsPick n q, hχ'mem⟩) ⟨y, hyb⟩
        have h2 := le_of_lt (lt_of_le_of_lt h1 hd)
        rw [show bsEmb n χ0 ⟨y, hyb⟩ = (χ y, bsGradS χ y) from rfl,
          show bsEmb n ⟨bsPick n q, hχ'mem⟩ ⟨y, hyb⟩ = (bsPick n q y, bsGradS (bsPick n q) y) from rfl,
          Prod.dist_eq] at h2
        have h3 := le_trans (le_max_right _ _) h2
        rw [dist_eq_norm] at h3
        exact h3

end UnforcedLeray.Short.PartIIIb.Concrete
