import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N3

/-!
# Part I, `N5`: weak Leibniz rule for the advection term (source lines 261-288)

Proves `advectionWeakLeibniz : AdvectionWeakLeibniz` from `cylWeakProductSmul` (N1),
`cylWeakDerivCommute` (N3) and the value/derivative calculus of `Sob.W`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The representative of an `H^m` element is square integrable on the cell. -/
theorem adv5_memLp_hVal {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m) :
    MemLp (hVal x) 2 (Cyl.cellμ c) := by
  unfold hVal
  exact MemLp.mono_measure (wμ_zero_eq c).symm.le (Lp.memLp _)

/-- Components of a square integrable `Vec2`-valued field are square integrable. -/
theorem adv5_memLp_comp {f : Plane → Cyl.Vec2} {μ : Measure Plane} (hf : MemLp f 2 μ)
    (i : Fin 2) : MemLp (fun z => f z i) 2 μ := by
  exact hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)

/-- The `i`-th component of `v` has weak `∂_j`-derivative the `i`-th component of `∂_j v`. -/
theorem adv5_hw_comp {c : ℝ} {m : ℕ} (v : Cyl.H ℝ Cyl.Vec2 c 0 (m + 2)) (j i : Fin 2) :
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j]
      (fun z => hVal (Sob.W.restrict (by omega : m + 1 ≤ m + 2) v :
        Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) z i)
      (fun z => hVal (Sob.W.partialDeriv (k := m + 1) j v) z i) := by
  have h := Sob.W.hasWeakDeriv v (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 (m + 1)))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at h
  exact h.map_clm (EuclideanSpace.proj (𝕜 := ℝ) i)

/-- The field `∂_i (res w)` has weak `∂_j`-derivative `∂_j ∂_i w` (as values). -/
theorem adv5_hw_dd {c : ℝ} {m : ℕ} (w : Cyl.H ℝ Cyl.Vec2 c 0 (m + 2)) (i j : Fin 2) :
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j]
      (hVal (Sob.W.partialDeriv (k := m) i
        (Sob.W.restrict (by omega : m + 1 ≤ m + 2) w : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1))))
      (hVal (Sob.W.partialDeriv (k := m) j (Sob.W.partialDeriv (k := m + 1) i w))) := by
  have h1 := Sob.W.hasWeakDeriv w (Sob.Idx.cons i (Sob.Idx.zero : Sob.Idx 2 (m + 1)))
  have h2 := Sob.W.hasWeakDeriv w
    (Sob.Idx.cons i (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 m)))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at h1
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at h2
  have h := Sob.HasWeakDeriv.of_cons h1 h2
  unfold hVal
  rw [Sob.W.value_partialDeriv, Sob.W.value_partialDeriv, Sob.W.deriv_partialDeriv]
  exact h

/-- **Lemma N5 (weak Leibniz rule for the advection term, from N1 and N3).** -/
theorem advectionWeakLeibniz : AdvectionWeakLeibniz := by
  intro c m v w j
  refine Sob.HasWeakDeriv.sum Finset.univ (fun i _ => ?_)
  have hc := cylWeakProductSmul c j
    (fun z => hVal (Sob.W.restrict (by omega : m + 1 ≤ m + 2) v :
      Cyl.H ℝ Cyl.Vec2 c 0 (m + 1)) z i)
    (fun z => hVal (Sob.W.partialDeriv (k := m + 1) j v) z i)
    (hVal (Sob.W.partialDeriv (k := m) i
      (Sob.W.restrict (by omega : m + 1 ≤ m + 2) w : Cyl.H ℝ Cyl.Vec2 c 0 (m + 1))))
    (hVal (Sob.W.partialDeriv (k := m) j (Sob.W.partialDeriv (k := m + 1) i w)))
    (adv5_memLp_comp (adv5_memLp_hVal _) i) (adv5_memLp_comp (adv5_memLp_hVal _) i)
    (adv5_memLp_hVal _) (adv5_memLp_hVal _)
    (adv5_hw_comp v j i) (adv5_hw_dd w i j)
  refine hc.congr_ae EventuallyEq.rfl ?_
  filter_upwards [(cylWeakDerivCommute c m i j w).symm.filter_mono (ae_cyl_le c)] with z hz
  simp only [hz]

end UnforcedLeray.Short.PartI
