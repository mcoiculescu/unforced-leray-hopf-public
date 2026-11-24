import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.AdvInt

/-!
# Part I, task `PartI:T08/7/2/3/1` (`JTExpand`): integrated Leibniz expansion

Source: `the November 2 reference manuscript` lines 352-358.

Pointwise, `∂_w f_k · ∂_w (u·∇)h_k` is the list sum over `wacSplits w` of
`∑_m ∂_w f_k · (∂_a u_m)(∂_{b·dirOf m} h_k)` (`jai_expand` and `dirOf 0 = true`,
`dirOf 1 = false`). Integrating over the cell, the finite sums are exchanged with the integral
(`integral_finsetSum`, `integral_finset_sum`-style) and the list sum with the integral
(induction on the list), each summand being integrable by `jai_int3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem jte_int_list {μ : Measure Plane} {α : Type*} (G : α → Plane → ℝ) :
    ∀ L : List α, (∀ p ∈ L, Integrable (G p) μ) →
      ∫ z, (L.map (fun p => G p z)).sum ∂μ = (L.map (fun p => ∫ z, G p z ∂μ)).sum
  | [], _ => by simp
  | p :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (h p (by simp)) (jai_list_integrable G L fun q hq => h q (by simp [hq])),
      jte_int_list G L fun q hq => h q (by simp [hq])]

theorem jte_dir0 : dirOf 0 = true := by decide

theorem jte_dir1 : dirOf 1 = false := by decide

/-- Pointwise Leibniz expansion of one word of the `k`-th component of `f · ∂_w (u·∇)h`. -/
theorem jte_pointwise (u h f : Plane → Vec) (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w f k z * wordComp w (advB u h) k z =
      ((wacSplits w).map (fun p => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))).sum := by
  rw [jai_expand u h hu hh w k z, jai_list_mul]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [Fin.sum_univ_two, jte_dir0, jte_dir1]
  ring

theorem jtExpand_proof : UnforcedLeray.Short.PartI.JTExpand := by
  intro j c u h f hu hh hf hor hbu hbh
  have hbnd : ∀ (a : List Bool) (m : Fin 2) (b : List Bool) (k : Fin 2),
      (MemLp (wordComp a u m) 2 (Cyl.cellμ c) ∧ ∃ M : ℝ, ∀ z, |wordComp b h k z| ≤ M) ∨
      (MemLp (wordComp b h k) 2 (Cyl.cellμ c) ∧ ∃ M : ℝ, ∀ z, |wordComp a u m z| ≤ M) := by
    intro a m b k
    rcases hor with hUL | hHL
    · exact Or.inl ⟨hUL.2.2 a m, hbh b k⟩
    · exact Or.inr ⟨hHL.2.2 b k, hbu a m⟩
  have hT : ∀ (w : List Bool) (k : Fin 2) (p : List Bool × List Bool) (m : Fin 2),
      Integrable (fun z => wordComp w f k z *
        (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z)) (Cyl.cellμ c) := by
    intro w k p m
    exact jai_int3 (μ := Cyl.cellμ c) (wordComp w f k)
      (fun z => wordComp p.1 u m z) (fun z => wordComp (p.2 ++ [dirOf m]) h k z) (hf.2.2 w k)
      (contDiff_wordComp hu p.1 m).continuous.aestronglyMeasurable
      (contDiff_wordComp hh (p.2 ++ [dirOf m]) k).continuous.aestronglyMeasurable
      (hbnd p.1 m (p.2 ++ [dirOf m]) k)
  have hG : ∀ (w : List Bool) (k : Fin 2) (p : List Bool × List Bool),
      Integrable (fun z => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z)) (Cyl.cellμ c) :=
    fun w k p => integrable_finsetSum _ fun m _ => hT w k p m
  have hL : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      Integrable (fun z => ((wacSplits w).map (fun p => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))).sum)
        (Cyl.cellμ c) := by
    intro w _ k
    have key := jai_list_integrable (μ := Cyl.cellμ c)
      (G := fun (p : List Bool × List Bool) (z : Plane) => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))
      (wacSplits w) (fun p _ => hG w k p)
    exact key
  have hW : ∀ w ∈ wordsOfLength j, Integrable (fun z => ∑ k : Fin 2,
      ((wacSplits w).map (fun p => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))).sum)
        (Cyl.cellμ c) := fun w hw => integrable_finsetSum _ fun k _ => hL w hw k
  have e : (fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      wordComp w f k z * wordComp w (advB u h) k z) = fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ((wacSplits w).map (fun p => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))).sum := by
    funext z
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ =>
      jte_pointwise u h f hu hh w k z
  unfold jetPair
  show ∫ z, (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w (advB u h) k z)
      ∂(Cyl.cellμ c) = _
  rw [e, integral_finsetSum _ hW]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [integral_finsetSum _ (fun k _ => hL w hw k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [jte_int_list (μ := Cyl.cellμ c) (fun (p : List Bool × List Bool) (z : Plane) => ∑ m : Fin 2,
        wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))
      (wacSplits w) fun p _ => hG w k p]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  exact integral_finsetSum _ fun m _ => hT w k p m

end UnforcedLeray.Short.PartI
