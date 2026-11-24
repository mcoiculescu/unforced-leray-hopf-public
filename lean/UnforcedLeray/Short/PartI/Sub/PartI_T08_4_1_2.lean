import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1

/-!
# Part I, task `PartI:T08/4/1/2` (`TrainJetEnergyTimeDerivOfLocal`): decomposition

Source `the November 2 reference manuscript` lines 341-348 (differentiated energy).
The jet energy is a finite sum over words `w` of length `j` and components `k` of the scalar
cell energies `∫_cell (∂_w e_k)²`; the work is the scalar derivative under the integral over the
uncut cell (leaf), and the summation (proved here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf (scalar word energy, differentiation under the integral over the uncut cell)**
(lines 341-348). Assuming the time-local `L²` majorant `TrainTimeDerivLocalL2`: for each word `w`
and component `k`, `∂_w e_k(r) ∈ L²(cell)` for `r` near `s`, `∂_w ∂_s e_k(s) ∈ L²(cell)`, and
`r ↦ ∫_cell (∂_w e_k(r))²` has derivative `2 ∫_cell ∂_w e_k(s) ∂_w ∂_s e_k(s)` at `s`.
(Route: generic `L²` lemma — `F(r) - F(s) = ∫_s^r ∂F`, Minkowski gives `‖F(r) - F(s)‖₂ ≤
|r-s| K^{1/2}`; difference quotients are `L²`-bounded and converge pointwise, hence weakly, while
`F(r) + F(s) → 2F(s)` strongly; time and word derivatives commute by `swtc_main`.) -/
def TrainWordEnergyHasDerivAt : Prop :=
  TrainTimeDerivLocalL2 →
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 → ∀ (w : List Bool) (k : Fin 2),
      (∀ᶠ r in 𝓝 s, MemLp (wordComp w (trainErr tr r) k) 2 (Cyl.cellμ c)) ∧
      MemLp (wordComp w (fun y => deriv (fun t => trainErr tr t y) s) k) 2 (Cyl.cellμ c) ∧
      HasDerivAt (fun r => ∫ z in Cyl.cell c, (wordComp w (trainErr tr r) k z) ^ 2)
        (2 * ∫ z in Cyl.cell c, wordComp w (trainErr tr s) k z *
          wordComp w (fun y => deriv (fun t => trainErr tr t y) s) k z) s

theorem trainJetEnergyTimeDerivOfLocal_of (h : TrainWordEnergyHasDerivAt) :
    TrainJetEnergyTimeDerivOfLocal := by
  intro hloc ν c hν hc tr htr s hs hw j
  have H := h hloc ν c hν hc tr htr s hs hw
  set d : Plane → Vec := fun y => deriv (fun t => trainErr tr t y) s with hd
  have hev : ∀ᶠ r in 𝓝 s, ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (trainErr tr r) k) 2 (Cyl.cellμ c) := by
    rw [Filter.eventually_all_finset]
    intro w _
    rw [Filter.eventually_all]
    intro k
    exact (H w k).1
  have hs0 : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (trainErr tr s) k) 2 (Cyl.cellμ c) := fun w hw' k =>
    (H w k).1.self_of_nhds
  have hder : HasDerivAt (fun r => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, (wordComp w (trainErr tr r) k z) ^ 2)
      (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, 2 * ∫ z in Cyl.cell c,
        wordComp w (trainErr tr s) k z * wordComp w d k z) s := by
    refine HasDerivAt.fun_sum (fun w _ => ?_)
    exact HasDerivAt.fun_sum (fun k _ => (H w k).2.2)
  have hint : ∀ r, (∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      MemLp (wordComp w (trainErr tr r) k) 2 (Cyl.cellμ c)) →
      jetEnergy c j (trainErr tr r) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ∫ z in Cyl.cell c, (wordComp w (trainErr tr r) k z) ^ 2 := by
    intro r hr
    unfold jetEnergy jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun w hw' => ?_)
      rw [integral_finsetSum]
      · simp [sq]
      · intro k _
        exact (hr w hw' k).integrable_mul (hr w hw' k)
    · intro w hw'
      refine integrable_finsetSum _ (fun k _ => ?_)
      exact (hr w hw' k).integrable_mul (hr w hw' k)
  have hpair : jetPair c j (trainErr tr s) d = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w (trainErr tr s) k z * wordComp w d k z := by
    unfold jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun w hw' => ?_)
      rw [integral_finsetSum]
      intro k _
      exact (hs0 w hw' k).integrable_mul (H w k).2.1
    · intro w hw'
      refine integrable_finsetSum _ (fun k _ => ?_)
      exact (hs0 w hw' k).integrable_mul (H w k).2.1
  have hsum : (2 * jetPair c j (trainErr tr s) d) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      2 * ∫ z in Cyl.cell c, wordComp w (trainErr tr s) k z * wordComp w d k z := by
    rw [hpair, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by rw [Finset.mul_sum])
  rw [hsum]
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [hev] with r hr using hint r hr

end UnforcedLeray.Short.PartI
