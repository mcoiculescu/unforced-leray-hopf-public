import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `PartIII-b:C/near/masked/30`: `outBandPartition` (source 3974-3977)

The output regions `s < s₋`, the bins `[l_j, l_{j+1})` (`j < N`, `l_j = binEdge s₋ S N j`) and
`s ≥ S` partition the chart.  Pointwise, the indicators telescope (induction on the number of bins
for a monotone edge sequence); on `L²` each restriction is `ind · u` a.e., and the sum is the
identity by `Lp.ext`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- One step of the telescope: for `l_N ≤ l_{N+1}`, `1_{s ≥ l_N} = 1_{l_N ≤ s < l_{N+1}} + 1_{s ≥ l_{N+1}}`. -/
theorem ind_ageAbove_step {a b : ℝ} (hab : a ≤ b) (x : Chart) :
    ind (ageAbove a) x = ind (ageBand a b) x + ind (ageAbove b) x := by
  unfold ind ageAbove ageBand
  by_cases h1 : a ≤ x.1
  · by_cases h2 : b ≤ x.1
    · have h3 : ¬ x.1 < b := not_lt.2 h2
      simp [Set.indicator, h1, h2, h3]
    · have h3 : x.1 < b := lt_of_not_ge h2
      simp [Set.indicator, h1, h2, h3]
  · have h2 : ¬ b ≤ x.1 := fun h => h1 (le_trans hab h)
    simp [Set.indicator, h1, h2]

/-- The telescoped partition of the chart by a monotone edge sequence. -/
theorem ind_partition_telescope (l : ℕ → ℝ) (hl : Monotone l) (N : ℕ) (x : Chart) :
    ind (ageBelow (l 0)) x + (∑ j ∈ Finset.range N, ind (ageBand (l j) (l (j + 1))) x) +
      ind (ageAbove (l N)) x = 1 := by
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, add_zero]
    exact ind_below_add_above (l 0) x
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := ind_ageAbove_step (hl (Nat.le_succ N)) x
    linarith

/-- The sum of output restrictions of `u`, a.e. pointwise. -/
theorem sum_outRestr_ae (c : ℝ) (A : ℕ → Set Chart) (hA : ∀ j, MeasurableSet (A j)) (N : ℕ)
    (u : Hsp c) :
    ((∑ j ∈ Finset.range N, outRestr c (A j) u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      fun x => ∑ j ∈ Finset.range N, ind (A j) x • (u : Chart → EuclideanSpace ℝ (Fin 2)) x := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact (Lp.coeFn_zero _ _ _).trans (by rfl)
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    filter_upwards [Lp.coeFn_add (∑ j ∈ Finset.range N, outRestr c (A j) u) (outRestr c (A N) u),
      ih, restrLp_ae (hA N) u] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2]
    change _ + (restrLp (ageμ c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (A N) u : Chart → EuclideanSpace ℝ (Fin 2)) x = _
    rw [h3]
    rfl

/-- **`outBandPartition`** (source 3974-3977): the output regions partition `H`. -/
theorem outBandPartition : OutBandPartition := by
  intro c sm S δ hsm hS hδ u
  have hN : binCount sm S δ ≠ 0 := (binCount_pos sm S δ).ne'
  set N := binCount sm S δ with hNdef
  have hmono : Monotone (binEdge sm S N) :=
    monotone_nat_of_le_succ (fun j => (binEdge_lt_succ hsm hS hN j).le)
  have hl0 : binEdge sm S N 0 = sm := binEdge_zero sm S N
  have hlN : binEdge sm S N N = S := binEdge_last hsm hN
  have hA : ∀ j, MeasurableSet (ageBand (binEdge sm S N j) (binEdge sm S N (j + 1))) :=
    fun j => measurableSet_ageBand _ _
  have hsum := sum_outRestr_ae c (fun j => ageBand (binEdge sm S N j) (binEdge sm S N (j + 1)))
    hA N u
  have hbelow : (outRestr c (ageBelow sm) u : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      fun x => ind (ageBelow sm) x • (u : Chart → EuclideanSpace ℝ (Fin 2)) x :=
    restrLp_ae (measurableSet_ageBelow sm) u
  have habove : (outRestr c (ageAbove S) u : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      fun x => ind (ageAbove S) x • (u : Chart → EuclideanSpace ℝ (Fin 2)) x :=
    restrLp_ae (measurableSet_ageAbove S) u
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (outRestr c (ageBelow sm) u +
      (∑ j ∈ Finset.range N, outRestr c (ageBand (binEdge sm S N j) (binEdge sm S N (j + 1))) u))
      (outRestr c (ageAbove S) u),
    Lp.coeFn_add (outRestr c (ageBelow sm) u)
      (∑ j ∈ Finset.range N, outRestr c (ageBand (binEdge sm S N j) (binEdge sm S N (j + 1))) u),
    hsum, hbelow, habove] with x e1 e2 e3 e4 e5
  have hT := ind_partition_telescope (binEdge sm S N) hmono N x
  rw [hl0, hlN] at hT
  rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, e5]
  calc _ = (ind (ageBelow sm) x + (∑ j ∈ Finset.range N,
        ind (ageBand (binEdge sm S N j) (binEdge sm S N (j + 1))) x) + ind (ageAbove S) x) •
          (u : Chart → EuclideanSpace ℝ (Fin 2)) x := by
        rw [add_smul, add_smul, Finset.sum_smul]
    _ = (u : Chart → EuclideanSpace ℝ (Fin 2)) x := by rw [hT, one_smul]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
