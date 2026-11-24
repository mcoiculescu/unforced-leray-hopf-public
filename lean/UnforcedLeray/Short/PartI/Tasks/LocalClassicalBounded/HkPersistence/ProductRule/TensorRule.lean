import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.ScalarLeibniz
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.Component

/-!
# Part I, task `PartI:T02/1/2/3/3`: weak product rule for `tensorH3Bilinear`

Source of record: `the November 2 reference manuscript`, lines 261-288.

The tensor product is the finite sum over the four coordinate pairs of the scalar H³ products,
inserted into the tensor carrier by `scalarH3TensorEntry`. Each summand has a weak `∂_j`-derivative
by the scalar Leibniz rule (`bdp_scalar_leibniz`) and the constant-coefficient insertion
(`tensorEntryCLM`, via `Sob.HasWeakDeriv.map_clm`); the finite sum is handled by
`Sob.HasWeakDeriv.sum`.
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
open UnforcedLeray.HeatCylinder

/-- A coordinate insertion `scalarH3TensorEntry i k` carries weak `∂_j`-derivatives to weak
`∂_j`-derivatives. -/
theorem bdp_entry_hasWeakDeriv {c : ℝ} (j i k : Fin 2) (u u' : ScalarH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val u : Plane → ℝ) (Cyl.H.val u' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (scalarH3TensorEntry (c := c) i k u) : Plane → TensorVal)
      (Cyl.H.val (scalarH3TensorEntry (c := c) i k u') : Plane → TensorVal) := by
  intro h
  have hw := h.map_clm (tensorEntryCLM i k)
  have hμ : (Sob.cylinder c).μ = Cyl.cellμ c := Cyl.cylinder_μ_eq c
  have hf := scalarH3TensorEntry_value_ae (c := c) i k u
  have hg := scalarH3TensorEntry_value_ae (c := c) i k u'
  rw [← hμ] at hf hg
  refine hw.congr_ae ?_ ?_
  · filter_upwards [hf] with z hz
    exact hz.symm
  · filter_upwards [hg] with z hz
    exact hz.symm

/-- The value of a finite sum of `H³` tensor elements is, almost everywhere, the sum of the
values. -/
theorem bdp_coe_sum_ae {c : ℝ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → TensorH3 c) :
    (Cyl.H.val (∑ i ∈ s, f i) : Plane → TensorVal) =ᵐ[(Sob.cylinder c).μ]
      fun z => ∑ i ∈ s, (Cyl.H.val (f i) : Plane → TensorVal) z := by
  have e : Cyl.H.val (∑ i ∈ s, f i) = ∑ i ∈ s, Cyl.H.val (f i) :=
    map_sum (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2) f s
  have key : ∀ t : Finset ι,
      (⇑(∑ i ∈ t, Cyl.H.val (f i)) : Plane → TensorVal) =ᵐ[
        Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))]
        fun z => ∑ i ∈ t, (Cyl.H.val (f i) : Plane → TensorVal) z := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
    | insert a t ha ih =>
      filter_upwards [Lp.coeFn_add (Cyl.H.val (f a)) (∑ i ∈ t, Cyl.H.val (f i)), ih]
        with z h1 h2
      rw [Finset.sum_insert ha, h1, Pi.add_apply, h2, Finset.sum_insert ha]
  rw [e]
  exact (Sob.ae_eq_wμ_iff _ _).mp (key s)

/-- **Weak product rule for the tensor product** (`BdpTensorProductRule`, ingredient (i)). -/
theorem bdp_tensorProductRule (c : ℝ) (hc1 : 1 ≤ c) (j : Fin 2) (x x' y y' : VectorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → Vec) (Cyl.H.val y' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (tensorH3Bilinear hc1 x y) : Plane → TensorVal)
      (Cyl.H.val (tensorH3Bilinear hc1 x' y + tensorH3Bilinear hc1 x y') : Plane → TensorVal) := by
  intro hx hy
  have hX : ∀ i : Fin 2, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (vectorH3Component (c := c) i x) : Plane → ℝ)
      (Cyl.H.val (vectorH3Component (c := c) i x') : Plane → ℝ) :=
    fun i => bdp_vectorH3Component_hasWeakDeriv j i x x' hx
  have hY : ∀ i : Fin 2, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (vectorH3Component (c := c) i y) : Plane → ℝ)
      (Cyl.H.val (vectorH3Component (c := c) i y') : Plane → ℝ) :=
    fun i => bdp_vectorH3Component_hasWeakDeriv j i y y' hy
  have hE : ∀ ij : Fin 2 × Fin 2, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (scalarH3TensorEntry (c := c) ij.1 ij.2
        (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x)
          (vectorH3Component (c := c) ij.2 y))) : Plane → TensorVal)
      (Cyl.H.val (scalarH3TensorEntry (c := c) ij.1 ij.2
        (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x') (vectorH3Component (c := c) ij.2 y)
          + scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x)
            (vectorH3Component (c := c) ij.2 y'))) : Plane → TensorVal) :=
    fun ij => bdp_entry_hasWeakDeriv j ij.1 ij.2 _ _
      (bdp_scalar_leibniz hc1 j _ _ _ _ (hX ij.1) (hY ij.2))
  have hL : tensorH3Bilinear hc1 x y = ∑ ij : Fin 2 × Fin 2, scalarH3TensorEntry (c := c) ij.1 ij.2
      (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x)
        (vectorH3Component (c := c) ij.2 y)) := rfl
  have hR : tensorH3Bilinear hc1 x' y + tensorH3Bilinear hc1 x y' =
      ∑ ij : Fin 2 × Fin 2, scalarH3TensorEntry (c := c) ij.1 ij.2
        (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x') (vectorH3Component (c := c) ij.2 y)
          + scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x)
            (vectorH3Component (c := c) ij.2 y')) := by
    show tensorH3ProductValue hc1 x' y + tensorH3ProductValue hc1 x y' = _
    unfold tensorH3ProductValue
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ij _ =>
      (map_add (scalarH3TensorEntry (c := c) ij.1 ij.2) _ _).symm
  rw [hL, hR]
  have hS := Sob.HasWeakDeriv.sum (Finset.univ : Finset (Fin 2 × Fin 2)) (fun ij _ => hE ij)
  refine hS.congr_ae ?_ ?_
  · exact (bdp_coe_sum_ae _ _).symm
  · exact (bdp_coe_sum_ae _ _).symm

end UnforcedLeray.Short.PartI
