import UnforcedLeray.Short.PartI.Sub.T02_1_2_4
import UnforcedLeray.Lib.SobolevC.CylDensity

/-!
# Part I, task `PartI:T02/1/2/4`: density of derivative paths (`DerivDense`)

Target `derivDense : DerivDense` (`Short/PartI/Sub/T02_1_2_4.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288
(smoothness of the data; density of smooth periodic fields).

Proof route.

1. Pointwise density (`dd_exists_near`): the elements `y ∈ H³` having a weak `∂_j`-derivative
   `y' ∈ H³` are dense in `H³`. Smooth periodic fields with compact support in `η` are dense
   (`Sob.W.cylinder_dense_smooth`); for such a field `u` the field `∂_j u` is again smooth and
   periodic (`IsCylSmooth.dir`), so `W.ofCylSmooth (∂_j u)` is the derivative element
   (`Sob.hasWeakDeriv_cylinder_dir`, `Sob.W.value_ofCylSmooth`).
2. Finite partition (`derivDense`): for each time `t`, pick `ξ t` with a derivative and
   `dist (u t) (ξ t) < η/2`. The sets `{s | dist (u s) (ξ t) < η/2}` are open and cover the
   compact interval, so finitely many `F` suffice. The weights `g t s = max 0 (η/2 - dist (u s) (ξ t))`
   are continuous and not all zero, and `φ t s = g t s / Σ_{t'∈F} g t' s` is a continuous partition of
   unity subordinate to the cover. Then `v s = Σ_{t∈F} φ t s • ξ t` and `v' s = Σ_{t∈F} φ t s • ξ' t`
   give the derivative path and `‖u s - v s‖ ≤ η/2`.
3. Linearity (`dd_hasWD_sum`): the weak derivative relation is preserved by finite sums and
   scalar multiples with fixed real weights.
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

/-! ### The pointwise weak-derivative relation -/

/-- `DDHasWD c j x x'`: `x'` is the periodic weak `∂_j`-derivative of `x` in `H³`. This is the
pointwise content of `HasDerivPath c T j a a'` (`Short/PartI/Sub/T02_1_2.lean`). -/
def DDHasWD (c : ℝ) (j : Fin 2) (x x' : VectorH3 c) : Prop :=
  Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
    (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec)

theorem dd_hasWD_add {c : ℝ} {j : Fin 2} {y y' z z' : VectorH3 c}
    (hy : DDHasWD c j y y') (hz : DDHasWD c j z z') : DDHasWD c j (y + z) (y' + z') := by
  unfold DDHasWD at hy hz ⊢
  exact (hy.add hz).congr_ae (val_add_ae y z).symm (val_add_ae y' z').symm

theorem dd_hasWD_smul {c : ℝ} {j : Fin 2} (a : ℝ) {y y' : VectorH3 c}
    (hy : DDHasWD c j y y') : DDHasWD c j (a • y) (a • y') := by
  unfold DDHasWD at hy ⊢
  have e : ∀ z : VectorH3 c, (Cyl.H.val (a • z) : Plane → Vec) =ᵐ[(Sob.cylinder c).μ]
      a • (Cyl.H.val z : Plane → Vec) := fun z => by
    have hl : Cyl.H.val (a • z) = a • Cyl.H.val z :=
      map_smul (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2) a z
    refine (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))).mp ?_
    rw [hl]
    exact Lp.coeFn_smul a _
  exact (hy.smul a).congr_ae (e y).symm (e y').symm

/-- Finite sums with real weights preserve the weak-derivative relation. -/
theorem dd_hasWD_sum {c : ℝ} {j : Fin 2} {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (a : ι → ℝ) (x x' : ι → VectorH3 c) (h : ∀ i ∈ F, DDHasWD c j (x i) (x' i)) :
    DDHasWD c j (∑ i ∈ F, a i • x i) (∑ i ∈ F, a i • x' i) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold DDHasWD
    have h0 : (Cyl.H.val (0 : VectorH3 c) : Plane → Vec) =ᵐ[(Sob.cylinder c).μ] 0 := by
      have hl : Cyl.H.val (0 : VectorH3 c) = 0 :=
        map_zero (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2)
      refine (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))).mp ?_
      rw [hl]
      exact Lp.coeFn_zero _ _ _
    exact Sob.HasWeakDeriv.congr_ae Sob.HasWeakDeriv.zero h0.symm h0.symm
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact dd_hasWD_add (dd_hasWD_smul (a i) (h i (Finset.mem_insert_self i F)))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-! ### Pointwise density of elements with a derivative -/

/-- The elements of `H³` with a weak `∂_j`-derivative in `H³` are dense (step 1). -/
theorem dd_exists_near (c : ℝ) (hc : 0 < c) (j : Fin 2) (x : VectorH3 c) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : VectorH3 c, (∃ y' : VectorH3 c, DDHasWD c j y y') ∧ dist x y < ε := by
  obtain ⟨y, hy, hxy⟩ := (Sob.W.cylinder_dense_smooth (𝕜 := ℝ) (F := Vec) (k := 3)
    (ρ := Cyl.ρwW c ^ (0 : ℝ)) (p := 2) hc (by simp)).exists_dist_lt x hε
  obtain ⟨u, hu, hyu⟩ := hy
  have hu' : Sob.IsCylSmooth c (fun z => fderiv ℝ u z ((Sob.cylinder c).dir j)) :=
    hu.dir ((Sob.cylinder c).dir j)
  obtain ⟨y', hy'⟩ : ∃ y' : VectorH3 c,
      (Cyl.H.val y' : ℝ × ℝ → Vec) =ᵐ[(Sob.cylinder c).μ]
        (fun z => fderiv ℝ u z ((Sob.cylinder c).dir j)) :=
    ⟨Sob.W.ofCylSmooth (𝕜 := ℝ) (k := 3) (p := 2) (ρ := Cyl.ρwW c ^ (0 : ℝ)) hc _ hu',
      (Sob.ae_eq_wμ_iff _ _).mp
        (Sob.W.value_ofCylSmooth (𝕜 := ℝ) (k := 3) (p := 2) (ρ := Cyl.ρwW c ^ (0 : ℝ))
          hc _ hu')⟩
  refine ⟨y, ⟨y', ?_⟩, hxy⟩
  unfold DDHasWD
  exact (Sob.hasWeakDeriv_cylinder_dir hc hu ((Sob.cylinder c).dir j)).congr_ae
    hyu.symm hy'.symm

/-! ### Density of derivative paths -/

theorem derivDense : DerivDense := by
  intro c T hc _hT j u η hη
  have hnear : ∀ t : Icc (0 : ℝ) T,
      ∃ y : VectorH3 c, (∃ y' : VectorH3 c, DDHasWD c j y y') ∧ dist (u t) y < η / 2 :=
    fun t => dd_exists_near c hc j (u t) (by linarith)
  choose ξ hξD hξ using hnear
  choose ξ' hξ' using hξD
  -- A finite subcover by the sets where `u` is close to a derivative element.
  have hopen : ∀ t : Icc (0 : ℝ) T, IsOpen {s : Icc (0 : ℝ) T | dist (u s) (ξ t) < η / 2} :=
    fun t => isOpen_lt (u.continuous.dist continuous_const) continuous_const
  have hcov : (Set.univ : Set (Icc (0 : ℝ) T)) ⊆
      ⋃ t, {s : Icc (0 : ℝ) T | dist (u s) (ξ t) < η / 2} :=
    fun s _ => Set.mem_iUnion.mpr ⟨s, hξ s⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t : Icc (0 : ℝ) T => {s : Icc (0 : ℝ) T | dist (u s) (ξ t) < η / 2}) hopen hcov
  have hcov' : ∀ s : Icc (0 : ℝ) T, ∃ t ∈ F, dist (u s) (ξ t) < η / 2 := by
    intro s
    obtain ⟨t, ht, hst⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ s))
    exact ⟨t, ht, hst⟩
  -- Unnormalised weights and their normalisation.
  obtain ⟨g, hg⟩ : ∃ g : Icc (0 : ℝ) T → Icc (0 : ℝ) T → ℝ,
      ∀ t s, g t s = max 0 (η / 2 - dist (u s) (ξ t)) :=
    ⟨fun t s => max 0 (η / 2 - dist (u s) (ξ t)), fun _ _ => rfl⟩
  have hg0 : ∀ t s, 0 ≤ g t s := fun t s => by
    rw [hg]
    exact le_max_left _ _
  have hgc : ∀ t, Continuous (g t) := fun t => by
    have e : g t = fun s => max 0 (η / 2 - dist (u s) (ξ t)) := funext fun s => hg t s
    rw [e]
    exact continuous_const.max (continuous_const.sub (u.continuous.dist continuous_const))
  obtain ⟨G, hG⟩ : ∃ G : Icc (0 : ℝ) T → ℝ, ∀ s, G s = ∑ t ∈ F, g t s :=
    ⟨fun s => ∑ t ∈ F, g t s, fun _ => rfl⟩
  have hGpos : ∀ s, 0 < G s := by
    intro s
    obtain ⟨t, ht, hdt⟩ := hcov' s
    have h1 : 0 < g t s := by
      rw [hg]
      exact lt_max_of_lt_right (by linarith)
    rw [hG]
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (fun t' _ => hg0 t' s) ht)
  have hGc : Continuous G := by
    have e : G = fun s => ∑ t ∈ F, g t s := funext fun s => hG s
    rw [e]
    exact continuous_finsetSum F (fun t _ => hgc t)
  obtain ⟨φ, hφ⟩ : ∃ φ : Icc (0 : ℝ) T → Icc (0 : ℝ) T → ℝ, ∀ t s, φ t s = g t s / G s :=
    ⟨fun t s => g t s / G s, fun _ _ => rfl⟩
  have hφ0 : ∀ t s, 0 ≤ φ t s := fun t s => by
    rw [hφ]
    exact div_nonneg (hg0 t s) (hGpos s).le
  have hφc : ∀ t, Continuous (φ t) := fun t => by
    have e : φ t = fun s => g t s / G s := funext fun s => hφ t s
    rw [e]
    exact (hgc t).div hGc (fun s => (hGpos s).ne')
  have hφsum : ∀ s, ∑ t ∈ F, φ t s = 1 := fun s => by
    simp only [hφ]
    rw [← Finset.sum_div, ← hG s]
    exact div_self (hGpos s).ne'
  have hφdist : ∀ t s, 0 < φ t s → dist (u s) (ξ t) < η / 2 := by
    intro t s hpos
    rw [hφ] at hpos
    have hgpos : 0 < g t s := (div_pos_iff_of_pos_right (hGpos s)).mp hpos
    rw [hg] at hgpos
    by_contra hcon
    have hz : max (0 : ℝ) (η / 2 - dist (u s) (ξ t)) = 0 :=
      max_eq_left (by linarith [not_lt.mp hcon])
    linarith
  -- The approximating path and its derivative.
  obtain ⟨v0, hv0⟩ : ∃ v : Icc (0 : ℝ) T → VectorH3 c,
      ∀ s, v s = ∑ t ∈ F, φ t s • ξ t :=
    ⟨fun s => ∑ t ∈ F, φ t s • ξ t, fun _ => rfl⟩
  obtain ⟨v0', hv0'⟩ : ∃ v : Icc (0 : ℝ) T → VectorH3 c,
      ∀ s, v s = ∑ t ∈ F, φ t s • ξ' t :=
    ⟨fun s => ∑ t ∈ F, φ t s • ξ' t, fun _ => rfl⟩
  have hv0c : Continuous v0 := by
    have e : v0 = fun s => ∑ t ∈ F, φ t s • ξ t := funext hv0
    rw [e]
    exact continuous_finsetSum F (fun t _ => (hφc t).smul continuous_const)
  have hv0c' : Continuous v0' := by
    have e : v0' = fun s => ∑ t ∈ F, φ t s • ξ' t := funext hv0'
    rw [e]
    exact continuous_finsetSum F (fun t _ => (hφc t).smul continuous_const)
  refine ⟨⟨v0, hv0c⟩, ⟨v0', hv0c'⟩, ?_, ?_⟩
  · intro s
    show DDHasWD c j (v0 s) (v0' s)
    rw [hv0 s, hv0' s]
    exact dd_hasWD_sum F (fun t => φ t s) ξ ξ' (fun t _ => hξ' t)
  · intro s
    show ‖u s - v0 s‖ ≤ η
    rw [hv0 s]
    have key : u s - ∑ t ∈ F, φ t s • ξ t = ∑ t ∈ F, φ t s • (u s - ξ t) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hφsum s, one_smul]
    rw [key]
    have hterm : ∀ t ∈ F, φ t s * dist (u s) (ξ t) ≤ φ t s * (η / 2) := by
      intro t _
      rcases (hφ0 t s).eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      · exact mul_le_mul_of_nonneg_left (hφdist t s hpos).le (hφ0 t s)
    calc ‖∑ t ∈ F, φ t s • (u s - ξ t)‖ ≤ ∑ t ∈ F, ‖φ t s • (u s - ξ t)‖ := norm_sum_le _ _
      _ = ∑ t ∈ F, φ t s * dist (u s) (ξ t) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hφ0 t s), dist_eq_norm]
      _ ≤ ∑ t ∈ F, φ t s * (η / 2) := Finset.sum_le_sum hterm
      _ = η / 2 := by rw [← Finset.sum_mul, hφsum s, one_mul]
      _ ≤ η := by linarith

end UnforcedLeray.Short.PartI
