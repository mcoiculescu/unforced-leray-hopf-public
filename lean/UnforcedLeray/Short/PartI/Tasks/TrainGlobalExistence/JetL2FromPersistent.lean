import Mathlib.Algebra.Order.Chebyshev
import UnforcedLeray.Short.PartI.Sub.T04.Defs
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSobolevRep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.AePeriodicEq

/-!
# Part I, task `PartI:T04/3`, target `jetL2FromPersistent`: all jets in `L²(cell)`

Source of record: `the November 2 reference manuscript`, lines 268-269 and 285
(the datum is in every `H^k`, and the solution continues `L²` membership).

For the jet order `j` take `k := j` and the lift `uk ∈ C([0,T], H^{j+3})` of `u`.  The Sobolev
representative `g (uk t)` (`cylSobolevRep`) and `w t` are continuous periodic and agree a.e. on the
cell (both represent the value of `u t`), so they agree (`aePeriodicEq`).  The jet norm of `w t` is
bounded by the sum of its `2^j` coordinate words, each a.e. a weak derivative of `uk t`, of cell
`L²` norm `≤ ‖uk t‖ ≤ ‖uk‖`; hence `‖D^j w t‖²_{L²} ≤ 4^j ‖uk‖²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem jl_norm_sq_L2 {c : ℝ} (f : Cyl.L2v c) :
    ‖f‖ ^ 2 = ∫ z, ‖(f : Plane → Vec) z‖ ^ 2 ∂(Cyl.cellμ c) := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℝ) f f
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact real_inner_self_eq_norm_sq _

theorem jl_integrable_L2 {c : ℝ} (f : Cyl.L2v c) :
    Integrable (fun z => ‖(f : Plane → Vec) z‖ ^ 2) (Cyl.cellμ c) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  exact real_inner_self_eq_norm_sq _

theorem jl_iterD_ofFn (f : Plane → Vec) (hf : ContDiff ℝ ∞ f) :
    ∀ (n : ℕ) (m : Fin n → Plane) (z : Plane),
      Sob.iterD (List.ofFn m) f z = iteratedFDeriv ℝ n f z m := by
  intro n
  induction n with
  | zero =>
    intro m z
    simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m z
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    have hIH : Sob.iterD (List.ofFn fun i => m i.succ) f =
        fun y => iteratedFDeriv ℝ n f y (fun i => m i.succ) := by
      funext y
      exact ih (fun i => m i.succ) y
    have key := (hd z).iteratedFDeriv_succ_apply_left' (m := m)
    rw [List.ofFn_succ, Sob.iterD_cons, hIH]
    exact key.symm

/-- The coordinate of a point of the plane along `cylDir b`. -/
def jlCoord (b : Fin 2) (x : Plane) : ℝ := if b = 0 then x.1 else x.2

theorem jl_decomp (x : Plane) : x = ∑ b : Fin 2, jlCoord b x • Sob.cylDir b := by
  rw [Fin.sum_univ_two]
  ext <;> simp [jlCoord, Sob.cylDir]

theorem jl_coord_le (b : Fin 2) (x : Plane) : |jlCoord b x| ≤ ‖x‖ := by
  unfold jlCoord
  split_ifs
  · rw [← Real.norm_eq_abs]; exact norm_fst_le x
  · rw [← Real.norm_eq_abs]; exact norm_snd_le x

/-- The jet norm is bounded by the sum of the coordinate words of length `l`. -/
theorem jl_norm_le_sum (f : Plane → Vec) (hf : ContDiff ℝ ∞ f) (l : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ l f z‖ ≤
      ∑ r : Fin l → Fin 2, ‖iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun r _ => norm_nonneg _)) ?_
  intro m
  have hexp : iteratedFDeriv ℝ l f z m =
      ∑ r : Fin l → Fin 2, (∏ i, jlCoord (r i) (m i)) •
        iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i)) := by
    have h1 : iteratedFDeriv ℝ l f z m =
        iteratedFDeriv ℝ l f z (fun i => ∑ b : Fin 2, jlCoord b (m i) • Sob.cylDir b) := by
      congr 1
      funext i
      exact jl_decomp (m i)
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ContinuousMultilinearMap.map_smul_univ]
  have hbound : ∀ r : Fin l → Fin 2, |∏ i, jlCoord (r i) (m i)| ≤ ∏ i, ‖m i‖ := by
    intro r
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => jl_coord_le _ _)
  rw [hexp]
  calc ‖∑ r : Fin l → Fin 2, (∏ i, jlCoord (r i) (m i)) •
          iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i))‖
      ≤ ∑ r : Fin l → Fin 2, ‖(∏ i, jlCoord (r i) (m i)) •
          iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin l → Fin 2, (∏ i, ‖m i‖) *
          ‖iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i))‖ := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbound r) (norm_nonneg _)
    _ = (∑ r : Fin l → Fin 2, ‖iteratedFDeriv ℝ l f z (fun i => Sob.cylDir (r i))‖) *
          ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

/-- **Target** `jetL2FromPersistent` (`PartI:T04/3`). -/
theorem jetL2FromPersistent : JetL2FromPersistent := by
  intro c T u w hc hc1 hT hpers hw j
  obtain ⟨uk, huk⟩ := hpers j
  obtain ⟨g, C, hgsm, hgrep, -⟩ := cylSobolevRep c hc hc1 j
  refine ⟨(4 : ℝ) ^ j * ‖uk‖ ^ 2, ?_⟩
  intro s hs
  set t : Icc (0 : ℝ) T := ⟨s, hs⟩ with ht
  -- the representative `w s` is `g (uk t)`
  have hwg : w s = g (uk t) := by
    refine aePeriodicEq c hc _ _ (hw.smooth s hs).continuous (hgsm (uk t)).1.continuous
      (hw.periodic s hs) (hgsm (uk t)).2 ?_
    have h1 := hw.represents t Sob.Idx.zero
    have h2 := hgrep (uk t) Sob.Idx.zero
    have e0 : (vecH3CellDerivCLM (Sob.Idx.zero : Sob.Idx 2 3) (u t) : Plane → Vec) =
        cellDeriv c (Sob.Idx.castLE (by omega : j + 1 ≤ j + 3)
          (Sob.Idx.zero : Sob.Idx 2 (j + 1))) (uk t) := by
      rw [← huk t]
      rfl
    rw [e0] at h1
    filter_upwards [h1, h2] with z hz1 hz2
    have a1 : Sob.iterD ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 3)) (w t.1) z = w s z :=
      rfl
    have a2 : Sob.iterD ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 (j + 1))) (g (uk t)) z
        = g (uk t) z := rfl
    rw [a1] at hz1
    rw [a2] at hz2
    exact hz1.symm.trans hz2
  have hsm := hw.smooth s hs
  -- the coordinate words
  let β : (Fin j → Fin 2) → Sob.Idx 2 (j + 1) := fun r => ⟨⟨j, by omega⟩, r⟩
  let F : (Fin j → Fin 2) → Cyl.L2v c := fun r =>
    weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (j + 3) 2
        (Sob.Idx.castLE (by omega : j + 1 ≤ j + 3) (β r)) (uk t))
  have hFae : ∀ r, (F r : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) := by
    intro r
    have h := hgrep (uk t) (β r)
    rw [hwg]
    exact h
  have hFnorm : ∀ r, ‖F r‖ ^ 2 ≤ ‖uk‖ ^ 2 := by
    intro r
    have h1 : ‖F r‖ =
        ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (j + 3) 2
          (Sob.Idx.castLE (by omega : j + 1 ≤ j + 3) (β r)) (uk t)‖ :=
      (weightedToCellL2Isometry c).norm_map _
    have h2 : ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (j + 3) 2
          (Sob.Idx.castLE (by omega : j + 1 ≤ j + 3) (β r)) (uk t)‖ ^ 2 ≤ ‖uk t‖ ^ 2 := by
      rw [Sob.W.norm_sq (uk t)]
      exact Finset.single_le_sum (f := fun α : Sob.Idx 2 (j + 3) =>
        ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (j + 3) 2 α (uk t)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ _)
    rw [h1]
    exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm uk t) 2)
  have hWint : ∀ r : Fin j → Fin 2, Integrable (fun z => ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2)
      (Cyl.cellμ c) := by
    intro r
    refine (jl_integrable_L2 (F r)).congr ?_
    filter_upwards [hFae r] with z hz
    rw [hz]
  have hWint' : ∀ r : Fin j → Fin 2, ∫ z, ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2
      ∂(Cyl.cellμ c) ≤ ‖uk‖ ^ 2 := by
    intro r
    have e : ∫ z, ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2 ∂(Cyl.cellμ c) =
        ‖F r‖ ^ 2 := by
      rw [jl_norm_sq_L2 (F r)]
      refine integral_congr_ae ?_
      filter_upwards [hFae r] with z hz
      rw [hz]
    rw [e]
    exact hFnorm r
  have hcard : (Finset.univ : Finset (Fin j → Fin 2)).card = 2 ^ j := by simp
  have hpt : ∀ z, ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2 ≤
      (2 : ℝ) ^ j * ∑ r : Fin j → Fin 2,
        ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2 := by
    intro z
    have h1 := jl_norm_le_sum (w s) hsm j z
    have h2 : ∑ r : Fin j → Fin 2, ‖iteratedFDeriv ℝ j (w s) z (fun i => Sob.cylDir (r i))‖ =
        ∑ r : Fin j → Fin 2, ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [jl_iterD_ofFn (w s) hsm j (fun i => Sob.cylDir (r i)) z]
    rw [h2] at h1
    calc ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2
        ≤ (∑ r : Fin j → Fin 2,
            ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ((Finset.univ : Finset (Fin j → Fin 2)).card : ℝ) * ∑ r : Fin j → Fin 2,
            ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by rw [hcard]; push_cast; rfl
  have hGint : Integrable (fun z => (2 : ℝ) ^ j * ∑ r : Fin j → Fin 2,
        ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2) (Cyl.cellμ c) :=
    (integrable_finsetSum _ (fun r _ => hWint r)).const_mul _
  have hmeas : AEStronglyMeasurable (fun z => ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2)
      (Cyl.cellμ c) :=
    ((hsm.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm.pow 2
      ).aestronglyMeasurable
  have hint : Integrable (fun z => ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2) (Cyl.cellμ c) :=
    hGint.mono' hmeas (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt z)
  refine ⟨hint, ?_⟩
  change ∫ z, ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2 ∂(Cyl.cellμ c) ≤ _
  calc ∫ z, ‖iteratedFDeriv ℝ j (w s) z‖ ^ 2 ∂(Cyl.cellμ c)
      ≤ ∫ z, (2 : ℝ) ^ j * ∑ r : Fin j → Fin 2,
          ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2 ∂(Cyl.cellμ c) :=
        integral_mono hint hGint hpt
    _ = (2 : ℝ) ^ j * ∑ r : Fin j → Fin 2, ∫ z,
          ‖Sob.iterD (List.ofFn fun i => Sob.cylDir (r i)) (w s) z‖ ^ 2 ∂(Cyl.cellμ c) := by
        rw [integral_const_mul, integral_finsetSum _ (fun r _ => hWint r)]
    _ ≤ (2 : ℝ) ^ j * ∑ _r : Fin j → Fin 2, ‖uk‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => hWint' r) (by positivity)
    _ = (4 : ℝ) ^ j * ‖uk‖ ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring

end UnforcedLeray.Short.PartI
