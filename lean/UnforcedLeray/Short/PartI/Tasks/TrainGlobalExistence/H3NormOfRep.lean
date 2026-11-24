import UnforcedLeray.Short.PartI.Sub.T04.Defs

/-!
# Part I, task `PartI:T04/2`, target `h3NormOfRep`: the `H³` norm through the smooth representative

Source of record: `the November 2 reference manuscript`, line 254 (cell norms
unnormalized) and lines 268-269 (the datum in `BUC ∩ H^k`).

`‖u‖²_{H³} = Σ_α ‖∂^α u‖²` (`Sob.W.norm_sq`); `∂^α u` is, through the isometry to cell `L²`,
a.e. the classical word `iterD (word α) (w t)` (`IsSpatialRepOn.represents`); a word of length
`j` along unit directions is bounded by the jet norm (`le_opNorm`), so each term is `≤ B`, and
there are `card (Idx 2 3)` terms.
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

/-- The squared norm of an element of cell `L²` is the integral of the squared pointwise norm. -/
theorem h3n_norm_sq_L2 {c : ℝ} (f : Cyl.L2v c) :
    ‖f‖ ^ 2 = ∫ z, ‖(f : Plane → Vec) z‖ ^ 2 ∂(Cyl.cellμ c) := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℝ) f f
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact real_inner_self_eq_norm_sq _

theorem h3n_integrable_L2 {c : ℝ} (f : Cyl.L2v c) :
    Integrable (fun z => ‖(f : Plane → Vec) z‖ ^ 2) (Cyl.cellμ c) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  exact real_inner_self_eq_norm_sq _

/-- The classical word derivative is the jet on the letters. -/
theorem h3n_iterD_ofFn (f : Plane → Vec) (hf : ContDiff ℝ ∞ f) :
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

theorem h3n_cylDir_norm (i : Fin 2) : ‖Sob.cylDir i‖ = 1 := by
  fin_cases i <;> simp [Sob.cylDir, Prod.norm_def]

/-- A word along the cylinder directions is bounded by the jet norm. -/
theorem h3n_word_le (c : ℝ) (f : Plane → Vec) (hf : ContDiff ℝ ∞ f) {k : ℕ} (α : Sob.Idx 2 k)
    (z : Plane) :
    ‖Sob.iterD ((Sob.cylinder c).word α) f z‖ ≤ ‖iteratedFDeriv ℝ (α.1 : ℕ) f z‖ := by
  have e : (Sob.cylinder c).word α = List.ofFn (fun i : Fin (α.1 : ℕ) => Sob.cylDir (α.2 i)) := rfl
  rw [e, h3n_iterD_ofFn f hf]
  have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ (α.1 : ℕ) f z)
    (fun i : Fin (α.1 : ℕ) => Sob.cylDir (α.2 i))
  have h2 : ∏ i : Fin (α.1 : ℕ), ‖Sob.cylDir (α.2 i)‖ = 1 := by simp [h3n_cylDir_norm]
  rw [h2, mul_one] at h1
  exact h1

/-- **Target** `h3NormOfRep` (`PartI:T04/2`). -/
theorem h3NormOfRep : H3NormOfRep := by
  refine ⟨(Fintype.card (Sob.Idx 2 3) : ℝ), Nat.cast_nonneg _, ?_⟩
  intro c T u w B hc hw hB t
  have hnorm : ‖u t‖ ^ 2 = ∑ α : Sob.Idx 2 3,
      ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α (u t)‖ ^ 2 :=
    Sob.W.norm_sq (u t)
  rw [hnorm]
  have hterm : ∀ α : Sob.Idx 2 3,
      ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α (u t)‖ ^ 2 ≤ B := by
    intro α
    have hj : (α.1 : ℕ) ≤ 3 := Nat.lt_succ_iff.mp α.1.2
    obtain ⟨hint, hvel⟩ := hB t.1 t.2 (α.1 : ℕ) hj
    set f : Cyl.L2v c := vecH3CellDerivCLM α (u t) with hf
    have hfn : ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α (u t)‖ =
        ‖f‖ := by
      rw [hf]
      exact ((weightedToCellL2Isometry c).norm_map _).symm
    rw [hfn, h3n_norm_sq_L2 f]
    have hrep := hw.represents t α
    have hsm := hw.smooth t.1 t.2
    calc ∫ z, ‖(f : Plane → Vec) z‖ ^ 2 ∂(Cyl.cellμ c)
        = ∫ z, ‖Sob.iterD ((Sob.cylinder c).word α) (w t.1) z‖ ^ 2 ∂(Cyl.cellμ c) := by
          refine integral_congr_ae ?_
          filter_upwards [hrep] with z hz
          rw [hz]
      _ ≤ ∫ z, ‖iteratedFDeriv ℝ (α.1 : ℕ) (w t.1) z‖ ^ 2 ∂(Cyl.cellμ c) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
            hint (Filter.Eventually.of_forall fun z => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (h3n_word_le c (w t.1) hsm α z) 2
      _ ≤ B := hvel
  calc ∑ α : Sob.Idx 2 3,
        ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2 α (u t)‖ ^ 2
      ≤ ∑ _α : Sob.Idx 2 3, B := Finset.sum_le_sum fun α _ => hterm α
    _ = (Fintype.card (Sob.Idx 2 3) : ℝ) * B := by
        simp [Finset.sum_const, nsmul_eq_mul]

end UnforcedLeray.Short.PartI
