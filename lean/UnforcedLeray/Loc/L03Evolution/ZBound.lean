import UnforcedLeray.Loc.L03Evolution.Free
import UnforcedLeray.Loc.L02FreeEvolution.Operators

/-!
# L3 helper: the free evolution is bounded on `Z = H²_div`

`paper/main.tex` lines 292–298 (`loc:eq:free-evolution`, blueprint unit B0712) and line 302
("uniformly bounded on `L², X, Z`", blueprint unit B0713). For `S` with `IsFreeEvolution h S`
and `0 < t ≤ 1`,
`‖S₀(t) g‖_{H²} ≤ (1 + 12 e) ‖g‖_{H²}` for `g ∈ Z`.

Proof. `S₀(t) = D(t) e^{h(e^t-1)Δ}` on `L²` (`L02.dil_heatOperator`); the heat operator
commutes with weak derivatives (`L02.hasWeak_heatOperator`) and the dilation `D(t)`
multiplies a weak derivative by `e^{t/2}` (`L02.hasWeak_dil`). By uniqueness of `L²` weak
derivatives, the first and ordered second derivatives of `S₀(t) g` are
`e^{t/2} S₀(t) ∂ᵢ g` and `e^{t} S₀(t) ∂ⱼ∂ᵢ g`. Each `S₀(t)` contracts `L²` by `e^{-t/4}`
(`L02.norm_freeL2_le`), and `e^{t/2}, e^{t} ≤ e` for `t ≤ 1`.

The value of `S.S0Z t (ι_Z g)` is pinned to the compiled
`AncientLocalization.freeEvolution h t` by `IsFreeEvolution.repZ`, so the bound holds for
every such `S`, with no condition on `h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Loc.L03Evolution

open UnforcedLeray.Blueprint SobolevGraph

/-- The first derivatives of an `H²` field are bounded by its `H²` norm. -/
theorem norm_first_le_H2 (F : H2) (i : Fin 3) : ‖F.first i‖ ≤ ‖F‖ := by
  have h := H2.norm_sq F
  have h1 : ‖F.first i‖ ^ 2 ≤ ∑ j : Fin 3, ‖F.first j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖F.first j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖F.second i j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖F.value‖])

/-- The ordered second derivatives of an `H²` field are bounded by its `H²` norm. -/
theorem norm_second_le_H2 (F : H2) (i j : Fin 3) : ‖F.second i j‖ ≤ ‖F‖ := by
  have h := H2.norm_sq F
  have h1 : ‖F.second i j‖ ^ 2 ≤ ∑ k : Fin 3, ‖F.second i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖F.second i k‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ k : Fin 3, ‖F.second i k‖ ^ 2 ≤ ∑ l : Fin 3, ∑ k : Fin 3, ‖F.second l k‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ∑ k : Fin 3, ‖F.second l k‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i : Fin 3, ‖F.first i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖F.value‖])

/-- `S₀(t)` does not increase `L²` norms for `t ≥ 0` (`‖S₀(t)‖_{L²→L²} ≤ e^{-t/4}`). -/
theorem norm_freeL2_apply_le_self (h : ℝ) {t : ℝ} (ht : 0 ≤ t) (F : L2Space) :
    ‖L02.freeL2 h t F‖ ≤ ‖F‖ := by
  refine ((L02.freeL2 h t).le_opNorm F).trans ?_
  have h1 : ‖L02.freeL2 h t‖ ≤ 1 :=
    (L02.norm_freeL2_le h t).trans (Real.exp_le_one_iff.mpr (by linarith))
  calc ‖L02.freeL2 h t‖ * ‖F‖ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖F‖ := one_mul _

/-- `S₀(t)` maps a weak derivative pair `(F, G)` to `(S₀(t)F, e^{t/2} S₀(t)G)`. -/
theorem hasWeak_freeL2 (h t : ℝ) {F G : L2Space} {i : Fin 3}
    (hFG : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i (L02.freeL2 h t F : SpatialField)
      ((Real.exp (t / 2) • L02.freeL2 h t G : L2Space) : SpatialField) := by
  have h1 := L02.hasWeak_dil t (L02.hasWeak_heatOperator (L02.heatTime h t) hFG)
  rwa [L02.dil_heatOperator, L02.dil_heatOperator] at h1

section ZBound

variable {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S)
include hS

/-- The value of `S₀(t) g` for `g ∈ Z`, `t > 0`: `S₀(t)` applied to the value of `g`
(`IsFreeEvolution.repZ`, line 294). -/
theorem value_S0Z_ιZ {t : ℝ} (ht : 0 < t) (g : Z) :
    (S.S0Z t (ιZ g)).toH2.value = L02.freeL2 h t g.toH2.value :=
  Lp.ext ((hS.repZ t ht (ιZ g)).trans (L02.coeFn_freeL2 h t g.toH2.value).symm)

/-- `∂ᵢ S₀(t) g = e^{t/2} S₀(t) ∂ᵢ g` for `g ∈ Z`, `t > 0`. -/
theorem first_S0Z_ιZ {t : ℝ} (ht : 0 < t) (g : Z) (i : Fin 3) :
    (S.S0Z t (ιZ g)).toH2.first i = Real.exp (t / 2) • L02.freeL2 h t (g.toH2.first i) := by
  apply Lp.ext
  have h1 := (S.S0Z t (ιZ g)).toH2.hasWeakFirst i
  have h2 := hasWeak_freeL2 h t (g.toH2.hasWeakFirst i)
  rw [← value_S0Z_ιZ hS ht g] at h2
  exact h1.ae_eq h2 (Lp.memLp _) (Lp.memLp _)

/-- `∂ⱼ∂ᵢ S₀(t) g = e^{t} S₀(t) ∂ⱼ∂ᵢ g` for `g ∈ Z`, `t > 0`. -/
theorem second_S0Z_ιZ {t : ℝ} (ht : 0 < t) (g : Z) (i j : Fin 3) :
    (S.S0Z t (ιZ g)).toH2.second i j =
      Real.exp t • L02.freeL2 h t (g.toH2.second i j) := by
  apply Lp.ext
  have h1 := (S.S0Z t (ιZ g)).toH2.hasWeakSecond i j
  have h2 := L02.hasWeak_smul_L2 (Real.exp (t / 2)) (hasWeak_freeL2 h t (g.toH2.hasWeakSecond i j))
  rw [smul_smul, ← Real.exp_add, add_halves, ← first_S0Z_ιZ hS ht g i] at h2
  exact h1.ae_eq h2 (Lp.memLp _) (Lp.memLp _)

/-- **`S₀` is bounded on `Z` for short times** (lines 292–298, 302):
`‖S₀(t) g‖_{H²} ≤ (1 + 12 e) ‖g‖_{H²}` for `g ∈ Z`, `0 < t ≤ 1`. -/
theorem norm_S0Z_ιZ_apply_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (g : Z) :
    ‖S.S0Z t (ιZ g)‖ ≤ (1 + 12 * Real.exp 1) * ‖g‖ := by
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hhalf : Real.exp (t / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have hone : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1
  have hv : ‖(S.S0Z t (ιZ g)).toH2.value‖ ≤ ‖g‖ := by
    rw [value_S0Z_ιZ hS ht g]
    exact (norm_freeL2_apply_le_self h ht.le _).trans (norm_value_le_H2 g.toH2)
  have hf : ∀ i, ‖(S.S0Z t (ιZ g)).toH2.first i‖ ≤ Real.exp 1 * ‖g‖ := by
    intro i
    rw [first_S0Z_ιZ hS ht g i, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul hhalf ((norm_freeL2_apply_le_self h ht.le _).trans
      (norm_first_le_H2 g.toH2 i)) (norm_nonneg _) he0
  have hs : ∀ i j, ‖(S.S0Z t (ιZ g)).toH2.second i j‖ ≤ Real.exp 1 * ‖g‖ := by
    intro i j
    rw [second_S0Z_ιZ hS ht g i j, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul hone ((norm_freeL2_apply_le_self h ht.le _).trans
      (norm_second_le_H2 g.toH2 i j)) (norm_nonneg _) he0
  have hb := L02.h2_norm_le_of hg0 (mul_nonneg he0 hg0) (mul_nonneg he0 hg0) hv hf hs
  rw [← norm_toH2]
  linarith

/-- The operator form: `‖S₀(t)|_Z‖_{Z→Z} ≤ 1 + 12 e` for `0 < t ≤ 1`. -/
theorem exists_norm_S0Z_comp_ιZ_le :
    ∃ C : ℝ, ∀ t, 0 < t → t ≤ 1 → ‖(S.S0Z t).comp ιZ‖ ≤ C :=
  ⟨1 + 12 * Real.exp 1, fun t ht ht1 =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => by
      rw [ContinuousLinearMap.comp_apply]
      exact norm_S0Z_ιZ_apply_le hS ht ht1 g⟩

end ZBound

end UnforcedLeray.Loc.L03Evolution
