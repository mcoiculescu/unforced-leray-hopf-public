import UnforcedLeray.Loc.L10Nonlinear.Pairing
import UnforcedLeray.Loc.L10Nonlinear.WeakProduct

/-!
# Step L10, helpers: the operator `g ↦ -𝔓 div(K ⊗ g + g ⊗ K)`

Support for `Loc/L10Nonlinear.lean` (step L10 `NonlinearStep`, `paper/main.tex` lines 464–466
and 504–505, blueprint units B0721, B0722). For a smooth field `K` with
`|K|, |DK|, |D²K| ≤ M` (a `W^{2,∞}` field, `loc:eq:heat-correction`), the tensor `K ⊗ g + g ⊗ K` has `H²` columns
for every `g ∈ H²` (`exists_H2_bilin`), so `-𝔓 div(K ⊗ g + g ⊗ K) ∈ X = H¹_div`
(`isMinusLerayDiv_minusLerayDivX`). This file packages it as a bounded operator
`mulOp K : H² → X` with
* `mulOp_spec`: `Xclass (mulOp K g) = -𝔓 div(K ⊗ g + g ⊗ K)` (literal weak form);
* `norm_mulOp_le`: `‖mulOp K‖ ≤ mulConst · M`;
* `mulOp_sub`: `mulOp K - mulOp K' = mulOp (K - K')` (uniqueness of the weak form).

The column `j` of `u ⊗ v + v ⊗ u` is `v_j u + u_j v = symBilin j u v` (line 107).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L10

open SobolevGraph

/-- `symBilin j u v = v_j u + u_j v`, the column `j` of `u ⊗ v + v ⊗ u`. -/
def symBilin (j : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj j) +
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (ContinuousLinearMap.id ℝ Space)

theorem symBilin_apply (j : Fin 3) (u v : Space) : symBilin j u v = v j • u + u j • v := by
  simp [symBilin]

theorem symTensorColumns_eq (K v : SpatialField) (j : Fin 3) (y : Space) :
    symTensorColumns K v j y = symBilin j (K y) (v y) := by
  rw [symBilin_apply]
  rfl

/-- `K` is smooth with `|K|, |DK|, |D²K| ≤ M` everywhere (a `W^{2,∞}` bound). -/
def IsW2Bounded (K : Space → Space) (M : ℝ) : Prop :=
  ContDiff ℝ ∞ K ∧ ∀ y, ‖K y‖ ≤ M ∧ ‖fderiv ℝ K y‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 K y‖ ≤ M

theorem IsW2Bounded.nonneg {K : Space → Space} {M : ℝ} (hK : IsW2Bounded K M) : 0 ≤ M :=
  (norm_nonneg _).trans (hK.2 0).1

/-- The multiplier constant `13 ∑ⱼ ‖symBilin j‖`. -/
def mulConst : ℝ := 13 * ∑ j : Fin 3, ‖symBilin j‖

theorem mulConst_nonneg : 0 ≤ mulConst :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => norm_nonneg (symBilin j))

/-- The `H²` columns of `K ⊗ g + g ⊗ K` and the bound `‖-𝔓 div(K ⊗ g + g ⊗ K)‖_X ≤ mulConst M ‖g‖`. -/
theorem exists_mulOp {K : Space → Space} {M : ℝ} (hK : IsW2Bounded K M) :
    ∃ T : H2 →L[ℝ] X,
      (∀ g : H2, IsMinusLerayDiv (symTensorColumns K (g.value : SpatialField)) (Xclass (T g))) ∧
      ‖T‖ ≤ mulConst * M := by
  have hM := hK.nonneg
  refine exists_clm (fun g : H2 => symTensorColumns K (g.value : SpatialField)) ?_ ?_
    (mul_nonneg mulConst_nonneg hM) ?_
  · intro g g' j
    have e : (g + g').value = g.value + g'.value := map_add H2.valueCLM g g'
    filter_upwards [Lp.coeFn_add g.value g'.value] with z hz
    simp only [symTensorColumns, e, hz, Pi.add_apply, PiLp.add_apply, add_smul, smul_add]
    abel
  · intro a g j
    have e : (a • g).value = a • g.value := map_smul H2.valueCLM a g
    filter_upwards [Lp.coeFn_smul a g.value] with z hz
    simp only [symTensorColumns, e, hz, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    module
  · intro g
    choose P hP hPn using fun j => exists_H2_bilin (symBilin j) hK.1 hK.2 g
    refine ⟨minusLerayDivX P, isMinusLerayDiv_minusLerayDivX P _ (fun j => ?_), ?_⟩
    · refine (hP j).trans (Eventually.of_forall fun y => ?_)
      exact (symTensorColumns_eq K _ j y).symm
    · calc ‖minusLerayDivX P‖ ≤ ∑ j : Fin 3, ‖P j‖ := norm_minusLerayDivX_le P
        _ ≤ ∑ j : Fin 3, 13 * (‖symBilin j‖ * M * ‖g‖) := Finset.sum_le_sum fun j _ => hPn j
        _ = mulConst * M * ‖g‖ := by
          simp only [mulConst, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring

/-- The operator `g ↦ -𝔓 div(K ⊗ g + g ⊗ K)` on `H²` (`0` unless `K` is `W^{2,∞}`). -/
def mulOp (K : Space → Space) : H2 →L[ℝ] X := by
  classical
  exact if h : ∃ M, IsW2Bounded K M then Classical.choose (exists_mulOp (Classical.choose_spec h))
    else 0

/-- Uniqueness: any operator with the weak `-𝔓 div` property is `mulOp K`. -/
theorem mulOp_eq {K : Space → Space} {M : ℝ} (hK : IsW2Bounded K M) {T : H2 →L[ℝ] X}
    (hT : ∀ g : H2, IsMinusLerayDiv (symTensorColumns K (g.value : SpatialField)) (Xclass (T g))) :
    mulOp K = T := by
  have h : ∃ M, IsW2Bounded K M := ⟨M, hK⟩
  have hspec := (Classical.choose_spec (exists_mulOp (Classical.choose_spec h))).1
  ext1 g
  apply Xclass_injective
  have e : mulOp K = Classical.choose (exists_mulOp (Classical.choose_spec h)) := by
    unfold mulOp
    rw [dif_pos h]
  rw [e]
  exact IsMinusLerayDiv.unique (hspec g) (hT g)

theorem mulOp_spec {K : Space → Space} {M : ℝ} (hK : IsW2Bounded K M) (g : H2) :
    IsMinusLerayDiv (symTensorColumns K (g.value : SpatialField)) (Xclass (mulOp K g)) := by
  obtain ⟨T, hT, _⟩ := exists_mulOp hK
  rw [mulOp_eq hK hT]
  exact hT g

theorem norm_mulOp_le {K : Space → Space} {M : ℝ} (hK : IsW2Bounded K M) :
    ‖mulOp K‖ ≤ mulConst * M := by
  obtain ⟨T, hT, hTn⟩ := exists_mulOp hK
  rw [mulOp_eq hK hT]
  exact hTn

theorem mulOp_sub {K K' : Space → Space} {M M' N : ℝ} (hK : IsW2Bounded K M)
    (hK' : IsW2Bounded K' M') (hd : IsW2Bounded (fun y => K y - K' y) N) :
    mulOp K - mulOp K' = mulOp (fun y => K y - K' y) := by
  symm
  apply mulOp_eq hd
  intro g
  have h := IsMinusLerayDiv.sub (mulOp_spec hK g) (mulOp_spec hK' g)
  rw [ContinuousLinearMap.sub_apply, Xclass_sub]
  refine IsMinusLerayDiv.congr h (fun j => Eventually.of_forall fun z => ?_)
  simp only [symTensorColumns, Pi.sub_apply, PiLp.sub_apply]
  module

/-- A difference of two smooth fields is `W^{2,∞}`-bounded by the sup distances. -/
theorem isW2Bounded_sub {K K' : Space → Space} (hK : ContDiff ℝ ∞ K) (hK' : ContDiff ℝ ∞ K')
    {ε : ℝ} (h : ∀ y, ‖K y - K' y‖ ≤ ε ∧ ‖fderiv ℝ K y - fderiv ℝ K' y‖ ≤ ε ∧
      ‖iteratedFDeriv ℝ 2 K y - iteratedFDeriv ℝ 2 K' y‖ ≤ ε) :
    IsW2Bounded (fun y => K y - K' y) ε := by
  refine ⟨hK.sub hK', fun y => ⟨(h y).1, ?_, ?_⟩⟩
  · rw [fderiv_fun_sub ((hK.differentiable (by simp)) y) ((hK'.differentiable (by simp)) y)]
    exact (h y).2.1
  · rw [show (fun y => K y - K' y) = K - K' from rfl,
      iteratedFDeriv_sub_apply (hK.of_le (by simp)).contDiffAt (hK'.of_le (by simp)).contDiffAt]
    exact (h y).2.2

end UnforcedLeray.Blueprint.L10
