import UnforcedLeray.Units.B0008
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# B0061 helper: the inclusion `H^{k}_M → H^j_M` (`j ≤ k`) and compactness into `H^j_M`

Helper for blueprint unit **B0061** (`paper/main.tex:1222`, proof of "Compactness of the Euler
interaction", section `sec:st18-1373`). The weighted spaces are those of B0008
(`UnforcedLeray.B0008.HjM`, `paper/main.tex:653–660`).

* `incl hjk : HjM k M →L[ℂ] HjM j M` forgets the derivatives of order `> j`; it is the inclusion
  `H^k_M ⊂ H^j_M` (same function, `incl_value`; same derivatives, `incl_der`), and
  `‖incl F‖ ≤ ‖F‖` (`norm_incl_le`). B0061 uses it to view `A_E : H^j_M → H^{j+1}_M` as an
  operator on `H^j_M` (tex 1222).
* `isCompactOperator_of_derCLM`: an operator `T : X → H^j_M` is compact as soon as every
  component `∂^α ∘ T : X → L²(⟨y⟩^{2M} dy)`, `|α| ≤ j`, is compact (`H^j_M` is a closed subspace
  of the finite product of the weighted `L²` spaces). The proof is adapted from

  INF11 target S12), which states it for the library spaces `W D ρ 𝕜 F k p`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.B0061

open NonUniqueEuler.Sob UnforcedLeray.B0008

theorem mem_multiIdx_of_le {j k : ℕ} (hjk : j ≤ k) {α : ℕ × ℕ} (h : α ∈ multiIdx j) :
    α ∈ multiIdx k :=
  mem_multiIdx.2 ((mem_multiIdx.1 h).trans hjk)

/-- A multi-index of order `≤ j` as one of order `≤ k`, `j ≤ k`. -/
def idxIncl {j k : ℕ} (hjk : j ≤ k) (α : Idx j) : Idx k := ⟨α.1, mem_multiIdx_of_le hjk α.2⟩

@[simp] theorem idxIncl_val {j k : ℕ} (hjk : j ≤ k) (α : Idx j) : (idxIncl hjk α).1 = α.1 := rfl

theorem idxIncl_idx0 {j k : ℕ} (hjk : j ≤ k) : idxIncl hjk (idx0 j) = idx0 k := rfl

variable {M : ℝ}

/-- Restriction of tuples `(F_β)_{|β| ≤ k} ↦ (F_α)_{|α| ≤ j}`. -/
def tupleRestrict {j k : ℕ} (hjk : j ≤ k) (M : ℝ) : Tuple k M →L[ℂ] Tuple j M :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Idx j => L2w M)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α : Idx j =>
      (PiLp.proj 2 (fun _ : Idx k => L2w M) (idxIncl hjk α) : Tuple k M →L[ℂ] L2w M))

theorem tupleRestrict_apply {j k : ℕ} (hjk : j ≤ k) (T : Tuple k M) (α : Idx j) :
    (tupleRestrict hjk M T).ofLp α = T.ofLp (idxIncl hjk α) := rfl

theorem tupleRestrict_mem {j k : ℕ} (hjk : j ≤ k) (F : HjM k M) :
    tupleRestrict hjk M (F : Tuple k M) ∈ HSub j M := by
  rw [mem_HSub_iff]
  intro α
  have h := (mem_HSub_iff (F : Tuple k M)).1 F.2 (idxIncl hjk α)
  rw [tupleRestrict_apply, tupleRestrict_apply, idxIncl_idx0]
  exact h

/-- **The inclusion `H^k_M ⊂ H^j_M`, `j ≤ k`**, as a bounded operator (it forgets the
derivatives of order `> j`). -/
def incl {j k : ℕ} (hjk : j ≤ k) (M : ℝ) : HjM k M →L[ℂ] HjM j M :=
  ((tupleRestrict hjk M).comp (HSub k M).subtypeL).codRestrict (HSub j M)
    (fun F => tupleRestrict_mem hjk F)

@[simp] theorem incl_value {j k : ℕ} (hjk : j ≤ k) (F : HjM k M) :
    (incl hjk M F).value = F.value := rfl

@[simp] theorem incl_der {j k : ℕ} (hjk : j ≤ k) (F : HjM k M) (α : Idx j) :
    (incl hjk M F).der α = F.der (idxIncl hjk α) := rfl

theorem idxIncl_injective {j k : ℕ} (hjk : j ≤ k) : Function.Injective (idxIncl hjk) := by
  intro α β h
  have h' : (idxIncl hjk α).1 = (idxIncl hjk β).1 := congrArg Subtype.val h
  exact Subtype.ext h'

/-- `‖F‖_{H^j_M} ≤ ‖F‖_{H^k_M}` for `j ≤ k`. -/
theorem norm_incl_le {j k : ℕ} (hjk : j ≤ k) (F : HjM k M) : ‖incl hjk M F‖ ≤ ‖F‖ := by
  have h1 := B0008.HjM.norm_sq (incl hjk M F)
  have h2 := B0008.HjM.norm_sq F
  have hle : ‖incl hjk M F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [h1, h2]
    simp only [incl_der]
    calc ∑ α : Idx j, ‖F.der (idxIncl hjk α)‖ ^ 2
        = ∑ β ∈ Finset.univ.map ⟨idxIncl hjk, idxIncl_injective hjk⟩, ‖F.der β‖ ^ 2 := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ β : Idx k, ‖F.der β‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

/-- **Compactness into `H^j_M`**: an operator `T : X → H^j_M` is compact if every component
`∂^α ∘ T : X → L²(⟨y⟩^{2M} dy)`, `|α| ≤ j`, is compact. Adapted from
`Lib/SobolevC/Compact.lean` (`isCompactOperator_into_W_iff`). -/
theorem isCompactOperator_of_derCLM {j : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] HjM j M)
    (h : ∀ α : Idx j, IsCompactOperator ((B0008.HjM.derCLM j M α).comp T)) :
    IsCompactOperator T := by
  choose K hK hKT using h
  set Kt : Set (Tuple j M) := WithLp.toLp 2 '' Set.pi univ K with hKt_def
  have hKt : IsCompact Kt := (isCompact_univ_pi hK).image (PiLp.continuous_toLp 2 _)
  have hKW : IsCompact (((↑) : HjM j M → Tuple j M) ⁻¹' Kt) :=
    (isClosed_HSub j M).isClosedEmbedding_subtypeVal.isCompact_preimage hKt
  refine ⟨_, hKW, ?_⟩
  have hV : (⋂ α, ((B0008.HjM.derCLM j M α).comp T) ⁻¹' K α) ∈ 𝓝 (0 : X) :=
    Filter.iInter_mem.mpr hKT
  refine Filter.mem_of_superset hV fun x hx => ?_
  simp only [mem_iInter, mem_preimage] at hx
  simp only [mem_preimage, hKt_def, mem_image]
  exact ⟨fun α => (T x : Tuple j M).ofLp α, fun α _ => hx α, rfl⟩

end UnforcedLeray.B0061
