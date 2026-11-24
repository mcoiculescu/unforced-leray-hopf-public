import UnforcedLeray.Units.B0061.Coeff
import UnforcedLeray.Units.B0061.KernelCompact
import UnforcedLeray.Units.B0061.Incl

/-!
# B0061: `A_E` is bounded `H^j_M → H^{j+1}_M` and compact on `H^j_M`

Blueprint unit **B0061** (unlabeled, `paper/main.tex` line 1222, in the proof of "Compactness of
the Euler interaction", section `sec:st18-1373`). Dependencies: B0059 (`eq:st18-t00048`,
`UnforcedLeray.B0059`) and B0060 (`eq:st18-t00049`, `UnforcedLeray.B0060`); through them B0008
(the weighted spaces `H^j_M`, `UnforcedLeray.B0008`) and B0009 (the planar Biot–Savart velocity
`biotSavart f i` and `A_E f = perturbation f`, `UnforcedLeray.B0009`).

**Statement (tex 1222).** "It follows that `A_E f = (Kf)·∇E₀` is bounded `H^j_M → H^{j+1}_M` and
compact `H^j_M → H^j_M`. For compactness truncate `∇E₀` to a fixed disk, apply
`eq:st18-t00048` and Rellich there, and then let the disk grow; the omitted operator norm tends
to zero by `eq:st18-t00049` because all required weighted coefficient seminorms tend to zero."

**Formalization.** `M > 1` and `j ≥ 0` are the standing hypotheses of the spaces (tex 655, B0008).
`A_E f` is B0009's `perturbation f = (Kf)₁ ∂₁E₀ + (Kf)₂ ∂₂E₀`, a function defined pointwise
(the Biot–Savart integral converges a.e. for `f ∈ H^j_M`, B0009).
* `AE hM j : H^j_M →L[ℂ] H^{j+1}_M` with `(AE hM j F).value = A_E F.value` a.e. (`AE_value`): the
  bounded operator with gain. It is `eq:st18-t00049` (B0060, `mulBiotSavart`) with the Schwartz
  coefficients `b = ∂_k E₀` (`gradS k`, `Units/B0061/Coeff.lean`).
* `AEj hM j : H^j_M →L[ℂ] H^j_M`, the same operator followed by the inclusion
  `H^{j+1}_M ⊂ H^j_M` (`incl`, `Units/B0061/Incl.lean`), and `isCompactOperator_AEj`: it is
  compact.
* `unit_statement`: both claims at the level of functions, with exactly the manuscript's
  hypotheses (`M > 1`, every `j`): for every `f ∈ H^j_M`, `A_E f ∈ H^{j+1}_M` with
  `‖A_E f‖_{H^{j+1}_M} ≤ C ‖f‖_{H^j_M}`, and the map `f ↦ A_E f` on `H^j_M` is a compact
  operator (an element of `H^j_M` is determined by its function, `B0008.HjM.ext`, so the operator
  in the statement is unique).

**Proof route for compactness (a bypass of the Rellich step; scoping plan

compactness of a specific operator, never of an embedding").** Instead of truncating `∇E₀` in space
and using Rellich on disks (no Rellich–Kondrachov in Mathlib or the library for `H^j_M`), we use:
1. compactness into `H^j_M` is checked on each component `∂^α`, `|α| ≤ j`
   (`isCompactOperator_of_derCLM`);
2. Leibniz (B0060's `hasWeakDerivOn_mul_biotSavart`) and the commutation `∂^δ (Kf) = K(∂^δ f)`
   (B0059's `hasWeakDerivOn_biotSavart`) give
   `∂^α A_E f = ∑_k ∑_{β ≤ α} C(α,β) ∂^β ∂_kE₀ · K_k(∂^{α-β} f)` (`derAEj_ae_eq`), with
   `∂^{α-β} f ∈ L²(⟨y⟩^{2M} dy)` bounded by `‖f‖_{H^j_M}`;
3. each `g ↦ c (Kg)_k` with `c = ∂^β ∂_kE₀` is compact on `L²(⟨y⟩^{2M} dy)`
   (`isCompactOperator_mulK`, `Units/B0061/KernelCompact.lean`): it is the operator-norm limit of
   the Hilbert–Schmidt operators obtained by cutting the kernel singularity at radius
   `1/(n+1)`, the omitted operator norm tending to zero because `‖K 1_{|z| < r}‖_{L¹} → 0` and the
   weighted coefficient seminorm `sup ⟨y⟩^M |c|` is finite. Norm limits of compact operators are
   compact (Mathlib `isClosed_setOfPred_isCompactOperator`), as in the manuscript.
The truncation is in the kernel rather than in the coefficient; the closing step (operator-norm
limit, weighted coefficient bounds, `eq:st18-t00048`'s near/far kernel split) is the manuscript's.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0061

open NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0009

variable {M : ℝ} {j : ℕ}

/-! ### The coefficients `∂^β ∂_k E₀` are weighted coefficients -/

/-- Every Schwartz function is a weighted coefficient (B0060 `Coeff.lean`). -/
theorem WCoeff.of_schwartz (M : ℝ) (g : SchwartzMap ℂ ℂ) : WCoeff M (g : ℂ → ℂ) :=
  ⟨g.continuous, B0060.exists_weighted_sup g M, B0060.memLp_weighted g M⟩

theorem wcoeff_partialD (M : ℝ) (k : Fin 2) (β : ℕ × ℕ) :
    WCoeff M (partialD β (gradS k : ℂ → ℂ)) := by
  rw [B0060.partialD_eq_schwartzIter]
  exact WCoeff.of_schwartz M _

/-! ### `A_E : H^j_M → H^{j+1}_M` -/

variable (j) in
/-- **`A_E f = (Kf)·∇E₀` as a bounded operator `H^j_M → H^{j+1}_M`** (tex 1222, first claim):
`eq:st18-t00049` (B0060's `mulBiotSavart`) with `b = ∂₁E₀` and `b = ∂₂E₀`. -/
def AE (hM : 1 < M) : HjM j M →L[ℂ] HjM (j + 1) M :=
  B0060.mulBiotSavart hM j (gradS 0) 0 + B0060.mulBiotSavart hM j (gradS 1) 1

theorem AE_value_sum (hM : 1 < M) (F : HjM j M) :
    ((AE j hM F).value : ℂ → ℂ) =ᵐ[volume]
      fun y => ∑ k : Fin 2, gradS k y * biotSavart F.value k y := by
  have h : (AE j hM F).value = (B0060.mulBiotSavart hM j (gradS 0) 0 F).value +
      (B0060.mulBiotSavart hM j (gradS 1) 1 F).value := rfl
  filter_upwards [(volume_ac M).ae_le (Lp.coeFn_add (B0060.mulBiotSavart hM j (gradS 0) 0 F).value
      (B0060.mulBiotSavart hM j (gradS 1) 1 F).value),
    B0060.mulBiotSavart_value hM (gradS 0) 0 F, B0060.mulBiotSavart_value hM (gradS 1) 1 F]
    with y e1 e2 e3
  rw [h, e1, Pi.add_apply, e2, e3, Fin.sum_univ_two]

/-- **`AE` is `A_E`**: `(AE F).value = (Kf)·∇E₀` almost everywhere. -/
theorem AE_value (hM : 1 < M) (F : HjM j M) :
    ((AE j hM F).value : ℂ → ℂ) =ᵐ[volume] perturbation (F.value : ℂ → ℂ) := by
  filter_upwards [AE_value_sum hM F] with y hy
  rw [hy, perturbation_eq_sum]

/-- `A_E f ∈ H^{j+1}_M` for every `f ∈ H^j_M` (`M > 1`). -/
theorem memHjM_perturbation (hM : 1 < M) (F : HjM j M) :
    MemHjM (j + 1) M (perturbation (F.value : ℂ → ℂ)) :=
  (memHjM_iff _).2 ⟨AE j hM F, AE_value hM F⟩

/-! ### `A_E` on `H^j_M` -/

variable (j) in
/-- **`A_E` as an operator `H^j_M → H^j_M`**: `AE` followed by the inclusion
`H^{j+1}_M ⊂ H^j_M`. -/
def AEj (hM : 1 < M) : HjM j M →L[ℂ] HjM j M :=
  (incl (Nat.le_succ j) M).comp (AE j hM)

theorem AEj_value (hM : 1 < M) (F : HjM j M) : (AEj j hM F).value = (AE j hM F).value := rfl

theorem AEj_value_ae (hM : 1 < M) (F : HjM j M) :
    ((AEj j hM F).value : ℂ → ℂ) =ᵐ[volume] perturbation (F.value : ℂ → ℂ) :=
  AE_value hM F

/-! ### The derivatives of `A_E f` -/

/-- The multi-index `α - β` (truncated subtraction), of order `≤ |α|`. -/
def subIdx (α : Idx j) (β : ℕ × ℕ) : Idx j :=
  ⟨(α.1.1 - β.1, α.1.2 - β.2), mem_multiIdx.2 (by have := mem_multiIdx.1 α.2; simp only; omega)⟩

/-- For `|δ| ≤ j`, B0060's chosen derivative `∂^δ (Kf)_k` is `K_k(∂^δ f)` a.e. -/
theorem velDer_ae_eq (hM : 1 < M) (F : HjM j M) (k : Fin 2) (δ : Idx j) :
    B0060.velDer F.value k δ.1 =ᵐ[volume] biotSavart (F.der δ) k := by
  have hM0 : 0 ≤ M := by linarith
  have hδ : δ.1 ∈ multiIdx (j + 1) := mem_multiIdx_of_le (Nat.le_succ j) δ.2
  have h1 := B0060.hasWeakDerivOn_velDer hM F k hδ
  have h2 : HasWeakDerivOn univ (pdList δ.1) (biotSavart F.value k) (biotSavart (F.der δ) k) :=
    B0059.hasWeakDerivOn_biotSavart (B0008.HjM.integrable_value hM F)
      (integrable_L2w hM (F.der δ)) (F.hasWeakDeriv δ) k
  have hl1 := (B0060.locallyIntegrable_velDer hM F k hδ).locallyIntegrableOn univ
  have hl2 := (B0059.locallyIntegrable_biotSavart (integrable_L2w hM (F.der δ))
    (B0059.HjM.memLp_der_volume hM0 F δ) k).locallyIntegrableOn univ
  filter_upwards [HasWeakDerivOn.ae_eq isOpen_univ hl1 hl2 h1 h2] with x hx
  exact hx (mem_univ x)

/-- **Leibniz for `A_E f`** (tex 1218, 1222): for `|α| ≤ j`,
`∂^α (A_E f) = ∑_k ∑_{β ≤ α} C(α,β) ∂^β ∂_kE₀ · ∂^{α-β} (Kf)_k` a.e. -/
theorem derAEj_ae_eq_leibSum (hM : 1 < M) (F : HjM j M) (α : Idx j) :
    ((AEj j hM F).der α : ℂ → ℂ) =ᵐ[volume]
      fun x => ∑ k : Fin 2, B0060.leibSum (gradS k : ℂ → ℂ) F.value k α.1 x := by
  have hM0 : 0 ≤ M := by linarith
  have hα : α.1 ∈ multiIdx (j + 1) := mem_multiIdx_of_le (Nat.le_succ j) α.2
  have hder : (AEj j hM F).der α = (AE j hM F).der (idxIncl (Nat.le_succ j) α) := rfl
  have h1 := (AE j hM F).hasWeakDeriv (idxIncl (Nat.le_succ j) α)
  have hlocF : ∀ k : Fin 2, LocallyIntegrableOn
      (fun x => (gradS k : ℂ → ℂ) x * biotSavart F.value k x) univ := fun k =>
    ((B0059.locallyIntegrable_biotSavart (B0008.HjM.integrable_value hM F)
      (B0059.HjM.memLp_der_volume hM0 F (idx0 j)) k).continuous_mul
      (gradS k).continuous).locallyIntegrableOn univ
  have hlocG : ∀ k : Fin 2, LocallyIntegrableOn
      (B0060.leibSum (gradS k : ℂ → ℂ) F.value k α.1) univ := fun k =>
    (B0060.locallyIntegrable_leibSum hM F k ((gradS k).smooth ⊤) hα).locallyIntegrableOn univ
  have hsum := HasWeakDerivOn.add isOpen_univ (hlocF 0) (hlocF 1) (hlocG 0) (hlocG 1)
    (B0060.hasWeakDerivOn_mul_biotSavart hM F 0 ((gradS 0).smooth ⊤) hα)
    (B0060.hasWeakDerivOn_mul_biotSavart hM F 1 ((gradS 1).smooth ⊤) hα)
  have h1' : HasWeakDerivOn univ (pdList α.1)
      ((fun x => (gradS 0 : ℂ → ℂ) x * biotSavart F.value 0 x) +
        fun x => (gradS 1 : ℂ → ℂ) x * biotSavart F.value 1 x)
      ((AE j hM F).der (idxIncl (Nat.le_succ j) α) : ℂ → ℂ) := by
    refine h1.congr_ae ?_ (ae_of_all _ fun _ _ => rfl)
    filter_upwards [AE_value_sum hM F] with x hx _
    rw [hx, Fin.sum_univ_two, Pi.add_apply]
  have hloc1 := (locallyIntegrable_L2w M
    ((AE j hM F).der (idxIncl (Nat.le_succ j) α))).locallyIntegrableOn univ
  filter_upwards [HasWeakDerivOn.ae_eq isOpen_univ hloc1 ((hlocG 0).add (hlocG 1)) h1' hsum]
    with x hx
  rw [hder, hx (mem_univ x), Fin.sum_univ_two, Pi.add_apply]

/-! ### The Leibniz terms as compact operators -/

/-- `f ↦ ∂^β ∂_kE₀ · K_k(∂^{α-β} f)`, a bounded operator `H^j_M → L²(⟨y⟩^{2M} dy)`. -/
def termOp (hM : 1 < M) (α : Idx j) (k : Fin 2) (β : ℕ × ℕ) : HjM j M →L[ℂ] L2w M :=
  (mulK M hM (wcoeff_partialD M k β) k).comp (B0008.HjM.derCLM j M (subIdx α β))

/-- The Leibniz sum `∑_k ∑_{β ≤ α} C(α,β) termOp α k β`. -/
def sumOp (hM : 1 < M) (α : Idx j) : HjM j M →L[ℂ] L2w M :=
  ∑ k : Fin 2, ∑ β ∈ leIdx α.1, ((B0060.lc α.1 β : ℕ) : ℂ) • termOp hM α k β

theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → L2w M) (g : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, (f i : ℂ → ℂ) =ᵐ[volume] g i) :
    ((∑ i ∈ s, f i : L2w M) : ℂ → ℂ) =ᵐ[volume] fun x => ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [(volume_ac M).ae_le (Lp.coeFn_zero ℂ 2 (wMeasure M))] with x hx
    rw [hx, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [(volume_ac M).ae_le (Lp.coeFn_add (f a) (∑ i ∈ s, f i)),
      h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))] with x e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3, Finset.sum_insert ha]

theorem coeFn_sumOp (hM : 1 < M) (α : Idx j) (F : HjM j M) :
    (sumOp hM α F : ℂ → ℂ) =ᵐ[volume] fun x => ∑ k : Fin 2, ∑ β ∈ leIdx α.1,
      ((B0060.lc α.1 β : ℕ) : ℂ) *
        (partialD β (gradS k : ℂ → ℂ) x * biotSavart (F.der (subIdx α β)) k x) := by
  have happ : sumOp hM α F = ∑ k : Fin 2, ∑ β ∈ leIdx α.1,
      ((B0060.lc α.1 β : ℕ) : ℂ) • termOp hM α k β F := by
    simp only [sumOp, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
  rw [happ]
  refine coeFn_finset_sum _ _ _ fun k _ => coeFn_finset_sum _ _ _ fun β _ => ?_
  filter_upwards [(volume_ac M).ae_le (Lp.coeFn_smul ((B0060.lc α.1 β : ℕ) : ℂ)
      (termOp hM α k β F)),
    coeFn_mulK hM (wcoeff_partialD M k β) k (F.der (subIdx α β))] with x e1 e2
  rw [e1, Pi.smul_apply, smul_eq_mul]
  change ((B0060.lc α.1 β : ℕ) : ℂ) *
    (mulK M hM (wcoeff_partialD M k β) k (F.der (subIdx α β)) : ℂ → ℂ) x = _
  rw [e2]

/-- **`∂^α ∘ A_E` is the Leibniz sum of the operators `termOp`** (`|α| ≤ j`). -/
theorem derCLM_comp_AEj (hM : 1 < M) (α : Idx j) :
    (B0008.HjM.derCLM j M α).comp (AEj j hM) = sumOp hM α := by
  ext1 F
  apply Lp.ext
  have hv : ∀ᵐ x ∂(volume : Measure ℂ), ∀ k : Fin 2, ∀ β : ℕ × ℕ,
      B0060.velDer F.value k (subIdx α β).1 x = biotSavart (F.der (subIdx α β)) k x := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro β
    exact velDer_ae_eq hM F k (subIdx α β)
  filter_upwards [(wMeasure_ac M).ae_le (derAEj_ae_eq_leibSum hM F α),
    (wMeasure_ac M).ae_le (coeFn_sumOp hM α F), (wMeasure_ac M).ae_le hv] with x e1 e2 e3
  change ((AEj j hM F).der α : ℂ → ℂ) x = (sumOp hM α F : ℂ → ℂ) x
  rw [e1, e2]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B0060.leibSum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have := e3 k β
  rw [show ((subIdx α β : Idx j) : ℕ × ℕ) = ((α : ℕ × ℕ).1 - β.1, (α : ℕ × ℕ).2 - β.2)
    from rfl] at this
  rw [this]
  ring

/-- **`A_E` is compact `H^j_M → H^j_M`** (tex 1222, second claim). -/
theorem isCompactOperator_AEj (hM : 1 < M) : IsCompactOperator (AEj j hM) := by
  refine isCompactOperator_of_derCLM _ fun α => ?_
  rw [derCLM_comp_AEj hM α]
  have hmem : sumOp hM α ∈ compactOperator (RingHom.id ℂ) (HjM j M) (L2w M) :=
    Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _
        ((isCompactOperator_mulK hM (wcoeff_partialD M k β) k).comp_clm
          (B0008.HjM.derCLM j M (subIdx α β)))
  exact hmem

/-! ### The unit -/

/-- **B0061, bounded with gain** (`paper/main.tex:1222`): for `M > 1` and every `j` there is
`C ≥ 0` such that for every `f ∈ H^j_M`, `A_E f = (Kf)·∇E₀ ∈ H^{j+1}_M` and the element
`G ∈ H^{j+1}_M` it defines has `‖G‖_{H^{j+1}_M} ≤ C ‖f‖_{H^j_M}`. -/
theorem bounded_gain (hM : 1 < M) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : HjM j M,
      MemHjM (j + 1) M (perturbation (F.value : ℂ → ℂ)) ∧
        ∃ G : HjM (j + 1) M, (G.value : ℂ → ℂ) =ᵐ[volume] perturbation (F.value : ℂ → ℂ) ∧
          ‖G‖ ≤ C * ‖F‖ :=
  ⟨‖AE j hM‖, (AE j hM).opNorm_nonneg, fun F =>
    ⟨memHjM_perturbation hM F, AE j hM F, AE_value hM F, (AE j hM).le_opNorm F⟩⟩

/-- **B0061** (`paper/main.tex:1222`): for `M > 1` and every `j ≥ 0`,
1. `A_E f = (Kf)·∇E₀` is bounded `H^j_M → H^{j+1}_M`: there is a bounded operator
   `T₁ : H^j_M → H^{j+1}_M` with `T₁ f = A_E f` a.e. (so `A_E f ∈ H^{j+1}_M` and
   `‖A_E f‖_{H^{j+1}_M} ≤ ‖T₁‖ ‖f‖_{H^j_M}`);
2. `A_E` is compact `H^j_M → H^j_M`: there is a compact bounded operator `T₀ : H^j_M → H^j_M`
   with `T₀ f = A_E f` a.e. (unique, since an element of `H^j_M` is determined by its function). -/
theorem unit_statement (hM : 1 < M) (j : ℕ) :
    (∃ T₁ : HjM j M →L[ℂ] HjM (j + 1) M,
      ∀ F : HjM j M, ((T₁ F).value : ℂ → ℂ) =ᵐ[volume] perturbation (F.value : ℂ → ℂ)) ∧
    (∃ T₀ : HjM j M →L[ℂ] HjM j M,
      (∀ F : HjM j M, ((T₀ F).value : ℂ → ℂ) =ᵐ[volume] perturbation (F.value : ℂ → ℂ)) ∧
        IsCompactOperator T₀) :=
  ⟨⟨AE j hM, AE_value hM⟩, ⟨AEj j hM, AEj_value_ae hM, isCompactOperator_AEj hM⟩⟩

end UnforcedLeray.B0061
