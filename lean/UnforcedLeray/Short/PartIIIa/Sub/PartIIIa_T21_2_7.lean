import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a, `PartIII-a:T21/2/7`: existence of the reverse-time adjoint, decomposed

Source of record: `the November 2 reference manuscript`, line 3060 (the reverse-time
adjoint) with lines 2819-2836 (forward existence, `FullFlowExists`) and 270-288 (the train).

`AdjointExists m` is split into the construction of a weak solution (`AdjointWeakExists`: terminal
datum, `X_{-m,c}` membership and strong continuity, periodicity, and the weak identity against every
`IsCylTest c` with its kernel velocity) and the parabolic smoothing of weak solutions before the
terminal age (`AdjointSmoothing`: `C^∞` in space, jointly `C^∞` on `[t,s) × ℝ²`,
`C([t,s); H^1_{-m,c})`; the full regularity is now `IsAdjointFlow.higherCont` as well,
Sub/PartIIIa_T21_2_7_2.lean).

All three are stated in one form: small `ν`, the trains of the BUC class `PartI.IsBUCTrain`
(SP 270-288). The construction needs `sup |v| < ∞` and the weighted decay of `∇E` on `[0, s]`, which
`B0140.IsTrain` does not give (`Short/PartI/TrainClass.lean`). `AdjointWeakExists m` is verbatim
`AdjointWeakExistsBUC m` of `Sub/T21_2_7/AdjWeakDefs.lean`, which imports this file
(`adjointWeakExists_iff_BUC`, `Sub/T21_2_7/WeakExistsForm.lean`).

`AdjointSmoothing` is false, since it is asked of every weak solution, and nothing consumes it
(`not_adjointSmoothing_of_weak`, `Sub/PartIIIa_T21_2_7_2.lean`). Its replacement is
`AdjointWeakRegular` of that file, and `AdjointExists m` is proved by `adjointExistsBUC_of_regular`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The weak-solution part of `IsAdjointFlow` (everything except the smoothing fields). -/
structure IsAdjointWeak (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop where
  terminal : φ s =ᵐ[volume.restrict (B0579.cell c)] g
  memX : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m))
  strongCont : ∀ r ∈ Icc t s,
    Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0)
  periodic : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x
  integrable : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ → ∀ r ∈ Icc t s,
    IntegrableOn (adjIntegrand tr (φ r) r ψ uψ) (B0579.cell c)
  timeIntegrable : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) volume t s
  weak : ∀ ψ uψ, B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ → ∀ r ∈ Icc t s,
    ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)) +
        ∫ r' in r..s, ∫ x in B0579.cell c, adjIntegrand tr (φ r') r' ψ uψ x

/-- **Construction of the weak reverse-time adjoint** (SP 3060; Volterra construction in
`X_{-m,c}` as in SP 2819-2836, bounded nonlocal term `K_c^T(φ∇E)` as in `AdjointLocalizedBound`,
SP 3052-3058): for small `ν` and the trains of the BUC class `PartI.IsBUCTrain` (SP 270-288), every
terminal datum `g = physAdj a_s G`, `G ∈ X_{-m,d_s}`, has a weak solution on `[t, s]`. The body is
that of `AdjointWeakExistsBUC` (`Sub/T21_2_7/AdjWeakDefs.lean`), which is the form of
`AdjointExists` and of `LinAdjDualityBUC`. -/
def AdjointWeakExists (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∃ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ

/-- **Parabolic smoothing of the adjoint before the terminal age** (SP 3060-3061), in the form of
`AdjointWeakExists`: every weak solution for `g = physAdj a_s G` is `C^∞` in space for `r ∈ [t, s)`,
jointly `C^∞` on `[t, s) × ℝ²`, and lies in `C([t, s); H^1_{-m,c})`.

This is FALSE as soon as weak solutions exist for BUC trains at arbitrarily small `ν`: changing a
weak solution on a null line keeps it a weak solution (`not_adjointSmoothing_of_weak`,
`Sub/PartIIIa_T21_2_7_2.lean`). It is kept for the record and consumed by nothing; the correct
statement is `AdjointWeakRegular` of that file. -/
def AdjointSmoothing (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        (∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ r)) ∧
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) ∧
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ∧
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (φ r') - pdCx k (φ r)))
            (𝓝[Ico t s] r) (𝓝 0))

end UnforcedLeray.Short.IIIa
