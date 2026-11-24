import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2

/-!
# `PartIII-a:T21/2/7/2/2`: `AdjointWeakH1` from the integrated energy and the Gronwall step

Source: `the November 2 reference manuscript` (SP) lines 3060-3071
(`E_0' + β E_1 ≤ C E_0`, `E_1' + β E_2 ≤ C(E_1 + E_0)`, then `(s - r)E_1(r)` bound), 3044-3049
(log-derivative bounds of the weight), 3052-3058 (localized term bound).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Integrated weighted gradient energy** (SP 3060-3067: cutoff energy identity for `E_0` with
weight `p^{-1} = density(-m)`, transport by `sup|v|` and `|∇ log p|`, localized term by
`⟨x⟩^{m+2}|∇E|`; integrate on `[r, s']`, `s' → s` by `strongCont`, `R → ∞` by monotone
convergence): for a weak adjoint jointly `C^∞` on `[t, s) × ℝ²`, `∫_r^s E_1 < ∞` for `r ∈ [t, s)`. -/
def AdjointIntegratedH1 (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        ∀ r ∈ Ico t s, ∀ k : Fin 2,
          ∫⁻ ρ in Ioc r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
            ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤

/-- **Gronwall step** (SP 3068-3071: `d/dτ(τ E_1) ≤ E_1 + C τ(E_1 + E_0)` with `E_0` bounded, the
transport term integrated by parts onto `Δφ`, only `sup|v|` needed): a jointly smooth weak adjoint
with `∫_r^s E_1 < ∞` for all `r ∈ [t, s)` has `E_1(r) < ∞` for every `r ∈ [t, s)`. -/
def AdjointH1Gronwall (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          ∫⁻ ρ in Ioc r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
            ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤) →
        ∀ r ∈ Ico t s, ∀ k : Fin 2,
          MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))

/-- `AdjointWeakH1` from the integrated energy and the Gronwall step. -/
theorem adjointWeakH1_of (m : ℝ) (h1 : AdjointIntegratedH1 m) (h2 : AdjointH1Gronwall m) :
    AdjointWeakH1 m := by
  intro ν hν hν1 tr hb t s ht hts G hG φ hφ hs
  exact h2 ν hν hν1 tr hb t s ht hts G hG φ hφ hs (h1 ν hν hν1 tr hb t s ht hts G hG φ hφ hs)

end UnforcedLeray.Short.IIIa
