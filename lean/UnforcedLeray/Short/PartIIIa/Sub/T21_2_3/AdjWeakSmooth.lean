import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2

/-!
# Part III-a: the classical adjoint equation and `χ` for jointly smooth weak solutions

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3060 (the
adjoint localized interaction, the reverse-time adjoint), 2854-2865.

`LadAdjPointwise` and `LadChiBound` (`Sub/T21_2_3/LinAdjDualitySub.lean`) are stated for an
`IsAdjointFlow`. Their content, `χ = ∂_ρφ + νΔφ + v·∇φ` is the adjoint localized interaction of
`φ(ρ)` and is bounded in `X_{-m,c}`, uses only the weak equation and the joint smoothness. The
weighted `H^1` regularity of `IsAdjointFlow` (`memH1`, `strongContH1`) is proved FROM this content
(`AdjointWeakH1`, `AdjointWeakH1Cont`, SP 3060-3071), so it has to be available before the flow
exists. Here it is stated for a jointly smooth weak solution, and the two statements for flows are
corollaries (`ladAdjPointwise_of_weak`, `ladChiBound_of_weak`).

The leaves `AdjWRateCont`, `AdjWDtDeriv`, `AdjWIBP`, `AdjWInt` are `LadAdjRateCont`, `LadAdjDtDeriv`,
`LadAdjIBP`, `LadAdjInt` of `Sub/PartIIIa_T21_2_3_1_7.lean` in this context, and replace them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- A jointly smooth weak solution of the adjoint equation, for a train with the bounds
`LadTrainBdd`. -/
def AdjWCtx (m : ℝ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  0 < ν ∧ 0 < c ∧ 0 ≤ t ∧ t < s ∧ (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) ∧
    IsAdjointWeak ν c m tr t s g φ ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)

/-- **Leaf 1** (SP 3052-3058, 2854-2865): `r ↦ ∫_cell adjIntegrand tr (φ r) r ψ uψ` is continuous
on `(t, s)` (local part: joint continuity on the compact strip; global part: `φ r → φ ρ` in
`X_{-m}`, `uψ·∇E(r) → uψ·∇E(ρ)` in `X_m` by `LadTrainBdd` tails and uniform continuity of `∇E`
on compact strips). -/
def AdjWRateCont (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
    ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
        ContinuousOn (fun r => ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) (Ioo t s)

/-- **Leaf 2** (differentiation under the integral on the compact support of `ψ`):
`d/dr ∫_cell φ(r) ψ = ∫_cell ∂_rφ(ρ) ψ` at `ρ ∈ (t, s)`. -/
def AdjWDtDeriv (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ))
        (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) ρ

/-- **Leaf 3** (cell integration by parts, `c`-periodicity, compact support of `ψ` in `η`,
`div v = 0`): `∫ φ(νΔψ - v·∇ψ) = ∫ (νΔφ + v·∇φ) ψ`, written with `ladChi - ladDt`. -/
def AdjWIBP (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      (∫ x in B0579.cell c, φ ρ x *
          ((ν * lapP ψ x - (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) =
        ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ)

/-- **Leaf 4** (integrability, `φ(ρ)` smooth, `ψ` compactly supported in `η`, `∇E` bounded with
weight): the three integrands are integrable on the cell. -/
def AdjWInt (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
      IntegrableOn (fun x => ladDt φ ρ x * (ψ x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => ladChi tr φ ρ x * (ψ x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => φ ρ x *
        ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
          uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) (B0579.cell c)

/-- **The classical adjoint equation for a jointly smooth weak solution** (SP 3060): for
`ρ ∈ (t, s)` and every cylinder test `ψ` with kernel velocity `K_cψ`,
`∫ χ(ρ) ψ = ∫ φ(ρ) (K_cψ)·∇E(ρ)`, `χ = ladChi`. -/
def AdjWeakPointwise (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
        ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) =
          ∫ x in B0579.cell c, φ ρ x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)

/-- **`χ` is bounded in `X_{-m,c}` for a jointly smooth weak solution** (SP 3052-3058, in physical
variables: "The adjoint localized interaction maps `X_{-m,d}` to `H¹_{-m,d}`", localized source
bounded by weighted Cauchy-Schwarz, near/far splitting of the kernel, the horizontal mean). -/
def AdjWeakChiBound (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 1 ≤ c → AdjWCtx m ν c tr t s g φ →
    ∃ M : ℝ, ∀ ρ ∈ Ioo t s, MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) ∧
      eLpNorm (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M

/-- The classical equation from the four leaves. -/
theorem adjWeakPointwise_of (m : ℝ) (h1 : AdjWRateCont m) (h2 : AdjWDtDeriv m)
    (h3 : AdjWIBP m) (h4 : AdjWInt m) : AdjWeakPointwise m := by
  intro ν c tr t s g φ hctx ρ hρ ψ uψ hψ hu
  have hA : IsAdjointWeak ν c m tr t s g φ := hctx.2.2.2.2.2.1
  have hts : t < s := hctx.2.2.2.1
  obtain ⟨hI1, hI2, hI3⟩ := h4 ν c tr t s g φ hctx ρ hρ ψ uψ hψ hu
  have hcont := h1 ν c tr t s g φ hctx ψ uψ hψ hu
  set Af : ℝ → ℂ := fun r => ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x with hAf
  have hIcc : Icc t s ∈ 𝓝 ρ := Icc_mem_nhds hρ.1 hρ.2
  have hIoo : Ioo t s ∈ 𝓝 ρ := Ioo_mem_nhds hρ.1 hρ.2
  -- derivative via the weak formulation
  have hint : IntervalIntegrable Af volume t s := hA.timeIntegrable ψ uψ hψ hu
  have hmeas : StronglyMeasurableAtFilter Af (𝓝 ρ) :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioo ρ hρ
  have hcA : ContinuousAt Af ρ := hcont.continuousAt hIoo
  have hint' : IntervalIntegrable Af volume ρ s :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hts.le, Set.uIcc_of_le hρ.2.le]; exact Icc_subset_Icc hρ.1.le le_rfl)
  have hder1 : HasDerivAt (fun r => ∫ x in B0579.cell c, φ r x * (ψ x : ℂ))
      (-Af ρ) ρ := by
    have h0 : HasDerivAt (fun r => (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ r' in r..s, Af r')
        (-Af ρ) ρ := by
      have := intervalIntegral.integral_hasDerivAt_left hint' hmeas hcA
      simpa using this.const_add (∫ x in B0579.cell c, g x * (ψ x : ℂ))
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [hIcc] with r hr
    exact hA.weak ψ uψ hψ hu r hr
  have hder2 := h2 ν c tr t s g φ hctx ρ hρ ψ hψ
  have heq : (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) = -Af ρ := hder2.unique hder1
  -- split Af ρ
  have hAρ : Af ρ =
      (∫ x in B0579.cell c, φ ρ x *
          ((ν * lapP ψ x - (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) -
        ∫ x in B0579.cell c, φ ρ x *
          ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
            uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ) := by
    have hadj := hA.integrable ψ uψ hψ hu ρ (Ioo_subset_Icc_self hρ)
    have hsum : IntegrableOn (fun x => φ ρ x *
        ((ν * lapP ψ x - (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
        (B0579.cell c) := by
      refine (hadj.add hI3).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.add_apply, adjIntegrand]
      push_cast
      ring
    rw [hAf]
    simp only
    rw [← integral_sub hsum hI3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [adjIntegrand]
    push_cast
    ring
  have hibp := h3 ν c tr t s g φ hctx ρ hρ ψ hψ
  have hsplit : (∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ)) =
      (∫ x in B0579.cell c, ladDt φ ρ x * (ψ x : ℂ)) +
        ∫ x in B0579.cell c, (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ) := by
    have hI4 : IntegrableOn (fun x => (ladChi tr φ ρ x - ladDt φ ρ x) * (ψ x : ℂ))
        (B0579.cell c) := by
      refine (hI2.sub hI1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.sub_apply]
      ring
    rw [← integral_add hI1 hI4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hsplit, heq, ← hibp, hAρ]
  ring

/-- `LadAdjPointwise` is the case of an adjoint flow. -/
theorem ladAdjPointwise_of_weak (m : ℝ) (h : AdjWeakPointwise m) : LadAdjPointwise m := by
  intro ν c tr t s g φ hν hc ht hts hB hφ ρ hρ ψ uψ hψ hu
  exact h ν c tr t s g φ ⟨hν, hc, ht, hts, hB, hφ.toWeak, hφ.jointSmooth⟩ ρ hρ ψ uψ hψ hu

/-- `LadChiBound` is the case of an adjoint flow. -/
theorem ladChiBound_of_weak (m : ℝ) (h : AdjWeakChiBound m) : LadChiBound m := by
  intro ν c tr t s g φ hν hc ht hts hB hφ
  exact h ν c tr t s g φ hc
    ⟨hν, lt_of_lt_of_le one_pos hc, ht, hts, hB, hφ.toWeak, hφ.jointSmooth⟩

end UnforcedLeray.Short.IIIa
