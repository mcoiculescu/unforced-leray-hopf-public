import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Part III-a, `PartIII-a:T21/2/7/2`: parabolic smoothing of the weak reverse-time adjoint

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071 (the
reverse-time adjoint, its weighted energies `E_j` = squared `H^j_{-m}` norms and the energy
inequalities `E_0' + β_min E_1 ≤ C_b E_0`, `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`), lines 3052-3058 (the
adjoint localized interaction `K_c^T(φ∇E)`, bounded `X_{-m} → H^1_{-m}`), lines 3044-3051 (weights,
bounded train coefficients).

## Why `AdjointSmoothing` is replaced

`AdjointSmoothing m` (`Sub/PartIIIa_T21_2_7.lean`) asks EVERY weak solution `φ` (`IsAdjointWeak`)
to be `C^∞` before the terminal age. Every field of `IsAdjointWeak` except `periodic` sees `φ r`
only up to Lebesgue-null sets, and `periodic` survives a change on the line `{x₂ = 0}`. Changing a
weak solution there for `r < s` gives a weak solution that is not continuous
(`IsAdjointWeak.congr_ae`). `not_adjointSmoothing_of_weak` compiles this: `AdjointSmoothing m` leaves
no weak solution at all for small `ν`, and `not_adjointSmoothing_of_adjointWeakExists` refutes it from
`AdjointWeakExists m` as soon as BUC trains exist at arbitrarily small `ν`. Uniqueness up to null
sets cannot repair it.

The corrected statement is about versions. `AdjointWeakRegular m`: every weak solution agrees, at
every age of `[t, s]` and almost everywhere on the plane, with an `IsAdjointFlow`. Its four leaves:
* `AdjointWeakSmoothVersion m` (parabolic smoothing, SP 3060): a version jointly `C^∞` on
  `[t, s) × ℝ²`;
* `AdjointWeakH1 m` (weighted energy, SP 3052-3071): a jointly smooth weak solution has
  `H^1_{-m,c}` slices before the terminal age;
* `AdjointWeakH1Cont m` (differentiated weighted energy, SP 3067-3071): such a solution lies in
  `C([t, s); H^1_{-m,c})`;
* `AdjointWeakHigherCont m` (SP 3060-3073, `E_1`, `E_2` used as classical quantities): such a
  solution lies in `C¹([t, s); H^3_{-m,c})`, `AdjHigherCont`. It needs, besides `LadTrainBdd`, the
  weighted jets `TrainJetsBdd` (of `v`, hence of `∇E`).
`AdjointWeakH1 m`, `AdjointWeakH1Cont m` and `AdjointWeakHigherCont m` are stated for `ν ≤ 1` and
trains with the time-local bounds `LadTrainBdd` (bounded velocity and `⟨x⟩^{m+2}|∇E|` bounded on the
cell, the coefficient bounds of the energy, SP 3050-3058): the form of `LadAdjPointwise` and of the
bounded-train weak existence `AdjointWeakExistsBdd`. `ν ≤ 1` is `c = ν⁻² ≥ 1`, the range of the
adjoint localized interaction `AdjLocalizedCoeff`. `AdjointWeakHigherCont m` has in addition the
hypothesis `TrainJetsBdd tr m S` on every `[0, S]` (`TrainJetsBddAll m` passes it from the BUC form;
it follows from `TrainWeightedJetPoly` for finitely many orders, the thresholds `ν₀` of
`TrainWeightedJetPoly` depending on the order).

`AdjointWeakSmoothVersion m` and `AdjointWeakRegular m` are stated for the train of the source, the
BUC class `PartI.IsBUCTrain` (SP 270-288), with these bounds (`AdjointWeakRegular m` with
`TrainJetsBdd` as well). A version `C^∞` in the age needs every weighted space-time jet of the
train: the age derivatives of `K_c^T(φ∇E)` pair `∂_r^j(φ∇E)` with the Biot-Savart kernel on the whole
cylinder (SP 3052-3058). `LadTrainBdd` bounds no derivative of `∇E` and `TrainJetsBdd` only the
orders `≤ 6`; the BUC train has them all (`TrainSTJetsOfBUC`, `Sub/AdjInterior/Defs.lean`).

## The two forms

`AdjointWeakExists m`, `AdjointSmoothExists m` and `AdjointExists m` have the BUC form: `ν ≤ ν₀`, the
trains of `PartI.IsBUCTrain` (SP 270-288). `LadTrainBddAll m` and `TrainJetsBddAll m` pass from it to
the form of `AdjointWeakRegular m` (`ν ≤ 1`, the BUC train with the bounds `LadTrainBdd` and
`TrainJetsBdd`), and every assembly here takes the minimum of the thresholds.

Proved here: `IsAdjointWeak.congr_ae` (almost-everywhere changes preserve weak solutions),
`adjPeriodic_of_ae_eq` (a continuous version of a periodic function is periodic), the
assemblies `adjointWeakRegular_of`, `adjointExists_of'` (from `AdjointSmoothExists`), its converse
`adjointSmoothExists_of_adjointExists`, `adjointSmoothExists_of` and `adjointExistsBUC_of_regular`
(both from `LadTrainBddAll` and `TrainJetsBddAll`), and the refutations `not_adjointSmoothing_of_weak`,
`not_adjointSmoothing_of_adjointWeakExists`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The statements -/

/-- Weighted jets of the train on `[0, S]` (SP 270-288, 2866-2873; `TrainWeightedJetPoly`): for the
orders `j ≤ 6` (`φ` to third order and `∂_rφ` to first order need `∂^j∇E` for `j ≤ 4` and `∂^jv` for
`j ≤ 4`, SP 3052-3058, 3067-3071), the derivatives `D^jv(ρ)(x)` on the whole plane, weighted by
`(1 + x₂²)^k`, `k = ⌈(m + 2)/2⌉`, are bounded for `ρ ∈ [0, S]`. -/
def TrainJetsBdd {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m S : ℝ) : Prop :=
  ∃ C : ℝ, ∀ j : ℕ, j ≤ 6 → ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
    (1 + x.2 ^ 2) ^ (⌈max 0 ((m + 2) / 2)⌉₊) * ‖iteratedFDeriv ℝ j (tr.v ρ) x‖ ≤ C

/-- **Weighted jets of BUC trains** (from `TrainWeightedJetPoly`, finitely many orders, as
`ladTrainBddAll`, `Sub/T21_2_3/LinAdjDuality/TrainBdd.lean`): for small `ν` every BUC train has
`TrainJetsBdd tr m S` for every `S ≥ 0`. -/
def TrainJetsBddAll (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S

/-- **The construction yields a smooth weak solution** (SP 3060-3061): for small `ν` and the trains
of the BUC class `PartI.IsBUCTrain` (SP 270-288), every terminal datum `g = physAdj a_s G`,
`G ∈ X_{-m,d_s}`, has a weak reverse-time solution on `[t, s]` (`IsAdjointWeak`) which is `C^∞` in
space for `r ∈ [t, s)`, jointly `C^∞` on `[t, s) × ℝ²`, and lies in `C([t, s); H^1_{-m,c})`. This is
`AdjointExists m` with the fields of `IsAdjointFlow` regrouped (`adjointExists_of'`,
`adjointSmoothExists_of_adjointExists`). -/
def AdjointSmoothExists (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∃ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ ∧
        (∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ r)) ∧
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) ∧
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ∧
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (φ r') - pdCx k (φ r)))
            (𝓝[Ico t s] r) (𝓝 0)) ∧
        AdjHigherCont (ν ^ (-2 : ℝ)) m t s φ

/-- **Parabolic smoothing, up to null sets** (SP 3060: the reverse-time adjoint
`-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` has smooth coefficients `v`, `E` (`B0140.IsTrain.smooth_v`) and
a nonlocal term of order `-1`, SP 3052-3058; interior parabolic regularity, which holds up to the
age `t` because the reverse-time evolution runs from `s` down to `t`). For `ν ≤ 1` and a BUC train
(`PartI.IsBUCTrain`, SP 270-288: its weighted space-time jets of every order are the coefficients of
the smoothing) with the time-local bounds `LadTrainBdd`, every weak solution `φ` with terminal datum
`physAdj a_s G` has a version `φ'`, equal to `φ r` almost everywhere on the plane for each
`r ∈ [t, s)`, which is jointly `C^∞` on `[t, s) × ℝ²`. -/
def AdjointWeakSmoothVersion (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∃ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r) ∧
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ico t s ×ˢ univ)

/-- **Weighted `H^1` before the terminal age** (SP 3060-3071: the weighted energy
`E_0 = ‖φ‖²_{X_{-m}}` satisfies `E_0' + β E_1 ≤ C E_0` by Reynolds cancellation, with the
diffusion-weight errors bounded by the log-derivative bounds of the weight, SP 3044-3049, the
transport term by `sup|v|` and the localized term by `⟨x⟩^{m+2}|∇E|`, SP 3052-3058; so
`∫_r^s E_1 < ∞`, and the inequality for `(s - r)E_1(r)` gives `E_1(r) < ∞` for every `r < s`).
For `ν ≤ 1` and a train with the bounds `LadTrainBdd`, a weak solution which is jointly `C^∞` on
`[t, s) × ℝ²` has `∂_kφ(r) ∈ X_{-m,c}` for every `r ∈ [t, s)`. -/
def AdjointWeakH1 (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        ∀ r ∈ Ico t s, ∀ k : Fin 2,
          MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))

/-- **Strong continuity in `H^1_{-m,c}` before the terminal age** (SP 3067-3071: the differentiated
weighted energy `E_1' + β E_2 ≤ C(E_1 + E_0)` is integrated, so `E_1` is continuous; the transport
term is integrated by parts onto `Δφ`, and needs only `sup|v|`). For `ν ≤ 1` and a train with the
bounds `LadTrainBdd`, a weak solution which is jointly `C^∞` on `[t, s) × ℝ²` and has `H^1_{-m,c}`
slices there lies in `C([t, s); H^1_{-m,c})`. This supplies `IsAdjointFlow.strongContH1`. -/
def AdjointWeakH1Cont (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        (∀ r ∈ Ico t s, ∀ k : Fin 2,
          MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) →
        ∀ r ∈ Ico t s, ∀ k : Fin 2,
          Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (φ r') - pdCx k (φ r)))
            (𝓝[Ico t s] r) (𝓝 0)

/-- **`φ ∈ C¹([t, s); H^3_{-m,c})`, `∂_rφ ∈ C([t, s); H^1_{-m,c})` before the terminal age** (SP 3060-3073:
the energies `E_1`, `E_2` are used as classical quantities, `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)` is
integrated after multiplying by the reverse time; so `∂^wφ`, `|w| ≤ 3`, `∂^w∂_rφ`, `|w| ≤ 1`, are
continuous into `X_{-m,c}`). The proof is the induction on `|w|` of `AdjointWeakH1Cont`
(`PartIII-a:T21/2/7/2/3`): `CutE1Deriv`, `CutRateBound`, `CutEnergySqueeze`, `L2StrongOfEnergy`
(`Sub/PartIII-a_T21_2_7_2_3.lean`) are stated for a general field, source and drift, and apply to
`∂^wφ` with source `∂^wχ + Σ (∂^{w₁}v)·∇∂^{w₂}φ` (`χ = ∂_rφ + νΔφ + v·∇φ`, the adjoint localized
interaction); this needs, besides `LadTrainBdd`, the weighted jets `TrainJetsBdd` of `v` (hence of
`∇E`, SP 3052-3058), which is why it has the extra train hypothesis. The time derivative follows from
the equation `∂_rφ = -νΔφ - v·∇φ + χ`. -/
def AdjointWeakHigherCont (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        AdjHigherCont (ν ^ (-2 : ℝ)) m t s φ

/-- **Parabolic smoothing of weak adjoint solutions** (SP 3060-3071; the corrected
`AdjointSmoothing`): for `ν ≤ 1` and a BUC train (`PartI.IsBUCTrain`, SP 270-288) with the bounds
`LadTrainBdd` and the weighted jets `TrainJetsBdd`, every weak solution `φ` with terminal datum
`physAdj a_s G` agrees, at every age `r ∈ [t, s]` and almost everywhere on the plane, with a
reverse-time adjoint flow `φ'` (`IsAdjointFlow`: smooth before `s`, in `C([t, s); H^1_{-m,c})`,
`C¹([t, s); H^3_{-m,c})`). -/
def AdjointWeakRegular (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∃ φ' : ℝ → ℝ × ℝ → ℂ,
          IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ' ∧
          ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r

/-! ## Weak solutions and flows -/

/-- An adjoint flow is a weak solution. -/
theorem IsAdjointFlow.toWeak {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (h : IsAdjointFlow ν c m tr t s g φ) :
    IsAdjointWeak ν c m tr t s g φ :=
  ⟨h.terminal, h.memX, h.strongCont, h.periodic, h.integrable, h.timeIntegrable, h.weak⟩

/-- A weak solution with the smoothing conclusions is an adjoint flow. -/
theorem IsAdjointWeak.toFlow {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (h : IsAdjointWeak ν c m tr t s g φ)
    (hs : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ r))
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hm : ∀ r ∈ Ico t s, ∀ k : Fin 2, MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure c (-m)))
    (hc : ∀ r ∈ Ico t s, ∀ k : Fin 2,
      Tendsto (fun r' => xNorm c (-m) (pdCx k (φ r') - pdCx k (φ r))) (𝓝[Ico t s] r) (𝓝 0))
    (hh : AdjHigherCont c m t s φ) :
    IsAdjointFlow ν c m tr t s g φ :=
  ⟨h.terminal, h.memX, h.strongCont, h.periodic, hs, hj, hm, hc, hh, h.integrable,
    h.timeIntegrable, h.weak⟩

/-- **Almost-everywhere changes preserve weak solutions**: if `φ' r = φ r` almost everywhere on the
plane for every `r ∈ [t, s]` and `φ'` is `c`-periodic before `s`, then `φ'` is a weak solution
with the same terminal datum. -/
theorem IsAdjointWeak.congr_ae {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ φ' : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν c m tr t s g φ) (hts : t ≤ s)
    (hae : ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r)
    (hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x) :
    IsAdjointWeak ν c m tr t s g φ' := by
  have hcell : ∀ r ∈ Icc t s, φ' r =ᵐ[volume.restrict (B0579.cell c)] φ r :=
    fun r hr => ae_restrict_of_ae (hae r hr)
  have hX : ∀ r ∈ Icc t s, φ' r =ᵐ[B0579.cellMeasure c (-m)] φ r :=
    fun r hr => (B0579.cellMeasure_ac c (-m)).ae_le (hcell r hr)
  have hint : ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), ∀ r ∈ Icc t s,
      adjIntegrand tr (φ' r) r ψ uψ =ᵐ[volume.restrict (B0579.cell c)]
        adjIntegrand tr (φ r) r ψ uψ :=
    fun ψ uψ r hr => (hcell r hr).mono fun x hx => by simp only [adjIntegrand, hx]
  have hI : ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), ∀ r ∈ Icc t s,
      ∫ x in B0579.cell c, adjIntegrand tr (φ' r) r ψ uψ x =
        ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x :=
    fun ψ uψ r hr => integral_congr_ae (hint ψ uψ r hr)
  refine ⟨(hcell s ⟨hts, le_rfl⟩).trans hφ.terminal,
    fun r hr => (hφ.memX r hr).ae_eq (hX r hr).symm, ?_, hper, ?_, ?_, ?_⟩
  · intro r hr
    have heq : ∀ r' ∈ Icc t s, xNorm c (-m) (φ r' - φ r) = xNorm c (-m) (φ' r' - φ' r) := by
      intro r' hr'
      unfold xNorm
      exact eLpNorm_congr_ae ((hX r' hr').symm.sub (hX r hr).symm)
    exact (hφ.strongCont r hr).congr' (eventually_nhdsWithin_of_forall heq)
  · intro ψ uψ hψ hu r hr
    exact (hφ.integrable ψ uψ hψ hu r hr).congr (hint ψ uψ r hr).symm
  · intro ψ uψ hψ hu
    refine (intervalIntegrable_congr ?_).1 (hφ.timeIntegrable ψ uψ hψ hu)
    intro r hr
    rw [uIoc_of_le hts] at hr
    exact (hI ψ uψ r (Ioc_subset_Icc_self hr)).symm
  · intro ψ uψ hψ hu r hr
    have h1 : ∫ x in B0579.cell c, φ' r x * (ψ x : ℂ) = ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) :=
      integral_congr_ae ((hcell r hr).mono fun x hx => by simp only [hx])
    rw [h1, hφ.weak ψ uψ hψ hu r hr]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro r' hr'
    rw [uIcc_of_le hr.2] at hr'
    exact (hI ψ uψ r' ⟨hr.1.trans hr'.1, hr'.2⟩).symm

/-- A continuous function equal almost everywhere on the plane to a `c`-periodic one is
`c`-periodic (translation by `(c, 0)` preserves Lebesgue measure; continuous functions equal
almost everywhere are equal). -/
theorem adjPeriodic_of_ae_eq {c : ℝ} {f g : ℝ × ℝ → ℂ} (hf : Continuous f)
    (hfg : f =ᵐ[volume] g) (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (x : ℝ × ℝ) :
    f (x.1 + c, x.2) = f x := by
  have e : ∀ y : ℝ × ℝ, ((c, 0) : ℝ × ℝ) + y = (y.1 + c, y.2) :=
    fun y => Prod.ext (add_comm c y.1) (zero_add y.2)
  have hT : (f ∘ fun y : ℝ × ℝ => ((c, 0) : ℝ × ℝ) + y) =ᵐ[volume]
      (g ∘ fun y : ℝ × ℝ => ((c, 0) : ℝ × ℝ) + y) :=
    (measurePreserving_add_left (volume : Measure (ℝ × ℝ)) ((c, 0) : ℝ × ℝ)).quasiMeasurePreserving.ae_eq_comp
      hfg
  have hT' : (f ∘ fun y : ℝ × ℝ => ((c, 0) : ℝ × ℝ) + y) =ᵐ[volume] f := by
    refine (hT.trans (Eventually.of_forall fun y => ?_)).trans hfg.symm
    simp only [Function.comp_apply, e, hg y]
  have hcont : Continuous (f ∘ fun y : ℝ × ℝ => ((c, 0) : ℝ × ℝ) + y) :=
    hf.comp (continuous_const.add continuous_id)
  have h := congrFun ((Continuous.ae_eq_iff_eq volume hcont hf).1 hT') x
  simpa only [Function.comp_apply, e] using h

/-- A slice of a function jointly `C^∞` on `[t, s) × ℝ²` is `C^∞` for `r ∈ [t, s)`. -/
theorem adjContDiff_slice {φ : ℝ → ℝ × ℝ → ℂ} {t s : ℝ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) {r : ℝ}
    (hr : r ∈ Ico t s) : ContDiff ℝ ∞ (φ r) :=
  hj.comp_contDiff (contDiff_const.prodMk contDiff_id) fun _ => ⟨hr, mem_univ _⟩

/-! ## The assemblies -/

/-- **Parabolic smoothing of weak adjoint solutions from its four leaves**: the jointly smooth
version (`AdjointWeakSmoothVersion`) is redefined to be `φ s` at the terminal age; it is periodic
(`adjPeriodic_of_ae_eq`), hence a weak solution (`IsAdjointWeak.congr_ae`), hence has `H^1_{-m,c}`
slices (`AdjointWeakH1`), hence lies in `C([t, s); H^1_{-m,c})` (`AdjointWeakH1Cont`) and in `C¹([t, s); H^3_{-m,c})`
(`AdjointWeakHigherCont`), hence is an adjoint flow. -/
theorem adjointWeakRegular_of (m : ℝ) (h1 : AdjointWeakSmoothVersion m) (h2 : AdjointWeakH1 m)
    (h3 : AdjointWeakH1Cont m) (h4 : AdjointWeakHigherCont m) : AdjointWeakRegular m := by
  intro ν hν hν1 tr htr hB hJ t s ht hts G hG φ hφ
  obtain ⟨ψ, hψae, hψj⟩ := h1 ν hν hν1 tr htr hB t s ht hts G hG φ hφ
  obtain ⟨φ', hφ'⟩ : ∃ φ' : ℝ → ℝ × ℝ → ℂ, ∀ r, φ' r = if r < s then ψ r else φ r :=
    ⟨_, fun _ => rfl⟩
  have hEq : ∀ r ∈ Ico t s, φ' r = ψ r := fun r hr => by rw [hφ', if_pos hr.2]
  have hj' : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ico t s ×ˢ univ) :=
    hψj.congr fun p hp => by rw [hEq p.1 hp.1]
  have hsm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r) := fun r hr => adjContDiff_slice hj' hr
  have hae : ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r := by
    intro r hr
    by_cases hrs : r < s
    · rw [hEq r ⟨hr.1, hrs⟩]
      exact hψae r ⟨hr.1, hrs⟩
    · rw [hφ', if_neg hrs]
  have hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + ν ^ (-2 : ℝ), x.2) = φ' r x :=
    fun r hr => adjPeriodic_of_ae_eq (hsm r hr).continuous (hae r (Ico_subset_Icc_self hr))
      (hφ.periodic r hr)
  have hw : IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ' :=
    hφ.congr_ae hts.le hae hper
  have hH1 := h2 ν hν hν1 tr hB t s ht hts G hG φ' hw hj'
  exact ⟨φ', hw.toFlow hsm hj' hH1 (h3 ν hν hν1 tr hB t s ht hts G hG φ' hw hj' hH1)
    (h4 ν hν hν1 tr hB hJ t s ht hts G hG φ' hw hj'), hae⟩

/-- `AdjointExists` from `AdjointSmoothExists` (the spec form of `PartIII-a:T21/2/7/2/org`). -/
theorem adjointExists_of' (m : ℝ) (h1 : AdjointSmoothExists m) : AdjointExists m := by
  obtain ⟨ν₀, hν₀, h1⟩ := h1
  refine ⟨ν₀, hν₀, fun ν hν tr htr t s ht hts G hG => ?_⟩
  obtain ⟨φ, hw, hs, hj, hm, hc, hh⟩ := h1 ν hν tr htr t s ht hts G hG
  exact ⟨φ, hw.toFlow hs hj hm hc hh⟩

/-- The converse: the fields of `AdjointExists m` regrouped. -/
theorem adjointSmoothExists_of_adjointExists (m : ℝ) (h : AdjointExists m) :
    AdjointSmoothExists m := by
  obtain ⟨ν₀, hν₀, h⟩ := h
  refine ⟨ν₀, hν₀, fun ν hν tr htr t s ht hts G hG => ?_⟩
  obtain ⟨φ, hφ⟩ := h ν hν tr htr t s ht hts G hG
  exact ⟨φ, hφ.toWeak, hφ.smooth, hφ.jointSmooth, hφ.memH1, hφ.strongContH1, hφ.higherCont⟩

/-- **Smooth weak solutions for the BUC train** (SP 3060, train of SP 270-288): weak existence
(`AdjointWeakExists`, `PartIII-a:T21/2/7/1`), the train bounds `LadTrainBddAll` (accepted
`ladTrainBddAll`, `PartIII-a:T21/2/3/1/6`), the weighted jets `TrainJetsBddAll` and parabolic
smoothing (`AdjointWeakRegular`, applied to the same BUC train); the threshold is the minimum of
those of the first three and `1`. -/
theorem adjointSmoothExists_of (m : ℝ) (hB : LadTrainBddAll m) (hJ : TrainJetsBddAll m)
    (h1 : AdjointWeakExists m) (h2 : AdjointWeakRegular m) : AdjointSmoothExists m := by
  obtain ⟨ν₁, hν₁, hB⟩ := hB
  obtain ⟨ν₃, hν₃, hJ⟩ := hJ
  obtain ⟨ν₂, hν₂, h1⟩ := h1
  refine ⟨min (min (min ν₁ ν₂) ν₃) 1, lt_min (lt_min (lt_min hν₁ hν₂) hν₃) one_pos,
    fun ν hν tr htr t s ht hts G hG => ?_⟩
  have hν₁' : ν ∈ Ioc 0 ν₁ :=
    ⟨hν.1, hν.2.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))⟩
  have hν₂' : ν ∈ Ioc 0 ν₂ :=
    ⟨hν.1, hν.2.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))⟩
  have hν₃' : ν ∈ Ioc 0 ν₃ := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨φ, hφ⟩ := h1 ν hν₂' tr htr t s ht hts G hG
  obtain ⟨φ', hφ', -⟩ := h2 ν hν.1 (hν.2.trans (min_le_right _ _)) tr htr (hB ν hν₁' tr htr)
    (hJ ν hν₃' tr htr) t s ht hts G hG φ hφ
  exact ⟨φ', hφ'.toWeak, hφ'.smooth, hφ'.jointSmooth, hφ'.memH1, hφ'.strongContH1,
    hφ'.higherCont⟩

/-- **The adjoint flow for the BUC train** (SP 3060, train of SP 270-288): `AdjointExists m` from
the weak existence, the train bounds and jets, and parabolic smoothing, as in
`adjointSmoothExists_of`. -/
theorem adjointExistsBUC_of_regular (m : ℝ) (hB : LadTrainBddAll m) (hJ : TrainJetsBddAll m)
    (h1 : AdjointWeakExists m) (h2 : AdjointWeakRegular m) : AdjointExists m :=
  adjointExists_of' m (adjointSmoothExists_of m hB hJ h1 h2)

/-! ## The refutation of `AdjointSmoothing` -/

/-- The core of the refutation, at fixed data. Add `1` to a weak solution on the null line
`{x₂ = 0}` for `r < s`: the result is still a periodic weak solution (`IsAdjointWeak.congr_ae`), and
two continuous functions equal almost everywhere are equal. So not every weak solution is
continuous at the age `t`. -/
theorem not_forall_weak_contDiff {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    (hts : t < s) {g : ℝ × ℝ → ℂ}
    (h : ∀ φ : ℝ → ℝ × ℝ → ℂ, IsAdjointWeak ν c m tr t s g φ → ContDiff ℝ ∞ (φ t))
    {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν c m tr t s g φ) : False := by
  obtain ⟨φ', hφ'⟩ : ∃ φ' : ℝ → ℝ × ℝ → ℂ,
      ∀ r x, φ' r x = if r < s ∧ x.2 = 0 then φ r x + 1 else φ r x :=
    ⟨_, fun _ _ => rfl⟩
  have hnull : (volume : Measure (ℝ × ℝ)) {x | x.2 = 0} = 0 := by
    have e : {x : ℝ × ℝ | x.2 = 0} = univ ×ˢ {0} := by ext x; simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  have hne : ∀ᵐ x : ℝ × ℝ ∂volume, x.2 ≠ 0 :=
    ae_iff.2 (by simp only [ne_eq, not_not]; exact hnull)
  have hae : ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r := by
    intro r _
    filter_upwards [hne] with x hx
    rw [hφ']
    simp [hx]
  have hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x := by
    intro r hr x
    simp only [hφ', hφ.periodic r hr x]
  have hw := hφ.congr_ae hts.le hae hper
  have h1 := h φ hφ
  have h2 := h φ' hw
  have heq := (Continuous.ae_eq_iff_eq volume h2.continuous h1.continuous).1
    (hae t ⟨le_rfl, hts.le⟩)
  have h0 := congrFun heq (0, 0)
  rw [hφ'] at h0
  simp [hts] at h0

/-- **`AdjointSmoothing m` leaves no weak solutions**: under it there is, for small `ν` and BUC
trains, no weak solution with terminal datum `physAdj a_s G`. -/
theorem not_adjointSmoothing_of_weak {m : ℝ} (h : AdjointSmoothing m) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
        MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
        ∀ φ : ℝ → ℝ × ℝ → ℂ,
          ¬ IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ := by
  obtain ⟨ν₀, hν₀, h⟩ := h
  refine ⟨ν₀, hν₀, fun ν hν tr htr t s ht hts G hG φ hφ => ?_⟩
  exact not_forall_weak_contDiff hts
    (fun φ' hφ' => (h ν hν tr htr t s ht hts G hG φ' hφ').1 t ⟨le_rfl, hts⟩) hφ

/-- The old leaf is refuted by the weak existence it was paired with, as soon as BUC trains exist at
arbitrarily small `ν` (the train of SP 270-288). -/
theorem not_adjointSmoothing_of_adjointWeakExists {m : ℝ} (hW : AdjointWeakExists m)
    (htr : ∀ ν₀ : ℝ, 0 < ν₀ → ∃ ν ∈ Ioc 0 ν₀, ∃ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr) : ¬ AdjointSmoothing m := by
  intro h
  obtain ⟨ν₁, hν₁, hN⟩ := not_adjointSmoothing_of_weak h
  obtain ⟨ν₂, hν₂, hW⟩ := hW
  obtain ⟨ν, hν, tr, hb⟩ := htr (min ν₁ ν₂) (lt_min hν₁ hν₂)
  have hG : MemLp (0 : ℝ × ℝ → ℂ) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν 1)) (-m)) := MemLp.zero
  obtain ⟨φ, hφ⟩ := hW ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩ tr hb 0 1 le_rfl one_pos 0 hG
  exact hN ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ tr hb 0 1 le_rfl one_pos 0 hG φ hφ

end UnforcedLeray.Short.IIIa
