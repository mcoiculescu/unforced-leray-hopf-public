import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, `PartIII-a:T21/2/3/1`: the weak duality of the linearised flow and its adjoint

Source of record: `the November 2 reference manuscript` (SP), lines 3074-3075
("By duality, the moving weak-to-strong norm is at most ..."): the pairing
`r ↦ ∫_{C_c} w(r) φ(r)` of the weak linearised flow `w` (`IsLinearisedFlow`, `Defs.lean`,
SP 2819-2830) and the weak reverse-time adjoint `φ` (`IsAdjointFlow`, `Clock/WeakSmoothing/Adjoint.lean`,
SP 3060) is constant on `[t, s]`, so `∫ w(s) g = ∫ f φ(t)` (`LinAdjDuality`, `Sub/PartIIIa_T21_2_3.lean`).

## The class of the train and the weight

`LinAdjDuality m` quantifies over every `B0140.TrainSol`. The duality needs the train velocity
to be bounded and the train vorticity gradient to decay against the weight on the whole cell
(the cut-off commutator `∫ w φ v·∇χ_R` and the interaction `∫ (K_cw)·∇E φ` with `φ ∈ X_{-m}`);
`B0140.IsTrain` gives no such bound (`Short/PartI/TrainClass.lean`). The train of the source is
the Gallay-Slijepcevic train in `BUC` (SP 270-288) with the weighted bounds of SP 2866-2873
(`TrainWeightedJetPoly`, `Sub/PartIIIa_T21_2_6.lean`, small `ν`), and the weight is `m > 8`
(SP 2824, "Fix `m > 8`"; the Biot-Savart embedding `‖K_cf‖₂ ≤ C_m‖f‖_{X_{m,c}}`, SP 3230-3240).
The target proved from the leaves is therefore `LinAdjDualityBUC m` (BUC trains, `ν ≤ ν₀`), a
weakening of `LinAdjDuality m` (`linAdjDualityBUC_of_all`).

## The route (SP 3074-3075)

With the transverse cutoff `χ_R = ladCut R` (`χ_R = 1` on `|η| ≤ R`, `0` on `|η| ≥ √2 R`) the
cut-off adjoint `χ_Rφ(r)` is a cylinder test, jointly smooth on `[t, s) × ℝ²`, so
* (`LadProductRule`) the cut pairing `P_R(r) = ∫ w(r) χ_R φ(r)` satisfies
  `P_R(r) - P_R(t) = ∫_t^r ladRate R`, where `ladRate R ρ` is the forward weak right-hand side
  tested against `χ_Rφ(ρ)` plus `∫ w(ρ) χ_R ∂_ρφ(ρ)` (the product rule for `d/dr` of the pairing);
* (`LadRateSplit`) `ladRate R ρ = ∫ w χ_R χ - ∫ (K_cw·∇E) χ_R φ + ladComm R ρ`, with
  `χ = ladChi = ∂_ρφ + νΔφ + v·∇φ` (the transport terms cancel exactly);
* (`LadAdjPointwise`) `χ(ρ)` is the adjoint localized interaction `K_c^T(φ∇E)`:
  `∫ χ ψ = ∫ φ (K_cψ)·∇E` for every test `ψ` (the weak adjoint equation with a smooth `φ`);
* (`LadChiBound`, SP 3052-3058) `χ(ρ) ∈ X_{-m}`, uniformly; (`LadTransposition`)
  `∫ w χ = ∫ (K_cw·∇E) φ`; (`LadCommVanish`) the commutator tends to `0`; hence
  `ladRate R ρ → 0` (`ladRatePointwise_of`, proved here);
* (`LadRateBound`, with `LadAdjGradInt`, the reverse-time energy bound of SP 3060-3071) a
  dominating function in `ρ`, so `∫_t^r ladRate R → 0` (dominated convergence);
* (`LadCutLimit`) `P_R(r) → P(r)`; so `P` is constant on `[t, s)`, and (`LadPairCont`) by
  continuity on `[t, s]`.

## Contents

* objects: `ladCut`, `ladCutPhi`, `ladDt`, `ladLapCx`, `ladTransport`, `ladForce`, `ladFlowCx`,
  `ladPair`, `ladCutPair`, `ladRate`, `ladChi`, `ladComm`, `LadTrainBdd`;
* the target `LinAdjDualityBUC` and the weakening `linAdjDualityBUC_of_all`;
* the leaves `LadCutProps`, `LadPairCont`, `LadCutLimit`, `LadVelLip`, `LadProductRule`,
  `LadTrainBddAll`, `LadAdjPointwise`, `LadChiBound`, `LadTransposition`, `LadForceMemX`,
  `LadRateSplit`, `LadCommVanish`, `LadAdjGradInt`, `LadRateBound`;
* the assemblies `ladRatePointwise_of` and `linAdjDualityBUC_of` (proved here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-! ## Objects -/

/-- The transverse cutoff `χ_R(x) = ζ(2 - η²/R²)`, `ζ = Real.smoothTransition`: smooth, depends
on `η = x.2` only, `χ_R = 1` for `η² ≤ R²` and `χ_R = 0` for `η² ≥ 2R²`. -/
def ladCut (R : ℝ) (x : ℝ × ℝ) : ℝ := Real.smoothTransition (2 - x.2 ^ 2 / R ^ 2)

/-- The cut-off adjoint `χ_R φ(ρ)`. -/
def ladCutPhi (φ : ℝ → ℝ × ℝ → ℂ) (R ρ : ℝ) (x : ℝ × ℝ) : ℂ := (ladCut R x : ℂ) * φ ρ x

/-- The classical time derivative `∂_ρφ(ρ, x)`. -/
def ladDt (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℂ :=
  derivWithin (fun r => φ r x) (Set.Ici ρ) ρ

/-- Where `r ↦ φ r x` is differentiable at `ρ`, `ladDt` is the ordinary derivative (it is the right
derivative, so it is also meaningful at the initial age `ρ = t`). -/
theorem ladDt_eq_of_hasDerivAt {φ : ℝ → ℝ × ℝ → ℂ} {ρ : ℝ} {x : ℝ × ℝ} {d : ℂ}
    (h : HasDerivAt (fun r => φ r x) d ρ) : ladDt φ ρ x = d :=
  h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)

/-- The classical Laplacian of a complex field, `∂₁²Ψ + ∂₂²Ψ` (`pdCx`). -/
def ladLapCx (Ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := pdCx 0 (pdCx 0 Ψ) x + pdCx 1 (pdCx 1 Ψ) x

/-- The transport `v(ρ)·∇Ψ` by the actual train velocity. -/
def ladTransport {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ) (Ψ : ℝ × ℝ → ℂ)
    (x : ℝ × ℝ) : ℂ :=
  ((tr.v ρ x 0 : ℝ) : ℂ) * pdCx 0 Ψ x + ((tr.v ρ x 1 : ℝ) : ℂ) * pdCx 1 Ψ x

/-- The interaction density `u·∇E(ρ)` of a velocity `u` against the actual train vorticity. -/
def ladForce {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ)
    (x : ℝ × ℝ) : ℂ :=
  u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
    u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)

/-- The tested right-hand side of the linearised vorticity equation against a complex test `Ψ`:
`ω(νΔΨ + v·∇Ψ) - (u·∇E)Ψ` (for real `Ψ` this is `flowIntegrand`, `Defs.lean`). -/
def ladFlowCx {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ) (Ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  om x * ((ν : ℂ) * ladLapCx Ψ x + ladTransport tr ρ Ψ x) - ladForce tr u ρ x * Ψ x

/-- The duality pairing `P(ρ) = ∫_{C_c} w(ρ) φ(ρ)` (SP 3074-3075). -/
def ladPair (c : ℝ) (w φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) : ℂ := ∫ x in B0579.cell c, w ρ x * φ ρ x

/-- The cut pairing `P_R(ρ) = ∫_{C_c} w(ρ) χ_R φ(ρ)`. -/
def ladCutPair (c R : ℝ) (w φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∫ x in B0579.cell c, w ρ x * ladCutPhi φ R ρ x

/-- The rate of the cut pairing: the forward weak right-hand side tested against `χ_Rφ(ρ)` plus
`∫ w(ρ) χ_R ∂_ρφ(ρ)`. -/
def ladRate {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (w : ℝ → ℝ × ℝ → ℂ)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (R ρ : ℝ) : ℂ :=
  (∫ x in B0579.cell c, ladFlowCx tr (w ρ) (u ρ) ρ (ladCutPhi φ R ρ) x) +
    ∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)

/-- `χ = ∂_ρφ + νΔφ + v·∇φ`: for the smooth adjoint this is the adjoint localized interaction
`K_c^T(φ∇E)` (the classical form `-∂_ρφ = νΔφ + v·∇φ - K_c^T(φ∇E)` of the adjoint equation,
SP 3060). -/
def ladChi {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ)
    (x : ℝ × ℝ) : ℂ :=
  ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x + ladTransport tr ρ (φ ρ) x

/-- The cutoff commutator `∫ w (ν(2∇χ_R·∇φ + (Δχ_R)φ) + (v·∇χ_R)φ)`. -/
def ladComm {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (w φ : ℝ → ℝ × ℝ → ℂ)
    (R ρ : ℝ) : ℂ :=
  ∫ x in B0579.cell c, w ρ x *
    ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
      ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
        φ ρ x)

/-- Time-local bounds of the actual train on `[0, S]` by `C` (SP 270-288, 2866-2873): the velocity
is bounded and the vorticity gradient is bounded with the weight `⟨x⟩^{m+2}` on the cell. -/
def LadTrainBdd {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m S C : ℝ) : Prop :=
  ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x ∈ B0579.cell c,
    (∀ j : Fin 2, |tr.v ρ x j| ≤ C) ∧
      ∀ j : Fin 2, B0579.jb x ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤ C

/-! ## The target -/

/-- **Weak duality for the BUC train** (SP 3074-3075, train of SP 270-288): `LinAdjDuality m`
for the trains of the class `PartI.IsBUCTrain` and `ν ≤ ν₀`. -/
def LinAdjDualityBUC (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ g : ℝ × ℝ → ℂ, ∀ φ : ℝ → ℝ × ℝ → ℂ,
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
        HasZeroCirculation (ν ^ (-2 : ℝ)) f →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * g x =
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ t x

/-- `LinAdjDuality m` (every train) implies the BUC version. -/
theorem linAdjDualityBUC_of_all (m : ℝ) (h : LinAdjDuality m) : LinAdjDualityBUC m :=
  ⟨1, one_pos, fun ν hν tr _ => h ν hν.1 tr⟩

/-! ## The leaves -/

/-- **The cutoff** (calculus): for `R > 0`, `χ_R` is a cylinder test of every period, takes values
in `[0, 1]`, equals `1` on `η² ≤ R²` and `0` on `η² ≥ 2R²`, and `|∂_jχ_R| ≤ K/R`,
`|Δχ_R| ≤ K/R²` (`χ_R(x) = h(η/R)`, `h(y) = ζ(2 - y²)` smooth with `h' , h''` supported in
`1 ≤ |y| ≤ √2`). -/
def LadCutProps : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
    (∀ c : ℝ, B0579.IsCylTest c (ladCut R)) ∧
    (∀ x : ℝ × ℝ, 0 ≤ ladCut R x ∧ ladCut R x ≤ 1) ∧
    (∀ x : ℝ × ℝ, x.2 ^ 2 ≤ R ^ 2 → ladCut R x = 1) ∧
    (∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 → ladCut R x = 0) ∧
    (∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ K / R) ∧
    (∀ x : ℝ × ℝ, |lapP (ladCut R) x| ≤ K / R ^ 2)

/-- **Continuity of the duality pairing** (SP 3074-3075; `X_{m,c}`-`X_{-m,c}` Cauchy-Schwarz,
`|∫FG| ≤ ‖F‖_{X_m}‖G‖_{X_{-m}}`, with the strong continuity of both flows): `P` is continuous on
`[t, s]`. -/
def LadPairCont : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    t < s → IsAdjointFlow ν c m tr t s g φ → IsLinearisedFlow ν c m tr t f w u →
      ContinuousOn (ladPair c w φ) (Icc t s)

/-- **Removing the cutoff** (dominated convergence; `FG ∈ L¹` by weighted Cauchy-Schwarz,
`0 ≤ χ_R ≤ 1`, `χ_R → 1`): `∫ F χ_R G → ∫ F G` for `F ∈ X_{m,c}`, `G ∈ X_{-m,c}`. -/
def LadCutLimit : Prop :=
  ∀ (c m : ℝ) (F G : ℝ × ℝ → ℂ), MemLp F 2 (B0579.cellMeasure c m) →
    MemLp G 2 (B0579.cellMeasure c (-m)) →
    Tendsto (fun R : ℝ => ∫ x in B0579.cell c, F x * ((ladCut R x : ℂ) * G x)) atTop
      (𝓝 (∫ x in B0579.cell c, F x * G x))

/-- **The velocity of the linearised flow is controlled by its vorticity** (SP 3230-3240,
`‖K_cf‖₂ ≤ C_m‖f‖_{X_{m,c}}`, `c ≥ 1`; with the uniqueness of the Biot-Savart velocity): the
weak flow keeps zero circulation (`u ∈ L²` with `curl u = w`), `u(ρ) - u(ρ')` is a Biot-Savart
velocity of `w(ρ) - w(ρ')`, so `‖u(ρ) - u(ρ')‖₂ ≤ C‖w(ρ) - w(ρ')‖_{X_m}`. Used for `m > 8`. -/
def LadVelLip (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    1 ≤ c → HasZeroCirculation c f → IsLinearisedFlow ν c m tr t f w u →
      ∃ C : ℝ, ∀ ρ ρ' : ℝ, t ≤ ρ → t ≤ ρ' → ∀ j : Fin 2,
        eLpNorm (fun x => u ρ x j - u ρ' x j) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal C * xNorm c m (w ρ - w ρ')

/-- **The product rule for the cut pairing** (SP 3074-3075: `IsLinearisedFlow.weak` tested
against the time-dependent cylinder test `χ_Rφ(ρ)`): for an adjoint-type family `φ`, jointly
smooth on `[t, s) × ℝ²` and `c`-periodic, `ρ ↦ ladRate R ρ` is integrable on `[t, r]` and
`P_R(r) - P_R(t) = ∫_t^r ladRate R`, `r < s`. (Partition `[t, r]`; on each piece use the weak
equation with the frozen test and the classical derivative of `χ_Rφ` in time; the local
bounds of the train come from its smoothness on `[0, ∞) × ℝ²` and the support `|η| ≤ √2 R`, the
continuity of `u` in `L²` from the hypothesis.) -/
def LadProductRule : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    0 < ν → 0 < c → 0 ≤ t → t < s → IsLinearisedFlow ν c m tr t f w u →
    (∃ C : ℝ, ∀ ρ ρ' : ℝ, t ≤ ρ → t ≤ ρ' → ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j - u ρ' x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal C * xNorm c m (w ρ - w ρ')) →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
    (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x) →
    ∀ R : ℝ, 0 < R → ∀ r ∈ Ico t s,
      IntervalIntegrable (fun ρ => ladRate tr w u φ R ρ) volume t r ∧
        ladCutPair c R w φ r - ladCutPair c R w φ t = ∫ ρ in t..r, ladRate tr w u φ R ρ

/-- **Time-local bounds of the BUC train** (SP 270-288: `BUC`, smooth for positive time;
SP 2866-2873 and `TrainWeightedJetPoly`: every fixed weighted derivative norm, `ν` small): on
every `[0, S]` the velocity is bounded and `⟨x⟩^{m+2}|∇E|` is bounded on the cell. -/
def LadTrainBddAll (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C

/-- **The classical adjoint equation** (SP 3060; `IsAdjointFlow.weak` with `φ` smooth on
`[t, s) × ℝ²`): for `ρ ∈ (t, s)` and every cylinder test `ψ` with kernel velocity `K_cψ`,
`∫ χ(ρ) ψ = ∫ φ(ρ) (K_cψ)·∇E(ρ)`, `χ = ladChi` (differentiate the weak equation at `ρ`: the
right-hand side is continuous in `ρ` by the train bounds; differentiate `∫ φ(ρ)ψ` under the
integral; integrate `νΔ` and `v·∇` by parts on the cylinder, `div v = 0`). -/
def LadAdjPointwise (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ),
    0 < ν → 0 < c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
        ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) =
          ∫ x in B0579.cell c, φ ρ x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)

/-- **The adjoint localized interaction is in `X_{-m}`** (SP 3052-3058, in physical variables:
"The adjoint localized interaction maps `X_{-m,d}` to `H¹_{-m,d}`", localized source bounded by
weighted Cauchy-Schwarz, near/far splitting of the kernel, the horizontal mean): `χ(ρ)`, which
`LadAdjPointwise` identifies with `K_c^T(φ(ρ)∇E(ρ))`, lies in `X_{-m,c}` with a bound uniform on
`(t, s)` (`‖φ(ρ)‖_{X_{-m}}` is bounded on `[t, s]`). Used for `m > 8`. -/
def LadChiBound (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    ∃ M : ℝ, ∀ ρ ∈ Ioo t s, MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) ∧
      eLpNorm (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M

/-- **Transposition of the localized interaction** (SP 3052-3058, 3074-3075): for the weak flow
`w(ρ)` (zero circulation, velocity `u(ρ) = K_cw(ρ)`), `∫ w(ρ) χ(ρ) = ∫ (u(ρ)·∇E(ρ)) φ(ρ)`
(approximate `w(ρ)` in `X_m` by zero-circulation tests, whose velocities converge in `L²` by
SP 3230-3240; pass to the limit in `LadAdjPointwise` with `χ ∈ X_{-m}`, `φ∇E ∈ L²`). Used for
`m > 8`. -/
def LadTransposition (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    MemLp f 2 (B0579.cellMeasure c m) → HasZeroCirculation c f →
    IsLinearisedFlow ν c m tr t f w u →
    ∀ ρ ∈ Ioo t s,
      ∫ x in B0579.cell c, w ρ x * ladChi tr φ ρ x =
        ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x

/-- **The interaction density is in `X_m`** (weighted Cauchy-Schwarz, SP 3053-3054): with the
train bound, `‖u·∇E(ρ)‖_{X_{m,c}} ≤ C(‖u₀‖₂ + ‖u₁‖₂)` for `ρ ∈ [0, S]`
(`⟨x⟩^m|∇E| ≤ ⟨x⟩^{m+2}|∇E| ≤ C` since `jb ≥ 1`). -/
def LadForceMemX (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (S C ρ : ℝ), LadTrainBdd tr m S C →
    ρ ∈ Icc (0 : ℝ) S → ∀ u : ℝ × ℝ → Fin 2 → ℂ,
      (∀ j : Fin 2, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c))) →
      MemLp (ladForce tr u ρ) 2 (B0579.cellMeasure c m) ∧
        eLpNorm (ladForce tr u ρ) 2 (B0579.cellMeasure c m) ≤
          ENNReal.ofReal C * (eLpNorm (fun x => u x 0) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => u x 1) 2 (volume.restrict (B0579.cell c)))

/-- **Splitting the rate** (calculus; product rule for `∂(χ_Rφ)`, `Δ(χ_Rφ)`): for `ρ ∈ (t, s)`,
`ladRate R ρ = ∫ w χ_R χ - ∫ (u·∇E) χ_Rφ + ladComm R ρ`; every piece is integrable on the cell
(supported in `|η| ≤ √2 R`; `w(ρ), u(ρ) ∈ L²` there, the other factors continuous). -/
def LadRateSplit : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    0 < c → 0 ≤ t → t < s → IsLinearisedFlow ν c m tr t f w u →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
    ∀ R : ℝ, 0 < R → ∀ ρ ∈ Ioo t s,
      ladRate tr w u φ R ρ =
        (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
          (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) +
            ladComm tr w φ R ρ

/-- **The commutator vanishes** (`|∇χ_R| ≤ K/R`, `|Δχ_R| ≤ K/R²`, `v` bounded; `w(ρ) ∈ X_m`,
`φ(ρ), ∇φ(ρ) ∈ X_{-m}` from `IsAdjointFlow.memX/memH1`): `ladComm R ρ → 0`, `ρ ∈ (t, s)`. -/
def LadCommVanish (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    0 < ν → 0 < c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ → IsLinearisedFlow ν c m tr t f w u →
    ∀ ρ ∈ Ioo t s, Tendsto (fun R : ℝ => ladComm tr w φ R ρ) atTop (𝓝 0)

/-- **The reverse-time adjoint gradient is integrable in time** (SP 3060-3071: "differentiated
weighted energy", here the cut-off `E_0` identity in physical variables): for `r < s`,
`ρ ↦ ‖∂_kφ(ρ)‖_{X_{-m}}` is integrable on `[t, r]` (with `ζ_R²` cutoffs:
`2ν∫_t^r∫ζ_R²⟨x⟩^{-2m}|∇φ|² ≤ ∫ζ_R²⟨x⟩^{-2m}|φ(r)|² + C∫_t^r(‖φ‖² + ‖φ‖‖χ‖)` uniformly in `R`,
`χ` bounded by `LadChiBound`; monotone convergence). Used for `m > 8`. -/
def LadAdjGradInt (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    ∀ r ∈ Ico t s, ∀ k : Fin 2,
      IntervalIntegrable
        (fun ρ => (eLpNorm (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) volume t r

/-- **A dominating function for the rate** (from `LadRateSplit`: `|∫wχ_Rχ| ≤ ‖w‖‖χ‖`,
`|∫(u·∇E)χ_Rφ| ≤ ‖u·∇E‖_{X_m}‖φ‖`, `|ladComm R ρ| ≤ K'(‖w‖‖∇φ‖ + ‖w‖‖φ‖)` for `R ≥ 1`;
`‖w‖, ‖u‖, ‖φ‖, ‖χ‖` bounded on `[t, r]`, `‖∇φ‖` integrable by `LadAdjGradInt`). Used for
`m > 8`. -/
def LadRateBound (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    MemLp f 2 (B0579.cellMeasure c m) → HasZeroCirculation c f →
    IsLinearisedFlow ν c m tr t f w u →
    ∀ r ∈ Ico t s, ∃ D : ℝ → ℝ, IntervalIntegrable D volume t r ∧
      ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t r, ‖ladRate tr w u φ R ρ‖ ≤ D ρ

/-! ## Assemblies -/

/-- The rate tends to `0` at every `ρ ∈ (t, s)`. -/
def LadRatePointwise (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    0 < ν → 1 ≤ c → 0 ≤ t → t < s →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    IsAdjointFlow ν c m tr t s g φ →
    MemLp f 2 (B0579.cellMeasure c m) → HasZeroCirculation c f →
    IsLinearisedFlow ν c m tr t f w u →
    ∀ ρ ∈ Ioo t s, Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop (𝓝 0)

/-- **Pointwise vanishing of the rate**: `ladRate R ρ = ∫wχ_Rχ - ∫(u·∇E)χ_Rφ + ladComm R ρ
→ ∫wχ - ∫(u·∇E)φ + 0 = 0`. -/
theorem ladRatePointwise_of (m : ℝ) (h2 : LadCutLimit) (h7 : LadChiBound m)
    (h8 : LadTransposition m) (h9 : LadForceMemX m) (h10 : LadRateSplit)
    (h11 : LadCommVanish m) : LadRatePointwise m := by
  intro ν c tr t s g φ f w u hν hc ht hts hB hφ hf hf0 hw ρ hρ
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  obtain ⟨M, hM⟩ := h7 ν c tr t s g φ hν hc ht hts hB hφ
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  obtain ⟨C, hC⟩ := hB s (ht.trans hts.le)
  have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨hρ0, hρ.2.le⟩
  have hwX : MemLp (w ρ) 2 (B0579.cellMeasure c m) := hw.memX ρ hρ.1.le
  have hφX : MemLp (φ ρ) 2 (B0579.cellMeasure c (-m)) := hφ.memX ρ ⟨hρ.1.le, hρ.2.le⟩
  have hFX : MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) :=
    (h9 ν c tr s C ρ hC hρS (u ρ) (hw.biotSavart ρ hρ.1.le).1).1
  have hA := h2 c m (w ρ) (ladChi tr φ ρ) hwX (hM ρ hρ).1
  have hBl := h2 c m (ladForce tr (u ρ) ρ) (φ ρ) hFX hφX
  have hCm := h11 ν c tr t s g φ f w u hν hc0 ht hts hB hφ hw ρ hρ
  have hsum := (hA.sub hBl).add hCm
  have htr := h8 ν c tr t s g φ f w u hν hc ht hts hB hφ hf hf0 hw ρ hρ
  rw [htr, sub_self, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [h10 ν c m tr t s f w u φ hc0 ht hts hw hφ.jointSmooth R hR ρ hρ]
  rfl

/-- `ρ ≠ r` almost everywhere. -/
theorem lad_ae_ne (r : ℝ) : ∀ᵐ ρ ∂(volume : Measure ℝ), ρ ≠ r := by
  rw [ae_iff]
  simp

/-- **Assembly** (SP 3074-3075): the cut pairings converge, their increments are the integrals of
the rate, which tend to `0` by dominated convergence; so the pairing is constant on `[t, s)`, hence
on `[t, s]` by continuity, and `∫ w(s) g = P(s) = P(t) = ∫ f φ(t)`. -/
theorem linAdjDualityBUC_of (m : ℝ) (h1 : LadPairCont) (h2 : LadCutLimit) (h3 : LadVelLip m)
    (h4 : LadProductRule) (h5 : LadTrainBddAll m) (hP : LadRatePointwise m)
    (h14 : LadRateBound m) : LinAdjDualityBUC m := by
  obtain ⟨ν₀, hν₀, hT⟩ := h5
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν tr hbuc t s ht hts g φ hφ f hf hf0 w u hw
  have hν0 : 0 < ν := hν.1
  have hνν₀ : ν ∈ Ioc 0 ν₀ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hc0 : 0 < ν ^ (-2 : ℝ) := lt_of_lt_of_le one_pos hc1
  have hB : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C := hT ν hνν₀ tr hbuc
  have hLip := h3 ν _ tr t f w u hc1 hf0 hw
  -- the pairing is constant on `[t, s)`
  have hconst : ∀ r ∈ Ico t s, ladPair (ν ^ (-2 : ℝ)) w φ r = ladPair (ν ^ (-2 : ℝ)) w φ t := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hrt | hrt
    · rw [hrt]
    obtain ⟨D, hD, hDb⟩ := h14 ν _ tr t s g φ f w u hν0 hc1 ht hts hB hφ hf hf0 hw r hr
    have hprod : ∀ R : ℝ, 0 < R →
        IntervalIntegrable (fun ρ => ladRate tr w u φ R ρ) volume t r ∧
          ladCutPair (ν ^ (-2 : ℝ)) R w φ r - ladCutPair (ν ^ (-2 : ℝ)) R w φ t =
            ∫ ρ in t..r, ladRate tr w u φ R ρ :=
      fun R hR => h4 ν _ m tr t s f w u φ hν0 hc0 ht hts hw hLip hφ.jointSmooth hφ.periodic
        R hR r hr
    have hI : Ι t r = Ioc t r := Set.uIoc_of_le hr.1
    have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in t..r, ladRate tr w u φ R ρ) atTop (𝓝 0) := by
      have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := atTop) (f := fun _ => (0 : ℂ))
        (F := fun R ρ => ladRate tr w u φ R ρ) D ?_ ?_ hD ?_
      · simpa using key
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact (intervalIntegrable_iff.mp (hprod R hR).1).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        filter_upwards [lad_ae_ne r] with ρ hρr hρI
        rw [hI] at hρI
        exact hDb R hR ρ ⟨hρI.1, lt_of_le_of_ne hρI.2 hρr⟩
      · filter_upwards [lad_ae_ne r] with ρ hρr hρI
        rw [hI] at hρI
        exact hP ν _ tr t s g φ f w u hν0 hc1 ht hts hB hφ hf hf0 hw ρ
          ⟨hρI.1, lt_of_lt_of_le (lt_of_le_of_ne hρI.2 hρr) hr.2.le⟩
    have hcutr : Tendsto (fun R : ℝ => ladCutPair (ν ^ (-2 : ℝ)) R w φ r) atTop
        (𝓝 (ladPair (ν ^ (-2 : ℝ)) w φ r)) :=
      h2 _ m (w r) (φ r) (hw.memX r hr.1) (hφ.memX r ⟨hr.1, hr.2.le⟩)
    have hcutt : Tendsto (fun R : ℝ => ladCutPair (ν ^ (-2 : ℝ)) R w φ t) atTop
        (𝓝 (ladPair (ν ^ (-2 : ℝ)) w φ t)) :=
      h2 _ m (w t) (φ t) (hw.memX t le_rfl) (hφ.memX t ⟨le_rfl, hts.le⟩)
    have hdiff' : Tendsto (fun R : ℝ =>
        ladCutPair (ν ^ (-2 : ℝ)) R w φ r - ladCutPair (ν ^ (-2 : ℝ)) R w φ t) atTop (𝓝 0) := by
      refine hlimInt.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact ((hprod R hR).2).symm
    exact sub_eq_zero.mp (tendsto_nhds_unique (hcutr.sub hcutt) hdiff')
  -- continuity up to `s`
  have hcont := h1 ν _ m tr t s g φ f w u hts hφ hw
  have hEq : EqOn (ladPair (ν ^ (-2 : ℝ)) w φ) (fun _ => ladPair (ν ^ (-2 : ℝ)) w φ t)
      (Icc t s) := by
    have h0 : EqOn (ladPair (ν ^ (-2 : ℝ)) w φ) (fun _ => ladPair (ν ^ (-2 : ℝ)) w φ t)
        (Ico t s) := fun r hr => hconst r hr
    refine h0.of_subset_closure hcont continuousOn_const Ico_subset_Icc_self ?_
    rw [closure_Ico hts.ne]
  have hs : ladPair (ν ^ (-2 : ℝ)) w φ s = ladPair (ν ^ (-2 : ℝ)) w φ t := hEq ⟨hts.le, le_rfl⟩
  have e1 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * g x = ladPair (ν ^ (-2 : ℝ)) w φ s := by
    unfold ladPair
    refine integral_congr_ae ?_
    filter_upwards [hφ.terminal] with x hx
    rw [hx]
  have e2 : ladPair (ν ^ (-2 : ℝ)) w φ t = ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ t x := by
    unfold ladPair
    refine integral_congr_ae ?_
    filter_upwards [hw.initial] with x hx
    rw [hx]
  rw [e1, hs, e2]

end UnforcedLeray.Short.IIIa
