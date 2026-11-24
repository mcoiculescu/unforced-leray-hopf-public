import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Part III-a, `PartIII-a:T21/2/7/1`: construction of the weak reverse-time adjoint (statements)

Source of record: `the November 2 reference manuscript` (SP), line 3060 (the
reverse-time adjoint), lines 2819-2836 (forward existence: Volterra iteration around the actual
train, heat semigroup and its divergence response as free part, bounded perturbation), lines
3052-3058 (the adjoint localized interaction `K_c^T(φ∇E)`), lines 3044-3050 (weights).

## The equation in reverse time

With `τ = s - r` and `Φ(τ) = φ(s - τ)` the adjoint `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)`
(`IsAdjointWeak`, `Sub/PartIIIa_T21_2_7.lean`) is the forward equation
`∂_τΦ = νΔΦ - ∇·F + h`, `F = -v(s-τ)Φ` (`div v = 0`), `h = -K_c^T(Φ∇E(s-τ))`,
on `X_{-m,c} = L²(C_c, ⟨x⟩^{-2m}dx)` (complex, `AdjX`).  As in the forward construction
(`Sub/T21_3_Strip.lean`) the free part is the heat semigroup `S₀` of diffusivity `ν` and its
source response `S(τ)(F, h) = e^{ντΔ}(-∇·F + h)` (`AdjHeatSupplier` on `AdjY = X_{-m,c}² × X_{-m,c}`,
weak identities `AdjHeatWeak`), the bounded perturbation is `B(τ)Φ = (-vΦ, -K_c^T(Φ∇E))`
(`AdjCoeffExists`, with the transport part `AdjTransportCoeff` and the adjoint localized
interaction `AdjLocalizedCoeff`), and the audited Volterra construction
(`Infra/VolterraEvolution`: Picard series on unit strips, strong continuity, evolution law) gives
`Φ(τ) = D.evolution τ 0 g`.  `VolterraWeakForm` is the abstract mild-to-weak step.

## The train class

The coefficient bounds need `sup|v| < ∞` and `⟨x⟩^{m+2}|∇E|` bounded on the cell on `[0, s]`
(`LadTrainBdd`, `Sub/T21_2_3/LinAdjDualitySub.lean`; SP 270-288, 2866-2873).  `B0140.IsTrain`
gives no such bound (`Short/PartI/TrainClass.lean`), so the construction is proved for trains
with these bounds (`AdjointWeakExistsBdd`) and, with `LadTrainBddAll`, for the BUC class at small
`ν` (`AdjointWeakExistsBUC`), the form `LinAdjDualityBUC` already uses (a weakening of `AdjointWeakExists m`: drop the class
hypothesis).

## Contents

* objects: `AdjX`, `AdjY`, `perRep` (the `c`-periodic representative of a cell function),
  `AdjHeatSupplier`, `AdjHeatWeak`;
* the leaves: `AdjWeightGrad` (spec (a)), `AdjHeatExists`, `AdjTransportCoeff`,
  `AdjLocalizedCoeff` (spec (b)), `AdjCoeffExists`, `VolterraWeakForm` (spec (c)), `AdjPairing`,
  `AdjTerminalMem` (pieces of spec (d));
* the targets `AdjointWeakExistsBdd`, `AdjointWeakExistsBUC`.
The assemblies are in `AdjWeakOf.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Infra.VolterraEvolution

/-! ## Spaces and the periodic representative -/

/-- `X_{-m,c} = L²(C_c, ⟨x⟩^{-2m} dx)` (complex), the state space of the adjoint (SP 2819-2826,
3060). -/
abbrev AdjX (c m : ℝ) : Type := Lp ℂ 2 (B0579.cellMeasure c (-m))

/-- The source space of the adjoint Volterra problem: a flux `F ∈ X_{-m,c}²` (entering as
`-∇·F`) and a zeroth-order source `h ∈ X_{-m,c}`. -/
abbrev AdjY (c m : ℝ) : Type := (Fin 2 → AdjX c m) × AdjX c m

/-- The `c`-periodic representative of a function on the cell `C_c = [-c/2, c/2) × ℝ`:
`perRep c f (q, η) = f(q mod c, η)` with `q mod c ∈ [-c/2, c/2)`. -/
def perRep (c : ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  if hc : 0 < c then f (toIcoMod hc (-(c / 2)) x.1, x.2) else f x

theorem perRep_periodic {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perRep c f (x.1 + c, x.2) = perRep c f x := by
  simp only [perRep, dif_pos hc, toIcoMod_add_right]

theorem perRep_of_mem_cell {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) {x : ℝ × ℝ}
    (hx : x ∈ B0579.cell c) : perRep c f x = f x := by
  have h1 : x.1 ∈ Ico (-(c / 2)) (-(c / 2) + c) := by
    have := hx.1
    rw [show -(c / 2) + c = c / 2 by ring]
    exact this
  simp only [perRep, dif_pos hc, (toIcoMod_eq_self hc).2 h1]

theorem perRep_eqOn_cell {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) :
    EqOn (perRep c f) f (B0579.cell c) := fun _ hx => perRep_of_mem_cell hc f hx

theorem perRep_ae_cell {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) :
    perRep c f =ᵐ[volume.restrict (B0579.cell c)] f :=
  ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun _ hx => perRep_of_mem_cell hc f hx

theorem perRep_ae_cellMeasure {c : ℝ} (hc : 0 < c) (m : ℝ) (f : ℝ × ℝ → ℂ) :
    perRep c f =ᵐ[B0579.cellMeasure c m] f :=
  (B0579.cellMeasure_ac c m).ae_le (perRep_ae_cell hc f)

/-! ## The free part: heat semigroup and source response on `X_{-m,c}` -/

/-- The free part of the adjoint Volterra problem on `X_{-m,c}` (SP 2819-2836, as
`WeightedHeatStripSupplier` of the forward construction): the heat family `S₀(τ)` (`τ ∈ [0,1]`)
and the source response `S(τ) : AdjY → AdjX`, with the bounds and semigroup laws of
`Infra.VolterraEvolution.VolterraData`. It is pinned by the weak identities `AdjHeatWeak`. -/
structure AdjHeatSupplier (c m : ℝ) where
  S₀ : ℝ → AdjX c m →L[ℂ] AdjX c m
  S : ℝ → AdjY c m →L[ℂ] AdjX c m
  M₀ : ℝ
  C₀ : ℝ
  S₀_zero : S₀ 0 = ContinuousLinearMap.id ℂ (AdjX c m)
  norm_S₀_le : ∀ τ, 0 ≤ τ → τ ≤ 1 → ‖S₀ τ‖ ≤ M₀
  norm_S_le : ∀ τ, 0 < τ → τ ≤ 1 → ‖S τ‖ ≤ C₀ * τ ^ (-(1 / 2 : ℝ))
  continuousOn_S₀ : ∀ x, ContinuousOn (fun τ => S₀ τ x) (Icc 0 1)
  continuousOn_S : ∀ y, ContinuousOn (fun τ => S τ y) (Ioc 0 1)
  S₀_comp_S₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 → (S₀ a).comp (S₀ b) = S₀ (a + b)
  S₀_comp_S : ∀ a b : ℝ, 0 ≤ a → 0 < b → a + b ≤ 1 → (S₀ a).comp (S b) = S (a + b)

/-- **Weak identities of the free part with diffusivity `ν`** (SP 2819-2836): (a) `τ ↦ S₀(τ)w`
is the weak solution of `∂_τΦ = νΔΦ` from `w`; (b) for a continuous source path `F` on
`[a, b] ⊆ [a, a+1]`, the Duhamel term `Y(τ) = ∫_a^τ S(τ-r) F(r) dr` is the weak solution of
`∂_τY = νΔY - ∇·F₁ + F₂` from `0`:
`∫ Y(τ)ψ = ∫_a^τ (ν∫ Y(r)Δψ + ∫ F₁(r)·∇ψ + ∫ F₂(r)ψ) dr`, tested against every cylinder test. -/
def AdjHeatWeak (ν c m : ℝ) (H : AdjHeatSupplier c m) : Prop :=
  (∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ → ∀ τ ∈ Icc (0 : ℝ) 1,
    ∫ x in B0579.cell c, (H.S₀ τ w) x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, w x * (ψ x : ℂ)) +
        ∫ r in (0 : ℝ)..τ, (ν : ℂ) * ∫ x in B0579.cell c, (H.S₀ r w) x * (lapP ψ x : ℂ)) ∧
  (∀ (F : ℝ → AdjY c m) (a b : ℝ), a ≤ b → b ≤ a + 1 → ContinuousOn F (Icc a b) →
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc a b,
      ∫ x in B0579.cell c, (∫ r in a..τ, H.S (τ - r) (F r)) x * (ψ x : ℂ) =
        (∫ r in a..τ, (ν : ℂ) * ∫ x in B0579.cell c,
            (∫ σ in a..r, H.S (r - σ) (F σ)) x * (lapP ψ x : ℂ)) +
          ∫ r in a..τ, ((∫ x in B0579.cell c, (F r).1 0 x * (B0579.pd 0 ψ x : ℂ)) +
            (∫ x in B0579.cell c, (F r).1 1 x * (B0579.pd 1 ψ x : ℂ)) +
            ∫ x in B0579.cell c, (F r).2 x * (ψ x : ℂ)))

/-! ## The leaves -/

/-- **(a) The weight error** (SP 3044-3050; the diffusion-weight errors of the energy method):
`|∂_k ⟨x⟩^{-2m}| ≤ 2|m| ⟨x⟩^{-2m}` on the plane (`⟨x⟩^{-2m} = jb^{-m}`, the density of
`cellMeasure c (-m)`), uniformly in the cell length. Input of `AdjHeatExists` (boundedness of the
heat semigroup on `X_{-m,c}`). -/
def AdjWeightGrad : Prop :=
  ∀ (m : ℝ) (x : ℝ × ℝ) (k : Fin 2),
    |B0579.pd k (fun y => B0579.jb y ^ (-m)) x| ≤ 2 * |m| * B0579.jb x ^ (-m)

/-- **The free part exists on `X_{-m,c}`** (SP 2819-2836, at fixed `ν > 0`, `c > 0`): the
periodic heat semigroup of diffusivity `ν` (Gaussian convolution of the periodic lift, restricted
to the cell) and its source response `e^{ντΔ}(-∇·F + h)` form an `AdjHeatSupplier` with the weak
identities `AdjHeatWeak ν`. (On the cell `⟨x⟩ ≍_c ⟨η⟩`, so the weighted bounds follow from
`AdjWeightGrad` and Gaussian moments.) -/
def AdjHeatExists (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∃ H : AdjHeatSupplier c m, AdjHeatWeak ν c m H

/-- **(b1) The transport coefficient** (SP 2819-2836: `v` bounded): for a train with the bounds
`LadTrainBdd tr m T C` on `[0, T]`, multiplication by `-v_j(r)` is a bounded operator family on
`X_{-m,c}`, bounded by `C` and strongly continuous on `[0, T]`. -/
def AdjTransportCoeff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ, 0 ≤ T →
    LadTrainBdd tr m T C →
    ∃ Mv : ℝ → Fin 2 → AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjX (ν ^ (-2 : ℝ)) m,
      (∀ r ∈ Icc 0 T, ∀ j, ‖Mv r j‖ ≤ C) ∧
      (∀ j w, ContinuousOn (fun r => Mv r j w) (Icc 0 T)) ∧
      ∀ r ∈ Icc 0 T, ∀ j w, ⇑(Mv r j w) =ᵐ[B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)]
        fun x => -((tr.v r x j : ℝ) : ℂ) * w x

/-- **(b) The adjoint localized interaction at fixed `ν ≤ 1`** (SP 3052-3058 in physical
variables, as `AdjointLocalizedBound`; `c = ν⁻² ≥ 1` is the range of `KernelAdjointBound`,
`Sub/PartIIIa_T21_2_1.lean`, applied to `F = w∇E`): for a train with the bounds
`LadTrainBdd tr m T C`, every
`w ∈ X_{-m,c}` has `K_c^T(w∇E(r)) ∈ X_{-m,c}`, characterised by
`∫ K_c^T(w∇E) ψ = ∫ w (K_cψ)·∇E` for every cylinder test `ψ` (any circulation) with kernel
velocity `K_cψ`; the family is bounded and strongly continuous on `[0, T]`. -/
def AdjLocalizedCoeff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ, 0 ≤ T →
    LadTrainBdd tr m T C →
    ∃ (K : ℝ → AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjX (ν ^ (-2 : ℝ)) m) (β : ℝ),
      (∀ r ∈ Icc 0 T, ‖K r‖ ≤ β) ∧
      (∀ w, ContinuousOn (fun r => K r w) (Icc 0 T)) ∧
      ∀ r ∈ Icc 0 T, ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
          IntegrableOn (fun x => w x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
            (B0579.cell (ν ^ (-2 : ℝ))) ∧
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (K r w) x * (ψ x : ℂ) =
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x *
              ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)

/-- **The coefficient of the adjoint Volterra problem** (SP 2819-2836, 3052-3060): for `ν ≤ 1`
and a train
with the bounds `LadTrainBdd tr m T C`, a bounded, strongly continuous family
`A(r) : X_{-m,c} → AdjY` (in fact `A(r)w = (-v(r)w, -K_c^T(w∇E(r)))`, from `AdjTransportCoeff`
and `AdjLocalizedCoeff`) such that the tested adjoint right-hand side splits as
`∫ adjIntegrand(w) = ν ∫ w Δψ + ∫ A₁(r)w·∇ψ + ∫ A₂(r)w ψ` (integrable on the cell). -/
def AdjCoeffExists (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ T C : ℝ, 0 ≤ T →
    LadTrainBdd tr m T C →
    ∃ (A : ℝ → AdjX (ν ^ (-2 : ℝ)) m →L[ℂ] AdjY (ν ^ (-2 : ℝ)) m) (β : ℝ),
      (∀ r ∈ Icc 0 T, ‖A r‖ ≤ β) ∧
      (∀ w, ContinuousOn (fun r => A r w) (Icc 0 T)) ∧
      ∀ r ∈ Icc 0 T, ∀ (w : AdjX (ν ^ (-2 : ℝ)) m) (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
          IntegrableOn (adjIntegrand tr (⇑w) r ψ uψ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (⇑w) r ψ uψ x =
            (ν : ℂ) * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x * (lapP ψ x : ℂ)) +
              ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), (A r w).1 0 x * (B0579.pd 0 ψ x : ℂ)) +
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ)) +
                ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (A r w).2 x * (ψ x : ℂ))

/-- **(c) Mild solutions of the Volterra problem are weak** (abstract; the Duhamel step of
SP 2819-2836): for compatible Volterra data with `S₀(0) = 1` (`Infra.VolterraEvolution`), and
continuous functionals `ℓ, ℓ'` on `X`, `ℓB` on `Y` such that `ℓ(S₀(τ)x) = ℓx + ∫_0^τ ℓ'(S₀(r)x)`
on `[0,1]` and the Duhamel term of every continuous source path `F` on `[a, b] ⊆ [a, a+1]`
satisfies `ℓ(∫_a^τ S(τ-r)F(r)) = ∫_a^τ ℓ'(∫_a^r S(r-σ)F(σ)) + ∫_a^τ ℓB(F(r))`, the evolution
`u(τ) = D.evolution τ 0 x` satisfies `ℓ(u(τ)) = ℓx + ∫_0^τ (ℓ'(u(r)) + ℓB(B(r)u(r)))` for all
`τ ≥ 0` (strip by strip with the evolution law, then additivity of the integral). -/
def VolterraWeakForm : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X]
    [SMulCommClass ℝ ℂ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (D : VolterraData ℂ X Y), D.Compatible → D.S₀ 0 = ContinuousLinearMap.id ℂ X →
    ∀ (ℓ ℓ' : X →L[ℂ] ℂ) (ℓB : Y →L[ℂ] ℂ),
      (∀ x : X, ∀ τ ∈ Icc (0 : ℝ) 1, ℓ (D.S₀ τ x) = ℓ x + ∫ r in (0 : ℝ)..τ, ℓ' (D.S₀ r x)) →
      (∀ (F : ℝ → Y) (a b : ℝ), a ≤ b → b ≤ a + 1 → ContinuousOn F (Icc a b) →
        ∀ τ ∈ Icc a b,
          ℓ (∫ r in a..τ, D.S (τ - r) (F r)) =
            (∫ r in a..τ, ℓ' (∫ σ in a..r, D.S (r - σ) (F σ))) + ∫ r in a..τ, ℓB (F r)) →
      ∀ (x : X) (τ : ℝ), 0 ≤ τ →
        ℓ (D.evolution τ 0 x) =
          ℓ x + ∫ r in (0 : ℝ)..τ, (ℓ' (D.evolution r 0 x) + ℓB (D.B r (D.evolution r 0 x)))

/-- **The test pairing on `X_{-m,c}`** (SP 2823-2826, the unweighted pairing; weighted
Cauchy-Schwarz): for a cylinder test `χ`, `w ↦ ∫_{C_c} w χ` is integrable for every
`w ∈ X_{-m,c}` and is a continuous linear functional. -/
def AdjPairing : Prop :=
  ∀ (c m : ℝ), 0 < c → ∀ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ →
    (∀ w : AdjX c m, IntegrableOn (fun x => w x * (χ x : ℂ)) (B0579.cell c)) ∧
    ∃ L : AdjX c m →L[ℂ] ℂ, ∀ w : AdjX c m, L w = ∫ x in B0579.cell c, w x * (χ x : ℂ)

/-- **The physical terminal datum lies in `X_{-m,c}`** (SP 3036-3037, 3060: `g = a G(·/√a)`,
`a = a_s ≥ 1`; change of variables `x = √a y`, Jacobian `a`, and `⟨√a y⟩ ≥ ⟨y⟩`, `m ≥ 0`). -/
def AdjTerminalMem (m : ℝ) : Prop :=
  ∀ c a : ℝ, 0 < c → 1 ≤ a → ∀ G : ℝ × ℝ → ℂ,
    MemLp G 2 (B0579.cellMeasure (cellLen c a) (-m)) →
    MemLp (physAdj a G) 2 (B0579.cellMeasure c (-m))

/-! ## The targets -/

/-- `AdjointWeakExists m` for `ν ≤ 1` and trains with the time-local bounds `LadTrainBdd` on
every `[0, S]` (SP 3060, 2819-2836). -/
def AdjointWeakExistsBdd (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∃ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ

/-- **The weak reverse-time adjoint for the BUC train** (SP 3060; the train of SP 270-288):
`AdjointWeakExists m` for the trains of the class `PartI.IsBUCTrain` and `ν ≤ ν₀` (the form of
`LinAdjDualityBUC`). -/
def AdjointWeakExistsBUC (m : ℝ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∃ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ

/-- The BUC version from the bounded-train version and the train bounds `LadTrainBddAll`
(threshold `min ν₀ 1`). -/
theorem adjointWeakExistsBUC_of_bdd (m : ℝ) (hB : LadTrainBddAll m)
    (h : AdjointWeakExistsBdd m) : AdjointWeakExistsBUC m := by
  obtain ⟨ν₀, hν₀, hB⟩ := hB
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, fun ν hν tr htr => ?_⟩
  exact h ν hν.1 (hν.2.trans (min_le_right _ _)) tr
    (hB ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ tr htr)

end UnforcedLeray.Short.IIIa
