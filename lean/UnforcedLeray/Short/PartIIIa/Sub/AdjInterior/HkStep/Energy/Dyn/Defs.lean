import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/1`: the dynamics of the mollified adjoint (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(energies `E_j` of the reverse-time adjoint, classical quantities of the reverse time; the weak
solution is regularized in `x`), 3052-3058 (adjoint localized interaction `K_c^T(φ∇E)`, of order `-1`).

## Route to `MollRateDeriv m` (`Dyn/Assembly.lean`, `mollRateDeriv_of`)

For `F(r) = ρ_n ⋆ φ(r)`, `R(r) = mollRate ν v(r) n φ(r) χ(r)`:

1. `F` and `R` are in `C((a, b); H^∞_{-m,c})` (`AdjHkAll`): `MollConvJet` (convolution with a smooth
   kernel of a family `f(r)` continuous in `X_{-m,c}`), `MollRateJetAbs` (`R` is a linear combination of
   such convolutions of `φ`, `v_l φ`, `χ`), the continuity of the inputs `φ` (`IsAdjointWeak.strongCont`),
   `v_l φ` (`VelMulMemX`, `VelMulCont`), `χ` (`ChiCont`, `AdjLocalizedCoeff`, needs `8 < m`);
2. tested derivative `d/dr ∫ F(r) ψ = ∫ R(r) ψ` for every cylinder test `ψ` (by duality: `∫ (ρ_n ⋆ f) ψ =
   ∫ f (ρ̌_n ⋆ ψ)`, `MollDual`; then `AdjTestedDeriv` for the test `ρ̌_n ⋆ ψ`: `MollTestedAdj`; the
   identity `∫ R ψ = -∫ adjIntegrand(ρ̌_n ⋆ ψ)`: `MollRateTested`, from `AdjIntegrandSplit`,
   `XMulTestInt`, `CellIBP`, `MollDual`, the pairing identity of `χ`);
3. `XDerivOfTested` gives `HasXDerivOn F R` on `(a, b)`, `XDerivUpgrade` gives it word by word;
4. `EnergyDerivAbs` (Hilbert space calculus) gives the derivative of the energy, `EnergyContAbs` its
   continuity on `[a, b]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The adjoint mollification of a real test: `(ρ̌_n ⋆ h)(x) = ∫ ρ_n(y) h(x + y) dy`
(`ρ_n` is even, so this is `ρ_n ⋆ h`; written with `+ y` so that
`∫_{C_c} (ρ_n ⋆ f) h = ∫_{C_c} f (ρ̌_n ⋆ h)` is a change of variables). -/
def mollR (n : ℕ) (h : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := ∫ y, molKer n y * h (x + y)

/-- The age derivative of the mollified adjoint in terms of the pieces `V l = v_l φ`:
`mollRate ν v n φ χ = mollRateV ν n φ (fun l y => v_l(y) φ(y)) χ` (`rfl`). -/
def mollRateV (ν : ℝ) (n : ℕ) (φ : ℝ × ℝ → ℂ) (V : Fin 2 → ℝ × ℝ → ℂ) (χ : ℝ × ℝ → ℂ) :
    ℝ × ℝ → ℂ := fun x =>
  -((ν : ℂ) * (adjSpatial [0, 0] (cellMoll n φ) x + adjSpatial [1, 1] (cellMoll n φ) x) +
    ∑ l : Fin 2, cellConv (B0579.pd l (molKer n)) (V l) x - cellMoll n χ x)

theorem mollRate_eq (ν : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (φ χ : ℝ × ℝ → ℂ) :
    mollRate ν v n φ χ = mollRateV ν n φ (fun l y => ((v y l : ℝ) : ℂ) * φ y) χ := rfl

/-- A family `f(r)` of periodic fields of `X_{-m,c}`, continuous in `X_{-m,c}` on `(a, b)`. -/
def XFam (c m a b : ℝ) (f : ℝ → ℝ × ℝ → ℂ) : Prop :=
  (∀ r ∈ Ioo a b, (∀ x : ℝ × ℝ, f r (x.1 + c, x.2) = f r x) ∧
      MemLp (f r) 2 (B0579.cellMeasure c (-m))) ∧
    ∀ r ∈ Ioo a b, Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[Ioo a b] r) (𝓝 0)

/-- `χ(r)` represents `K_c^T(φ(r)∇E(r))` through the pairing identity of `AdjLocalizedCoeff`, for
`r ∈ [a, b]` (the hypothesis of `MollRateDeriv` on `χ`). -/
def ChiRep (m ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (φ χ : ℝ → ℝ × ℝ → ℂ)
    (a b : ℝ) : Prop :=
  ∀ r ∈ Icc a b, (∀ x : ℝ × ℝ, χ r (x.1 + ν ^ (-2 : ℝ), x.2) = χ r x) ∧
    MemLp (χ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
    ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
      IntegrableOn (fun x => φ r x *
          ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
            uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) ∧
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), χ r x * (ψ x : ℂ) =
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)

/-- **The context of `MollRateDeriv`**: every hypothesis of `MollRateDeriv m` (for `ν`, the train
`tr`, the weak adjoint `φ` on `[t, s]` with terminal datum `g`, `[a, b] ⊆ [t, s)` and `χ`). -/
def MollCtx (m ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  0 < ν ∧ ν ≤ 1 ∧ (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) ∧ 0 ≤ t ∧ t < s ∧
    IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ ∧ AdjTestedDeriv tr t s φ ∧
    t ≤ a ∧ a < b ∧ b < s ∧ ChiRep m ν tr φ χ a b

/-! ## Abstract leaves (calculus of the mollification on the periodic `X_{-m,c}`) -/

/-- **(A0) The mollifier kernel** `ρ_n = molKer n` is smooth, compactly supported, and vanishes
outside the closed unit (sup-norm) ball (`ContDiffBump.contDiff_normed`, `hasCompactSupport_normed`,
`support_normed_eq`: the support is the ball of radius `1/(n+1) ≤ 1`). -/
def MollKerProps : Prop :=
  ∀ n : ℕ, ContDiff ℝ ∞ (molKer n) ∧ HasCompactSupport (molKer n) ∧
    ∀ y : ℝ × ℝ, 1 < ‖y‖ → molKer n y = 0

/-- **(A1) A smooth periodic field with all partials in `X_{-m,c}` is a jet at every level**:
`D w = adjSpatial w F` is a level-`k` jet of `F` (`IsCellJet`: `adjSpatial (j :: w) F = pdCx j
(adjSpatial w F)` is smooth and periodic, and the classical derivative of a `C¹` periodic field is its
weak derivative on the cylinder, `HasWeakCellDerivC`: integration by parts on the cell with the seam
terms cancelling by periodicity, `WeakDerivC1` in `Sub/PartIIIa_T21_2_2_3_6/Unique.lean`). -/
def SmoothCellJet : Prop :=
  ∀ (c m : ℝ) (F : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ F →
    (∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) →
    (∀ w : List (Fin 2), MemLp (adjSpatial w F) 2 (B0579.cellMeasure c (-m))) →
    ∀ k : ℕ, IsCellJet c m k F (fun w => adjSpatial w F)

/-- **(A2) Convolution with a smooth kernel of an `X_{-m,c}`-continuous family is in
`C((a, b); H^∞_{-m,c})`** (SP 3060-3071: the regularization in `x`): for `K` smooth, compactly
supported in the closed unit ball and a family `f(r)` periodic in `X_{-m,c}`, continuous in
`X_{-m,c}` on `(a, b)`, the fields `cellConv K (f r)` have the jet `D r w = adjSpatial w (cellConv K
(f r))` (`= cellConv (pdWordR w K) (f r)`, `CellConvDeriv`), at every level (`SmoothCellJet` with
`CellConvDeriv`, `CellConvBound` for the `X`-bounds) and every `r ↦ D r w` is continuous into
`X_{-m,c}` on `(a, b)` (`cellConv K₁ (f r') - cellConv K₁ (f r) = cellConv K₁ (f r' - f r)`, linear in `f`,
`CellConvBound` with `K₁ = pdWordR w K`, smooth, supported in the unit ball). -/
def MollConvJet : Prop :=
  ∀ (c m : ℝ) (K : ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (a b : ℝ), 0 < c → ContDiff ℝ ∞ K →
    HasCompactSupport K → (∀ y : ℝ × ℝ, 1 < ‖y‖ → K y = 0) → XFam c m a b f →
    AdjHkAll c m (Ioo a b) (fun r => cellConv K (f r)) (fun r w => adjSpatial w (cellConv K (f r)))

/-- **(A3) The age derivative `R(r) = mollRateV ν n φ(r) (V l r) χ(r)` is in
`C((a, b); H^∞_{-m,c})`** (SP 3060): `R = -(ν(∂₀₀ + ∂₁₁)(ρ_n ⋆ φ) + Σ_l (∂_lρ_n) ⋆ V_l - ρ_n ⋆ χ)` is
a linear combination of the convolutions `cellConv (pdWordR w' (molKer n)) (·)` of `φ`, `V_l`, `χ`
(`adjSpatial w (cellConv K f) = cellConv (pdWordR w K) f`, `CellConvDeriv`), each in `C((a, b);
H^∞)` by `MollConvJet`; combine with `AdjHkAllLinear` (`Sub/AdjInterior/TimeJets/Defs.lean`) or
directly (`adjSpatial w` is linear on smooth fields). -/
def MollRateJetAbs : Prop :=
  ∀ (c m ν : ℝ) (n : ℕ) (a b : ℝ) (φ χ : ℝ → ℝ × ℝ → ℂ) (V : Fin 2 → ℝ → ℝ × ℝ → ℂ), 0 < c →
    XFam c m a b φ → (∀ l, XFam c m a b (V l)) → XFam c m a b χ →
    AdjHkAll c m (Ioo a b) (fun r => mollRateV ν n (φ r) (fun l => V l r) (χ r))
      (fun r w => adjSpatial w (mollRateV ν n (φ r) (fun l => V l r) (χ r)))

/-- **(A4) Duality for the mollification** (change of variables, Fubini; `ρ_n` has compact support):
for a cylinder test `h`, `ρ̌_n ⋆ h = mollR n h` is a cylinder test (smooth, `c`-periodic, vanishing for
`|x₂|` large), `∂_l` commutes with `mollR n` (`HasCompactSupport.hasFDerivAt_convolution_left` or
differentiation under the integral), and for every periodic `f ∈ X_{-m,c}`
`∫_{C_c} (ρ_n ⋆ f) h = ∫_{C_c} f (ρ̌_n ⋆ h)` (both integrable). Proof: Fubini on `C_c × B_{1/(n+1)}`
(`f` is locally integrable on the plane, `CellPeriodicLocInt`; `h` bounded and supported in a band),
then `x ↦ x + y` maps the cell to a translate, and periodicity of `f (·) (ρ̌ ⋆ h)(·)` makes the
cell integral translation invariant (`Cyl.isAddFundamentalDomain_cell`); or via `CellPeriodize`
(`perKer`). -/
def MollDual : Prop :=
  ∀ (c m : ℝ) (n : ℕ), 0 < c → ∀ h : ℝ × ℝ → ℝ, B0579.IsCylTest c h →
    B0579.IsCylTest c (mollR n h) ∧ (∀ l : Fin 2, B0579.pd l (mollR n h) = mollR n (B0579.pd l h)) ∧
    ∀ f : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
      MemLp f 2 (B0579.cellMeasure c (-m)) →
      IntegrableOn (fun x => cellMoll n f x * (h x : ℂ)) (B0579.cell c) ∧
        ∫ x in B0579.cell c, cellMoll n f x * (h x : ℂ) =
          ∫ x in B0579.cell c, f x * (mollR n h x : ℂ)

/-- **(A5) Integration by parts on the cell** (classical, seam terms cancel by periodicity): for a
smooth `c`-periodic complex `g` and a cylinder test `h`,
`∫_{C_c} g ∂_l h = -∫_{C_c} (∂_l g) h` (`pdCx`; cf. `IbpPdCxWeak`, `WeakDerivC1`). -/
def CellIBP : Prop :=
  ∀ (c : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℝ), 0 < c → ContDiff ℝ ∞ g →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → B0579.IsCylTest c h → ∀ l : Fin 2,
      ∫ x in B0579.cell c, g x * (B0579.pd l h x : ℂ) =
        -∫ x in B0579.cell c, pdCx l g x * (h x : ℂ)

/-- **(A6) A field of `X_{-m,c}` is integrable against a cylinder test on the cell** (weighted
Cauchy-Schwarz, `WeightedCS`; the test is bounded and vanishes outside a band; cf. `integrable_pair` in
`Sub/PartIII-a_T21_2_7_2_1_1_3.lean`, `BandMulTest` in `Sub/PartIIIa_T21_2_2_3_6/Unique.lean`). -/
def XMulTestInt : Prop :=
  ∀ (c m : ℝ) (f : ℝ × ℝ → ℂ) (g : ℝ × ℝ → ℝ), 0 < c →
    MemLp f 2 (B0579.cellMeasure c (-m)) → B0579.IsCylTest c g →
    IntegrableOn (fun x => f x * (g x : ℂ)) (B0579.cell c)

/-- **(A7) Energy derivative along an `X`-differentiable path** (Hilbert space calculus): if every
`r ↦ ∂^w F(r)` has the `X_{-m,c}`-derivative `∂^w F'(r)` on `(a, b)` (all slices in `X_{-m,c}`), then
`N_j(r) = Σ_{|w| ≤ j} ‖∂^w F(r)‖²_X` has the derivative `energyRate c m j (F r) (F' r)
= Σ_{|w| ≤ j} 2 Re ⟨∂^w F, ∂^w F'⟩` on `(a, b)`.  Per word: `xNorm` is the norm of the `Lp ℂ 2`
element (`MemLp.toLp`, `Lp.norm_def`), `HasXDerivOn` is a `HasDerivAt` of the `Lp`-valued path
(`hasDerivAt_iff_tendsto_slope`), `HasDerivAt.norm_sq` for the (real) inner product space `Lp ℂ 2` gives
`2 re ⟪F, F'⟫`, and `re ⟪F, F'⟫ = ipX` (`L2.inner_def`, conjugate on the second slot:
`ipX c m f g = re ∫ f ḡ dcellMeasure`). Sum over `wordsLE j` (`HasDerivAt.sum`). -/
def EnergyDerivAbs : Prop :=
  ∀ (c m : ℝ) (j : ℕ) (F F' : ℝ → ℝ × ℝ → ℂ) (a b : ℝ), 0 < c →
    (∀ r ∈ Ioo a b, ∀ w : List (Fin 2), MemLp (adjSpatial w (F r)) 2 (B0579.cellMeasure c (-m)) ∧
      MemLp (adjSpatial w (F' r)) 2 (B0579.cellMeasure c (-m))) →
    (∀ w : List (Fin 2), HasXDerivOn c m (Ioo a b) (fun r => adjSpatial w (F r))
      (fun r => adjSpatial w (F' r))) →
    ∀ r ∈ Ioo a b, HasDerivAt (fun r' => cellEnergy c m j (F r'))
      (energyRate c m j (F r) (F' r)) r

/-- **(A8) Continuity of the mollified energies** (SP 3060-3071; `CellConvBound`, `CellConvDeriv`): if `φ(r)`
is periodic in `X_{-m,c}` and `X_{-m,c}`-continuous on `[a, b]` (within `[a, b]`), then
`r ↦ cellEnergy c m j (ρ_n ⋆ φ(r))` is continuous on `[a, b]`: `adjSpatial w (ρ_n ⋆ φ(r')) -
adjSpatial w (ρ_n ⋆ φ(r)) = cellConv (pdWordR w (molKer n)) (φ r' - φ r)`, bounded in `xNorm` by
`C (∫|∂^wρ_n|) xNorm (φ r' - φ r) → 0`; and `xNorm`'s `toReal` squared is continuous in the norm. -/
def EnergyContAbs : Prop :=
  ∀ (c m : ℝ) (j n : ℕ) (a b : ℝ) (φ : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ r ∈ Icc a b, (∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x) ∧
      MemLp (φ r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Icc a b, Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc a b] r) (𝓝 0)) →
    ContinuousOn (fun r => cellEnergy c m j (cellMoll n (φ r))) (Icc a b)

/-! ## Leaves in the context of `MollRateDeriv` (the train, the weak adjoint, `χ`) -/

/-- **(C1) `v_l(r) φ(r)` is a periodic field of `X_{-m,c}`** (`IsTrain.periodic_v`; the velocity is
bounded on the cell by `LadTrainBdd`, hence everywhere by periodicity; `v(r)` is continuous
(`IsTrain.smooth_v`), so `v_l φ` is measurable and `|v_l φ| ≤ C |φ|`). -/
def VelMulMemX (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ), MollCtx m ν tr t s g φ a b χ →
    ∀ r ∈ Ioo a b, ∀ l : Fin 2,
      (∀ x : ℝ × ℝ, ((tr.v r (x.1 + ν ^ (-2 : ℝ), x.2) l : ℝ) : ℂ) * φ r (x.1 + ν ^ (-2 : ℝ), x.2) =
        ((tr.v r x l : ℝ) : ℂ) * φ r x) ∧
      MemLp (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))

/-- **(C2) `r ↦ v_l(r) φ(r)` is continuous into `X_{-m,c}` on `(a, b)`**:
`v(r')φ(r') - v(r)φ(r) = v(r')(φ(r') - φ(r)) + (v(r') - v(r))φ(r)`; the first term is bounded by
`C ‖φ(r') - φ(r)‖_X → 0` (`LadTrainBdd` on `[0, s]`, periodicity, `IsAdjointWeak.strongCont`); the
second tends to `0` by dominated convergence in `L²(cellMeasure)`: pointwise `v(r') x → v(r) x`
(`IsTrain.smooth_v` jointly continuous), dominated by `(2C)²|φ(r)|²`. -/
def VelMulCont (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ), MollCtx m ν tr t s g φ a b χ →
    ∀ r ∈ Ioo a b, ∀ l : Fin 2,
      Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m)
        ((fun y => ((tr.v r' y l : ℝ) : ℂ) * φ r' y) - (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y)))
        (𝓝[Ioo a b] r) (𝓝 0)

/-- **(C3) `χ` is continuous into `X_{-m,c}` on `(a, b)`** (SP 3052-3058; needs `8 < m`): by
`adjLocalizedCoeff m hm` (`Sub/T21_2_7/LocalizedCoeff.lean`; `LadTrainBdd tr m s C` from the
hypothesis) there are `K r : AdjX c m →L[ℂ] AdjX c m` bounded by `β`, with `r ↦ K r w` continuous on
`[0, s]`, satisfying the same pairing identity as `χ(r)`. The pairing determines an element of `X_{-m,c}`
(`LocCylUniq`, both sides in `AdjX`, the tests separate; `AdjPairing`), so `χ(r) = K r (φ r)` a.e., and
`K r' (φ r') - K r (φ r) = K r' (φ r' - φ r) + (K r' - K r)(φ r)`, bounded by `β ‖φ r' - φ r‖ +
‖K r' (φ r) - K r (φ r)‖ → 0`. -/
def ChiCont (m : ℝ) : Prop :=
  8 < m → ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ),
    MollCtx m ν tr t s g φ a b χ →
    ∀ r ∈ Ioo a b, Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (χ r' - χ r)) (𝓝[Ioo a b] r) (𝓝 0)

/-- **(C4) The tested adjoint right-hand side splits** (linearity of the integral; the three
integrands are integrable: `φ(r) lapP ψ` by `XMulTestInt` (`lapP ψ` is a test, `isCylTest_lapP`),
`φ (v·∇ψ)` by `VelMulMemX` and `XMulTestInt` (`pd l ψ` is a test, `IsCylTest.pd`), and `φ (u·∇E)` by
`ChiRep`): for `r ∈ (a, b)`, a test `ψ` with kernel velocity `uψ`,
`∫ adjIntegrand = ν ∫ φ lapP ψ - ∫ φ (v·∇ψ) - ∫ φ (uψ·∇E)`. -/
def AdjIntegrandSplit (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ), MollCtx m ν tr t s g φ a b χ →
    ∀ r ∈ Ioo a b, ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r) r ψ uψ x =
        (ν : ℂ) * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x * (lapP ψ x : ℂ)) -
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x *
            ((tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x : ℝ) : ℂ)) -
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)

/-- **(D1) The tested derivative of the mollified adjoint, dual form** (SP 3060): for a cylinder test
`ψ` and any kernel velocity `u'` of the test `ρ̌_n ⋆ ψ` (`MollDual`), `r ∈ (a, b)`:
`d/dr ∫ (ρ_n ⋆ φ(r)) ψ = -∫ adjIntegrand (ρ̌_n ⋆ ψ) u'` at `φ(r)`.  Proof: for `r'` near `r`
(`r' ∈ (a, b)`: `φ(r')` periodic in `X`, `IsAdjointWeak.periodic/memX`) `∫ (ρ_n ⋆ φ(r')) ψ = ∫ φ(r')
(ρ̌_n ⋆ ψ)` (`MollDual`), so this is `AdjTestedDeriv` at the test `ρ̌_n ⋆ ψ` with the velocity `u'`
(`HasDerivWithinAt` on `[t, s]` is `HasDerivAt` at the interior point `r`, `HasDerivWithinAt.hasDerivAt`,
`Icc_mem_nhds`), transported along the eventual equality of the two functions of `r'`
(`HasDerivAt.congr_of_eventuallyEq`). -/
def MollTestedAdj (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ), MollCtx m ν tr t s g φ a b χ →
    ∀ (n : ℕ) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      ∀ u' : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart (ν ^ (-2 : ℝ)) (mollR n ψ) u' →
      ∀ r ∈ Ioo a b,
        HasDerivAt (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), cellMoll n (φ r') x * (ψ x : ℂ))
          (-∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r) r (mollR n ψ) u' x) r

/-- **(D2) The mollified rate tested against `ψ`** (SP 3060; integration by parts): for `r ∈ (a, b)`,
a cylinder test `ψ` and any kernel velocity `u'` of `ρ̌_n ⋆ ψ`,
`∫_{C_c} mollRate ν v(r) n φ(r) χ(r) ψ = -∫_{C_c} adjIntegrand (φ r) (ρ̌_n ⋆ ψ) u'`.
Proof: `AdjIntegrandSplit` splits the right side.  (i) `∫ φ lapP(ρ̌_n⋆ψ) = ∫ φ ρ̌_n⋆(lapP ψ) = ∫ (ρ_n ⋆ φ) lapP ψ
= ∫ Δ(ρ_n ⋆ φ) ψ` (`MollDual` twice with `h = lapP ψ`, `isCylTest_lapP`; `CellIBP` twice for the smooth
periodic `ρ_n ⋆ φ` (`CellConvDeriv`), `adjSpatial [l, l] = pdCx l ∘ pdCx l`).  (ii) `∫ φ (v·∇(ρ̌_n⋆ψ)) =
Σ_l ∫ (v_lφ) ∂_l(ρ̌_n⋆ψ) = Σ_l ∫ (ρ_n ⋆ (v_lφ)) ∂_lψ = -Σ_l ∫ ∂_l(ρ_n ⋆ (v_lφ)) ψ = -Σ_l ∫ cellConv (∂_lρ_n)
(v_lφ) ψ` (`MollDual`, `VelMulMemX`, `CellIBP`, `CellConvDeriv`).  (iii) `∫ φ (u'·∇E) = ∫ χ (ρ̌_n⋆ψ)` by the
pairing identity in `ChiRep`, `= ∫ (ρ_n ⋆ χ) ψ` by `MollDual`. -/
def MollRateTested (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (a b : ℝ) (χ : ℝ → ℝ × ℝ → ℂ), MollCtx m ν tr t s g φ a b χ →
    ∀ (n : ℕ) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      ∀ u' : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart (ν ^ (-2 : ℝ)) (mollR n ψ) u' →
      ∀ r ∈ Ioo a b,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), mollRate ν (tr.v r) n (φ r) (χ r) x * (ψ x : ℂ) =
          -∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr (φ r) r (mollR n ψ) u' x

end UnforcedLeray.Short.IIIa
