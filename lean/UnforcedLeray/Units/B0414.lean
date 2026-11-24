import UnforcedLeray.Units.B0414.PhaseOrthogonal
import UnforcedLeray.Lib.LerayC.DilateC

/-!
# B0414 — the Leray projection `P_σ`: `L^q` boundedness, orthogonality at `q = 2`, commutations

Blueprint unit B0414 (`unlabeled:7336`), `paper/main.tex` lines 7336–7344 (§`sec:st18-8879`,
"Spaces, symmetry, and statement"):

> The spatial Leray projection is denoted by `P_σ`; its Fourier multiplier is
> `Id − ξ⊗ξ/|ξ|²`. The Riesz-transform bound [Grafakos, Cor. 5.2.8] makes it bounded on `L^q`
> for `1 < q < ∞`, and it is an orthogonal projection at `q = 2`. Its multiplier is homogeneous
> of degree zero, so it commutes with spatial dilations as well as with the heat semigroup and
> phase translations.

Here `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` with the normalized phase measure (tex 7313–7317), modelled
by the drafted `PhaseSpace.Yq P q` (decision D2 of

the phase `τ`.

## The operator (no Fourier multiplier; scoping decision D5, bypass §4.2 of `INF01-CZ.md`)

* On `L^q(ℝ³; ℝ³)`: `RieszLp.lerayLp q = Id + R ⊗ R`, with `R_iR_k = ∂_i∂_k(-Δ)^{-1}` the
  Newton-Hessian Calderón–Zygmund operators (`Lib/LerayLp`, INF01 T13–T14). The Riesz-transform
  bound cited from Grafakos is proved there through the drafted Calderón–Zygmund theorem
  (`Lib/CZCore`), not assumed.
* On `L^q(ℝ³; ℂ³)`: `RieszLp.lerayC q`, `P_σF = P_σ(Re F) + i P_σ(Im F)` (`Lib/LerayC/Complex`).
* On `Y_q`: `RieszLp.lerayY P q`, `lerayC q` applied slice by slice (`Lib/LerayC/Phase`).

That this is the manuscript's `P_σ` is the identification at `q = 2` with the orthogonal
projection onto the distributionally solenoidal fields (part (ii)), together with the a.e.
agreement of `lerayC q` with that projection on `L^q ∩ L²` (part (i)). The orthogonal
projection onto solenoidal fields is the operator whose `L²` Fourier multiplier is
`Id − ξ⊗ξ/|ξ|²`; that Fourier-side description is not formalized (the scoping note records that
it "is used only at `q = 2` and is not needed for any estimate").

## What is formalized (`statement : Statement`)

* (i) `Statement_i q`: for `1 < q < ∞`, `lerayC q` is bounded on `L^q(ℝ³; ℂ³)` with
  `‖lerayC q‖ ≤ 2‖lerayLp q‖` (a constant depending on `q` only); `lerayY P q` acts slice by
  slice and is bounded on `Y_q` with `‖lerayY P q‖ ≤ ‖lerayC q‖` uniformly in the period `P`;
  on real fields `lerayC q` is `lerayLp q`; on `L^q ∩ L²` it agrees a.e. with the orthogonal
  projection onto the solenoidal fields.
* (ii) `Statement_ii`: at `q = 2`, `lerayC 2` is the orthogonal projection
  (`Submodule.starProjection`) of `L²(ℝ³; ℂ³)` onto `solenoidalC`, the fields with
  `div F = 0` in distributions (`IsSolenoidalC`); `lerayLp 2` is the library's orthogonal
  projection `Leray.projection` onto the real solenoidal fields; on `Y_2`, `lerayY P 2` is the
  orthogonal projection onto `solenoidalY P`, the fields with a.e. distributionally solenoidal
  phase slices, and `lerayY P q f` is solenoidal in the phase-space distribution sense
  `PhaseSpace.IsPhaseSolenoidal` for every `q`.
* (iii) `Statement_iii q b`: for `1 < q < ∞` and `b > 0`, `P_σ` commutes with the spatial
  dilation `u ↦ u(b ·)` on `L^q(ℝ³; ℝ³)`, on `L^q(ℝ³; ℂ³)` and, slice by slice, on `Y_q`.
* (iv) `Statement_iv q`: for `1 < q < ∞`, `P_σ` commutes with the heat semigroup `e^{θΔ}`
  on `L^q(ℝ³; ℂ³)` and slice by slice on `Y_q`, and with every phase translation
  `f ↦ f(σ + ·)`, `σ ∈ ℝ/Pℤ`, on `Y_q`.

## Conventions and junk values

* `1 < q`, `q ≠ ∞` are explicit hypotheses (with the instance `Fact (1 ≤ q)` that `Lp` needs);
  no statement is made at `q = 1` or `q = ∞`, where the manuscript makes none.
* `Heat.heatLp _ _ θ` is the Gaussian average `e^{θΔ}` for `θ > 0` and the identity for
  `θ ≤ 0` (`Lib/HeatR3/LpOp.lean`); the commutation is stated for every `θ`, which for `θ ≤ 0`
  is trivial and for `θ > 0` is the manuscript's claim.
* The amplitude factor of the manuscript's dilations is a scalar and commutes trivially; only
  `u ↦ u(b ·)` is stated (`RieszLp.dilateLp`, `RieszLp.dilateLpE`, `Lib/LerayC/DilateC.lean`).
* Phase translation is Mathlib's `DomAddAct.mk σ +ᵥ f`, i.e. `f ↦ f(σ + ·)` on
  `L^q(haarAddCircle)`.
* Distributional solenoidality uses real compactly supported smooth tests with integrable
  pairings, as the library's `IsSolenoidal` (`lean/UnforcedLeray/Statement.lean`); for `L²`
  fields the integrability is automatic.

## Not formalized

* The Fourier-multiplier formula `Id − ξ⊗ξ/|ξ|²` itself (bypassed by D5, see above).
* The converse of `isPhaseSolenoidal_of_mem_solenoidalY`: that a field of `Y_2` solenoidal in
  the phase-space distribution sense has a.e. solenoidal slices. Hence the range in (ii) on `Y_2`
  is described slice-wise.

Status: draft. It does not prove Theorem A or `UnforcedLeray.MainClaim`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.B0414

open UnforcedLeray.RieszLp
open UnforcedLeray.PhaseSpace (CVec3 Yq)

/-! ### (i) Boundedness on `L^q(ℝ³; ℂ³)` and on `Y_q` -/

/-- **B0414 (i)** (tex 7338–7341): for `1 < q < ∞`, `P_σ` is bounded on `L^q(ℝ³; ℂ³)` with a
constant depending on `q` only, hence on `Y_q` uniformly in the period; it acts pointwise in the
phase; on real fields it is the real Leray projection; on `L^q ∩ L²` it is the orthogonal
projection onto the distributionally solenoidal fields. -/
def Statement_i (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ F : Lp CVec3 q (volume : Measure Space),
      ‖lerayC q hq1 hq F‖ ≤ C * ‖F‖) ∧
    ‖lerayC q hq1 hq‖ ≤ 2 * ‖lerayLp q hq1 hq‖ ∧
    (∀ (P : ℝ) [Fact (0 < P)], ‖lerayY P q hq1 hq‖ ≤ ‖lerayC q hq1 hq‖ ∧
      ∀ f : Yq P q, (lerayY P q hq1 hq f : AddCircle P → Lp CVec3 q (volume : Measure Space))
        =ᵐ[AddCircle.haarAddCircle] fun τ => lerayC q hq1 hq (f τ)) ∧
    (∀ G : Lp Space q (volume : Measure Space),
      lerayC q hq1 hq (ofReV.compLpL q volume G) = ofReV.compLpL q volume (lerayLp q hq1 hq G)) ∧
    (∀ (F : Lp CVec3 q (volume : Measure Space)) (hF2 : MemLp F 2 volume),
      (lerayC q hq1 hq F : Space → CVec3) =ᵐ[volume] solenoidalC.starProjection (hF2.toLp F))

theorem statement_i (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) :
    Statement_i q hq1 hq :=
  ⟨⟨‖lerayC q hq1 hq‖, norm_nonneg _, fun F => (lerayC q hq1 hq).le_opNorm F⟩,
    norm_lerayC_le hq1 hq,
    fun _ _ => ⟨norm_lerayY_le hq1 hq, fun f => coeFn_lerayY hq1 hq f⟩,
    fun G => lerayC_ofRe hq1 hq G,
    fun F hF2 => lerayC_ae_eq_starProjection hq1 hq F hF2⟩

/-! ### (ii) The orthogonal projection at `q = 2` -/

/-- **B0414 (ii)** (tex 7341–7342): at `q = 2`, `P_σ` is the orthogonal projection onto the
distributionally solenoidal fields: on `L²(ℝ³; ℂ³)` (`solenoidalC`, membership
`IsSolenoidalC`), on `L²(ℝ³; ℝ³)` (the library's `Leray.projection`, the orthogonal projection
onto `Leray.solenoidalSubspace`, membership `IsSolenoidal`), and on `Y_2` (`solenoidalY P`, the
fields with a.e. solenoidal phase slices); and `P_σ` takes values in the phase-space solenoidal
fields `PhaseSpace.IsPhaseSolenoidal` for every `1 < q < ∞`. -/
def Statement_ii : Prop :=
  lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = solenoidalC.starProjection ∧
    (∀ F : Lp CVec3 2 (volume : Measure Space),
      F ∈ solenoidalC ↔ IsSolenoidalC (F : Space → CVec3)) ∧
    lerayLp 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = Leray.solenoidalSubspace.starProjection ∧
    (∀ F : L2Space, F ∈ Leray.solenoidalSubspace ↔ IsSolenoidal (F : SpatialField)) ∧
    (∀ (P : ℝ) [Fact (0 < P)],
      lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = (solenoidalY P).starProjection ∧
      (∀ f : Yq P 2, f ∈ solenoidalY P ↔
        ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), IsSolenoidalC (f τ : Space → CVec3)) ∧
      (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) (f : Yq P q),
        PhaseSpace.IsPhaseSolenoidal (lerayY P q hq1 hq f)))

theorem statement_ii : Statement_ii :=
  ⟨lerayC_two, mem_solenoidalC_iff, lerayLp_two, Leray.mem_solenoidalSubspace_iff,
    fun _ _ => ⟨lerayY_two, mem_solenoidalY_iff,
      fun _ _ hq1 hq f => lerayY_isPhaseSolenoidal hq1 hq f⟩⟩

/-! ### (iii) Spatial dilations -/

/-- **B0414 (iii)** (tex 7342–7343): for `1 < q < ∞` and `b > 0`, `P_σ` commutes with the
spatial dilation `u ↦ u(b ·)` on `L^q(ℝ³; ℝ³)`, on `L^q(ℝ³; ℂ³)` and, slice by slice, on
`Y_q`. -/
def Statement_iii (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) {b : ℝ} (hb : 0 < b) :
    Prop :=
  (lerayLp q hq1 hq).comp (dilateLp q hq hb.ne') = (dilateLp q hq hb.ne').comp (lerayLp q hq1 hq) ∧
    ((lerayC q hq1 hq).restrictScalars ℝ).comp (dilateLpE CVec3 q hq hb.ne') =
      (dilateLpE CVec3 q hq hb.ne').comp ((lerayC q hq1 hq).restrictScalars ℝ) ∧
    ∀ (P : ℝ) [Fact (0 < P)],
      ((lerayY P q hq1 hq).restrictScalars ℝ).comp
          ((dilateLpE CVec3 q hq hb.ne').compLpL q AddCircle.haarAddCircle) =
        ((dilateLpE CVec3 q hq hb.ne').compLpL q AddCircle.haarAddCircle).comp
          ((lerayY P q hq1 hq).restrictScalars ℝ)

theorem statement_iii (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) {b : ℝ}
    (hb : 0 < b) : Statement_iii q hq1 hq hb :=
  ⟨lerayLp_dilate hq1 hq hb, lerayC_dilate hq1 hq hb, fun _ _ => lerayY_dilate hq1 hq hb⟩

/-! ### (iv) The heat semigroup and phase translations -/

/-- **B0414 (iv)** (tex 7343–7344): for `1 < q < ∞`, `P_σ` commutes with the heat semigroup
`e^{θΔ}` on `L^q(ℝ³; ℂ³)` and slice by slice on `Y_q`, and with every phase translation
`f ↦ f(σ + ·)` on `Y_q`. -/
def Statement_iv (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) : Prop :=
  (∀ θ : ℝ, ((lerayC q hq1 hq).restrictScalars ℝ).comp
        (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ) =
      (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ).comp
        ((lerayC q hq1 hq).restrictScalars ℝ)) ∧
    ∀ (P : ℝ) [Fact (0 < P)],
      (∀ θ : ℝ, ((lerayY P q hq1 hq).restrictScalars ℝ).comp
          ((Heat.heatLp (AddMonoidHom.id Space) continuous_id θ :
            Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q volume).compLpL q
            AddCircle.haarAddCircle) =
        ((Heat.heatLp (AddMonoidHom.id Space) continuous_id θ :
            Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q volume).compLpL q
            AddCircle.haarAddCircle).comp ((lerayY P q hq1 hq).restrictScalars ℝ)) ∧
      ∀ (σ : AddCircle P) (f : Yq P q),
        lerayY P q hq1 hq (DomAddAct.mk σ +ᵥ f) = DomAddAct.mk σ +ᵥ lerayY P q hq1 hq f

theorem statement_iv (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) :
    Statement_iv q hq1 hq :=
  ⟨fun θ => lerayC_heat hq1 hq θ,
    fun _ _ => ⟨fun θ => lerayY_heat hq1 hq θ, fun σ f => lerayY_phase hq1 hq σ f⟩⟩

/-! ### The unit -/

/-- **B0414** (`paper/main.tex` lines 7336–7344): the spatial Leray projection `P_σ`, applied
pointwise in the phase, is bounded on `L^q(ℝ³; ℂ³)` and on `Y_q` for every `1 < q < ∞` (i), is
the orthogonal projection onto the distributionally solenoidal fields at `q = 2` (ii), and
commutes with spatial dilations (iii), with the heat semigroup and with phase translations
(iv). -/
def Statement : Prop :=
  (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤), Statement_i q hq1 hq) ∧
    Statement_ii ∧
    (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) (b : ℝ) (hb : 0 < b),
      Statement_iii q hq1 hq hb) ∧
    (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤), Statement_iv q hq1 hq)

/-- **B0414**, proved (as a draft; see the module docstring for the scope). -/
theorem statement : Statement :=
  ⟨fun q _ hq1 hq => statement_i q hq1 hq, statement_ii,
    fun q _ hq1 hq _ hb => statement_iii q hq1 hq hb,
    fun q _ hq1 hq => statement_iv q hq1 hq⟩

end UnforcedLeray.B0414
