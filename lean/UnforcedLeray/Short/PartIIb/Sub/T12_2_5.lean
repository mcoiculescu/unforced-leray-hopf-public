import UnforcedLeray.Short.PartIIb.Sub.T12_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.PeriodizeCellTest
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Part II-b, task `PartII-b:T12/2/5` (`SliceWeakSolenoidal`): sub-lemma Props

Source of record: `the November 2 reference manuscript`, lines 1901-1903 (`H_r` for
`1 < r < 3`) and 1923-1926 (`P_0` applied at each age `s`). Target: `LerayLiftSub.SliceWeakSolenoidal`
(`Sub/T12_2.lean`).

Route of the target (the cell identities at a.e. age give the weak solenoidality on `Coord`):

1. a compact planar test `φ` (`IsCoordTest`, supported in `s > 0`) is periodized in `q` at each age `s`:
   `Φ_s(z) = pcellPer c φ (s, z) = ∑ₙ φ(s, q - nc, η)` is a cell test (`SlicePerCylTest`), whose
   derivatives are the periodizations of the derivatives of `φ` (`SlicePerFDeriv`);
2. `G ∈ H_r` with `1 < r` is integrable on compact subsets of `{s > 0}` (`WindowCellFinite`,
   `WindowStripFinite`, `IntegrableOnCompact`), so the planar pairings `G_i ∂_jφ` are integrable on
   `Coord` (`IntegrableTestPair`);
3. at a fixed age, the unfolding `∫_cell (P_c f) g = ∫_{ℝ²} f g` (`Cyl.integral_cell_periodize_mul`,
   with cell integrability `CellPeriodizeMulIntegrable`) turns the planar slice integral into the
   cell identity of `Φ_s` (`SlicePlanarSolZero`);
4. Fubini in `s` (`integral_prod`, `Integrable.prod_right_ae`) gives `WeakSolenoidal G`.

The same lemmas serve `SlicePerpPlanar` (`Sub/T12_2_6.lean`). No proofs here: each Prop is a task.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

/-- **Sub-lemma `T12/2/5/1`** (periodized test is a cell test; SP 1923-1926). For a smooth compactly
supported `φ` on `Coord` and every age `s`, the `q`-periodization `z ↦ ∑ₙ φ(s, q - nc, η)` is smooth,
exactly `c`-periodic in `q` and vanishes for `|η|` large. Reuse `pcellPer_contDiff`,
`pcellPer_periodic`, `pcellPer_compact`, `pcell_bound_gen`
(`Tasks/HilbertEnergy/ProductRule/PeriodizeCellTest.lean`). -/
def SlicePerCylTest : Prop :=
  ∀ (c : ℝ) (φ : Coord → ℝ), 0 < c → ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ s : ℝ,
    CylTest c (fun z : ℝ × ℝ => pcellPer c φ (s, z))

/-- **Sub-lemma `T12/2/5/2`** (derivatives commute with the periodization; SP 1923-1926). For a smooth
compactly supported `φ`, the derivative in `z = (q, η)` of `z ↦ pcellPer c φ (s, z)` in direction `v` is
the periodization of `x ↦ Dφ(x)(0, v)`. Near each point only a finite window of `n` contributes
(as in `pcellPer_contDiff`), and `Dφ` vanishes off `tsupport φ` (`support_fderiv_subset`). -/
def SlicePerFDeriv : Prop :=
  ∀ (c : ℝ) (φ : Coord → ℝ), 0 < c → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ (s : ℝ) (z v : ℝ × ℝ),
      fderiv ℝ (fun w : ℝ × ℝ => pcellPer c φ (s, w)) z v =
        pcellPer c (fun x => fderiv ℝ φ x (0, v)) (s, z)

/-- **Sub-lemma `T12/2/5/3`** (finite `L^r` mass on an age window; SP 1901-1903). If `G` has finite
`H_r` norm (`H_r = L^r(s^{r/2-5/2} ds dq/c dη)` on `(0,∞) × cell`), then for `0 < a` the Lebesgue
integral of `‖G‖^r` over `[a, b] × cell` is finite: the weight `c⁻¹ s^{r/2-5/2}` is bounded below by a
positive constant on `[a, b]`. Reuse `Axi.lintegral_ageμ` (`Lib/AxisymmetricB/Lift.lean`) and
`eLpNorm_eq_lintegral_rpow_enorm`. -/
def WindowCellFinite : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 0 < r → StronglyMeasurable G → hNorm c r G < ⊤ →
    ∀ a b : ℝ, 0 < a → ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, ‖G x‖ₑ ^ r < ⊤

/-- **Sub-lemma `T12/2/5/4`** (periodicity spreads the window mass over a strip). For `G` exactly
`c`-periodic in `q`, finiteness of `∫⁻_{[a,b] × cell} ‖G‖^r` gives finiteness over
`[a, b] × [-Q, Q] × ℝ`: the strip is covered by finitely many `q`-translates of the cell, each carrying
the same integral (translation invariance of Lebesgue measure and periodicity). -/
def WindowStripFinite : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → StronglyMeasurable G →
    (∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) →
    ∀ a b : ℝ, ∫⁻ x in Icc a b ×ˢ UnforcedLeray.Cyl.cell c, ‖G x‖ₑ ^ r < ⊤ →
      ∀ Q : ℝ, ∫⁻ x in Icc a b ×ˢ (Icc (-Q) Q ×ˢ (univ : Set ℝ)), ‖G x‖ₑ ^ r < ⊤

/-- **Sub-lemma `T12/2/5/5`** (local integrability of `H_r`, `1 < r`). An exactly periodic strongly
measurable `G` of finite `H_r` norm is Lebesgue integrable on every compact `K ⊆ {s > 0}`: `K` lies in a
box `[a, b] × [-Q, Q] × [-L, L]` with `a > 0`, on which `G ∈ L^r` (`WindowCellFinite`,
`WindowStripFinite`), and `L^r ⊆ L^1` on a finite-measure set for `r ≥ 1` (`MemLp.integrable`). -/
def IntegrableOnCompact : Prop :=
  ∀ (c r : ℝ) (G : CProf), 0 < c → 1 < r → StronglyMeasurable G →
    (∀ (s : ℝ) (z : ℝ × ℝ), G (s, (z.1 + c, z.2)) = G (s, z)) → hNorm c r G < ⊤ →
    ∀ K : Set Coord, IsCompact K → K ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) → IntegrableOn G K

/-- **Sub-lemma `T12/2/5/6`** (pairings with a coordinate test are integrable). If `G` is integrable on
`tsupport φ` for a test `φ`, then `G_i φ` and `G_i ∂_jφ` are integrable on `Coord` (continuous factors
vanishing off the compact set `tsupport φ`). -/
def IntegrableTestPair : Prop :=
  ∀ (G : CProf) (φ : Coord → ℝ), IsCoordTest φ → IntegrableOn G (tsupport φ) →
    (∀ i : Fin 2, Integrable (fun x => G x i * (φ x : ℂ))) ∧
      ∀ (i : Fin 2) (j : Fin 3), Integrable (fun x => G x i * (cpd j φ x : ℂ))

/-- **Sub-lemma `T12/2/5/7`** (cell integrability of an unfolded product; the `[0,∞]` analogue of
`Cyl.integral_cell_periodize_mul`, `Lib/CylinderB/Periodize.lean`). For periodic `g` with `f g`
integrable on the plane, `(P_c f) g` is integrable on the cell:
`‖(P_c f)(z) g(z)‖ ≤ ∑ₙ ‖f(z - nc) g(z - nc)‖` (`enorm_tsum_le_tsum_enorm`, periodicity of `g`) and
`Cyl.lintegral_cell_periodize`. The measurability of `P_c f` is a hypothesis (in the applications `P_c f`
is continuous). -/
def CellPeriodizeMulIntegrable : Prop :=
  ∀ (c : ℝ) (f g : ℝ × ℝ → ℂ), 0 < c → StronglyMeasurable f → StronglyMeasurable g →
    StronglyMeasurable (UnforcedLeray.Cyl.periodize c f) → UnforcedLeray.Cyl.IsPeriodic c g →
    Integrable (fun z => f z * g z) →
    IntegrableOn (fun z => UnforcedLeray.Cyl.periodize c f z * g z) (UnforcedLeray.Cyl.cell c)

/-- **Sub-lemma `T12/2/5/8`** (one age: the planar identity from the cell identity; SP 1923-1926). Let
`g` be an exactly periodic strongly measurable cell field satisfying the cell identity
`∫_cell g·∇Φ = 0` for every cell test `Φ` (the weak solenoidality clause of `IsCylHelmholtz`). For a
coordinate test `φ` and an age `s` with `g_0 ∂_qφ(s,·)`, `g_1 ∂_ηφ(s,·)` integrable on the plane, the
planar integral `∫_{ℝ²} g·∇_zφ(s,·)` vanishes: with `Φ_s = pcellPer c φ (s, ·)` (`SlicePerCylTest`,
`SlicePerFDeriv`), `Cyl.integral_cell_periodize_mul` and `CellPeriodizeMulIntegrable` turn it into
`c ∫ g·∇Φ_s d(avgμ c) = 0`. -/
def SlicePlanarSolZero : Prop :=
  ∀ (c : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → StronglyMeasurable g →
    (∀ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) →
    (∀ Φ : ℝ × ℝ → ℝ, CylTest c Φ →
        Integrable (fun z => g z 0 * (fderiv ℝ Φ z (1, 0) : ℂ) + g z 1 * (fderiv ℝ Φ z (0, 1) : ℂ))
            (UnforcedLeray.Cyl.avgμ c) ∧
          ∫ z, (g z 0 * (fderiv ℝ Φ z (1, 0) : ℂ) + g z 1 * (fderiv ℝ Φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
    ∀ (φ : Coord → ℝ) (s : ℝ), IsCoordTest φ →
      Integrable (fun z : ℝ × ℝ => g z 0 * (cpd 1 φ (s, z) : ℂ)) →
      Integrable (fun z : ℝ × ℝ => g z 1 * (cpd 2 φ (s, z) : ℂ)) →
      ∫ z : ℝ × ℝ, (g z 0 * (cpd 1 φ (s, z) : ℂ) + g z 1 * (cpd 2 φ (s, z) : ℂ)) = 0

end UnforcedLeray.Short.IIb.LerayLiftSub
