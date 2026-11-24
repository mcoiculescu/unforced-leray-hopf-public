import UnforcedLeray.Lib.ParabolicB

/-!
# B0423: parabolic `L^q` maximal regularity, uniform in viscosity (`eq:free-stress-11`)

Blueprint unit B0423 (label `unlabeled:7452`), `paper/main.tex` lines 7447–7477: the lemma at
lines 7452–7461 and its proof at lines 7463–7477. Infrastructure: INF02 T8 (scoping note

drafted leaf modules `Lib/Parabolic` (T5–T7, `q = 2`) and `Lib/ParabolicB` (T8, every
`1 < q < ∞`), under decisions D4 and BP-B of `scoping/README.md` (the Calderón–Zygmund bound for
the single causal kernel `1_{θ>0} ∂_{ij} H_θ` replaces the citation of Fabes–Rivière at
line 7466).

The manuscript's lemma (lines 7452–7461): if `d ≥ 1`, `1 < q < ∞`, `ν > 0`, and
`u, F ∈ L^q(ℝ × ℝ^d)` satisfy `(∂_θ - νΔ_x)u = F` distributionally, with `u` compactly supported
in time, then `‖ν D_x² u‖_{L^q} + ‖∂_θ u‖_{L^q} ≤ C_{d,q} ‖F‖_{L^q}`, with `C_{d,q}`
independent of `ν`.

## Conventions

* Space-time is `PS d = ℝ × ℝ^d` (`UnforcedLeray.Parabolic.PS`), first coordinate the time `θ`,
  with the product Lebesgue measure. Tests are `IsSTTest φ` (`C^∞`, compact support).
* "Distributionally" is read against tests: `IsWeakHeatSol ν u F` is
  `∫ u (-∂_θ φ - νΔ_x φ) = ∫ F φ` for every test `φ`. The manuscript's `D_x² u` and `∂_θ u` are
  the distributional derivatives; the lemma asserts that they are `L^q` functions with the bound.
  We state this as the existence of `D2 i j, Dt ∈ L^q` that are the weak derivatives
  (`HasWeakSpaceDeriv2`, `HasWeakTimeDeriv`). Weak derivatives are unique a.e., so this is the
  manuscript's claim.
* `‖ν D_x² u‖_{L^q}` is the `L^q` norm of the pointwise Frobenius norm of the spatial Hessian,
  `hessNorm D2 X = (Σ_{i,j} |D2 i j X|²)^{1/2}` (any other matrix norm changes `C_{d,q}` by a
  factor depending only on `d`).
* "Compactly supported in time" is `IsTimeCompact u`: `u = 0` a.e. outside a slab
  `{|θ| ≤ R}` (an a.e. condition, since `u` is an `L^q` class).
* The constant: `∃ C, ∀ ν > 0, ∀ u F, …`, so `C` depends on `d, q` only.
* No junk values: `u, F ∈ L^q` and tests are in every `L^p`, so every integral in the
  hypotheses and conclusions is of an integrable function; norms are `eLpNorm` in `ℝ≥0∞`.

## Main declarations

* `FreeStress11 d q`: the statement of the lemma (with the manuscript's hypotheses, literally).
* `freeStress11`: `1 ≤ d → 1 < q → FreeStress11 d q` (the unit).
* `heat_estimate`: the same conclusion without the hypotheses `1 ≤ d` and compact time support,
  which the proof does not use.
* `heat_estimate_componentwise`: `‖ν ∂_i∂_j u‖_q ≤ C‖F‖_q` for every `i, j` and
  `‖∂_θ u‖_q ≤ C‖F‖_q` (the form in `Lib/ParabolicB`, `Parabolic.heat_maximal_regularity`).
* `heat_estimate_laplacian`: `‖ν Δ_x u‖_q ≤ C‖F‖_q`, the form used at line 7510 (B0424).
* `heat_estimate_complex`, `heat_estimate_complex_laplacian`: the same for complex-valued
  `u, F` (the manuscript's fields are complex; B0424 applies the lemma componentwise to complex
  `Y_q` fields), with real tests.

## Deviations

* The manuscript's proof mollifies `u, F` and uses the causal heat formula (lines 7472–7476);
  `Lib/ParabolicB` identifies the derivatives by duality with the backward test instead, so
  compact time support of `u` is not needed. `FreeStress11` keeps it as a hypothesis.
* The viscosity scaling is the time dilation `θ = s/ν` (`Parabolic.tsc`) instead of the spatial
  dilation `x = √ν z` of line 7469.
* The cylinder version used at line 3796 (unit B0501; INF02 T9, bypass BP-F) is not part of this
  unit (lines 7449–7450 only announce it) and is not stated here.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0423

open MeasureTheory Real Set Filter Complex
open scoped ENNReal NNReal ContDiff

open UnforcedLeray.Parabolic (PS IsSTTest tD sD2 sLap)

variable {d : ℕ}

/-! ## Definitions -/

/-- `(∂_θ - νΔ_x)u = F` in distributions on `ℝ × ℝ^d` (`paper/main.tex` line 7455, blueprint
B0423): `∫ u (-∂_θ φ - νΔ_x φ) = ∫ F φ` for every smooth compactly supported test `φ`. -/
def IsWeakHeatSol (ν : ℝ) (u F : PS d → ℝ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X

/-- `D` is the distributional derivative `∂_{x_i}∂_{x_j} u` (`paper/main.tex` line 7457,
blueprint B0423): `∫ u ∂_i∂_j φ = ∫ D φ` for every test `φ`. -/
def HasWeakSpaceDeriv2 (u : PS d → ℝ) (i j : Fin d) (D : PS d → ℝ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D X * φ X

/-- `Dt` is the distributional derivative `∂_θ u` (`paper/main.tex` line 7457, blueprint
B0423): `∫ u ∂_θ φ = -∫ Dt φ` for every test `φ`. -/
def HasWeakTimeDeriv (u Dt : PS d → ℝ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * tD φ X = -∫ X, Dt X * φ X

/-- `u` is compactly supported in time (`paper/main.tex` line 7456, blueprint B0423): it vanishes
a.e. outside a slab `{|θ| ≤ R}`. -/
def IsTimeCompact {E : Type*} [Zero E] (u : PS d → E) : Prop :=
  ∃ R : ℝ, ∀ᵐ X ∂(volume : Measure (PS d)), R < |X.1| → u X = 0

/-- The pointwise Frobenius norm `|D_x² u|(X) = (Σ_{i,j} |∂_i∂_j u(X)|²)^{1/2}` of a spatial
Hessian `D2` (`paper/main.tex` line 7458, blueprint B0423). -/
def hessNorm (D2 : Fin d → Fin d → PS d → ℝ) (X : PS d) : ℝ :=
  √(∑ i, ∑ j, D2 i j X ^ 2)

/-- **The statement of `eq:free-stress-11`** (`paper/main.tex` lines 7452–7461, blueprint unit
B0423), with the manuscript's hypotheses: there is `C = C_{d,q}` such that for every `ν > 0` and
all `u, F ∈ L^q(ℝ × ℝ^d)` with `u` compactly supported in time and `(∂_θ - νΔ_x)u = F` in
distributions, the distributional derivatives `D_x² u` and `∂_θ u` are `L^q` functions and
`‖ν D_x² u‖_{L^q} + ‖∂_θ u‖_{L^q} ≤ C ‖F‖_{L^q}`. The constant does not depend on `ν`. -/
def FreeStress11 (d : ℕ) (q : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℝ,
    MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
    IsTimeCompact u → IsWeakHeatSol ν u F →
    ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
      (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧ HasWeakSpaceDeriv2 u i j (D2 i j)) ∧
      MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDeriv u Dt ∧
      eLpNorm (fun X => ν * hessNorm D2 X) (ENNReal.ofReal q) volume +
          eLpNorm Dt (ENNReal.ofReal q) volume ≤
        C * eLpNorm F (ENNReal.ofReal q) volume

/-! ## Elementary norm facts -/

/-- The Frobenius norm is nonnegative. -/
theorem hessNorm_nonneg (D2 : Fin d → Fin d → PS d → ℝ) (X : PS d) : 0 ≤ hessNorm D2 X :=
  Real.sqrt_nonneg _

/-- The Frobenius norm is at most the sum of the absolute values of the entries. -/
theorem hessNorm_le (D2 : Fin d → Fin d → PS d → ℝ) (X : PS d) :
    hessNorm D2 X ≤ ∑ i, ∑ j, |D2 i j X| := by
  unfold hessNorm
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ i, ∑ j, D2 i j X ^ 2 ≤ ∑ i, (∑ j, |D2 i j X|) ^ 2 := by
        gcongr with i
        calc ∑ j, D2 i j X ^ 2 = ∑ j, |D2 i j X| ^ 2 := by simp only [sq_abs]
          _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg _)
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => by positivity)

/-- `L^p` triangle inequality for a finite sum of `d` functions with a common bound. -/
theorem eLpNorm_sum_le_card_mul {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ι : Type*} [Fintype ι] {f : ι → PS d → E}
    (hm : ∀ i, AEStronglyMeasurable (f i) volume) {B : ℝ≥0∞}
    (hb : ∀ i, eLpNorm (f i) p volume ≤ B) :
    eLpNorm (fun X => ∑ i, f i X) p volume ≤ Fintype.card ι * B := by
  have hfun : (fun X => ∑ i, f i X) = ∑ i, f i := by
    funext X; rw [Finset.sum_apply]
  rw [hfun]
  calc eLpNorm (∑ i, f i) p volume ≤ ∑ i, eLpNorm (f i) p volume :=
        eLpNorm_sum_le (fun i _ => hm i) hp
    _ ≤ ∑ _i : ι, B := by gcongr with i; exact hb i
    _ = Fintype.card ι * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `‖ν |D_x² u|‖_p ≤ Σ_{i,j} ‖ν ∂_i∂_j u‖_p`. -/
theorem eLpNorm_hessNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) {ν : ℝ} (hν : 0 ≤ ν)
    {D2 : Fin d → Fin d → PS d → ℝ} (hm : ∀ i j, AEStronglyMeasurable (D2 i j) volume) :
    eLpNorm (fun X => ν * hessNorm D2 X) p volume ≤
      ∑ i, ∑ j, eLpNorm (fun X => ν * D2 i j X) p volume := by
  have hmn : ∀ i j, AEStronglyMeasurable (fun X => ‖ν * D2 i j X‖) volume :=
    fun i j => ((hm i j).const_mul ν).norm
  calc eLpNorm (fun X => ν * hessNorm D2 X) p volume
      ≤ eLpNorm (fun X => ∑ i, ∑ j, ‖ν * D2 i j X‖) p volume := by
        refine eLpNorm_mono_real fun X => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hν (hessNorm_nonneg D2 X))]
        calc ν * hessNorm D2 X ≤ ν * ∑ i, ∑ j, |D2 i j X| :=
              mul_le_mul_of_nonneg_left (hessNorm_le D2 X) hν
          _ = ∑ i, ∑ j, ‖ν * D2 i j X‖ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hν]
    _ = eLpNorm (∑ i, ∑ j, fun X => ‖ν * D2 i j X‖) p volume := by
        congr 1; funext X; simp only [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (∑ j, fun X => ‖ν * D2 i j X‖) p volume :=
        eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ => hmn i j) hp
    _ ≤ ∑ i, ∑ j, eLpNorm (fun X => ‖ν * D2 i j X‖) p volume := by
        gcongr with i
        exact eLpNorm_sum_le (fun j _ => hmn i j) hp
    _ = ∑ i, ∑ j, eLpNorm (fun X => ν * D2 i j X) p volume := by
        simp only [eLpNorm_norm]

/-! ## The real-valued estimate -/

/-- **eq:free-stress-11, componentwise** (`paper/main.tex` lines 7452–7461, blueprint unit
B0423; INF02 T8): for `1 < q < ∞` there is `C = C(d, q)` such that for every `ν > 0` and all
`u, F ∈ L^q(ℝ × ℝ^d)` with `(∂_θ - νΔ_x)u = F` in distributions, `u` has weak derivatives
`∂_i∂_j u, ∂_θ u ∈ L^q` with `‖ν ∂_i∂_j u‖_q ≤ C ‖F‖_q` for all `i, j` and
`‖∂_θ u‖_q ≤ C ‖F‖_q`. Neither `d ≥ 1` nor compact time support is needed. This is
`Parabolic.heat_maximal_regularity` (`Lib/ParabolicB`) in the vocabulary of this unit. -/
theorem heat_estimate_componentwise {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℝ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      IsWeakHeatSol ν u F →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧ HasWeakSpaceDeriv2 u i j (D2 i j)) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDeriv u Dt ∧
        (∀ i j, eLpNorm (fun X => ν * D2 i j X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume) ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := UnforcedLeray.Parabolic.heat_maximal_regularity (d := d) hq
  exact ⟨C, fun ν hν u F hu hF heq => hC hν hu hF heq⟩

/-- **eq:free-stress-11 with the Frobenius norm of the Hessian, without the unused hypotheses**
(`paper/main.tex` lines 7452–7461, blueprint unit B0423): the conclusion of `FreeStress11` for
every `d` and without compact time support of `u`. -/
theorem heat_estimate {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℝ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      IsWeakHeatSol ν u F →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧ HasWeakSpaceDeriv2 u i j (D2 i j)) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDeriv u Dt ∧
        eLpNorm (fun X => ν * hessNorm D2 X) (ENNReal.ofReal q) volume +
            eLpNorm Dt (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := heat_estimate_componentwise (d := d) hq
  refine ⟨(d : ℝ≥0) * d * C + C, fun ν hν u F hu hF heq => ?_⟩
  obtain ⟨D2, Dt, hD2, hDt, hDtw, hb, hbt⟩ := hC ν hν u F hu hF heq
  refine ⟨D2, Dt, hD2, hDt, hDtw, ?_⟩
  have hq1 := UnforcedLeray.Parabolic.one_le_ofReal_of_one_lt hq
  have hH := eLpNorm_hessNorm_le hq1 hν.le (fun i j => (hD2 i j).1.1)
  have hS : ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun X => ν * D2 i j X) (ENNReal.ofReal q) volume ≤
      ∑ _i : Fin d, ∑ _j : Fin d, (C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
    gcongr with i _ j _
    exact hb i j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  calc eLpNorm (fun X => ν * hessNorm D2 X) (ENNReal.ofReal q) volume +
        eLpNorm Dt (ENNReal.ofReal q) volume
      ≤ (d : ℝ≥0∞) * ((d : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume)) +
          (C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := add_le_add (hH.trans hS) hbt
    _ = (((d : ℝ≥0) * d * C + C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
        push_cast; ring

/-- **The unit B0423: eq:free-stress-11** (`paper/main.tex` lines 7452–7461; proof 7463–7477):
for `d ≥ 1` and `1 < q < ∞`, `FreeStress11 d q` holds. The constant is independent of `ν`. -/
theorem freeStress11 {q : ℝ} (_hd : 1 ≤ d) (hq : 1 < q) : FreeStress11 d q := by
  obtain ⟨C, hC⟩ := heat_estimate (d := d) hq
  exact ⟨C, fun ν hν u F hu hF _ heq => hC ν hν u F hu hF heq⟩

/-- **The Laplacian form of eq:free-stress-11** (`paper/main.tex` lines 7452–7461, as used at
line 7510 for `‖νΔw‖_q`, blueprint units B0423, B0424): with the derivatives of
`heat_estimate_componentwise`, `‖ν Δ_x u‖_q ≤ C ‖F‖_q`, `Δ_x u = Σ_i ∂_i∂_i u`. -/
theorem heat_estimate_laplacian {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℝ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      IsWeakHeatSol ν u F →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧ HasWeakSpaceDeriv2 u i j (D2 i j)) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDeriv u Dt ∧
        eLpNorm (fun X => ν * ∑ i, D2 i i X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := heat_estimate_componentwise (d := d) hq
  refine ⟨(d : ℝ≥0) * C + C, fun ν hν u F hu hF heq => ?_⟩
  obtain ⟨D2, Dt, hD2, hDt, hDtw, hb, hbt⟩ := hC ν hν u F hu hF heq
  refine ⟨D2, Dt, hD2, hDt, hDtw, ?_, ?_⟩
  · have hq1 := UnforcedLeray.Parabolic.one_le_ofReal_of_one_lt hq
    have hfun : (fun X => ν * ∑ i, D2 i i X) = fun X => ∑ i, ν * D2 i i X := by
      funext X; rw [Finset.mul_sum]
    rw [hfun]
    refine (eLpNorm_sum_le_card_mul hq1 (fun i => (hD2 i i).1.1.const_mul ν)
      (fun i => hb i i)).trans ?_
    rw [Fintype.card_fin]
    calc (d : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume)
        = (((d : ℝ≥0) * C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          push_cast; ring
      _ ≤ (((d : ℝ≥0) * C + C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          gcongr; exact le_self_add
  · refine hbt.trans ?_
    gcongr
    exact le_add_self

/-! ## Complex-valued fields

The manuscript's fields are complex (`Y_q` is a space of `ℂ³`-valued fields), and B0424 applies
eq:free-stress-11 to them componentwise. The tests stay real; the complex statement follows from
the real one applied to the real and imaginary parts. -/

/-- `(∂_θ - νΔ_x)u = F` in distributions for complex `u, F` (`paper/main.tex` line 7455,
blueprint B0423), tested against real tests. -/
def IsWeakHeatSolC (ν : ℝ) (u F : PS d → ℂ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ →
    ∫ X, u X * ((-tD φ X - ν * sLap φ X : ℝ) : ℂ) = ∫ X, F X * (φ X : ℂ)

/-- `D = ∂_{x_i}∂_{x_j} u` in distributions for complex `u` (blueprint B0423). -/
def HasWeakSpaceDeriv2C (u : PS d → ℂ) (i j : Fin d) (D : PS d → ℂ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * (sD2 i j φ X : ℂ) = ∫ X, D X * (φ X : ℂ)

/-- `Dt = ∂_θ u` in distributions for complex `u` (blueprint B0423). -/
def HasWeakTimeDerivC (u Dt : PS d → ℂ) : Prop :=
  ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * (tD φ X : ℂ) = -∫ X, Dt X * (φ X : ℂ)

/-- The adjoint heat operator maps tests to tests. -/
theorem isSTTest_heatAdj {φ : PS d → ℝ} (hφ : IsSTTest φ) (ν : ℝ) :
    IsSTTest (fun X => -tD φ X - ν * sLap φ X) := by
  have h := ((UnforcedLeray.Parabolic.isSTTest_tD hφ).smul (-1)).add
    ((UnforcedLeray.Parabolic.isSTTest_sLap hφ).smul (-ν))
  convert h using 1
  funext X
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- Integral of `f + g i` for real integrable `f, g`. -/
theorem integral_ofReal_add_mul_I {f g : PS d → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) :
    ∫ X, ((f X : ℂ) + (g X : ℂ) * I) = ((∫ X, f X : ℝ) : ℂ) + ((∫ X, g X : ℝ) : ℂ) * I := by
  have h1 : Integrable (fun X => (f X : ℂ)) volume := hf.ofReal
  have h2 : Integrable (fun X => (g X : ℂ) * I) volume := (hg.ofReal (𝕜 := ℂ)).mul_const I
  rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- Splitting `∫ u g` into real and imaginary parts, for complex `u ∈ L^q` and a real test `g`. -/
theorem integral_mul_ofReal_eq {q : ℝ} (hq : 1 < q) {u : PS d → ℂ}
    (hu : MemLp u (ENNReal.ofReal q) volume) {g : PS d → ℝ} (hg : IsSTTest g) :
    ∫ X, u X * (g X : ℂ) =
      ((∫ X, (u X).re * g X : ℝ) : ℂ) + ((∫ X, (u X).im * g X : ℝ) : ℂ) * I := by
  have h1 : Integrable (fun X => (u X).re * g X) volume :=
    UnforcedLeray.Parabolic.integrable_mul_test_of_memLp hq hu.re hg
  have h2 : Integrable (fun X => (u X).im * g X) volume :=
    UnforcedLeray.Parabolic.integrable_mul_test_of_memLp hq hu.im hg
  have hpt : ∀ X, u X * (g X : ℂ) =
      (((u X).re * g X : ℝ) : ℂ) + (((u X).im * g X : ℝ) : ℂ) * I := by
    intro X
    conv_lhs => rw [← Complex.re_add_im (u X)]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_ofReal_add_mul_I h1 h2]

/-- Real and imaginary parts of `a + b i` determine `a, b`. -/
theorem ofReal_add_mul_I_inj {a b a' b' : ℝ}
    (h : (a : ℂ) + (b : ℂ) * I = (a' : ℂ) + (b' : ℂ) * I) : a = a' ∧ b = b' := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- The real and imaginary parts of a complex distributional heat solution are real ones. -/
theorem isWeakHeatSol_re_im {q ν : ℝ} (hq : 1 < q) {u F : PS d → ℂ}
    (hu : MemLp u (ENNReal.ofReal q) volume) (hF : MemLp F (ENNReal.ofReal q) volume)
    (h : IsWeakHeatSolC ν u F) :
    IsWeakHeatSol ν (fun X => (u X).re) (fun X => (F X).re) ∧
      IsWeakHeatSol ν (fun X => (u X).im) (fun X => (F X).im) := by
  have key : ∀ φ : PS d → ℝ, IsSTTest φ →
      (∫ X, (u X).re * (-tD φ X - ν * sLap φ X) = ∫ X, (F X).re * φ X) ∧
      (∫ X, (u X).im * (-tD φ X - ν * sLap φ X) = ∫ X, (F X).im * φ X) := by
    intro φ hφ
    have e := h φ hφ
    have e1 := integral_mul_ofReal_eq hq hu (isSTTest_heatAdj hφ ν)
    have e2 := integral_mul_ofReal_eq hq hF hφ
    beta_reduce at e1
    rw [e1, e2] at e
    exact ofReal_add_mul_I_inj e
  exact ⟨fun φ hφ => (key φ hφ).1, fun φ hφ => (key φ hφ).2⟩

/-- `|a + b i| ≤ |a| + |b|`. -/
theorem norm_ofReal_add_mul_I_le (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * I‖ ≤ ‖a‖ + ‖b‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]

/-- `‖a + b i‖_p ≤ ‖a‖_p + ‖b‖_p` for real `a, b`. -/
theorem eLpNorm_ofReal_add_mul_I_le {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : PS d → ℝ}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    eLpNorm (fun X => (a X : ℂ) + (b X : ℂ) * I) p volume ≤
      eLpNorm a p volume + eLpNorm b p volume := by
  calc eLpNorm (fun X => (a X : ℂ) + (b X : ℂ) * I) p volume
      ≤ eLpNorm (fun X => ‖a X‖ + ‖b X‖) p volume :=
        eLpNorm_mono_real fun X => norm_ofReal_add_mul_I_le (a X) (b X)
    _ ≤ eLpNorm (fun X => ‖a X‖) p volume + eLpNorm (fun X => ‖b X‖) p volume :=
        eLpNorm_add_le ha.norm hb.norm hp
    _ = eLpNorm a p volume + eLpNorm b p volume := by rw [eLpNorm_norm, eLpNorm_norm]

/-- `‖Re F‖_p ≤ ‖F‖_p`. -/
theorem eLpNorm_re_le {p : ℝ≥0∞} (F : PS d → ℂ) :
    eLpNorm (fun X => (F X).re) p volume ≤ eLpNorm F p volume :=
  eLpNorm_mono fun X => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _

/-- `‖Im F‖_p ≤ ‖F‖_p`. -/
theorem eLpNorm_im_le {p : ℝ≥0∞} (F : PS d → ℂ) :
    eLpNorm (fun X => (F X).im) p volume ≤ eLpNorm F p volume :=
  eLpNorm_mono fun X => by rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _

/-- `a + b i ∈ L^p` for real `a, b ∈ L^p`. -/
theorem memLp_ofReal_add_mul_I {p : ℝ≥0∞} {a b : PS d → ℝ} (ha : MemLp a p volume)
    (hb : MemLp b p volume) : MemLp (fun X => (a X : ℂ) + (b X : ℂ) * I) p volume := by
  have h1 : MemLp (fun X => (a X : ℂ)) p volume := ha.ofReal
  have h2 : MemLp (fun X => (b X : ℂ) * I) p volume := (hb.ofReal (K := ℂ)).mul_const I
  exact h1.add h2

/-- Splitting `∫ (a + b i) φ` for real `a, b ∈ L^q` and a real test `φ`. -/
theorem integral_ofReal_add_mul_I_mul {q : ℝ} (hq : 1 < q) {a b : PS d → ℝ}
    (ha : MemLp a (ENNReal.ofReal q) volume) (hb : MemLp b (ENNReal.ofReal q) volume)
    {φ : PS d → ℝ} (hφ : IsSTTest φ) :
    ∫ X, ((a X : ℂ) + (b X : ℂ) * I) * (φ X : ℂ) =
      ((∫ X, a X * φ X : ℝ) : ℂ) + ((∫ X, b X * φ X : ℝ) : ℂ) * I := by
  have hpt : ∀ X, ((a X : ℂ) + (b X : ℂ) * I) * (φ X : ℂ) =
      ((a X * φ X : ℝ) : ℂ) + ((b X * φ X : ℝ) : ℂ) * I := by
    intro X; push_cast; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_ofReal_add_mul_I
    (UnforcedLeray.Parabolic.integrable_mul_test_of_memLp hq ha hφ)
    (UnforcedLeray.Parabolic.integrable_mul_test_of_memLp hq hb hφ)]

/-- Weak second derivatives of the real and imaginary parts give one of `u`. -/
theorem hasWeakSpaceDeriv2C_of_re_im {q : ℝ} (hq : 1 < q) {u : PS d → ℂ}
    (hu : MemLp u (ENNReal.ofReal q) volume) {i j : Fin d} {a b : PS d → ℝ}
    (ha : MemLp a (ENNReal.ofReal q) volume) (hb : MemLp b (ENNReal.ofReal q) volume)
    (haw : HasWeakSpaceDeriv2 (fun X => (u X).re) i j a)
    (hbw : HasWeakSpaceDeriv2 (fun X => (u X).im) i j b) :
    HasWeakSpaceDeriv2C u i j (fun X => (a X : ℂ) + (b X : ℂ) * I) := by
  intro φ hφ
  have e1 := integral_mul_ofReal_eq hq hu (hφ.sD2 i j)
  have e2 := integral_ofReal_add_mul_I_mul hq ha hb hφ
  have e3 : ∫ X, (u X).re * sD2 i j φ X = ∫ X, a X * φ X := haw φ hφ
  have e4 : ∫ X, (u X).im * sD2 i j φ X = ∫ X, b X * φ X := hbw φ hφ
  rw [e1, e2, e3, e4]

/-- Weak time derivatives of the real and imaginary parts give one of `u`. -/
theorem hasWeakTimeDerivC_of_re_im {q : ℝ} (hq : 1 < q) {u : PS d → ℂ}
    (hu : MemLp u (ENNReal.ofReal q) volume) {a b : PS d → ℝ}
    (ha : MemLp a (ENNReal.ofReal q) volume) (hb : MemLp b (ENNReal.ofReal q) volume)
    (haw : HasWeakTimeDeriv (fun X => (u X).re) a)
    (hbw : HasWeakTimeDeriv (fun X => (u X).im) b) :
    HasWeakTimeDerivC u (fun X => (a X : ℂ) + (b X : ℂ) * I) := by
  intro φ hφ
  have e1 := integral_mul_ofReal_eq hq hu (UnforcedLeray.Parabolic.isSTTest_tD hφ)
  have e2 := integral_ofReal_add_mul_I_mul hq ha hb hφ
  have e3 : ∫ X, (u X).re * tD φ X = -∫ X, a X * φ X := haw φ hφ
  have e4 : ∫ X, (u X).im * tD φ X = -∫ X, b X * φ X := hbw φ hφ
  rw [e1, e2, e3, e4]
  push_cast
  ring

/-- `‖ν (a + b i)‖_p ≤ ‖ν a‖_p + ‖ν b‖_p`. -/
theorem eLpNorm_smul_ofReal_add_mul_I_le {p : ℝ≥0∞} (hp : 1 ≤ p) (ν : ℝ) {a b : PS d → ℝ}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    eLpNorm (fun X => (ν : ℂ) * ((a X : ℂ) + (b X : ℂ) * I)) p volume ≤
      eLpNorm (fun X => ν * a X) p volume + eLpNorm (fun X => ν * b X) p volume := by
  have hfun : (fun X => (ν : ℂ) * ((a X : ℂ) + (b X : ℂ) * I)) =
      fun X => ((ν * a X : ℝ) : ℂ) + ((ν * b X : ℝ) : ℂ) * I := by
    funext X; push_cast; ring
  rw [hfun]
  exact eLpNorm_ofReal_add_mul_I_le hp (ha.const_mul ν) (hb.const_mul ν)

/-- `a + b ≤ 2C N` from `a, b ≤ C N`. -/
theorem add_le_two_mul {C : ℝ≥0} {N a b : ℝ≥0∞} (ha : a ≤ C * N) (hb : b ≤ C * N) :
    a + b ≤ ((2 * C : ℝ≥0) : ℝ≥0∞) * N := by
  calc a + b ≤ (C : ℝ≥0∞) * N + (C : ℝ≥0∞) * N := add_le_add ha hb
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * N := by push_cast; ring

/-- **eq:free-stress-11 for complex fields, componentwise** (`paper/main.tex` lines 7452–7461,
blueprint unit B0423, in the form B0424 applies at line 7510 to the components of a complex
`Y_q` field): for `1 < q < ∞` there is `C = C(d, q)` such that for every `ν > 0` and all
complex `u, F ∈ L^q(ℝ × ℝ^d)` with `(∂_θ - νΔ_x)u = F` in distributions, `u` has weak
derivatives `∂_i∂_j u, ∂_θ u ∈ L^q` with `‖ν ∂_i∂_j u‖_q ≤ C ‖F‖_q` and `‖∂_θ u‖_q ≤ C ‖F‖_q`. -/
theorem heat_estimate_complex {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℂ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      IsWeakHeatSolC ν u F →
      ∃ D2 : Fin d → Fin d → PS d → ℂ, ∃ Dt : PS d → ℂ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
          HasWeakSpaceDeriv2C u i j (D2 i j)) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDerivC u Dt ∧
        (∀ i j, eLpNorm (fun X => (ν : ℂ) * D2 i j X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume) ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := heat_estimate_componentwise (d := d) hq
  refine ⟨2 * C, fun ν hν u F hu hF heq => ?_⟩
  have hq1 := UnforcedLeray.Parabolic.one_le_ofReal_of_one_lt hq
  obtain ⟨hre, him⟩ := isWeakHeatSol_re_im hq hu hF heq
  have hur : MemLp (fun X => (u X).re) (ENNReal.ofReal q) volume := hu.re
  have hui : MemLp (fun X => (u X).im) (ENNReal.ofReal q) volume := hu.im
  have hFr : MemLp (fun X => (F X).re) (ENNReal.ofReal q) volume := hF.re
  have hFi : MemLp (fun X => (F X).im) (ENNReal.ofReal q) volume := hF.im
  obtain ⟨A, At, hA, hAt, hAtw, hAb, hAtb⟩ := hC ν hν _ _ hur hFr hre
  obtain ⟨B, Bt, hB, hBt, hBtw, hBb, hBtb⟩ := hC ν hν _ _ hui hFi him
  have hCr : (C : ℝ≥0∞) * eLpNorm (fun X => (F X).re) (ENNReal.ofReal q) volume ≤
      C * eLpNorm F (ENNReal.ofReal q) volume :=
    mul_le_mul_of_nonneg_left (eLpNorm_re_le F) zero_le
  have hCi : (C : ℝ≥0∞) * eLpNorm (fun X => (F X).im) (ENNReal.ofReal q) volume ≤
      C * eLpNorm F (ENNReal.ofReal q) volume :=
    mul_le_mul_of_nonneg_left (eLpNorm_im_le F) zero_le
  refine ⟨fun i j X => (A i j X : ℂ) + (B i j X : ℂ) * I, fun X => (At X : ℂ) + (Bt X : ℂ) * I,
    fun i j => ⟨memLp_ofReal_add_mul_I (hA i j).1 (hB i j).1,
      hasWeakSpaceDeriv2C_of_re_im hq hu (hA i j).1 (hB i j).1 (hA i j).2 (hB i j).2⟩,
    memLp_ofReal_add_mul_I hAt hBt, hasWeakTimeDerivC_of_re_im hq hu hAt hBt hAtw hBtw,
    fun i j => ?_, ?_⟩
  · exact (eLpNorm_smul_ofReal_add_mul_I_le hq1 ν (hA i j).1.1 (hB i j).1.1).trans
      (add_le_two_mul ((hAb i j).trans hCr) ((hBb i j).trans hCi))
  · exact (eLpNorm_ofReal_add_mul_I_le hq1 hAt.1 hBt.1).trans
      (add_le_two_mul (hAtb.trans hCr) (hBtb.trans hCi))

/-- **The Laplacian form for complex fields** (`paper/main.tex` line 7510, blueprint units
B0423, B0424): with the derivatives of `heat_estimate_complex`, `‖ν Δ_x u‖_q ≤ C ‖F‖_q`. -/
theorem heat_estimate_complex_laplacian {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℂ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      IsWeakHeatSolC ν u F →
      ∃ D2 : Fin d → Fin d → PS d → ℂ, ∃ Dt : PS d → ℂ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
          HasWeakSpaceDeriv2C u i j (D2 i j)) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧ HasWeakTimeDerivC u Dt ∧
        eLpNorm (fun X => (ν : ℂ) * ∑ i, D2 i i X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := heat_estimate_complex (d := d) hq
  refine ⟨(d : ℝ≥0) * C + C, fun ν hν u F hu hF heq => ?_⟩
  obtain ⟨D2, Dt, hD2, hDt, hDtw, hb, hbt⟩ := hC ν hν u F hu hF heq
  refine ⟨D2, Dt, hD2, hDt, hDtw, ?_, ?_⟩
  · have hq1 := UnforcedLeray.Parabolic.one_le_ofReal_of_one_lt hq
    have hfun : (fun X => (ν : ℂ) * ∑ i, D2 i i X) = fun X => ∑ i, (ν : ℂ) * D2 i i X := by
      funext X; rw [Finset.mul_sum]
    rw [hfun]
    refine (eLpNorm_sum_le_card_mul hq1 (fun i => (hD2 i i).1.1.const_mul (ν : ℂ))
      (fun i => hb i i)).trans ?_
    rw [Fintype.card_fin]
    calc (d : ℝ≥0∞) * ((C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume)
        = (((d : ℝ≥0) * C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          push_cast; ring
      _ ≤ (((d : ℝ≥0) * C + C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          gcongr; exact le_self_add
  · refine hbt.trans ?_
    gcongr
    exact le_add_self

end UnforcedLeray.B0423
