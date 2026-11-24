import UnforcedLeray.Loc.L03Evolution.Abstract
import UnforcedLeray.Loc.L03Evolution.ZBound
import UnforcedLeray.Loc.L03Evolution.ZContinuity

/-!
# Step L8, forward smoothing: `τ ↦ E_Z(τ,σ) y` is continuous in `Z = H²_div`

Helper for `UnforcedLeray.Loc.L08Green` (step `GreenStep`, `paper/main.tex` lines 406–428,
blueprint units B1018–B1020).

The manuscript's `𝒵_β` (line 406) consists of continuous `Z`-valued functions, so the Green
operator `𝓡_β f` (lines 410–414) must be continuous in `Z`. Its kernels are built from the
smoothing `E_Z(τ,s) : X → Z` of the evolution of L3 (lines 299–306, unit B0713), and the
clauses of `IsEvolution` give `E_Z` only through `ι_Z E_Z(τ,s) = E(τ,s)` and its size
`C (τ-s)^{-1/2}`. This file proves, for *every* evolution satisfying `IsEvolution`, that
`τ ↦ E_Z(τ,σ) y` is continuous on `(σ, ∞)` in the `H²` norm
(`continuousOn_EZ_of_isEvolution`).

Proof (line 300, "Volterra iteration with `loc:eq:coefficient-maps`"):
* the `Z`-level Volterra problem with free part `S₀|_Z`, smoothing `S₀ : X → Z` and
  coefficient `𝓑_* : Z → X` has a strongly continuous evolution `E^Z(τ,s)` on `Z`
  (`Infra/VolterraEvolution`, `continuousOn_evolution`); its data are the ones of

  `zVolterra`), with the `Z`-bound and `Z`-continuity of `S₀` proved in
  `Loc/L03Evolution/ZBound.lean` and `Loc/L03Evolution/ZContinuity.lean`;
* `ι_Z E^Z(τ,s) = E^X(τ,s) ι_Z` for the `X`-level Volterra evolution `E^X`
  (`Loc/L03Evolution/Abstract.lean`, `intertwine`);
* the given `E` equals `E^X` (uniqueness, `VolterraData.eq_evolution_of_volterra`, from the
  Duhamel formula, the evolution law and the strong continuity in `IsEvolution`);
* for `σ < r < τ`, `ι_Z E_Z(τ,σ) y = E(τ,r) ι_Z E_Z(r,σ) y = ι_Z E^Z(τ,r) E_Z(r,σ) y`, so
  `E_Z(τ,σ) y = E^Z(τ,r) E_Z(r,σ) y` by injectivity of `ι_Z`, continuous in `τ ≥ r`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Blueprint.L08Green

open UnforcedLeray.Blueprint UnforcedLeray.Infra.VolterraEvolution
open UnforcedLeray.Loc.L03Evolution (S0ZZ S0ZZ_of_pos S0ZZ_of_nonpos free_bounds
  exists_norm_le_of_periodic exists_norm_S0Z_comp_ιZ_le tendsto_S0Z_of_bound continuousOn_S0ZZ
  continuousOn_S0L continuousOn_S0Z S0_comp_S0 S0_comp_S0L S0ZZ_comp_S0ZZ S0ZZ_comp_S0Z
  ιZ_S0ZZ ιZ_comp_S0Z S0L_comp_ιX intertwine)

/-- The Volterra data on `X = H¹_div` (line 300): `S₀`, `S₀ : L²_div → X`, `𝓑_* : X → L²_div`.
-/
def xVolterra (S : FreeEvolution) (c : Coefficients) (C β : ℝ)
    (hS0 : ∀ t, 0 ≤ t → t ≤ 1 → ‖S.S0 t‖ ≤ C)
    (hS0L : ∀ t, 0 < t → t ≤ 1 → ‖S.S0L t‖ ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hB : ∀ t, ‖c.B t‖ ≤ β)
    (hcS0 : ∀ x, ContinuousOn (fun t => S.S0 t x) (Icc 0 1))
    (hcS0L : ∀ y, ContinuousOn (fun t => S.S0L t y) (Ioc 0 1))
    (hcB : ∀ x, Continuous (fun t => c.B t x)) : VolterraData ℝ X L2div where
  S₀ := S.S0
  S := S.S0L
  B := c.B
  M₀ := C
  C₀ := C
  β := β
  norm_S₀_le := hS0
  norm_S_le := hS0L
  norm_B_le := hB
  continuousOn_S₀ := hcS0
  continuousOn_S := hcS0L
  continuous_B := hcB

/-- The Volterra data on `Z = H²_div` (line 300, `loc:eq:coefficient-maps`): `S₀|_Z`,
`S₀ : X → Z`, `𝓑_* : Z → X`. Copied from `zData` in
-/
def zVolterra (S : FreeEvolution) (c : Coefficients) (M C β : ℝ)
    (hS0 : ∀ t, 0 ≤ t → t ≤ 1 → ‖S0ZZ S t‖ ≤ M)
    (hS0Z : ∀ t, 0 < t → t ≤ 1 → ‖S.S0Z t‖ ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hB : ∀ t, ‖c.BZ t‖ ≤ β)
    (hcS0 : ∀ g, ContinuousOn (fun t => S0ZZ S t g) (Icc 0 1))
    (hcS0Z : ∀ y, ContinuousOn (fun t => S.S0Z t y) (Ioc 0 1))
    (hcB : ∀ g, Continuous (fun t => c.BZ t g)) : VolterraData ℝ Z X where
  S₀ := S0ZZ S
  S := S.S0Z
  B := c.BZ
  M₀ := M
  C₀ := C
  β := β
  norm_S₀_le := hS0
  norm_S_le := hS0Z
  norm_B_le := hB
  continuousOn_S₀ := hcS0
  continuousOn_S := hcS0Z
  continuous_B := hcB

/-- **Forward smoothing is continuous into `Z = H²_div`** (lines 299–306 and 406; units B0713,
B1018, B1020). For `h > 0`, `𝒯 > 0`, coefficients, free evolution and evolution with the
characterizations of L1–L3, `τ ↦ E_Z(τ,σ) y` is continuous on `(σ, ∞)` in the `H²` norm,
for every `σ` and `y ∈ X`. -/
theorem continuousOn_EZ_of_isEvolution {D : BackgroundData} {c : Coefficients}
    {S : FreeEvolution} {ev : Evolution} (hh : 0 < D.h) (hP : 0 < D.period)
    (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev)
    (σ : ℝ) (y : X) : ContinuousOn (fun τ => ev.EZ τ σ y) (Ioi σ) := by
  obtain ⟨C, -, hS0, hS0L, hS0Z⟩ := free_bounds hS
  obtain ⟨β, hβ⟩ := exists_norm_le_of_periodic hP.ne' hc.B_periodic hc.B_continuous
  obtain ⟨βZ, hβZ⟩ := exists_norm_le_of_periodic hP.ne' hc.BZ_periodic hc.BZ_continuous
  obtain ⟨CZ, hCZ⟩ := exists_norm_S0Z_comp_ιZ_le hS
  have hZZ : ∀ t, 0 ≤ t → t ≤ 1 → ‖S0ZZ S t‖ ≤ max CZ 1 := by
    intro t ht ht1
    rcases eq_or_lt_of_le ht with h0 | hpos
    · rw [← h0, S0ZZ_of_nonpos S le_rfl]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
    · rw [S0ZZ_of_pos S hpos]
      exact (hCZ t hpos ht1).trans (le_max_left _ _)
  set V := xVolterra S c C β (fun t ht _ => hS0 t ht) hS0L hβ
    (fun x => (hS.strongly_continuous x).mono Icc_subset_Ici_self)
    (fun y => (continuousOn_S0L hS hh.le y).mono fun t ht => ht.1)
    (fun x => hc.B_continuous.clm_apply continuous_const) with hV
  set VZ := zVolterra S c (max CZ 1) C βZ hZZ hS0Z hβZ
    (continuousOn_S0ZZ hS hh.le (tendsto_S0Z_of_bound hS hh.le ⟨CZ, hCZ⟩))
    (fun y => (continuousOn_S0Z hS hh.le y).mono fun t ht => ht.1)
    (fun g => hc.BZ_continuous.clm_apply continuous_const) with hVZ
  have hVc : V.Compatible :=
    ⟨fun a b ha hb _ => S0_comp_S0 hS hh.le ha hb,
      fun a b ha hb _ => S0_comp_S0L hS hh.le ha hb⟩
  have hZc : VZ.Compatible :=
    ⟨fun a b ha hb _ => S0ZZ_comp_S0ZZ hS hh.le ha hb,
      fun a b ha hb _ => S0ZZ_comp_S0Z hS hh.le ha hb⟩
  -- the `Z`-level evolution is `E^X` on `Z`
  have hint : ∀ s τ, s ≤ τ → ∀ g, ιZ (VZ.evolution τ s g) = V.evolution τ s (ιZ g) := by
    refine intertwine VZ hZc V hVc ιZ (fun t ht _ w => ?_) (fun t r ht _ w => ?_)
    · exact ιZ_S0ZZ hS ht w
    · show ιZ (S.S0Z t (c.BZ r w)) = S.S0L t (c.B r (ιZ w))
      rw [← hc.BZ_compat r w, ← ContinuousLinearMap.comp_apply ιZ,
        ιZ_comp_S0Z hS ht, ← ContinuousLinearMap.comp_apply (S.S0L t), S0L_comp_ιX hS ht]
  -- the given evolution is `E^X` (uniqueness of the Volterra evolution)
  have hEV : ∀ s τ, s ≤ τ → ev.E τ s = V.evolution τ s := by
    refine VolterraData.eq_evolution_of_volterra hVc ev.E (fun s x => ?_)
      (fun s τ hτ x => ?_) hev.law
    · have hm : ContinuousOn (fun τ : ℝ => ((τ, s) : ℝ × ℝ)) (Icc s (s + 1)) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact (hev.strongly_continuous x).comp hm (fun τ hτ => hτ.1)
    · show ev.E τ s x = S.S0 (τ - s) x + ∫ r in s..τ, S.S0L (τ - r) (c.B r (ev.E r s x))
      rw [intervalIntegral.integral_of_le hτ.1, integral_Ioc_eq_integral_Ioo]
      exact hev.duhamel s τ hτ.1 x
  intro τ₁ hτ₁
  have hστ₁ : σ < τ₁ := hτ₁
  have hσr : σ < (σ + τ₁) / 2 := by linarith
  have hrτ₁ : (σ + τ₁) / 2 < τ₁ := by linarith
  set r := (σ + τ₁) / 2 with hr
  set g := ev.EZ r σ y with hg
  have heq : ∀ τ, r < τ → ev.EZ τ σ y = VZ.evolution τ r g := by
    intro τ hτ
    apply UnforcedLeray.Loc.L03Evolution.ιZ_injective
    rw [hint r τ hτ.le g, ← hEV r τ hτ.le]
    calc ιZ (ev.EZ τ σ y) = ev.E τ σ y := DFunLike.congr_fun (hev.EZ_compat σ τ (hσr.trans hτ)) y
      _ = ev.E τ r (ev.E r σ y) := (DFunLike.congr_fun (hev.law σ r τ hσr.le hτ.le) y).symm
      _ = ev.E τ r (ιZ g) := by
        rw [hg]
        exact congrArg (ev.E τ r) (DFunLike.congr_fun (hev.EZ_compat σ r hσr) y).symm
  have hcont : ContinuousAt (fun τ => VZ.evolution τ r g) τ₁ :=
    (VolterraData.continuousOn_evolution hZc r g).continuousAt (Ici_mem_nhds hrτ₁)
  refine (hcont.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds hrτ₁] with τ hτ
  exact (heq τ hτ).symm

end UnforcedLeray.Blueprint.L08Green
