import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Minkowski's inequality for mixed norms, and phase translations (INF22 A3)

Blueprint infrastructure target **INF22 A3** of the scoping note

uses in §2.3). The manuscript bounds `L²_τ L^a_y` norms of superpositions
`∫ F_r(τ, y) dρ(r)` ("Minkowski in normalized phase and invariance under phase translations",
`paper/main.tex` 8950–8958, unit B0558; also 10338–10368, B0759; the mixed-norm Minkowski
`L^{q*}_{x'} L¹_z` of 9236–9245, B0740). This file provides, for the mixed norm
`mixedNorm q a μ ν F = ‖τ ↦ ‖F(τ, ·)‖_{L^a(ν)}‖_{L^q(μ)}`:

* `mixedNorm_lintegral_le` (`[0,∞]`-valued) and `mixedNorm_integral_le` (Bochner, the
  superposition `∫ F_r dρ(r)` taken pointwise in `(τ, y)`): Minkowski's integral inequality
  `‖∫ F_r dρ(r)‖_{L^q_τ L^a_y} ≤ ∫ ‖F_r‖_{L^q_τ L^a_y} dρ(r)` for `1 ≤ q, a < ∞`;
* `mixedNorm_integral_le_of_le`: the same with a per-`r` bound `‖F_r‖ ≤ c(r) M`;
* `mixedNorm_comp_add`: invariance under phase translations `τ ↦ τ + σ` for any
  translation-invariant measure on an abelian group, in particular `volume` and the normalized
  Haar measure `AddCircle.haarAddCircle` on `ℝ/Pℤ` (`mixedNorm_haarAddCircle_comp_add`);
* `mixedNorm_volume_eq`: `volume` on `ℝ/Pℤ` versus the normalized phase measure `dτ/P`
  (decision D2 of the scoping README uses `haarAddCircle`).

Minkowski's inequality is the vendored, compiled `NonUniqueEuler.Conv.eLpNorm_lintegral_le`
(`lean/NonUniqueEuler/P/Infra/ConvMinkowski/Minkowski.lean`).

**Conventions.** All norms are `eLpNorm`, valued in `[0,∞]`; no finiteness is assumed. In the
Bochner form, a non-integrable `r ↦ F_r(τ, y)` has the junk integral `0`, which only lowers the
left side: the proof goes through `‖∫ F‖ₑ ≤ ∫⁻ ‖F‖ₑ`. Joint measurability in `(r, τ, y)` is
assumed (strong measurability for the Bochner form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Conv

variable {T Y : Type*} [MeasurableSpace T] [MeasurableSpace Y]

/-- The mixed norm `‖F‖_{L^q_τ L^a_y} = ‖τ ↦ ‖F(τ, ·)‖_{L^a(ν)}‖_{L^q(μ)}` (INF22 A3). -/
def mixedNorm {ε : Type*} [ENorm ε] (q a : ℝ≥0∞) (μ : Measure T) (ν : Measure Y)
    (F : T → Y → ε) : ℝ≥0∞ :=
  eLpNorm (fun τ => eLpNorm (F τ) a ν) q μ

/-- Pointwise domination passes to mixed norms. -/
theorem mixedNorm_mono {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    [TopologicalSpace ε'] [ContinuousENorm ε'] {q a : ℝ≥0∞} {μ : Measure T} {ν : Measure Y}
    {F : T → Y → ε} {G : T → Y → ε'} (h : ∀ τ y, ‖F τ y‖ₑ ≤ ‖G τ y‖ₑ) :
    mixedNorm q a μ ν F ≤ mixedNorm q a μ ν G :=
  eLpNorm_mono_enorm fun τ => by
    rw [enorm_eq_self, enorm_eq_self]
    exact eLpNorm_mono_enorm (h τ)

/-! ### Minkowski for mixed norms -/

section Minkowski

variable {R : Type*} [MeasurableSpace R]

/-- **Minkowski's integral inequality for mixed norms**, `[0,∞]`-valued (INF22 A3): for
`1 ≤ q, a < ∞` and a jointly measurable `F : R → T → Y → [0,∞]`,
`‖∫⁻ F_r dρ(r)‖_{L^q_τ L^a_y} ≤ ∫⁻ ‖F_r‖_{L^q_τ L^a_y} dρ(r)`. -/
theorem mixedNorm_lintegral_le {μ : Measure T} {ν : Measure Y} {ρ : Measure R} [SigmaFinite μ]
    [SigmaFinite ν] [SigmaFinite ρ] {F : R → T → Y → ℝ≥0∞}
    (hF : Measurable fun z : R × T × Y => F z.1 z.2.1 z.2.2)
    {q a : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞) (ha : 1 ≤ a) (ha' : a ≠ ∞) :
    mixedNorm q a μ ν (fun τ y => ∫⁻ r, F r τ y ∂ρ) ≤ ∫⁻ r, mixedNorm q a μ ν (F r) ∂ρ := by
  have ha0 : a ≠ 0 := (lt_of_lt_of_le zero_lt_one ha).ne'
  have hin : ∀ τ, eLpNorm (fun y => ∫⁻ r, F r τ y ∂ρ) a ν ≤ ∫⁻ r, eLpNorm (F r τ) a ν ∂ρ := by
    intro τ
    have hm : Measurable (Function.uncurry fun (y : Y) (r : R) => F r τ y) :=
      hF.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
    exact NonUniqueEuler.Conv.eLpNorm_lintegral_le hm.aemeasurable ha ha'
  have hG : Measurable (Function.uncurry fun (τ : T) (r : R) => eLpNorm (F r τ) a ν) := by
    have h1 : Measurable fun z : (T × R) × Y => F z.1.2 z.1.1 z.2 ^ a.toReal :=
      (hF.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))).pow_const _
    have h3 : Measurable fun x : T × R => (∫⁻ y, F x.2 x.1 y ^ a.toReal ∂ν) ^ (1 / a.toReal) :=
      (h1.lintegral_prod_right' (ν := ν)).pow_const _
    convert h3 using 1
    funext x
    show eLpNorm (F x.2 x.1) a ν = _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal ha0 ha']
    simp only [enorm_eq_self]
  unfold mixedNorm
  calc eLpNorm (fun τ => eLpNorm (fun y => ∫⁻ r, F r τ y ∂ρ) a ν) q μ
      ≤ eLpNorm (fun τ => ∫⁻ r, eLpNorm (F r τ) a ν ∂ρ) q μ :=
        eLpNorm_mono_enorm fun τ => by
          rw [enorm_eq_self, enorm_eq_self]
          exact hin τ
    _ ≤ ∫⁻ r, eLpNorm (fun τ => eLpNorm (F r τ) a ν) q μ ∂ρ :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le (F := fun τ r => eLpNorm (F r τ) a ν)
          hG.aemeasurable hq hq'

/-- **Minkowski's integral inequality for mixed norms**, Bochner form (INF22 A3; "Minkowski in
normalized phase", `paper/main.tex` 8950–8958, B0558): for `1 ≤ q, a < ∞` and a jointly
strongly measurable `F : R → T → Y → E`,
`‖(τ, y) ↦ ∫ F_r(τ, y) dρ(r)‖_{L^q_τ L^a_y} ≤ ∫⁻ ‖F_r‖_{L^q_τ L^a_y} dρ(r)`. -/
theorem mixedNorm_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure T} {ν : Measure Y} {ρ : Measure R} [SigmaFinite μ] [SigmaFinite ν]
    [SigmaFinite ρ] {F : R → T → Y → E}
    (hF : StronglyMeasurable fun z : R × T × Y => F z.1 z.2.1 z.2.2)
    {q a : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞) (ha : 1 ≤ a) (ha' : a ≠ ∞) :
    mixedNorm q a μ ν (fun τ y => ∫ r, F r τ y ∂ρ) ≤ ∫⁻ r, mixedNorm q a μ ν (F r) ∂ρ := by
  calc mixedNorm q a μ ν (fun τ y => ∫ r, F r τ y ∂ρ)
      ≤ mixedNorm q a μ ν (fun τ y => ∫⁻ r, ‖F r τ y‖ₑ ∂ρ) :=
        mixedNorm_mono fun τ y =>
          (enorm_integral_le_lintegral_enorm _).trans_eq (enorm_eq_self _).symm
    _ ≤ ∫⁻ r, mixedNorm q a μ ν (fun τ y => ‖F r τ y‖ₑ) ∂ρ :=
        mixedNorm_lintegral_le (F := fun r τ y => ‖F r τ y‖ₑ) hF.enorm hq hq' ha ha'
    _ = ∫⁻ r, mixedNorm q a μ ν (F r) ∂ρ := by
        simp only [mixedNorm, eLpNorm_enorm]

/-- Minkowski for mixed norms with a per-`r` bound `‖F_r‖_{L^q_τ L^a_y} ≤ c(r) M`:
`‖∫ F_r dρ(r)‖_{L^q_τ L^a_y} ≤ (∫⁻ c dρ) M` (the shape of the dilation integrals of
`paper/main.tex` 8950–8958, B0558). -/
theorem mixedNorm_integral_le_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure T} {ν : Measure Y} {ρ : Measure R} [SigmaFinite μ] [SigmaFinite ν]
    [SigmaFinite ρ] {F : R → T → Y → E}
    (hF : StronglyMeasurable fun z : R × T × Y => F z.1 z.2.1 z.2.2)
    {q a : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞) (ha : 1 ≤ a) (ha' : a ≠ ∞)
    {c : R → ℝ≥0∞} (hc : AEMeasurable c ρ) {M : ℝ≥0∞}
    (hle : ∀ r, mixedNorm q a μ ν (F r) ≤ c r * M) :
    mixedNorm q a μ ν (fun τ y => ∫ r, F r τ y ∂ρ) ≤ (∫⁻ r, c r ∂ρ) * M := by
  refine (mixedNorm_integral_le hF hq hq' ha ha').trans ?_
  calc ∫⁻ r, mixedNorm q a μ ν (F r) ∂ρ ≤ ∫⁻ r, c r * M ∂ρ := lintegral_mono hle
    _ = (∫⁻ r, c r ∂ρ) * M := lintegral_mul_const'' M hc

end Minkowski

/-! ### Phase translations -/

/-- **Invariance under phase translations** (`paper/main.tex` 8956–8958, B0558, B0759): for a
translation-invariant measure `μ` on an abelian group,
`‖F(· + σ, ·)‖_{L^q_τ L^a_y} = ‖F‖_{L^q_τ L^a_y}`. No measurability is needed. -/
theorem mixedNorm_comp_add {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (q a : ℝ≥0∞) (ν : Measure Y) (σ : G) (F : G → Y → ε) :
    mixedNorm q a μ ν (fun τ => F (τ + σ)) = mixedNorm q a μ ν F := by
  unfold mixedNorm
  have h := (measurableEmbedding_addLeft σ).eLpNorm_map_measure
    (g := fun τ => eLpNorm (F τ) a ν) (p := q) (μ := μ)
  rw [map_add_left_eq_self μ σ] at h
  rw [h]
  congr 1
  funext τ
  show eLpNorm (F (τ + σ)) a ν = eLpNorm (F (σ + τ)) a ν
  rw [add_comm]

/-- Phase translations on `ℝ/Pℤ` with the normalized phase measure `dτ/P`
(`AddCircle.haarAddCircle`, decision D2). -/
theorem mixedNorm_haarAddCircle_comp_add {P : ℝ} [Fact (0 < P)] {ε : Type*} [TopologicalSpace ε]
    [ContinuousENorm ε] (q a : ℝ≥0∞) (ν : Measure Y) (σ : AddCircle P)
    (F : AddCircle P → Y → ε) :
    mixedNorm q a AddCircle.haarAddCircle ν (fun τ => F (τ + σ)) =
      mixedNorm q a AddCircle.haarAddCircle ν F :=
  mixedNorm_comp_add _ q a ν σ F

/-- Phase translations on `ℝ/Pℤ` with Lebesgue measure. -/
theorem mixedNorm_volume_addCircle_comp_add {P : ℝ} [Fact (0 < P)] {ε : Type*}
    [TopologicalSpace ε] [ContinuousENorm ε] (q a : ℝ≥0∞) (ν : Measure Y) (σ : AddCircle P)
    (F : AddCircle P → Y → ε) :
    mixedNorm q a (volume : Measure (AddCircle P)) ν (fun τ => F (τ + σ)) =
      mixedNorm q a (volume : Measure (AddCircle P)) ν F :=
  mixedNorm_comp_add _ q a ν σ F

/-- Lebesgue measure on `ℝ/Pℤ` versus the normalized phase measure `dτ/P`:
`‖F‖_{L^q(dτ) L^a_y} = P^{1/q} ‖F‖_{L^q(dτ/P) L^a_y}` for `q < ∞`. -/
theorem mixedNorm_volume_eq {P : ℝ} [Fact (0 < P)] {ε : Type*} [TopologicalSpace ε]
    [ContinuousENorm ε] {q : ℝ≥0∞} (hq : q ≠ ∞) (a : ℝ≥0∞) (ν : Measure Y)
    (F : AddCircle P → Y → ε) :
    mixedNorm q a (volume : Measure (AddCircle P)) ν F =
      ENNReal.ofReal P ^ (1 / q).toReal * mixedNorm q a AddCircle.haarAddCircle ν F := by
  unfold mixedNorm
  rw [AddCircle.volume_eq_smul_haarAddCircle, eLpNorm_smul_measure_of_ne_top hq, smul_eq_mul]

end UnforcedLeray.Conv
