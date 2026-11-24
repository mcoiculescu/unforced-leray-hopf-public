import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6

/-!
# Decomposition of `VtvTime` (source 4610, 4464-4467, 3511-3514)

Source of record: `the November 2 reference manuscript`.

Write `ζ(s) = s^μ η(s)` with `η = vtvEta μ ζ` (again a stream test, since `ζ` vanishes for
`s < s₁ > 0`).  Put `Y(s,φ) = s^μ⟨ω(s),φ⟩` (`vtvY`) and `R(r,φ) = r^μ(⟨g(r),φ⟩ + ℓ_r(φ))`
(`vtvR`, `ℓ_r` the integral of `flowIntegrand`).  The integrated Duhamel identity (source 4610,
last clause of `VtvHyps`) is `Y(s,φ) = ∫₀^s R(r,φ) dr` for every time independent cylinder test `φ`.

* `VtvSliceExpand`: `streamSlice(s) = Y(s,∂_sη(s)) + R(s,η(s))` (product rule for `∂_s(s^μ η)`;
  `⟨ω,∂_sζ⟩ - (μ/s)⟨ω,ζ⟩ = s^μ⟨ω,∂_sη⟩`).
* `VtvEtaStream`: `η` is a stream test.
* `VtvTimeIntegrable`: both `s ↦ Y(s,∂_sη(s))` and `s ↦ R(s,η(s))` are integrable on `(0,∞)`
  (`energyLoc`, `⟨ω,ψ⟩ = ∫ b·∇^⊥ψ`, local integrability of `f`, band support).
* `VtvTimeFubini`: `∫₀^∞ Y(s,∂_sη(s)) ds = -∫₀^∞ R(s,η(s)) ds` (Fubini on `{r < s}` and the
  Duhamel identity applied to `φ = ∂_sη(s)`; then `∫_r^∞ ∂_sη(s) ds = -η(r)` and linearity of
  `R(r,·)`, exchanged with the `s`-integral by a second Fubini).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel)

/-- `η(s) = s^{-μ} ζ(s)` (so `ζ(s) = s^μ η(s)`). -/
def vtvEta (μ : ℝ) (ζ : ℝ → ℝ × ℝ → ℝ) : ℝ → ℝ × ℝ → ℝ := fun s x => s ^ (-μ) * ζ s x

/-- `Y(s,φ) = s^μ ⟨ω(s),φ⟩`. -/
def vtvY (μ c : ℝ) (ω : ℝ → ℝ × ℝ → ℂ) (s : ℝ) (φ : ℝ × ℝ → ℝ) : ℂ :=
  ((s : ℂ) ^ (μ : ℂ)) * ∫ x in B0579.cell c, ω s x * (φ x : ℂ)

/-- `R(r,φ) = r^μ (⟨g(r),φ⟩ + ∫ flowIntegrand)`. -/
def vtvR {ν c : ℝ} (μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (r : ℝ) (φ : ℝ × ℝ → ℝ) : ℂ :=
  ((r : ℂ) ^ (μ : ℂ)) * ((∫ x in B0579.cell c, g r x * (φ x : ℂ)) +
    ∫ x in B0579.cell c, flowIntegrand tr (ω r) (fun x => b (r, x)) r φ x)

/-- **Pointwise expansion** (source 4464-4467, 3511-3514). -/
def VtvSliceExpand : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ ζ : ℝ → ℝ × ℝ → ℝ, IsStreamTest c ζ → ∀ s : ℝ, 0 < s →
      streamSlice μ tr ω g b ζ s =
        vtvY μ c ω s (fun x => deriv (fun s' => vtvEta μ ζ s' x) s) +
          vtvR μ tr ω g b s (vtvEta μ ζ s)

/-- **`η = s^{-μ}ζ` is a stream test.** -/
def VtvEtaStream : Prop :=
  ∀ (c μ : ℝ) (ζ : ℝ → ℝ × ℝ → ℝ), IsStreamTest c ζ → IsStreamTest c (vtvEta μ ζ)

/-- **Integrability of the two time integrands** (source 4610; `energyLoc`, band support). -/
def VtvTimeIntegrable : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      IntegrableOn (fun s => vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s)) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun s => vtvR μ tr ω g b s (η s)) (Ioi (0 : ℝ))

/-- **The time Fubini** (source 4610): `∫₀^∞ Y(s,∂_sη) ds + ∫₀^∞ R(s,η(s)) ds = 0`. -/
def VtvTimeFubini : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      (∫ s in Ioi (0 : ℝ), vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s)) +
        ∫ s in Ioi (0 : ℝ), vtvR μ tr ω g b s (η s) = 0

theorem vtvTime_of (h1 : VtvSliceExpand) (h2 : VtvEtaStream) (h3 : VtvTimeIntegrable)
    (h4 : VtvTimeFubini) : VtvTime := by
  intro ν c μ tr ω g b G f H ζ hζ
  have hη := h2 c μ ζ hζ
  obtain ⟨hY, hR⟩ := h3 ν c μ tr ω g b G f H _ hη
  have hEq : Set.EqOn (streamSlice μ tr ω g b ζ)
      (fun s => vtvY μ c ω s (fun x => deriv (fun s' => vtvEta μ ζ s' x) s) +
        vtvR μ tr ω g b s (vtvEta μ ζ s)) (Ioi (0 : ℝ)) :=
    fun s hs => h1 ν c μ tr ω g b G f H ζ hζ s hs
  have hInt : IntegrableOn (streamSlice μ tr ω g b ζ) (Ioi (0 : ℝ)) :=
    (hY.add hR).congr_fun hEq.symm measurableSet_Ioi
  refine ⟨hInt, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_add hY hR]
  exact h4 ν c μ tr ω g b G f H _ hη

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
