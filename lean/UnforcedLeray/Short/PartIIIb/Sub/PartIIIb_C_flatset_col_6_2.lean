import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6

/-!
# Decomposition of `VtvSlice` (source 3511-3514, 3420-3426, 4610-4612)

Source of record: `the November 2 reference manuscript` (73 pages).

`VtvSlice` is the conjunction of an a.e.-age `L²` statement (Fubini from the band hypotheses on
`b`, `f`) and a fixed-age identity (the pointwise algebra against `∇^⊥ζ`), which in turn rests on
the commutation of `∂_s`, `Δ` with `∇^⊥`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel flatDt flatLap lapP)

/-- The slice `s` of `b` and `f` is `L²` on the cell. -/
def SliceL2 (c : ℝ) (b f : Chart → Fin 2 → ℂ) (s : ℝ) : Prop :=
  ∀ i, MemLp (fun x => b (s, x) i) 2 (volume.restrict (B0579.cell c)) ∧
    MemLp (fun x => f (s, x) i) 2 (volume.restrict (B0579.cell c))

/-- **Commutation of `∂_s`, `Δ` with `∇^⊥`** (source 3511-3514): for a stream test `ζ`, `∂_sζ` and
`Δζ(s)` are again stream tests and `flatDt`, `flatLap` of `streamField ζ` are `streamField` of them
(joint smoothness, symmetry of second derivatives). -/
def SliceCommute : Prop :=
  ∀ (c : ℝ) (ζ : ℝ → ℝ × ℝ → ℝ), IsStreamTest c ζ →
    IsStreamTest c (fun s x => deriv (fun t => ζ t x) s) ∧
    IsStreamTest c (fun s x => lapP (ζ s) x) ∧
    (∀ s x i, flatDt (streamField ζ) s x i =
      streamField (fun s x => deriv (fun t => ζ t x) s) s x i) ∧
    (∀ s x i, flatLap (streamField ζ) s x i = streamField (fun s x => lapP (ζ s) x) s x i)

/-- **The `L²` slices exist for a.e. age** (source 3426-3440: `f` is in `L²` of every age band
times the cell, `energyLoc` for `b`; Fubini on `[s₁,s₂] × cell`, countable union over bands). -/
def SliceL2ae : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f →
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), SliceL2 c b f s

/-- **The fixed-age identity** (source 3511-3514, 3420-3426): at every age `s > 0` at which the
slices of `b`, `f` are `L²` on the cell, the forced integrand against `∇^⊥ζ(s)` is integrable on
the cell with integral `streamSlice`.  Route: see `VtvSlice` docstring (Biot-Savart pairings for
the cylinder tests `∂_sζ`, `Δζ`, `ζ`, `w = v·∇ζ`; pointwise stress identity with `div v = 0`;
`∫ b·∇Π = 0`). -/
def SliceEq : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ ζ : ℝ → ℝ × ℝ → ℝ, IsStreamTest c ζ →
      ∀ s : ℝ, 0 < s → SliceL2 c b f s →
        IntegrableOn (fun x => forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ)
          (s, x)) (B0579.cell c) ∧
        ∫ x in B0579.cell c, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x) =
          streamSlice μ tr ω g b ζ s

theorem vtvSlice_of (h1 : SliceL2ae) (h2 : SliceEq) : VtvSlice := by
  intro ν c μ tr ω g b G f H ζ hζ
  filter_upwards [h1 ν c μ tr ω g b G f H, ae_restrict_mem measurableSet_Ioi] with s hs hpos
  exact h2 ν c μ tr ω g b G f H ζ hζ s hpos hs

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
