import UnforcedLeray.Short.PartIIb.Sub.T11

/-!
# Part II-b, task `PartII-b:T11/5` (`FlatSliceOrthogonality`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1923-1938 (flat
equation, `a_r > 0`) and the proof recorded in `Sub/T11.lean` (steps 2-4).

The reduction avoids the approximate-identity averaging `ρ_δ`: from "for every `s`, the slice pairing
`⟨b(σ), ∇^⊥H(s-σ)⟩` vanishes for a.e. `σ < s`" (`SliceDualVanish`, from `T11/2`-`T11/4`) one gets, by
Fubini in `(σ, τ = s - σ)`, a joint null set (`SliceJointNull`), then `τ → 0+` along a sequence in the
good set gives `⟨b(σ), ∇^⊥ζ⟩ = 0` for a.e. `σ` (`SlicePointwise`); finally `SliceProductFormula`
identifies the pairing integral over `ageμ c 0 = ds ⊗ avgμ` with the iterated integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The slice pairing `∫ b(σ,·)·∇^⊥H(s-σ,·) d avgμ` (the function `F(σ)σ^{-μ}` of `FlatDualConstancy`). -/
def slicePair (c : ℝ) (b : CProf) (H : Coord → ℝ) (σ s : ℝ) : ℂ :=
  ∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ) ∂(Cyl.avgμ c)

/-- **Leaf `PartII-b:T11/5/1`** (SP 1923-1938, steps 2-3 of `Sub/T11.lean`): for `H` the heat flow of a
nice stream `ζ` (`HeatSol` with `L^{r'}`-contractive `∇^⊥H(τ)`), the slice pairing vanishes for a.e.
`σ ∈ (0, s)`, for every `s > 0`.  From `flatDualConstancy` (`F = κ_s` a.e.), the Hölder bound
`|F(σ)| ≤ C σ^{a_r} (σ^{1/2-3/(2r)} ‖b(σ)‖_{L^r})` and `smallSliceNorm` (`κ_s = 0` since `a_r > 0`). -/
def SliceDualVanish : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ), 0 < c → 0 < ν → 1 < r → r < 3 → 0 < μ.re + (3 / r - 1) / 2 →
    ∀ b : CProf, InFlatClass c r b → IsFlatResponse ν μ 0 b →
      ∀ (ζ : ℝ × ℝ → ℝ) (H : Coord → ℝ), NiceStream c ζ → HeatSol c ν (r / (r - 1)) H →
        (∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
          ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c) ≤
            ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) →
        ∀ s : ℝ, 0 < s →
          ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)), slicePair c b H σ s = 0

/-- **Leaf `PartII-b:T11/5/2`** (joint null set; Fubini/Tonelli on `(σ, τ)`): if for every `s > 0`
the slice pairing vanishes for a.e. `σ ∈ (0, s)`, then for a.e. `σ > 0` it vanishes at a.e. `s > σ`
(`s = σ + τ`).  Needs joint (a.e.-)measurability of `(σ, τ) ↦ slicePair c b H σ (σ + τ)` from
`b ∈ H_r` (`InHr.meas`) and continuity of the slices of `H` on `τ > 0`, then `ae_prod_iff_ae_ae`. -/
def SliceJointNull : Prop :=
  ∀ (c r ν : ℝ) (b : CProf) (H : Coord → ℝ), 0 < c → 1 < r → InHr c r b →
    HeatSol c ν (r / (r - 1)) H →
    (∀ s : ℝ, 0 < s → ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)), slicePair c b H σ s = 0) →
    ∀ᵐ σ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ τ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), slicePair c b H σ (σ + τ) = 0

/-- **Leaf `PartII-b:T11/5/3`** (limit `τ → 0+`): if `∇^⊥H(τ) → ∇^⊥ζ` in `L^{r'}(avgμ)` as `τ → 0+`
(third conjunct of `HeatStreamDual`) and the slice pairing vanishes at a.e. `τ`, for a.e. `σ`, then
`⟨b(σ), ∇^⊥ζ⟩ = 0` for a.e. `σ > 0`.  Proof: for a.e. `σ`, `b(σ) ∈ L^r(avgμ)` (`hNorm` finite,
`InHr`); choose `τ_n → 0+` in the good set (a.e. set in `(0,∞)` accumulates at `0`); Hölder
(componentwise over `Fin 2`) gives `|slicePair σ (σ+τ_n) - ⟨b(σ),∇^⊥ζ⟩| ≤ C ‖b(σ)‖_{L^r} · o(1)`. -/
def SlicePointwise : Prop :=
  ∀ (c r : ℝ) (b : CProf) (ζ : ℝ × ℝ → ℝ) (H : Coord → ℝ), 0 < c → 1 < r → InHr c r b →
    NiceStream c ζ →
    (∀ i : Fin 2, Tendsto
        (fun τ : ℝ => ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i‖ₑ ^ (r / (r - 1))
          ∂(Cyl.avgμ c)) (𝓝[>] (0 : ℝ)) (𝓝 0)) →
    (∀ᵐ σ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ τ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), slicePair c b H σ (σ + τ) = 0) →
    ∀ᵐ σ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) ∂(Cyl.avgμ c) = 0

/-- **Leaf `PartII-b:T11/5/4`** (product formula): for `b ∈ H_r`, a time test `θ` and a nice stream
`ζ`, the pairing integral over `ageμ c 0 = ds|_{(0,∞)} ⊗ avgμ` is the iterated integral
`∫_{σ>0} ∫ streamPair b θ ζ (σ, ·) d avgμ dσ`.  The integrand is integrable (`b ∈ L^r(s^{r/2-5/2}ds)`,
`θ` supported in a compact subset of `(0,∞)` where the weight is bounded, `∇^⊥ζ` bounded and
`η`-compact, Hölder), so this is `integral_prod` for `ageμ c 0` (`Axi.ageμ` def: density `s^0 = 1`). -/
def SliceProductFormula : Prop :=
  ∀ (c r : ℝ) (b : CProf) (θ : ℝ → ℝ) (ζ : ℝ × ℝ → ℝ), 0 < c → 1 < r → InHr c r b →
    TimeTest θ → NiceStream c ζ →
      ∫ x, streamPair b θ ζ x ∂(Axi.ageμ c 0) =
        ∫ σ in Ioi (0 : ℝ), ∫ p, streamPair b θ ζ (σ, p) ∂(Cyl.avgμ c)

/-- **Conditional slice orthogonality** (target `flatSliceOrthogonality`): glue of the four leaves and
`HeatStreamDual` (`heatStreamDual`, `T11/3`).  -/
theorem flatSliceOrthogonality_of (h3 : HeatStreamDual) (k1 : SliceDualVanish)
    (k2 : SliceJointNull) (k3 : SlicePointwise) (k4 : SliceProductFormula) :
    FlatSliceOrthogonality := by
  intro c r ν μ hc hν hr hr3 ha b hb h0 θ ζ hθ hζ
  rw [k4 c r b θ ζ hc hr hb.inHr hθ hζ]
  have hr' : 1 < r / (r - 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  obtain ⟨H, hH, hcon, hconv⟩ := h3 c ν (r / (r - 1)) ζ hc hν hr' hζ
  have e1 := fun s (hs : 0 < s) => k1 c r ν μ hc hν hr hr3 ha b hb h0 ζ H hζ hH hcon s hs
  have e2 := k2 c r ν b H hc hr hb.inHr hH e1
  have e3 := k3 c r b ζ H hc hr hb.inHr hζ hconv e2
  refine integral_eq_zero_of_ae ?_
  filter_upwards [e3] with σ hσ
  have : ∀ p, streamPair b θ ζ (σ, p) =
      (θ σ : ℂ) * ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) := by
    intro p
    simp only [streamPair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  simp_rw [this]
  simp only [Pi.zero_apply]
  rw [integral_const_mul, hσ, mul_zero]

end UnforcedLeray.Short.IIb
