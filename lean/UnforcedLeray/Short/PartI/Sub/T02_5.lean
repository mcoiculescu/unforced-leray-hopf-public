import UnforcedLeray.Short.PartI.Sub.T02

/-!
# Part I, task `PartI:T02/5`: `StreamExists` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288 ("Let
`v = ∇^⊥ψ` be the exact cylinder Navier-Stokes solution ... its vorticity is in `L¹ ∩ L^∞` and has
zero integral ... The scalar vorticity equation preserves zero circulation ... Uniqueness gives
`v(-q,-η,s) = -v(q,η,s)`").

The target is `StreamExists` (`Short/PartI/Sub/T02.lean`, line 165): an odd classical field with
bounded derivatives and finite vorticity first moment has a decaying stream.  The statement is
time-by-time, so it reduces to one fixed slice `w = v(s)`:

* `StreamSlice c w`: `w : ℝ × ℝ → Vec` is `C^∞`, `c`-periodic in `q`, divergence free, all
  derivatives bounded, centrally odd, of finite energy on the cell and with
  `∫_cell (1 + |η|) |curl w| < ∞`.
* `SliceStream`: every such `w` is `∇^⊥ψ` with `ψ` differentiable and `ψ → 0` as `|η| → ∞`.

`streamExists_of` (proved here) derives `StreamExists` from `SliceStream`: smoothness of the slice
is composition of `smooth_v` with `z ↦ (s, z)`, the other hypotheses are restrictions at `s`.

`sliceStream_of` (proved here) derives `SliceStream` from three leaf statements, by the explicit
formula `ψ = V - V̄ + g` where `V(q, η) = ∫₀^q w₂(s, η) ds`, `V̄(η) = c⁻¹ ∫₀^c V(q, η) dq` and `g` is
the function of `η` alone from `PsiBarExists`:
* `PsiBarExists`: a function `g` with `g' = -Γ/c`, `Γ(η) = ∫₀^c w₁(q, η) dq`, and `g → 0` at `±∞`;
* `PsiGradient`: for every such `g`, `ψ` is differentiable with `∇^⊥ψ = w`;
* `PsiDecay`: for every `g → 0` at `±∞`, `ψ → 0` uniformly in `q` as `|η| → ∞`.

The remaining statements (`TendstoZeroOfLipschitzIntegrable`, `SliceEnergyProfile`,
`HasDerivAtEtaIntervalIntegral`, `ContDiffPrimitiveQ`, `SliceFluxZero`, `GammaDeriv`, `GammaOdd`,
`GammaTendsto`, `CurlMeanMoment`, `GammaIntegrableIoi`, `MeanPrimDeriv`) are the exact lemmas from
which the three leaves follow; `sliceEnergy_tendsto` (proved here) combines the first two.

Why the argument works (all slices fixed): with `G(η) = ∫₀^c |w(q, η)|² dq` integrable and Lipschitz,
`G → 0` at `±∞`.  The horizontal flux `∫₀^c w₂ dq` has `η`-derivative `-∫₀^c ∂_q w₁ = 0`
(periodicity), so it is constant, and `|flux|² ≤ c G → 0` forces it to vanish: `V` is `c`-periodic in
`q`.  The circulation `Γ` satisfies `Γ' = -m`, `m = ∫₀^c curl w dq`, `Γ → 0` at `±∞`, `Γ` is odd
(oddness of `w` and periodicity), and `Γ(η) = ∫_η^∞ m` is integrable on `(0, ∞)` by the moment
`∫ (1 + |t|)|m(t)| dt < ∞`; hence `g(η) = c⁻¹ (∫₀^∞ Γ - ∫₀^η Γ)` tends to `0` at `+∞` and, by oddness
of `Γ`, at `-∞`.  Finally `|V(q, η)|² ≤ c G(η)`, `|V̄(η)|² ≤ c G(η)` bound the oscillating part.

The unconditional target is task `PartI:T02/5` (`Short/PartI/Sub/T02/StreamExists.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (perpendicularGradient)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### The slice and the reduction `StreamExists ⇐ SliceStream` -/

/-- A time slice `w = v(s)` of an odd classical field with bounded derivatives and finite
vorticity first moment. -/
structure StreamSlice (c : ℝ) (w : Plane → Vec) : Prop where
  pos : 0 < c
  smooth : ContDiff ℝ ∞ w
  periodic : Cyl.IsPeriodic c w
  div : ∀ z, Cyl.divergence w z = 0
  bdd : ∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ M
  odd : ∀ z, w (-z) = -w z
  energy : IntegrableOn (fun z => ‖w z‖ ^ 2) (Cyl.cell c)
  moment : IntegrableOn (fun z : Plane => (1 + |z.2|) * |Cyl.curl w z|) (Cyl.cell c)

/-- **The slice statement** (source lines 261-288): a slice has a differentiable stream `ψ` with
`w = ∇^⊥ψ` and `ψ → 0` as `|η| → ∞` (uniformly in `q`). -/
def SliceStream : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w →
    ∃ ψ : Plane → ℝ, Differentiable ℝ ψ ∧ (∀ z, w z = toVec (perpendicularGradient ψ z)) ∧
      Tendsto ψ (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **`PartI:T02/5`, conditional on the slice statement**: `StreamExists`. -/
theorem streamExists_of (h : SliceStream) : StreamExists := by
  intro ν c T v p hν hc hT hcl hb hodd hvm
  have hslice : ∀ s ∈ Icc (0 : ℝ) T, StreamSlice c (v s) := by
    intro s hs
    refine ⟨by linarith, ?_, hcl.periodic_v s hs, hcl.solenoidal s hs, ?_, hodd s hs,
      hcl.finite_energy s hs, hvm s hs⟩
    · have h2 : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
        contDiff_const.prodMk contDiff_id
      have h3 := hcl.smooth_v.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
        (fun z _ => ⟨hs, Set.mem_univ z⟩)
      exact contDiffOn_univ.1 h3
    · intro k
      obtain ⟨M, hM⟩ := hb k
      exact ⟨M, fun z => hM s hs z⟩
  classical
  refine ⟨fun s => if hs : s ∈ Icc (0 : ℝ) T then Classical.choose (h c (v s) (hslice s hs))
    else 0, ?_⟩
  intro s hs
  simp only [hs, ↓reduceDIte]
  exact Classical.choose_spec (h c (v s) (hslice s hs))

/-! ### The functions of a slice -/

/-- The energy profile `G(η) = ∫₀^c |w(q, η)|² dq`. -/
def sliceEnergy (c : ℝ) (w : Plane → Vec) (η : ℝ) : ℝ := ∫ q in (0 : ℝ)..c, ‖w (q, η)‖ ^ 2

/-- The circulation profile `Γ(η) = ∫₀^c w₁(q, η) dq` (first component, index `0`). -/
def sliceGamma (c : ℝ) (w : Plane → Vec) (η : ℝ) : ℝ := ∫ q in (0 : ℝ)..c, w (q, η) 0

/-- The `q`-integral of the vorticity, `m(η) = ∫₀^c curl w(q, η) dq`. -/
def sliceCurlMean (c : ℝ) (w : Plane → Vec) (η : ℝ) : ℝ := ∫ q in (0 : ℝ)..c, Cyl.curl w (q, η)

/-- The primitive `V(q, η) = ∫₀^q w₂(s, η) ds` (second component, index `1`). -/
def slicePrim (w : Plane → Vec) (q η : ℝ) : ℝ := ∫ s in (0 : ℝ)..q, w (s, η) 1

/-- The `q`-mean of the primitive, `V̄(η) = c⁻¹ ∫₀^c V(q, η) dq`. -/
def sliceMeanPrim (c : ℝ) (w : Plane → Vec) (η : ℝ) : ℝ :=
  c⁻¹ * ∫ q in (0 : ℝ)..c, slicePrim w q η

/-- The candidate stream `ψ(q, η) = V(q, η) - V̄(η) + g(η)`. -/
def slicePsi (c : ℝ) (w : Plane → Vec) (g : ℝ → ℝ) (z : Plane) : ℝ :=
  slicePrim w z.1 z.2 - sliceMeanPrim c w z.2 + g z.2

/-! ### The three leaves and the assembly `SliceStream ⇐ PsiBarExists, PsiGradient, PsiDecay` -/

/-- **Leaf `PsiBarExists`** (source lines 261-288, zero circulation): there is a function `g` of `η`
with `g' = -Γ/c` that tends to `0` at both ends: `g(η) = c⁻¹(∫_{(0,∞)} Γ - ∫₀^η Γ)`, with `Γ`
integrable on `(0, ∞)` and odd. -/
def PsiBarExists : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w →
    ∃ g : ℝ → ℝ, (∀ η, HasDerivAt g (-sliceGamma c w η / c) η) ∧
      Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0)

/-- **Leaf `PsiGradient`**: for every `g` with `g' = -Γ/c`, `ψ = V - V̄ + g` is differentiable with
`∇^⊥ψ = w` (`∂_qψ = w₂` by the fundamental theorem of calculus, `∂_ηψ = -w₁` from
`∂_η V = -(w₁(q, η) - w₁(0, η))` (divergence free), `V̄' = -Γ/c + w₁(0, η)`, `g' = -Γ/c`). -/
def PsiGradient : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ g : ℝ → ℝ,
    (∀ η, HasDerivAt g (-sliceGamma c w η / c) η) →
      Differentiable ℝ (slicePsi c w g) ∧
        ∀ z, w z = toVec (perpendicularGradient (slicePsi c w g) z)

/-- **Leaf `PsiDecay`**: for every `g` tending to `0` at both ends, `ψ = V - V̄ + g` tends to `0` as
`|η| → ∞`, uniformly in `q` (`V` is `c`-periodic in `q` because the flux vanishes, so
`|V|² ≤ c G`, `|V̄|² ≤ c G` and `G → 0`). -/
def PsiDecay : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ g : ℝ → ℝ,
    Tendsto g atTop (𝓝 0) → Tendsto g atBot (𝓝 0) →
      Tendsto (slicePsi c w g) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- `SliceStream` from the three leaves: take `g` from `PsiBarExists`, `ψ = V - V̄ + g`. -/
theorem sliceStream_of (hI : PsiBarExists) (hK : PsiGradient) (hL : PsiDecay) : SliceStream := by
  intro c w hs
  obtain ⟨g, hg, hg1, hg2⟩ := hI c w hs
  obtain ⟨hd, hgrad⟩ := hK c w hs g hg
  exact ⟨slicePsi c w g, hd, hgrad, hL c w hs g hg1 hg2⟩

/-- `StreamExists` from the three leaves. -/
theorem streamExists_of_leaves (hI : PsiBarExists) (hK : PsiGradient) (hL : PsiDecay) :
    StreamExists :=
  streamExists_of (sliceStream_of hI hK hL)

/-! ### Lemmas from which the leaves follow -/

/-- **Lemma `TendstoZeroOfLipschitzIntegrable`** (pure real analysis): a nonnegative Lipschitz
integrable function on `ℝ` tends to `0` at `±∞`.  (If `f(x_n) ≥ a` along `x_n → ∞`, then
`f ≥ a/2` on `[x_n, x_n + a/(2K)]`, disjoint intervals of length `a/(2K)` for a subsequence, so the
integral diverges.) -/
def TendstoZeroOfLipschitzIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) (K : ℝ), (∀ x, 0 ≤ f x) → (∀ x y, |f x - f y| ≤ K * |x - y|) → Integrable f →
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0)

/-- **Lemma `SliceEnergyProfile`**: the energy profile `G` of a slice is integrable (Fubini on the
cell and periodicity, `∫_cell |w|² = ∫ G`) and Lipschitz (`|G(η) - G(η')| ≤ 2 c M M₁ |η - η'|`
with `M = sup |w|`, `M₁ = sup |Dw|`, by the mean value theorem). -/
def SliceEnergyProfile : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w →
    Integrable (sliceEnergy c w) ∧
      ∃ K : ℝ, ∀ η η' : ℝ, |sliceEnergy c w η - sliceEnergy c w η'| ≤ K * |η - η'|

/-- The energy profile of a slice tends to `0` at both ends. -/
theorem sliceEnergy_tendsto (hB : TendstoZeroOfLipschitzIntegrable) (hC : SliceEnergyProfile)
    {c : ℝ} {w : Plane → Vec} (hs : StreamSlice c w) :
    Tendsto (sliceEnergy c w) atTop (𝓝 0) ∧ Tendsto (sliceEnergy c w) atBot (𝓝 0) := by
  obtain ⟨hi, K, hK⟩ := hC c w hs
  exact hB _ K
    (fun η => intervalIntegral.integral_nonneg hs.pos.le (fun q _ => by positivity)) hK hi

/-- **Lemma `HasDerivAtEtaIntervalIntegral`** (differentiation under the integral sign): for a `C¹`
function `f` on the plane, `η ↦ ∫_a^b f(q, η) dq` has derivative `∫_a^b ∂_η f(q, η) dq`. -/
def HasDerivAtEtaIntervalIntegral : Prop :=
  ∀ f : Plane → ℝ, ContDiff ℝ 1 f → ∀ a b η : ℝ,
    HasDerivAt (fun x => ∫ q in a..b, f (q, x)) (∫ q in a..b, Cyl.partialEta f (q, η)) η

/-- **Lemma `ContDiffPrimitiveQ`**: the `q`-primitive `(q, η) ↦ ∫₀^q f(s, η) ds` of a `C¹` function is
`C¹` on the plane (`∂_q = f`, `∂_η = ∫₀^q ∂_η f` is jointly continuous). -/
def ContDiffPrimitiveQ : Prop :=
  ∀ f : Plane → ℝ, ContDiff ℝ 1 f → ContDiff ℝ 1 (fun z : Plane => ∫ s in (0 : ℝ)..z.1, f (s, z.2))

/-- **Lemma `SliceFluxZero`**: the horizontal flux `∫₀^c w₂(q, η) dq` of a slice vanishes for every
`η`.  (Its `η`-derivative is `∫₀^c ∂_η w₂ = -∫₀^c ∂_q w₁ = -(w₁(c, η) - w₁(0, η)) = 0` by `div w = 0`
and periodicity, so it is constant; its square is `≤ c G(η) → 0`.) -/
def SliceFluxZero : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ η : ℝ, ∫ q in (0 : ℝ)..c, w (q, η) 1 = 0

/-- **Lemma `GammaDeriv`**: `Γ' = -m`, where `m` is the `q`-integral of the vorticity
(`curl w = ∂_q w₂ - ∂_η w₁` and `∫₀^c ∂_q w₂ = 0` by periodicity). -/
def GammaDeriv : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ η : ℝ,
    HasDerivAt (sliceGamma c w) (-sliceCurlMean c w η) η

/-- **Lemma `GammaOdd`**: `Γ(-η) = -Γ(η)` (`w₁(q, -η) = -w₁(-q, η)` by oddness; substitute `q ↦ -q`
and use periodicity). -/
def GammaOdd : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ η : ℝ,
    sliceGamma c w (-η) = -sliceGamma c w η

/-- **Lemma `GammaTendsto`**: `Γ → 0` at `±∞` (`|Γ|² ≤ c G` by Cauchy-Schwarz, and `G → 0` by
`SliceEnergyProfile` and `TendstoZeroOfLipschitzIntegrable`). -/
def GammaTendsto : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w →
    Tendsto (sliceGamma c w) atTop (𝓝 0) ∧ Tendsto (sliceGamma c w) atBot (𝓝 0)

/-- **Lemma `CurlMeanMoment`**: `∫_ℝ (1 + |t|) |m(t)| dt < ∞` (from the moment on the cell:
`|m(t)| ≤ ∫₀^c |curl w(q, t)| dq`, Fubini on the cell, and the integral over `[-c/2, c/2)` of a
`c`-periodic function equals the integral over `[0, c)`). -/
def CurlMeanMoment : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w →
    Integrable (fun t : ℝ => (1 + |t|) * |sliceCurlMean c w t|)

/-- **Lemma `GammaIntegrableIoi`**: `Γ` is integrable on `(0, ∞)`.  (`Γ' = -m`, `Γ → 0` at `+∞`, so
`|Γ(η)| ≤ ∫_η^∞ |m|`, and `∫_0^∞ ∫_η^∞ |m| dt dη = ∫_0^∞ t |m(t)| dt < ∞` by Tonelli.) -/
def GammaIntegrableIoi : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → IntegrableOn (sliceGamma c w) (Ioi 0)

/-- **Lemma `MeanPrimDeriv`**: `V̄' = -Γ/c + w₁(0, η)`.  (`∂_η V(q, η) = ∫₀^q ∂_η w₂(s, η) ds
= -∫₀^q ∂_q w₁ = -(w₁(q, η) - w₁(0, η))` by `div w = 0`; average over `q ∈ [0, c]` and differentiate
under the integral.) -/
def MeanPrimDeriv : Prop :=
  ∀ (c : ℝ) (w : Plane → Vec), StreamSlice c w → ∀ η : ℝ,
    HasDerivAt (sliceMeanPrim c w) (-sliceGamma c w η / c + w (0, η) 0) η

end UnforcedLeray.Short.PartI
