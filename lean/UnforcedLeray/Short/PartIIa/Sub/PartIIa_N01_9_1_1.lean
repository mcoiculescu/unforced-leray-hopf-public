import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1

/-!
# `PartII-a:N01/9/1/1` (decomposition): `SmoothForceDense` via stream functions

Source `the November 2 reference manuscript`
lines 1684-1689 ("smooth compactly supported forces"), 1676 (`P_0` flat Leray projection).

The Leray projection of a smooth force is NOT compactly supported in `η` (it is nonlocal), so the
route "project smooth forces" is wrong for `SmoothForceSet`.  Correct route: solenoidal fields are
approximated by stream-function fields `(∂_η ψ, -∂_q ψ)` with `ψ` smooth, `c`-periodic in `q`,
compactly supported in `s ∈ (0,∞)`, `|η| ≤ R` (fibrewise in `s` the divergence is
`∂_q b_r + ∂_η b_z`, `cgrad 0 Φ = (∂_qΦ, ∂_ηΦ)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- The stream field `(∂_η ψ, -∂_q ψ)` of a scalar `ψ`. -/
def StreamField (ψ : Profile → ℂ) : Profile → MeridC := fun p =>
  !₂[pdEta ψ p, -pdQ ψ p]

/-- Stream functions: smooth, `c`-periodic in `q`, supported in `s ∈ [s₁,s₂] ⊂ (0,∞)`,
`|η| ≤ R`. -/
def IsStreamFn (c : ℝ) (ψ : Profile → ℂ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ (∀ p : Profile, ψ (p.1, p.2.1 + c, p.2.2) = ψ p) ∧
    ∃ s₁ s₂ R : ℝ, 0 < s₁ ∧ ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → ψ p = 0

/-- Elements of `𝓗` represented by stream fields. -/
def StreamSet (c : ℝ) : Set (HSpace c MeridC) :=
  {g | ∃ ψ, IsStreamFn c ψ ∧ (g : Profile → MeridC) =ᵐ[measureH c] StreamField ψ}

/-- (A1) the stream field of a stream function is a smooth force (`C^∞`, `c`-periodic, support in
the band): derivatives of a smooth periodic band-supported function. -/
def StreamIsSmoothForce : Prop :=
  ∀ (c : ℝ) (ψ : Profile → ℂ), IsStreamFn c ψ → IsSmoothForceFn c (StreamField ψ)

/-- (A2) stream fields are solenoidal in `𝓗`: for every profile test `Φ` the pairing of
`(∂_ηψ, -∂_qψ)` with `(∂_qΦ, ∂_ηΦ)` in `L²(s^{-3/2} ds dq dη)` vanishes (integrate by parts in
`η` and `q`; the weight depends on `s` only, `Φ` periodic in `q`, `ψ` compactly supported in `η`).
Stated as membership of every `g ∈ StreamSet c` in `solenoidalHC 0 c`. -/
def StreamSolenoidal : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g ∈ StreamSet c, g ∈ solenoidalHC 0 c

/-- (B) density of stream fields in the solenoidal subspace (1684-1689).  Sketch: by Hilbert
duality it suffices that `h ∈ solenoidalHC 0 c` with `h ⟂ StreamSet c` is zero.  Orthogonality to all
stream fields says `∂_η h_r - ... ` i.e. `curl h = 0` weakly, so `h` is weakly div- and curl-free
in `(q,η)` for a.e. `s`; Fourier in `q` (modes `k ∈ (2π/c)ℤ`) and in `η` gives
`(k² + ξ²) ĥ = 0`, hence `h = 0` a.e. (the single frequency `(0,0)` is a null set in `L²`). -/
def StreamDense : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g ∈ solenoidalHC 0 c, g ∈ closure (StreamSet c)

theorem smoothForceDense_of (h1 : StreamIsSmoothForce) (h2 : StreamSolenoidal)
    (h3 : StreamDense) : SmoothForceDense := by
  intro c hc g hg
  refine closure_mono ?_ (h3 c hc g hg)
  intro x hx
  have hs := h2 c hc x hx
  obtain ⟨ψ, hψ, hx'⟩ := hx
  exact ⟨hs, StreamField ψ, h1 c ψ hψ, hx'⟩

end UnforcedLeray.Short.PartIIa.N01
