import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# Decomposition of `PartII-a:N01/9/1/1/3` (`StreamDense`), source lines 1684-1689

`StreamDense` reduces (via `streamDense_of` in `SmoothForceDense/StreamDense.lean`) to the orthogonal
core: a solenoidal `h ∈ 𝓗` orthogonal to all stream fields vanishes.  Here this core is reduced to
four true analytic lemmas, stated as `Prop`s:

* `SliceL2`: for a.e. `s` the `s`-slice of an `L²(s^{-3/2})` field is in `L²(cell)`;
* `ProdTestOrth`: orthogonality to the products `θ(s)ψ(q,η)` gives, for each cylinder test `ψ`,
  zero slice divergence and curl for a.e. `s`;
* `CylDense`: a countable family of cylinder tests is `W^{1,2}(cell)`-dense;
* `LimitStep`: zero pairing against a dense family passes to all cylinder tests (Cauchy-Schwarz);
* `SliceVanish`: a field with a.e. vanishing slices vanishes (Fubini).

The 2D uniqueness `T20_2.biot_re` finishes each slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa

/-- Slice at `s` of the `c`-periodic extension in `q` of a field (the field lives on the `q`-cell
`(0, c]`; the periodic extension is evaluated on the cylinder cell `[-c/2, c/2)`). -/
def sliceFn {c : ℝ} (h : HSpace c MeridC) (s : ℝ) : ℝ × ℝ → Fin 2 → ℂ :=
  fun z j => (h : Profile → MeridC) (s, UnforcedLeray.B0220.reduceIoc c z.1, z.2) j

/-- Weak divergence pairing `∫ (w₀ ∂_qψ + w₁ ∂_ηψ)` over the cell. -/
def divI (c : ℝ) (w : ℝ × ℝ → Fin 2 → ℂ) (ψ : ℝ × ℝ → ℝ) : ℂ :=
  ∫ z in UnforcedLeray.Cyl.cell c,
    (w z 0 * (fderiv ℝ ψ z (1, 0) : ℂ) + w z 1 * (fderiv ℝ ψ z (0, 1) : ℂ))

/-- Weak curl pairing `∫ (w₀ ∂_ηψ - w₁ ∂_qψ)` over the cell. -/
def curlI (c : ℝ) (w : ℝ × ℝ → Fin 2 → ℂ) (ψ : ℝ × ℝ → ℝ) : ℂ :=
  ∫ z in UnforcedLeray.Cyl.cell c,
    (w z 0 * (fderiv ℝ ψ z (0, 1) : ℂ) - w z 1 * (fderiv ℝ ψ z (1, 0) : ℂ))

/-- Slices of an `𝓗` field are in `L²(cell)` for a.e. `s` (Fubini/Tonelli with the weight
`s^{-3/2}`). -/
def SliceL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h : HSpace c MeridC,
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ j, MemLp (fun z => sliceFn h s z j) 2 (UnforcedLeray.Cyl.cellμ c)

/-- Orthogonality of `h ∈ solenoidalHC 0 c` to `StreamSet` gives, for each fixed cylinder test `ψ`,
zero slice divergence and curl for a.e. `s`: test `solenoidalHC 0 c` (profile gradients, `ε = 0`
so `D₀ = ∂_q`) and `StreamSet` (fields `(∂_ηψ,-∂_qψ)`) with `Φ = θ(s)ψ(q,η)` for all smooth
compactly supported `θ` on `(0,∞)`, then apply the fundamental lemma in `s`
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero`).  Source 1684-1689. -/
def ProdTestOrth : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h ∈ solenoidalHC 0 c, (∀ g ∈ StreamSet c, inner ℂ g h = 0) →
    ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        divI c (sliceFn h s) ψ = 0 ∧ curlI c (sliceFn h s) ψ = 0

/-- A countable family of cylinder tests whose gradients are `L²(cell)`-dense among cylinder tests
(separability; e.g. trigonometric polynomials in `q` times rational Hermite/cutoff data in `η`). -/
def CylDense : Prop :=
  ∀ c : ℝ, 0 < c → ∃ D : Set (ℝ × ℝ → ℝ), D.Countable ∧
    (∀ ψ ∈ D, UnforcedLeray.Sob.IsCylTest c ψ) ∧
    ∀ ψ, UnforcedLeray.Sob.IsCylTest c ψ → ∀ ε : ℝ, 0 < ε → ∃ ψ' ∈ D,
      ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ 2 < ENNReal.ofReal ε

/-- Passage to the limit: for an `L²(cell)` field `w`, if the weak div and curl pairings vanish on
cylinder tests `ψ'` arbitrarily `W^{1,2}`-close to `ψ`, they vanish at `ψ` (Cauchy-Schwarz). -/
def LimitStep : Prop :=
  ∀ c : ℝ, 0 < c → ∀ w : ℝ × ℝ → Fin 2 → ℂ,
    (∀ j, MemLp (fun z => w z j) 2 (UnforcedLeray.Cyl.cellμ c)) →
    ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
      (∀ ε : ℝ, 0 < ε → ∃ ψ' : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ' ∧
        divI c w ψ' = 0 ∧ curlI c w ψ' = 0 ∧
        ∫⁻ z in UnforcedLeray.Cyl.cell c,
          ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ 2 < ENNReal.ofReal ε) →
      divI c w ψ = 0 ∧ curlI c w ψ = 0

/-- A field of `𝓗` whose `s`-slices vanish a.e. on a.e. slice is zero (Fubini; `measureH` is
`s^{-3/2} ds dq dη` on the cell). -/
def SliceVanish : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h : HSpace c MeridC,
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ z ∂(UnforcedLeray.Cyl.cellμ c), sliceFn h s z = 0) → h = 0

/-- Slices of `h` have zero weak div and curl for all cylinder tests. -/
theorem sliceWeak_of (h1 : SliceL2) (h2 : ProdTestOrth) (h3 : CylDense) (h4 : LimitStep)
    (c : ℝ) (hc : 0 < c) (h : HSpace c MeridC) (hs : h ∈ solenoidalHC 0 c)
    (ho : ∀ g ∈ StreamSet c, inner ℂ g h = 0) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (∀ j, MemLp (fun z => sliceFn h s z j) 2 (UnforcedLeray.Cyl.cellμ c)) ∧
      ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
        divI c (sliceFn h s) ψ = 0 ∧ curlI c (sliceFn h s) ψ = 0 := by
  obtain ⟨D, hDc, hDt, hDd⟩ := h3 c hc
  have hD : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ ψ ∈ D,
      divI c (sliceFn h s) ψ = 0 ∧ curlI c (sliceFn h s) ψ = 0 := by
    rw [ae_ball_iff hDc]
    intro ψ hψ
    exact h2 c hc h hs ho ψ (hDt ψ hψ)
  filter_upwards [h1 c hc h, hD] with s hL hDs
  refine ⟨hL, fun ψ hψ => h4 c hc _ hL ψ hψ ?_⟩
  intro ε hε
  obtain ⟨ψ', hψ'D, hlt⟩ := hDd ψ hψ ε hε
  exact ⟨ψ', hDt ψ' hψ'D, (hDs ψ' hψ'D).1, (hDs ψ' hψ'D).2, hlt⟩

/-- The orthogonal core. -/
theorem streamOrthCore_of (h1 : SliceL2) (h2 : ProdTestOrth) (h3 : CylDense)
    (h4 : LimitStep) (h5 : SliceVanish) :
    ∀ c : ℝ, 0 < c → ∀ h ∈ solenoidalHC 0 c, (∀ g ∈ StreamSet c, inner ℂ g h = 0) → h = 0 := by
  intro c hc h hs ho
  refine h5 c hc h ?_
  filter_upwards [sliceWeak_of h1 h2 h3 h4 c hc h hs ho] with s hs'
  obtain ⟨hL, hz⟩ := hs'
  exact UnforcedLeray.Short.IIIa.CTE.T20_2.biot_re hc (sliceFn h s) hL
    (fun ψ hψ => (hz ψ hψ).1) (fun ψ hψ => (hz ψ hψ).2)

end UnforcedLeray.Short.PartIIa.N01.Sub
