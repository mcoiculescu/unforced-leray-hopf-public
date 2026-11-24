import UnforcedLeray.Short.PartIIb.Sub.T22_2

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2105 (the
free cylinder evolution `ω_s = νΔω - v_c·∇ω` on `X_{m,c}`, SP 2074-2093; "weighted integration by
parts", SP 2097-2101; the regular backward problem of the duality argument, SP 2100-2105).

`CylRegularTimeDep` (Sub/T22_2.lean) is the classical time-dependent identity for a regular flow
`ω` of the train velocity `v = tr.v` against a test `φ`:

  `∫ ω(t₁) φ(t₁) - ∫ ω(s) φ(s) = ∫_s^{t₁} ∫_cell ω (∂_r φ + νΔφ + v·∇φ)`.

With `F(r) = ∫_cell ω(r) φ(r)`:
* `F` is continuous on `[s, t₁]` (`RtdCont`, dominated convergence with the uniform decay);
* on `(s, t₁)`, `F' = ∫ (νΔω - v·∇ω) φ + ω ∂_r φ` (`RtdHasDeriv`, differentiation under the
  integral sign; the `pde` field of `IsRegularCylFlow` and the decay of `∂_r φ`);
* `∫ Δω φ = ∫ ω Δφ` (`RtdLapIBP`, periodic in `q`, decay in `η`) and
  `∫ (v·∇ω) φ = -∫ ω (v·∇φ)` (`RtdTransportIBP`, `div v = 0`), so `F' = ∫ ω(∂_r φ + νΔφ + v·∇φ)`;
* `F'` is bounded on `(s, t₁)` (`RtdRhsBound`), and the fundamental theorem of calculus with a
  bounded derivative (`RtdFTC`) concludes.
`RtdSlice` (slices of a `CylEtaTest` are `CylSmoothDecay`) feeds both integrations by parts;
`RtdTimeDeriv` (the `r`-derivative of a `CylEtaTest` is a genuine derivative inside `(t₀, t₁)` and
continuous in `x`) is the helper of `RtdHasDeriv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- **Leaf 1: slices of a test** (SP 2100-2105). Every age-slice of a `CylEtaTest` on
`[t₀, t₁]` is `C²`, `c`-periodic in `q` and decays with `∇` and `Δ` in `η`: restrict the joint
smoothness on `Icc t₀ t₁ ×ˢ univ` to `{r} ×ˢ univ`. -/
def RtdSlice : Prop :=
  ∀ (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), CylEtaTest c t₀ t₁ φ →
    ∀ r ∈ Icc t₀ t₁, CylSmoothDecay c (φ r)

/-- **Leaf 2: the age derivative of a test** (SP 2100-2105). Inside `(t₀, t₁)` the partial
derivative `∂_r φ(r, x)` exists and is continuous in `x` (joint smoothness on the open set
`Ioo t₀ t₁ ×ˢ univ`). -/
def RtdTimeDeriv : Prop :=
  ∀ (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), CylEtaTest c t₀ t₁ φ →
    ∀ r ∈ Ioo t₀ t₁, (∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x) (deriv (fun r' => φ r' x) r) r) ∧
      Continuous (fun x : B0579.Plane => deriv (fun r' => φ r' x) r)

/-- **Leaf 3: integration by parts of the Laplacian on the cell** (SP 2097-2101). For two `C²`
functions, `c`-periodic in `q`, decaying with `∇` and `Δ` faster than every power of `1 + η²`:
`∫_cell Δg h = ∫_cell g Δh`, both integrands integrable. -/
def RtdLapIBP : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g h : B0579.Plane → ℝ, CylSmoothDecay c g → CylSmoothDecay c h →
    IntegrableOn (fun x => lapP g x * h x) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * lapP h x) (B0579.cell c) ∧
      ∫ x in B0579.cell c, lapP g x * h x = ∫ x in B0579.cell c, g x * lapP h x

/-- **Leaf 4: integration by parts of the transport term on the cell** (SP 2092-2093,
2097-2101). For the train velocity at an age `r ≥ 0` (smooth, `c`-periodic, divergence free,
bounded): `∫_cell (v·∇g) h = -∫_cell g (v·∇h)`, both integrands integrable. -/
def RtdTransportIBP : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (r : ℝ), 0 ≤ r → 0 < c →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    ∀ g h : B0579.Plane → ℝ, CylSmoothDecay c g → CylSmoothDecay c h →
      IntegrableOn (fun x => (tr.v r x 0 * B0579.pd 0 g x + tr.v r x 1 * B0579.pd 1 g x) * h x)
          (B0579.cell c) ∧
        IntegrableOn (fun x => g x * (tr.v r x 0 * B0579.pd 0 h x + tr.v r x 1 * B0579.pd 1 h x))
          (B0579.cell c) ∧
        ∫ x in B0579.cell c, (tr.v r x 0 * B0579.pd 0 g x + tr.v r x 1 * B0579.pd 1 g x) * h x =
          -∫ x in B0579.cell c, g x * (tr.v r x 0 * B0579.pd 0 h x + tr.v r x 1 * B0579.pd 1 h x)

/-- **Leaf 5: continuity of the pairing** (SP 2074-2105). `r ↦ ∫_cell ω(r) φ(r)` is continuous on
`[s, t₁]` (joint continuity of `ω` and `φ`, domination by the uniform decay in `η`). -/
def RtdCont : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (s T t₁ : ℝ) (ω φ : ℝ → B0579.Plane → ℝ),
    0 < c → s ≤ t₁ → t₁ ≤ T → IsRegularCylFlow c ν tr.v s T ω → CylEtaTest c s t₁ φ →
    ContinuousOn (fun r => ∫ x in B0579.cell c, ω r x * φ r x) (Icc s t₁)

/-- **Leaf 6: differentiation of the pairing under the integral sign** (SP 2074-2105). Inside
`(s, t₁)`, `∂_r(ω φ) = (νΔω - v·∇ω) φ + ω ∂_r φ` (the `pde` field of `IsRegularCylFlow`), dominated
uniformly near `r` by the decay of `ω, ∇ω, Δω`, `φ` and `∂_r φ` and the bound on `v`; the pairing
`ω(r) ∂_r φ(r)` is integrable on the cell. -/
def RtdHasDeriv : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (s T t₁ : ℝ) (ω φ : ℝ → B0579.Plane → ℝ),
    0 < c → 0 ≤ s → s ≤ t₁ → t₁ ≤ T → IsRegularCylFlow c ν tr.v s T ω → CylEtaTest c s t₁ φ →
    (∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Ioo s t₁, ∀ x : B0579.Plane,
      |deriv (fun r' => φ r' x) r| * (1 + x.2 ^ 2) ^ N ≤ C) →
    (∃ M : ℝ, ∀ r ∈ Icc s T, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    ∀ r ∈ Ioo s t₁,
      IntegrableOn (fun x => ω r x * deriv (fun r' => φ r' x) r) (B0579.cell c) ∧
      HasDerivAt (fun r' => ∫ x in B0579.cell c, ω r' x * φ r' x)
        (∫ x in B0579.cell c, ((ν * lapP (ω r) x -
            (tr.v r x 0 * B0579.pd 0 (ω r) x + tr.v r x 1 * B0579.pd 1 (ω r) x)) * φ r x +
          ω r x * deriv (fun r' => φ r' x) r)) r

/-- **Leaf 7: the tested right-hand side is bounded** (SP 2074-2105) uniformly for ages in
`(s, t₁)`: `|ω| ≤ C (1 + η²)⁻¹` uniformly, `∂_r φ, Δφ, ∇φ` and `v` bounded, and
`∫_cell (1 + η²)⁻¹ < ∞`. -/
def RtdRhsBound : Prop :=
  ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (s T t₁ : ℝ) (ω φ : ℝ → B0579.Plane → ℝ),
    0 < c → s ≤ t₁ → t₁ ≤ T → IsRegularCylFlow c ν tr.v s T ω → CylEtaTest c s t₁ φ →
    (∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Ioo s t₁, ∀ x : B0579.Plane,
      |deriv (fun r' => φ r' x) r| * (1 + x.2 ^ 2) ^ N ≤ C) →
    (∃ M : ℝ, ∀ r ∈ Icc s T, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    ∃ C : ℝ, ∀ r ∈ Ioo s t₁, |∫ x in B0579.cell c, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))| ≤ C

/-- **Leaf 8: the fundamental theorem of calculus with a bounded derivative.** A function
continuous on `[a, b]`, differentiable on `(a, b)` with a bounded derivative `f'`, satisfies
`∫_a^b f' = f b - f a` (`f'` agrees with the measurable `deriv f` on `(a, b)`). -/
def RtdFTC : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) →
    (∀ r ∈ Ioo a b, HasDerivAt f (f' r) r) → (∃ C : ℝ, ∀ r ∈ Ioo a b, |f' r| ≤ C) →
    ∫ r in a..b, f' r = f b - f a

/-- **The assembly.** -/
theorem cylRegularTimeDep_of (h1 : RtdSlice) (h3 : RtdLapIBP) (h4 : RtdTransportIBP)
    (h5 : RtdCont) (h6 : RtdHasDeriv) (h7 : RtdRhsBound) (h8 : RtdFTC) :
    CylRegularTimeDep := by
  intro Sg ν c δ _hSg _hν hc _hδ tr _htr s T ω hs _hT hω t₁ φ hst ht₁ hφ hφr hM
  have hD : ∀ r ∈ Ioo s t₁, HasDerivAt (fun r' => ∫ x in B0579.cell c, ω r' x * φ r' x)
      (∫ x in B0579.cell c, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) r := by
    intro r hr
    obtain ⟨hi, hd⟩ := h6 ν c tr s T t₁ ω φ hc hs hst ht₁ hω hφ hφr hM r hr
    have hrT : r ∈ Icc s T := ⟨hr.1.le, hr.2.le.trans ht₁⟩
    have hg := hω.slice r hrT
    have hh := h1 c s t₁ φ hφ r ⟨hr.1.le, hr.2.le⟩
    obtain ⟨M, hM'⟩ := hM
    obtain ⟨iL1, iL2, eL⟩ := h3 c hc (ω r) (φ r) hg hh
    obtain ⟨iT1, iT2, eT⟩ :=
      h4 ν c tr r (hs.trans hr.1.le) hc ⟨M, hM' r hrT⟩ (ω r) (φ r) hg hh
    convert hd using 1
    have eA : (fun x => ω r x * (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
        (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) =
        fun x => (ω r x * deriv (fun r' => φ r' x) r + ν * (ω r x * lapP (φ r) x)) +
          ω r x * (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x) := by
      funext x; ring
    have eB : (fun x => (ν * lapP (ω r) x -
        (tr.v r x 0 * B0579.pd 0 (ω r) x + tr.v r x 1 * B0579.pd 1 (ω r) x)) * φ r x +
          ω r x * deriv (fun r' => φ r' x) r) =
        fun x => (ν * (lapP (ω r) x * φ r x) -
          (tr.v r x 0 * B0579.pd 0 (ω r) x + tr.v r x 1 * B0579.pd 1 (ω r) x) * φ r x) +
          ω r x * deriv (fun r' => φ r' x) r := by
      funext x; ring
    have jL1 : IntegrableOn (fun x => ν * (lapP (ω r) x * φ r x)) (B0579.cell c) :=
      iL1.const_mul ν
    have jL2 : IntegrableOn (fun x => ν * (ω r x * lapP (φ r) x)) (B0579.cell c) :=
      iL2.const_mul ν
    have j1 : IntegrableOn (fun x => ω r x * deriv (fun r' => φ r' x) r +
        ν * (ω r x * lapP (φ r) x)) (B0579.cell c) := hi.add jL2
    have j2 : IntegrableOn (fun x => ν * (lapP (ω r) x * φ r x) -
        (tr.v r x 0 * B0579.pd 0 (ω r) x + tr.v r x 1 * B0579.pd 1 (ω r) x) * φ r x)
        (B0579.cell c) := jL1.sub iT1
    rw [eA, eB, integral_add j1 iT2, integral_add hi jL2, integral_add j2 hi,
      integral_sub jL1 iT1, integral_const_mul, integral_const_mul, eL, eT]
    ring
  have hFTC := h8 (fun r' => ∫ x in B0579.cell c, ω r' x * φ r' x)
    (fun r => ∫ x in B0579.cell c, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))) s t₁ hst
    (h5 ν c tr s T t₁ ω φ hc hst ht₁ hω hφ) hD (h7 ν c tr s T t₁ ω φ hc hst ht₁ hω hφ hφr hM)
  exact hFTC.symm

end UnforcedLeray.Short.IIb
