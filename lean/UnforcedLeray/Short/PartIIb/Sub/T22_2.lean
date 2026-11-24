import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.DecayForcesZero
import UnforcedLeray.Short.PartIIb.Sub.T22

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2105
(uniqueness of weak solutions by duality with the regular backward problem).

The target `cylWeakEqClassical : CylWeakEqClassical` is NOT proved in this file. With the current
`CylSmoothDecay` (decay in `1 + η²`) the target is a genuine duality statement for every datum
`f`. `cylWeakEqClassical_of_parts` derives it from five named statements:
* `CylWeakTimeDep` (N1): weak identity of `IsFreeCylFlow` against time-dependent `CylEtaTest` tests,
* `CylRegularTimeDep` (N1'): the same identity for a regular flow (classical integration by parts),
* `CylBackwardSolve` (N2): the backward transport-diffusion problem with `η`-decaying solution
  (`CylEtaSpatial`; the decay of `∂_r φ` then follows from the equation and N4,
  `CylEtaSpatial.toCylEtaTest`),
* `CylFundLemma` (N3): two weighted `L²` functions with equal pairings against all `IsCylTest`
  tests agree a.e. on the cell,
* `CylTrainBound` (N4): the train velocity is bounded on `[0, Σ/ν]`,
* `CylRegularMem` (N5): slices of a regular flow lie in `L²(cellMeasure c m)`.
Proof: pair `ω σ` and `ω' σ` with `ψ`; solve the backward problem with terminal datum `ψ`; both
time-dependent identities have right-hand side `0` (the integrand carries the factor
`∂_r φ + νΔφ + v·∇φ = 0`) and the same datum term (`ω' s = f`); conclude with N3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-! ## The corrected test class and the four needed statements -/

/-- The spatial part of a time-dependent test: smooth on `[t₀, t₁] × ℝ²`, `c`-periodic in `q`, and
`φ, ∇φ, Δφ` decay of every order in `η` (weight `(1 + η²)^N`), uniformly for the ages
`r ∈ [t₀, t₁]` (SP 2074-2105). This is what the backward problem N2 produces; it does not control
the age derivative `∂_r φ` (`CylEtaTest` adds that). -/
structure CylEtaSpatial (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop where
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
    (Icc t₀ t₁ ×ˢ univ)
  periodic : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, φ r (x.1 + c, x.2) = φ r x
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
    (|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| + |lapP (φ r) x|) *
      (1 + x.2 ^ 2) ^ N ≤ C

/-- Time-dependent tests of the duality argument (SP 2074-2105): smooth, `c`-periodic in `q`, with
decay of every order in `η` (weight `(1 + η²)^N`), uniform for the ages `r ∈ [t₀, t₁]`, of
`φ, ∇φ, Δφ` (`decay`) and of the age derivative `∂_r φ` on `(t₀, t₁)` (`decay_r`). Unlike
`CylSmoothDecay` (weight `jb ^ N`), this class is not empty of nonzero members.

`decay_r` is not implied by the other fields (e.g. `φ = Σ_j j^(-j) B(η - j) sin(j^j r)`, `B` a bump),
and without it the pairing `∫_cell ω ∂_r φ` need not be integrable and `φ` need not be a weighted
`C¹` limit of separated sums (`CylTdApproxSums`, `Sub/PartIIb_T22_2_1_2.lean`). The duality
argument uses only backward solutions, for which `∂_r φ = -(νΔφ + v·∇φ)` decays
(`CylEtaSpatial.toCylEtaTest`). -/
structure CylEtaTest (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop where
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
    (Icc t₀ t₁ ×ˢ univ)
  periodic : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, φ r (x.1 + c, x.2) = φ r x
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
    (|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| + |lapP (φ r) x|) *
      (1 + x.2 ^ 2) ^ N ≤ C
  decay_r : ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
    |deriv (fun r' => φ r' x) r| * (1 + x.2 ^ 2) ^ N ≤ C

/-- The spatial part of a time-dependent test. -/
theorem CylEtaTest.toSpatial {c t₀ t₁ : ℝ} {φ : ℝ → B0579.Plane → ℝ} (h : CylEtaTest c t₀ t₁ φ) :
    CylEtaSpatial c t₀ t₁ φ :=
  ⟨h.smooth, h.periodic, h.decay⟩

/-- **A backward solution is a time-dependent test.** If `φ` has the spatial decay of
`CylEtaSpatial` and solves `∂_r φ = -(νΔφ + v·∇φ)` on `(t₀, t₁)` with a bounded drift `v`, then
`∂_r φ` decays like `Δφ, ∇φ`, with constant `(ν + M) C`. -/
theorem CylEtaSpatial.toCylEtaTest {ν c t₀ t₁ M : ℝ} (hν : 0 ≤ ν) {φ : ℝ → B0579.Plane → ℝ}
    (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (hφ : CylEtaSpatial c t₀ t₁ φ)
    (hM : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |v r x 0| + |v r x 1| ≤ M)
    (hPDE : ∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x)
        (-(ν * lapP (φ r) x + (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x))) r) :
    CylEtaTest c t₀ t₁ φ := by
  refine ⟨hφ.smooth, hφ.periodic, hφ.decay, ?_⟩
  intro N
  obtain ⟨C, hC⟩ := hφ.decay N
  refine ⟨(ν + M) * C, fun r hr x => ?_⟩
  have hrI : r ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hr
  rw [(hPDE r hr x).deriv]
  have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
  have hv := hM r hrI x
  have hv0 : |v r x 0| ≤ M := by linarith [abs_nonneg (v r x 1)]
  have hv1 : |v r x 1| ≤ M := by linarith [abs_nonneg (v r x 0)]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hv0
  have hCx := hC r hrI x
  have key : |-(ν * lapP (φ r) x + (v r x 0 * B0579.pd 0 (φ r) x +
      v r x 1 * B0579.pd 1 (φ r) x))| ≤ (ν + M) * (|φ r x| + |B0579.pd 0 (φ r) x| +
        |B0579.pd 1 (φ r) x| + |lapP (φ r) x|) := by
    rw [abs_neg]
    have e1 : |ν * lapP (φ r) x| = ν * |lapP (φ r) x| := by
      rw [abs_mul, abs_of_nonneg hν]
    have e2 : |v r x 0 * B0579.pd 0 (φ r) x| ≤ M * |B0579.pd 0 (φ r) x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv0 (abs_nonneg _)
    have e3 : |v r x 1 * B0579.pd 1 (φ r) x| ≤ M * |B0579.pd 1 (φ r) x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
    have t1 := abs_add_le (ν * lapP (φ r) x)
      (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x)
    have t2 := abs_add_le (v r x 0 * B0579.pd 0 (φ r) x) (v r x 1 * B0579.pd 1 (φ r) x)
    have a0 := abs_nonneg (φ r x)
    have a1 := abs_nonneg (B0579.pd 0 (φ r) x)
    have a2 := abs_nonneg (B0579.pd 1 (φ r) x)
    have a3 := abs_nonneg (lapP (φ r) x)
    nlinarith
  calc |-(ν * lapP (φ r) x + (v r x 0 * B0579.pd 0 (φ r) x +
          v r x 1 * B0579.pd 1 (φ r) x))| * (1 + x.2 ^ 2) ^ N
      ≤ (ν + M) * (|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
          |lapP (φ r) x|) * (1 + x.2 ^ 2) ^ N := mul_le_mul_of_nonneg_right key hw
    _ = (ν + M) * ((|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
          |lapP (φ r) x|) * (1 + x.2 ^ 2) ^ N) := by ring
    _ ≤ (ν + M) * C := mul_le_mul_of_nonneg_left hCx (by linarith)

/-- **Needed N1: the weak identity against time-dependent tests** (the extension of the
time-independent `weak` field of `IsFreeCylFlow` to `CylEtaTest` tests; the pairing of `ω` with
the transport-diffusion operator in `cylFreeIntegrand`, with the time derivative of the test). -/
def CylWeakTimeDep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), 0 < c → IsFreeCylFlow m tr t₀ f ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), t₀ ≤ t₁ → CylEtaTest c t₀ t₁ φ →
    (∃ M : ℝ, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    (∫ x in B0579.cell c, ω t₁ x * φ t₁ x) - ∫ x in B0579.cell c, f x * φ t₀ x =
      ∫ r in t₀..t₁, ∫ x in B0579.cell c, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))

/-- **Needed N2: the backward problem** (time-reversed transport-diffusion with the train velocity,
terminal datum `ψ` at age `t`). Standard parabolic theory on the periodic cylinder; the smoothness
and the `η`-decay are those of `CylEtaSpatial`.

Remark: the conclusion is `CylEtaSpatial`, not the full `CylEtaTest`. The remaining field
`CylEtaTest.decay_r` (decay of `∂_r φ`) is a consequence of the backward equation in the conclusion,
of `decay`, and of the train bound N4 (`CylTrainBound`): `∂_r φ = -(νΔφ + v·∇φ)`; it is supplied by
`CylEtaSpatial.toCylEtaTest` in `cylWeakEqClassical_of_parts`. -/
def CylBackwardSolve : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
      ∃ φ : ℝ → B0579.Plane → ℝ, φ t = ψ ∧ CylEtaSpatial c s t φ ∧
        ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
          HasDerivAt (fun r' => φ r' x)
            (-(ν * lapP (φ r) x + (tr.v r x 0 * B0579.pd 0 (φ r) x +
              tr.v r x 1 * B0579.pd 1 (φ r) x))) r

/-- **Needed N3: fundamental lemma on the cell** in the weighted space `L²(cellMeasure c m)`,
`0 ≤ m`: two functions with equal pairings against every `IsCylTest c` test agree a.e. on the
cell (the pairings are integrable: `L²` against a rapidly decaying test). -/
def CylFundLemma : Prop :=
  ∀ (c m : ℝ), 0 < c → 0 ≤ m → ∀ g₁ g₂ : B0579.Plane → ℝ,
    MemLp g₁ 2 (B0579.cellMeasure c m) → MemLp g₂ 2 (B0579.cellMeasure c m) →
    (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, g₁ x * φ x = ∫ x in B0579.cell c, g₂ x * φ x) →
    g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂

/-- **Needed N4: the train velocity is bounded** on the plane, uniformly for ages in `[0, Σ/ν]`
(from `TrainClose` and the boundedness of the periodized vortex `Train.Vc`). -/
def CylTrainBound : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ Sg / ν →
      ∀ x : B0579.Plane, |tr.v s x 0| + |tr.v s x 1| ≤ M

/-- **Needed N1': the time-dependent identity for a regular flow** (SP 2074-2105; classical
integration by parts on the cell, the step "a regular solution is a weak solution" of the
duality argument). The velocity is the train velocity `tr.v` under `TrainClose tr Σ δ` on ages
`[s, T] ⊆ [0, Σ/ν]`: smooth (`tr.isTrain.smooth_v`), `c`-periodic in `q` (`periodic_v`) and
divergence free (`tr.isTrain.solenoidal`, in the form `Cyl.divergence (tr.v r) x = 0`, used by
`cylTransportIBP`), so the transport term moves onto the test, `∫ (v·∇ω) φ = -∫ ω (v·∇φ)`. (The
first version of this Prop had a free velocity with only `|v| ≤ M`; then the identity is false,
the integration by parts leaves `-∫ ω φ div v`.)

The hypothesis that the time derivative of the test decays in `η` uniformly on `(s, t₁)` is the
field `CylEtaTest.decay_r` (added later); it is kept as a separate (redundant) hypothesis because the
decomposition `Sub/PartIIb_T22_2_2.lean` is stated with it. -/
def CylRegularTimeDep : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ (s T : ℝ) (ω : ℝ → B0579.Plane → ℝ), 0 ≤ s → T ≤ Sg / ν →
    IsRegularCylFlow c ν tr.v s T ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), s ≤ t₁ → t₁ ≤ T → CylEtaTest c s t₁ φ →
    (∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Ioo s t₁, ∀ x : B0579.Plane,
      |deriv (fun r' => φ r' x) r| * (1 + x.2 ^ 2) ^ N ≤ C) →
    (∃ M : ℝ, ∀ r ∈ Icc s T, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    (∫ x in B0579.cell c, ω t₁ x * φ t₁ x) - ∫ x in B0579.cell c, ω s x * φ s x =
      ∫ r in s..t₁, ∫ x in B0579.cell c, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))

/-- **Needed N5: slices of a regular flow lie in the weighted `L²`** (`C²` with decay in `η`). -/
def CylRegularMem : Prop :=
  ∀ (ν c m s T : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ω : ℝ → B0579.Plane → ℝ),
    0 < c → 0 ≤ m → IsRegularCylFlow c ν v s T ω →
    ∀ σ ∈ Icc s T, MemLp (ω σ) 2 (B0579.cellMeasure c m)

/-- The right-hand side of a time-dependent identity vanishes when `φ` solves the backward
problem on `(s, t)`. -/
theorem cyl_rhs_zero {ν : ℝ} {s t : ℝ} (hst : s ≤ t) (ω φ : ℝ → B0579.Plane → ℝ)
    (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (A : Set B0579.Plane)
    (hPDE : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x)
        (-(ν * lapP (φ r) x + (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x))) r)
    (μ : Measure B0579.Plane) :
    ∫ r in s..t, ∫ x in A, ω r x *
      (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
        (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x)) ∂μ = 0 := by
  have hpt : ∀ r ∈ Ioo s t, ∫ x in A, ω r x *
      (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
        (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x)) ∂μ = 0 := by
    intro r hr
    have hpx : ∀ x : B0579.Plane, ω r x *
        (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
          (v r x 0 * B0579.pd 0 (φ r) x + v r x 1 * B0579.pd 1 (φ r) x)) = 0 := by
      intro x
      rw [(hPDE r hr x).deriv]
      ring
    simp only [hpx, integral_zero]
  have htae : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t := by
    rw [ae_iff]
    simp
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
  · simp
  · filter_upwards [htae] with r hrt hr
    rw [Set.uIoc_of_le hst] at hr
    exact hpt r ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩

/-- **The duality reduction.** -/
theorem cylWeakEqClassical_of_parts (h1 : CylWeakTimeDep) (h1' : CylRegularTimeDep)
    (h2 : CylBackwardSolve) (h3 : CylFundLemma) (h4 : CylTrainBound) (h5 : CylRegularMem) :
    CylWeakEqClassical := by
  intro m hm Sg hSg ν c δ hν hc hδ tr htr s hs f _hf ω' hω' hω'f ω hω σ hσ
  have hsσ : s ≤ σ := hσ.1
  have hσT : σ ≤ Sg / ν := hσ.2
  obtain ⟨M, hM⟩ := h4 Sg ν c δ hSg hν hc hδ tr htr
  have hMr : ∀ r ∈ Icc s σ, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M :=
    fun r hr x => hM r (le_trans hs hr.1) (le_trans hr.2 hσT) x
  have hMT : ∃ M : ℝ, ∀ r ∈ Icc s (Sg / ν), ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M :=
    ⟨M, fun r hr x => hM r (le_trans hs hr.1) hr.2 x⟩
  refine h3 c m hc (by linarith) (ω' σ) (ω σ) (h5 ν c m s (Sg / ν) tr.v ω' hc (by linarith) hω' σ hσ)
    (hω.memX σ hsσ) ?_
  intro ψ hψ
  obtain ⟨φ, hφσ, hφ0, hPDE⟩ := h2 Sg ν c δ hSg hν hc hδ tr htr s σ hs hsσ hσT ψ hψ
  have hφ : CylEtaTest c s σ φ := hφ0.toCylEtaTest hν.le tr.v hMr hPDE
  have hφr := hφ.decay_r
  have k1 := h1 m hm ν c tr s f ω hc hω σ φ hsσ hφ ⟨M, hMr⟩
  have k2 := h1' Sg ν c δ hSg hν hc hδ tr htr s (Sg / ν) ω' hs le_rfl hω' σ φ hsσ hσT hφ hφr hMT
  rw [cyl_rhs_zero hsσ ω φ tr.v _ hPDE] at k1
  rw [cyl_rhs_zero hsσ ω' φ tr.v _ hPDE, hω'f] at k2
  rw [hφσ] at k1 k2
  linarith

end UnforcedLeray.Short.IIb
