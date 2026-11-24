import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T02/3/10`: `ClassicalEnergyBound` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 276-282 ("on each finite
interval ... which continues `L²` membership. Approximation and transverse cutoffs then give the
velocity ... energy identities") and the classical cutoff energy method.

The target is `ClassicalEnergyBound` (`Short/PartI/Sub/T02_3.lean`, line 183): for a classical
solution `(v, p)` on `[0, T]` with all spatial derivatives of `v` bounded and `|p| ≤ Mp`, the cell
energy `∫_cell |v(s)|²` is bounded on `[0, T]`.

## Mathematics (with `φ = φ_R = etaCutoff R`, `E_R(s) = ∫_cell φ |v(s)|²`)

Differentiating under the integral sign (everything is continuous and supported in `|η| ≤ 2R`),
and using `∂_s v = νΔv - (v·∇)v - ∇p` on `(0, T)`,

    E_R'(s) = ∫_cell φ · 2⟨v, ∂_s v⟩ = T_visc + T_conv + T_pres,
    T_visc = 2ν ∫ φ ⟨v, Δv⟩,   T_conv = -2 ∫ φ ⟨v, (v·∇)v⟩,   T_pres = -2 ∫ φ ⟨v, ∇p⟩.

Cell integration by parts (`φ = φ(η)`, `div v = 0`, `q`-periodicity):

* `T_visc = -2ν D_R - 2ν ∫ φ' ⟨v, ∂_η v⟩`, `D_R = ∫ φ |∇v|² ≥ 0`;
* `T_conv = ∫ |v|² v_η φ'`;
* `T_pres = 2 ∫ φ' p v_η`.

By `EtaCutoffFacts`, `|φ'| ≤ C₀/R` and `φ' = 0` outside `R ≤ |η| ≤ 2R`; that strip meets the cell in a
set of measure `2cR` (we bound it by the box `|η| ≤ 2R`, of measure `4cR`), so
`|∫_cell φ' g| ≤ 4 C₀ c sup|g|`, uniformly in `R`.  With `|v| ≤ Mv`,
`|∂_η v| ≤ Kv`, `|p| ≤ Mp` the sum of the three right sides is at most a constant `K` independent of
`R`.  Hence `E_R(s) ≤ E_R(0) + K s ≤ ∫_cell |v(0)|² + K T`, and `R → ∞` (monotone/dominated
convergence, `φ_R = 1` for `|η| ≤ R`) gives `∫_cell |v(s)|² ≤ ∫_cell |v(0)|² + K T`.

## What is proved here

`classicalEnergyBound_of` derives `ClassicalEnergyBound` from `EtaCutoffFacts` (proved by task
`PartI:T02/3/9`) and eight leaf statements `EbContinuous`, `EbHasDeriv`, `EbDecomp`,
`EbViscousIdentity`, `EbConvIdentity`, `EbPressureIdentity`, `EbFluxBound`, `EbLimit`.  Three toolkit
statements are shared by the leaves: `EbSliceSmooth`, `EbStripBound`, `EbDerivBounds`.  The cell
toolkit `CellIntegrableOfSupport`, `CellDerivZero` (`Sub/T05b_2.lean`) is already proved
(`cellToolkit`, `Tasks/TrainCutoffEnergyProof/CellToolkit.lean`).  The identity leaves are the
classical-solution analogues of the proved `TransportIdentity`, `PressureIdentity`,
`ViscousIdentity` for the difference of two trains (`Tasks/TrainCutoffEnergyProof/*.lean`).

The unconditional target is task `PartI:T02/3/10`
(`Short/PartI/Tasks/ClassicalOdd/ClassicalEnergyBound.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Notation -/

/-- The cutoff energy `E_R(s) = ∫_cell φ_R(η) |v(s)|²`. -/
def ebEnergy (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖v s z‖ ^ 2

/-- The cutoff dissipation `D_R(s) = ∫_cell φ_R |∇v(s)|²`. -/
def ebDissipation (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (v s) z

/-- The integrand of the time derivative of `E_R`: `∫_cell φ_R · 2⟨v, ∂_s v⟩`. -/
def ebDtIntegral (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s))

/-- The viscous term `T_visc = 2ν ∫_cell φ_R ⟨v, Δv⟩`. -/
def ebViscous (ν c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  2 * ν * ∫ z in Cyl.cell c,
    etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)

/-- The convective term `T_conv = -2 ∫_cell φ_R ⟨v, (v·∇)v⟩`. -/
def ebConv (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)

/-- The pressure term `T_pres = -2 ∫_cell φ_R ⟨v, ∇p⟩`. -/
def ebPres (c : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ) : ℝ :=
  -2 * ∫ z in Cyl.cell c, etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)

/-- Right side of the viscous identity: `-2νD_R - 2ν ∫ φ' ⟨v, ∂_η v⟩`. -/
def ebViscousRhs (ν c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  -2 * ν * ebDissipation c v R s - 2 * ν * ∫ z in Cyl.cell c,
    deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)

/-- Right side of the convective identity: `∫ |v|² v_η φ'`. -/
def ebConvRhs (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2

/-- Right side of the pressure identity: `2 ∫ φ' p v_η`. -/
def ebPresRhs (c : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) (R s : ℝ) : ℝ :=
  2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * p s z * v s z 1

/-! ### Toolkit leaves -/

/-- **Toolkit `EbSliceSmooth`**: for `s ∈ [0, T]` the slices `v(s)`, `p(s)` of a classical solution
are `C^∞` on the plane (compose `smooth_v`, `smooth_p` on `Icc 0 T ×ˢ univ` with `z ↦ (s, z)`; the
train analogue is `trainSliceSmooth`, `Tasks/TrainCutoffEnergyProof/SliceSmooth.lean`). -/
def EbSliceSmooth : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), IsClassicalOn ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (v s) ∧ ContDiff ℝ ∞ (p s)

/-- **Toolkit `EbStripBound`** (boundary strip estimate): there is `K₀ ≥ 0` such that for all
`c > 0`, `R ≥ 1` and every continuous `g` with `|g| ≤ B`,
`|∫_cell φ_R'(η) g| ≤ K₀ c B`.  (From `EtaCutoffFacts`: `|φ_R'| ≤ C₀/R` and `φ_R' = 0` for
`|η| ≥ 2R`, and the set `{|η| ≤ 2R} ∩ cell` has measure `4cR`, so `K₀ = 4C₀` works; the sharper
`2C₀` would also use `φ_R' = 0` for `|η| < R`.) -/
def EbStripBound : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (c R : ℝ), 0 < c → 1 ≤ R → ∀ (g : Plane → ℝ) (B : ℝ), Continuous g →
    (∀ z, |g z| ≤ B) → |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * g z| ≤ K₀ * c * B

/-- **Toolkit `EbDerivBounds`**: `HasBoundedDerivsOn` at orders `0` and `1` gives uniform bounds
`‖v(s, z)‖ ≤ Mv` and `‖∂_η v(s, z)‖ ≤ Kv` on `[0, T] × ℝ²` (`‖iteratedFDeriv ℝ 0 f z‖ = ‖f z‖`,
`‖iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f z‖`, `Cyl.partialEta_eq_fderiv`; pattern of
`Tasks/LocalClassicalBounded/FiniteEnergyDecay.lean`). -/
def EbDerivBounds : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), IsClassicalOn ν c T v p →
    HasBoundedDerivsOn T v → ∃ Mv Kv : ℝ, 0 ≤ Mv ∧ 0 ≤ Kv ∧ ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      ‖v s z‖ ≤ Mv ∧ ‖Cyl.partialEta (v s) z‖ ≤ Kv

/-! ### The cutoff energy: continuity, derivative, splitting -/

/-- **Leaf `EbContinuous`**: `E_R` is continuous on `[0, T]` (the integrand is jointly continuous
on `[0, T] × ℝ²` and supported in the compact box `[-c/2, c/2] × [-2R, 2R]`). -/
def EbContinuous : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ContinuousOn (ebEnergy c v R) (Icc (0 : ℝ) T)

/-- **Leaf `EbHasDeriv`** (differentiation under the integral sign): for `s ∈ (0, T)`,
`E_R'(s) = ∫_cell φ_R · 2⟨v, ∂_s v⟩`. -/
def EbHasDeriv : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (ebEnergy c v R) (ebDtIntegral c v R s) s

/-- **Leaf `EbDecomp`** (the momentum equation): for `s ∈ (0, T)`, `∂_s v = νΔv - (v·∇)v - ∇p`, so
`∫_cell φ_R · 2⟨v, ∂_s v⟩` is the sum of the three terms (all integrands are continuous with support
in `|η| ≤ 2R`, hence integrable on the cell). -/
def EbDecomp : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Ioo (0 : ℝ) T,
      ebDtIntegral c v R s = ebViscous ν c v R s + ebConv c v R s + ebPres c v p R s

/-! ### Identities -/

/-- **Leaf `EbViscousIdentity`**: `T_visc = -2νD_R - 2ν ∫ φ' ⟨v, ∂_η v⟩` (cell integration by parts of
`φ v_i (∂_q² + ∂_η²) v_i` for each component; `φ` depends on `η` only). -/
def EbViscousIdentity : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T, ebViscous ν c v R s = ebViscousRhs ν c v R s

/-- **Leaf `EbConvIdentity`**: `T_conv = ∫ |v|² v_η φ'` (`-2⟨v, (v·∇)v⟩ = -v·∇|v|²`, then
`∫ |v|² ∂_j(φ v_j) = ∫ |v|² φ' v_η` since `div v = 0`). -/
def EbConvIdentity : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T, ebConv c v R s = ebConvRhs c v R s

/-- **Leaf `EbPressureIdentity`**: `T_pres = 2 ∫ φ' p v_η` (`-2φ⟨v, ∇p⟩ = -2 div(φ p v) + 2p⟨v, ∇φ⟩`
since `div v = 0`; cell integration by parts in `q` and `η`). -/
def EbPressureIdentity : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < c → IsClassicalOn ν c T v p →
    ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T, ebPres c v p R s = ebPresRhs c v p R s

/-! ### The boundary terms and the limit -/

/-- **Leaf `EbFluxBound`**: with `|v| ≤ Mv`, `|∂_η v| ≤ Kv`, `|p| ≤ Mp`, the three right sides add up
to at most a constant `K` independent of `R` and `s`.  (Use `EbStripBound` with
`g = ⟨v, ∂_η v⟩` (`|g| ≤ Mv Kv`), `g = |v|² v_η` (`|g| ≤ Mv³`), `g = p v_η` (`|g| ≤ Mp Mv`), and
`-2νD_R ≤ 0`.) -/
def EbFluxBound : Prop :=
  ∀ (ν c T Mp : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 0 < c →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → (∀ s ∈ Icc (0 : ℝ) T, ∀ z, |p s z| ≤ Mp) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ebViscousRhs ν c v R s + ebConvRhs c v R s + ebPresRhs c v p R s ≤ K

/-- **Leaf `EbLimit`** (`R → ∞`): if `f ≥ 0` is integrable on the cell and `∫_cell φ_R f ≤ A` for all
`R ≥ 1`, then `∫_cell f ≤ A` (`φ_R = 1` for `|η| ≤ R`, so `φ_R f → f` pointwise, dominated by `f`). -/
def EbLimit : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Plane → ℝ) (A : ℝ), (∀ z, 0 ≤ f z) → IntegrableOn f (Cyl.cell c) →
    (∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * f z ≤ A) →
      ∫ z in Cyl.cell c, f z ≤ A

/-! ### The conditional theorem -/

/-- **`PartI:T02/3/10`, conditional form**: `ClassicalEnergyBound` from `EtaCutoffFacts` and the
eight leaves. -/
theorem classicalEnergyBound_of (hF : EtaCutoffFacts) (hC : EbContinuous) (hD : EbHasDeriv)
    (hE : EbDecomp) (hVi : EbViscousIdentity) (hTi : EbConvIdentity)
    (hPi : EbPressureIdentity) (hX : EbFluxBound) (hL : EbLimit) : ClassicalEnergyBound := by
  intro ν c T Mp v p hν hc hT hcl hb hp
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK0, HK⟩ := hX ν c T Mp v p hν hc0 hcl hb hp
  obtain ⟨C₀, -, hFC⟩ := hF
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hint0 : IntegrableOn (fun z => ‖v 0 z‖ ^ 2) (Cyl.cell c) :=
    hcl.finite_energy 0 ⟨le_rfl, hT0⟩
  refine ⟨(∫ z in Cyl.cell c, ‖v 0 z‖ ^ 2) + K * T, ?_⟩
  intro s hs
  refine hL c hc0 (fun z => ‖v s z‖ ^ 2) _ (fun z => sq_nonneg _) (hcl.finite_energy s hs) ?_
  intro R hR
  show ebEnergy c v R s ≤ _
  have hcont : ContinuousOn (ebEnergy c v R) (Icc 0 T) := hC ν c T v p hc0 hcl R hR
  -- the differential inequality
  have hle : ∀ r ∈ Ioo (0 : ℝ) T, ebDtIntegral c v R r ≤ K := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hr
    rw [hE ν c T v p hc0 hcl R hR r hr, hVi ν c T v p hc0 hcl R hR r hr',
      hTi ν c T v p hc0 hcl R hR r hr', hPi ν c T v p hc0 hcl R hR r hr']
    exact HK R hR r hr'
  -- integrate: `H r = E_R r - K r` is antitone on `[0, T]`
  set H : ℝ → ℝ := fun r => ebEnergy c v R r - K * r with hH
  have hHcont : ContinuousOn H (Icc 0 T) :=
    hcont.sub (continuousOn_const.mul continuousOn_id)
  have hHder : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt H (ebDtIntegral c v R r - K) r := by
    intro r hr
    have h := (hD ν c T v p hc0 hcl R hR r hr).sub ((hasDerivAt_id' r).const_mul K)
    rwa [mul_one] at h
  have hanti : AntitoneOn H (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hHcont
    · intro r hr
      rw [interior_Icc] at hr
      exact (hHder r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hHder r hr).deriv]
      have := hle r hr
      linarith
  have hHs : H s ≤ H 0 := hanti ⟨le_rfl, hT0⟩ hs hs.1
  -- the initial cutoff energy is at most the initial energy
  have hφ1 : ∀ z : Plane, etaCutoff R z.2 ≤ 1 := fun z => (hFC R hR).2.1 z.2 |>.2
  have h0 : ebEnergy c v R 0 ≤ ∫ z in Cyl.cell c, ‖v 0 z‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) hint0
      (Filter.Eventually.of_forall fun z => ?_)
    · exact mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _)
    · have := mul_le_mul_of_nonneg_right (hφ1 z) (sq_nonneg ‖v 0 z‖)
      simpa using this
  have hKs : K * s ≤ K * T := mul_le_mul_of_nonneg_left hs.2 hK0
  have hH0 : H 0 = ebEnergy c v R 0 := by simp [hH]
  have hHs' : ebEnergy c v R s - K * s ≤ ebEnergy c v R 0 := by
    have := hHs
    rw [hH0] at this
    simpa [hH] using this
  linarith

end UnforcedLeray.Short.PartI
