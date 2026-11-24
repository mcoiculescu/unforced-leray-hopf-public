import UnforcedLeray.Short.PartI.Sub.T02
import UnforcedLeray.Units.B0238.VorticityEq

/-!
# Part I, task `PartI:T02/4`: `VorticityFirstMoment` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288 (the train
datum has vorticity in `L¹ ∩ L^∞`; "the scalar vorticity equation preserves zero circulation and its
`L¹, L^∞` bounds"; the datum vorticity is the periodized Gaussian `(2 - |x|²/2) e^{-|x|²/4}`).

The target is `VorticityFirstMoment` (`Short/PartI/Sub/T02.lean`): for a classical solution on
`[0,T]` with bounded derivatives, `∫_cell (1 + |η|) |ω(s)| < ∞` for every `s ∈ [0,T]`.

## Route chosen (audit note)

A weighted `L¹` Gronwall argument with an `η`-cutoff does **not** close under the hypotheses of
`VorticityFirstMoment`: the cutoff error is `‖v‖_∞ R^{-1} ∫_{R ≤ |η| ≤ 2R} (1+|η|)|ω|`, and with `ω`
only bounded (no a priori `L¹`) this is `O(1)`, not `o(1)`.  The route that closes is a pointwise
parabolic comparison (Phragmen-Lindelof barrier):

* `ω = curl v` solves `ω_s + v·∇ω - νΔω = 0` on `(0,T)` with `v` bounded by `β`
  (`LocalVorticityEquation`); `ω` is bounded and smooth (`CurlRegularity`);
* the datum satisfies `|ω(0,z)| ≤ A / cosh(a η)` (`TrainDatumCurlSech`, Gaussian tails);
* `B = A e^{K s} / cosh(a η)` with `K > β a + ν a²` is a strict supersolution, and so is
  `B + ε e^{K s} cosh(a η)` for every `ε > 0`; the second term dominates the bounded `ω` at
  `|η| ≥ R_ε`, so the parabolic minimum principle (`ParabolicMinPrinciple`, `SechSupersolution`,
  assembled in `ParabolicSechBarrier`) gives `|ω| ≤ B + ε e^{K s} cosh(a η)`; let `ε → 0`;
* `∫_cell (1 + |η|) / cosh(a η) < ∞` (`SechMomentIntegrable`).

`vorticityFirstMoment_of` derives `VorticityFirstMoment` from `LocalVorticityEquation`,
`CurlRegularity`, `ParabolicSechBarrier`, `TrainDatumCurlSech`, `SechMomentIntegrable`.  The
unconditional target is task `PartI:T02/4` (`Short/PartI/Sub/T02/VorticityFirstMoment.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The transport-diffusion operator `∂_s F + b·∇F - νΔF` with classical partials. -/
def vorticityOp (ν : ℝ) (b : ℝ → Plane → Vec) (F : ℝ → Plane → ℝ) (s : ℝ) (z : Plane) : ℝ :=
  deriv (fun t => F t z) s +
    (b s z 0 * Cyl.partialQ (F s) z + b s z 1 * Cyl.partialEta (F s) z) -
    ν * Train.lapS (F s) z

/-- The vorticity residual of the library is the operator applied to `ω = curl v`. -/
theorem vorticityResidual_eq_op (ν : ℝ) (v : ℝ → Plane → Vec) (s : ℝ) (z : Plane) :
    B0238.vorticityResidual ν v s z = vorticityOp ν v (fun t w => Cyl.curl (v t) w) s z := rfl

/-- The barrier `A e^{K s} / cosh(a η)`. -/
def sechBarrier (A K a : ℝ) (s : ℝ) (z : Plane) : ℝ :=
  A * Real.exp (K * s) * (Real.cosh (a * z.2))⁻¹

/-- The growing comparison term `ε e^{K s} cosh(a η)` (Phragmen-Lindelof). -/
def coshBarrier (ε K a : ℝ) (s : ℝ) (z : Plane) : ℝ :=
  ε * Real.exp (K * s) * Real.cosh (a * z.2)

/-- **Local-time vorticity equation** (source lines 276-288; adapt
`Units/B0238/VorticityEq.lean`, `vorticityResidual_eq_zero`, whose proof takes the curl of the
momentum equation on the open set `s > 0`): for a classical solution on `[0,T]`, `ω = curl v` solves
`ω_s + v·∇ω - νΔω = 0` on `(0,T)`.  The proof only uses smoothness on the open set
`(0,T) × ℝ²`, the symmetry of second and third derivatives, `div v = 0` and the momentum equation. -/
def LocalVorticityEquation : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → ∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane, B0238.vorticityResidual ν v s z = 0

/-- **Regularity of the vorticity**: for a smooth `c`-periodic velocity with bounded derivatives on
`[0,T]`, `ω = curl v` is continuous on `[0,T] × ℝ²`, `C²` on `(0,T) × ℝ²`, bounded (by
`2 sup ‖Dv‖`, `HasBoundedDerivsOn` with `k = 1`) and `c`-periodic in `q`. -/
def CurlRegularity : Prop :=
  ∀ (c T : ℝ) (v : ℝ → Plane → Vec), 0 < c → 0 < T →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ) →
    (∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) → HasBoundedDerivsOn T v →
    ContinuousOn (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (Icc 0 T ×ˢ univ) ∧
    ContDiffOn ℝ 2 (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (Ioo 0 T ×ˢ univ) ∧
    (∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ M) ∧
    (∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (Cyl.curl (v s)))

/-- **Parabolic minimum principle on the cylinder.**  `D` is continuous on `[0,T] × ℝ²`, `C²` on
`(0,T) × ℝ²`, `c`-periodic in `q`, nonnegative at `s = 0` and for `|η| ≥ R`, and at every point of
`(0,T) × ℝ²` where `D < 0` one has `∂_s D + b·∇D - νΔD > 0`.  Then `D ≥ 0` on `[0,T) × ℝ²`.
Proof: if `D` took a negative value, restrict to `[0,T'] × [-c/2,c/2] × [-R,R]` with `T' < T` (compact,
containing the negative value, by periodicity); the minimum `m < 0` is attained at `(s₀, z₀)` with
`s₀ > 0` and `|η₀| < R`; by periodicity `z₀` minimizes `D(s₀, ·)` over all of `ℝ²`, so
`∇D = 0` and `ΔD ≥ 0` there (second-derivative test along the two coordinate lines), and
`∂_s D(s₀, z₀) ≤ 0` (left difference quotient); hence the operator is `≤ 0`, a contradiction. -/
def ParabolicMinPrinciple : Prop :=
  ∀ (ν c T R : ℝ) (b : ℝ → Plane → Vec) (D : ℝ → Plane → ℝ), 0 < ν → 0 < c → 0 < T →
    ContinuousOn (fun x : ℝ × Plane => D x.1 x.2) (Icc 0 T ×ˢ univ) →
    ContDiffOn ℝ 2 (fun x : ℝ × Plane => D x.1 x.2) (Ioo 0 T ×ˢ univ) →
    (∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (D s)) →
    (∀ z : Plane, 0 ≤ D 0 z) →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, R ≤ |z.2| → 0 ≤ D s z) →
    (∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane, D s z < 0 → 0 < vorticityOp ν b D s z) →
    ∀ s ∈ Ico (0 : ℝ) T, ∀ z : Plane, 0 ≤ D s z

/-- **The `sech` / `cosh` barriers are supersolutions.**  With `‖b‖ ≤ β`, `ν ≥ 0`, `a > 0`:
`(K - β a - ν a²) (B + Φ) ≤ ∂_s(B+Φ) + b·∇(B+Φ) - νΔ(B+Φ)`, where `B = sechBarrier A K a`,
`Φ = coshBarrier ε K a`.  (Both depend only on `s, η`: `∂_s = K`, `|∂_η| ≤ a` times the function
since `|tanh|, |sinh/cosh| ≤ 1`, `∂_η² sech(aη) = a² sech (1 - 2 sech²) ≤ a² sech`,
`∂_η² cosh(aη) = a² cosh`; `∂_q = 0`.) -/
def SechSupersolution : Prop :=
  ∀ (ν β A ε K a : ℝ) (b : ℝ → Plane → Vec) (s : ℝ) (z : Plane), 0 ≤ ν → 0 < a → 0 ≤ A → 0 ≤ ε →
    ‖b s z‖ ≤ β →
    (K - β * a - ν * a ^ 2) * (sechBarrier A K a s z + coshBarrier ε K a s z) ≤
      vorticityOp ν b (fun t w => sechBarrier A K a t w + coshBarrier ε K a t w) s z

/-- **Exponential-decay comparison** for the vorticity equation with a bounded drift: a bounded
solution whose datum is below `A / cosh(a η)` stays below `A e^{K s} / cosh(a η)` for every
`K > β a + ν a²` (Phragmen-Lindelof: compare with `B + ε e^{K s} cosh(a η)`, which dominates the
bounded solution for `|η| ≥ R_ε`, apply `ParabolicMinPrinciple` to `D = B + Φ ∓ ω`, use
`SechSupersolution`, extend from `[0,T)` to `T` by continuity, let `ε → 0`). -/
def ParabolicSechBarrier : Prop :=
  ∀ (ν c T β A a K : ℝ) (b : ℝ → Plane → Vec) (om : ℝ → Plane → ℝ),
    0 < ν → 0 < c → 0 < T → 0 < a → 0 < A → β * a + ν * a ^ 2 < K →
    ContinuousOn (fun x : ℝ × Plane => om x.1 x.2) (Icc 0 T ×ˢ univ) →
    ContDiffOn ℝ 2 (fun x : ℝ × Plane => om x.1 x.2) (Ioo 0 T ×ˢ univ) →
    (∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (om s)) →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖b s z‖ ≤ β) →
    (∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |om s z| ≤ M) →
    (∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane, vorticityOp ν b om s z = 0) →
    (∀ z : Plane, |om 0 z| ≤ A * (Real.cosh (a * z.2))⁻¹) →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |om s z| ≤ sechBarrier A K a s z

/-- **The datum vorticity has exponential tails** (source lines 262-270; Gaussian tails of the
periodized vorticity `(2 - |x|²/2) e^{-|x|²/4}`): for `c ≥ 1` there are `A, a > 0` with
`|curl(trainDatum c)(q, η)| ≤ A / cosh(a η)`.  Existing: `B0140.curl_trainDatum`,
`Lib/Train/Datum.lean` `abs_curl_datum_le` (needs `c ≥ 2`, constant `40 e^{-η²/8}`), and
`Gaussian.norm_periodize_le_of_gauss` (needs `a ≤ c²`); for `1 ≤ c < 2` bound the lattice sum
directly. -/
def TrainDatumCurlSech : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
    ∀ z : Plane, |Cyl.curl (B0140.trainDatum c) z| ≤ A * (Real.cosh (a * z.2))⁻¹

/-- **The `sech` first moment is integrable on the cell**: if `f` is continuous and
`|f| ≤ C / cosh(a η)`, then `(1 + |η|) |f|` is integrable over the cell `[-c/2, c/2) × ℝ`. -/
def SechMomentIntegrable : Prop :=
  ∀ (c a C : ℝ) (f : Plane → ℝ), 0 < c → 0 < a → Continuous f →
    (∀ z : Plane, |f z| ≤ C * (Real.cosh (a * z.2))⁻¹) →
    IntegrableOn (fun z : Plane => (1 + |z.2|) * |f z|) (Cyl.cell c)

/-! ### The conditional theorem -/

/-- A uniform bound on `‖v s z‖` from `HasBoundedDerivsOn` (order `0`). -/
theorem vfm_sup_bound {T : ℝ} {v : ℝ → Plane → Vec} (h : HasBoundedDerivsOn T v) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖v s z‖ ≤ M := by
  obtain ⟨M, hM⟩ := h 0
  refine ⟨M, fun s hs z => ?_⟩
  have := hM s hs z
  rwa [norm_iteratedFDeriv_zero] at this

/-- **`VorticityFirstMoment` from the five leaves.** -/
theorem vorticityFirstMoment_of (hEq : LocalVorticityEquation) (hReg : CurlRegularity)
    (hBar : ParabolicSechBarrier) (hDat : TrainDatumCurlSech) (hInt : SechMomentIntegrable) :
    VorticityFirstMoment := by
  intro ν c T v p hν hc hT hcl hb s hs
  have hc0 : 0 < c := by linarith
  obtain ⟨hcont, hC2, hMω, hper⟩ := hReg c T v hc0 hT hcl.smooth_v hcl.periodic_v hb
  obtain ⟨β, hβ⟩ := vfm_sup_bound hb
  obtain ⟨A, a, hA, ha, hdat⟩ := hDat c hc
  have hK : β * a + ν * a ^ 2 < β * a + ν * a ^ 2 + 1 := lt_add_one _
  have hbar := hBar ν c T β A a (β * a + ν * a ^ 2 + 1) v (fun t w => Cyl.curl (v t) w) hν hc0 hT
    ha hA hK hcont hC2 hper hβ hMω
    (fun r hr z => hEq ν c T v p hν hc hT hcl r hr z)
    (fun z => by
      have h0 := hdat z
      have hv0 : v 0 = B0140.trainDatum c := hcl.initial
      simpa only [hv0] using h0)
  have hcs : Continuous (fun z : Plane => Cyl.curl (v s) z) := by
    have h1 : ContinuousOn (fun z : Plane => Cyl.curl (v s) z) univ :=
      hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun z _ => ⟨hs, mem_univ z⟩)
    exact continuousOn_univ.1 h1
  exact hInt c a (A * Real.exp ((β * a + ν * a ^ 2 + 1) * s)) (fun z => Cyl.curl (v s) z) hc0 ha
    hcs (fun z => hbar s hs z)

end UnforcedLeray.Short.PartI
