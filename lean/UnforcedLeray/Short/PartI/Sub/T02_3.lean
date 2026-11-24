import UnforcedLeray.Short.PartI.Sub.T02
import UnforcedLeray.Short.PartI.Sub.T05

/-!
# Part I, task `PartI:T02/3`: `ClassicalOdd` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 276-288 ("Approximation
and transverse cutoffs then give the velocity and vorticity energy identities ... Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`") and the Gallay-Slijepcevic cylinder theory cited there.

The target is `ClassicalOdd` (`Short/PartI/Sub/T02.lean`): a classical solution `(v, p)` on `[0,T]`
with bounded derivatives and decaying pressure is centrally odd.  The argument is classical
uniqueness for the reflected pair `(reflV v, reflP p) = (-v(s,-z), p(s,-z))`, which is again a
classical solution with the same (odd) datum `trainDatum c` (`B0140.trainDatum_neg`).

## What is proved here

`classicalOdd_of` derives `ClassicalOdd` from six leaf statements:

1. `ReflectClassical`, `ReflectBoundedDerivs`, `ReflectPressureDecay`: the reflected pair stays in the
   class (reflection through the origin commutes with every operator in the system; the cell is
   mapped to a translate of itself, and a period-integral of a periodic function is
   translation invariant).
2. `ClassicalPressureBound`: the pressure of a classical solution with bounded derivatives and
   decaying pressure is bounded uniformly on `[0,T]`.  (Taking the divergence of the momentum
   equation gives `Δp = -∂_i v_j ∂_j v_i = -∂_i∂_j(v_i v_j)`; the `q`-mean of `p` is
   `-avg_q(v_η²)` because `p → 0` at infinity, and the `q`-oscillating part is bounded by the
   exponentially decaying Fourier-mode Green function of `Δ` on the cylinder.  This is the only
   place the decaying gauge is used, and the reason uniform-in-`s` bounds are available at all:
   `PressureDecayOn` and `finite_energy` alone are only pointwise in `s`.)
3. `ClassicalEnergyBound`: with `|v|, |∇v|, |p|` bounded the cell energy is bounded uniformly on
   `[0,T]` (cutoff energy identity; every cutoff flux term is `O(1)` uniformly in the cutoff radius,
   so `E_R(s) ≤ E(0) + C s`).
4. `ClassicalUniquenessBounded`: two classical solutions with the same datum, bounded derivatives
   and the uniform bounds `ClassicalBoundedBy` coincide on `[0,T]` (cutoff energy inequality
   `ClassicalCutoffEnergyIneq`, Gronwall, `R → ∞`).

`classicalPressureBound_of` further derives `ClassicalPressureBound` from `SlicePoisson` (divergence
of the momentum equation), `VelocityDecayOfEnergy` (finite energy and a bounded gradient force decay)
and `CylinderPoissonBound` (the elliptic estimate, Fourier modes in `q`).

Audit note.  `ClassicalOdd` cannot be proved from `finite_energy` and `PressureDecayOn` directly: both
are pointwise in `s`, while the energy method needs `sup_s` bounds of the pressure and of the cell
energy.  They are derived from the equation (`ClassicalPressureBound`, `ClassicalEnergyBound`), and
only then is uniqueness applied to the pair `(v, reflV v)`.

The unconditional target is task `PartI:T02/3`
(`Short/PartI/Sub/T02/ClassicalOdd.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### The reflected pair -/

/-- The reflected velocity `v'(s, z) = -v(s, -z)` (central reflection of a vector field). -/
def reflV (v : ℝ → Plane → Vec) : ℝ → Plane → Vec := fun s z => -v s (-z)

/-- The reflected pressure `p'(s, z) = p(s, -z)`. -/
def reflP (p : ℝ → Plane → ℝ) : ℝ → Plane → ℝ := fun s z => p s (-z)

/-- The reflected pair of a classical solution is a classical solution with the same datum
(`trainDatum` is odd, `B0140.trainDatum_neg`).  Smoothness is composition with `z ↦ -z`; the
momentum residual of the reflected pair at `z` is minus the residual of `(v,p)` at `-z`; finite
energy uses that `z ↦ -z` maps the cell onto a translate of itself. -/
def ReflectClassical : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → IsClassicalOn ν c T (reflV v) (reflP p)

/-- Reflection preserves bounded derivatives (`z ↦ -z` is a linear isometry). -/
def ReflectBoundedDerivs : Prop :=
  ∀ (T : ℝ) (v : ℝ → Plane → Vec), HasBoundedDerivsOn T v → HasBoundedDerivsOn T (reflV v)

/-- Reflection preserves pressure decay (`|(-z).2| = |z.2|`). -/
def ReflectPressureDecay : Prop :=
  ∀ (T : ℝ) (p : ℝ → Plane → ℝ), PressureDecayOn T p → PressureDecayOn T (reflP p)

/-! ### Uniform bounds and the cutoff energy of a difference -/

/-- Uniform bounds on `[0,T]` by `M`: sup of the velocity, sup of the pressure, unnormalized cell
energy (the classical-class analogue of `TrainBoundedBy`). -/
def ClassicalBoundedBy (c T M : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) T, (∀ z : Plane, ‖v s z‖ ≤ M) ∧ (∀ z : Plane, |p s z| ≤ M) ∧
    ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 ≤ M

/-- The cutoff energy `F_R(s) = ∫_cell φ_R(η) |v(s) - v'(s)|²` of the difference of two velocity
fields, with the cutoff `etaCutoff` of `Short/PartI/Sub/T05.lean`. -/
def classicalCutoffEnergy (c : ℝ) (v v' : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖v s z - v' s z‖ ^ 2

/-- **Uniform pressure bound** (source line 288 and the Gallay-Slijepcevic "bounded periodic
pressure"): a classical solution with bounded derivatives and decaying pressure has a pressure
bounded uniformly in `(s, z) ∈ [0,T] × ℝ²`.

Proof outline.  (i) `div` of the momentum equation: `Δp(s) = -(∂_i v_j ∂_j v_i)(s)` on `[0,T]`
(smoothness on the closed set, momentum on `(0,T)`, continuity at the endpoints).  (ii) `v(s) → 0`
as `|η| → ∞` (finite energy on the cell plus a bounded gradient).  (iii) `q`-mean: with
`P(η) = avg_q p`, `Δp = -∂_i∂_j(v_i v_j)` and `div v = 0` give `P'' = -(avg_q v_η²)''`, so
`P + avg_q v_η² = aη + b`, and `P → 0`, `avg_q v_η² → 0` force `a = b = 0`: `|P| ≤ sup|v|²`.
(iv) the zero-`q`-mean part is bounded through the Fourier modes `e^{2πikq/c}` (`k ≠ 0`): each mode
solves `p_k'' - λ_k² p_k = g_k` with `λ_k = 2π|k|/c`, the only bounded solution is the Green
function convolution, `|p_k| ≤ λ_k^{-2} sup|g_k|`, and `sup|g_k| ≲ k^{-2} sup|∂_q² g|` is summable
because all derivatives of `v` are bounded. -/
def ClassicalPressureBound : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → PressureDecayOn T p →
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |p s z| ≤ M

/-- **Facts about the transverse cutoff** `etaCutoff R = ζ(2 - |η|/R)²` (`ζ = Real.smoothTransition`),
shared by `ClassicalEnergyBound` and `ClassicalCutoffEnergyIneq`: for all `R ≥ 1`, `etaCutoff R` is
`C^∞`, takes values in `[0,1]`, equals `1` for `|η| ≤ R` and `0` for `|η| ≥ 2R`, and
`|φ_R'| ≤ (C₀/R) √φ_R` (since `φ_R' = ∓ 2ζ ζ'(2 - |η|/R)/R` for `η ≷ 0`, `ζ'` is bounded because
`ζ` is `C^∞` and constant outside `[0,1]`, and `√φ_R = ζ`).  The bound with `√φ_R` is what lets the
viscous cross term be absorbed by Young's inequality. -/
def EtaCutoffFacts : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ R : ℝ, 1 ≤ R →
    ContDiff ℝ ∞ (etaCutoff R) ∧ (∀ η : ℝ, 0 ≤ etaCutoff R η ∧ etaCutoff R η ≤ 1) ∧
    (∀ η : ℝ, |η| ≤ R → etaCutoff R η = 1) ∧ (∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0) ∧
    (∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C₀ / R * Real.sqrt (etaCutoff R η))

/-- The pressure Poisson source `∂_i v_j ∂_j v_i = (∂_q v_q)² + 2 ∂_q v_η ∂_η v_q + (∂_η v_η)²`
(components `0 = q`, `1 = η`) of a plane vector field. -/
def poissonSource (u : Plane → Vec) (z : Plane) : ℝ :=
  Cyl.partialQ (fun w => u w 0) z ^ 2 +
    2 * (Cyl.partialQ (fun w => u w 1) z * Cyl.partialEta (fun w => u w 0) z) +
    Cyl.partialEta (fun w => u w 1) z ^ 2

/-- **Pressure Poisson equation on every slice** (divergence of the momentum equation): for a
classical solution, `Δp(s) = -∂_i v_j ∂_j v_i` for every `s ∈ [0,T]`.  Proof: on `(0,T)`,
`div(∂_s v + v·∇v - νΔv + ∇p) = 0` with `div v = 0` and the symmetry of second and third derivatives
(smoothness on the open set `(0,T) × ℝ²`; adapt `Units/B0238/VorticityEq.lean`, which takes the curl
instead of the divergence); both sides are continuous on `[0,T] × ℝ²`, so the identity extends to
`s = 0` and `s = T`. -/
def SlicePoisson : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      Train.lapS (p s) z = - poissonSource (v s) z

/-- **Velocity decay from finite energy and a bounded gradient**: a classical solution with
bounded derivatives has `v(s) → 0` as `|η| → ∞` (uniformly in `q`), for every `s ∈ [0,T]`.
Proof: if `|v(s, z_n)| ≥ ε` along `|η_n| → ∞`, the bound `|Dv| ≤ B` gives
`|v(s,·)| ≥ ε/2` on a ball of radius `ε/(2B)` around `z_n`; by periodicity these balls give infinitely
many disjoint pieces of one cell's far tail of `∫_cell |v(s)|²`, contradicting finite energy. -/
def VelocityDecayOfEnergy : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → VelocityDecayOn T v

/-- **Bounded solutions of the pressure Poisson equation on the cylinder** (the elliptic core of
`ClassicalPressureBound`): for `c > 0` and `B` there is `M` such that every smooth `c`-periodic
divergence-free `u` with `‖D^k u‖ ≤ B` (`k ≤ 4`) tending to `0` at `|η| → ∞`, and every `C²`
`c`-periodic `q` tending to `0` at `|η| → ∞` with `Δq = -∂_i u_j ∂_j u_i`, satisfies `|q| ≤ M`.
Proof: the `q`-mean `P(η)` of `q` obeys `P'' = -(avg_q u_η²)''` (`∂_i∂_j(u_i u_j)` with `div u = 0`
and periodicity), so `P + avg_q u_η² = aη + b`, and decay forces `a = b = 0`: `|P| ≤ B²`.  Each
Fourier mode `k ≠ 0` of `q - P` solves `q_k'' - λ_k² q_k = g_k` with `λ_k = 2π|k|/c`; the only
bounded solution is `q_k = -(2λ_k)^{-1} ∫ e^{-λ_k |η-η'|} g_k(η') dη'`, so `|q_k| ≤ λ_k^{-2} sup |g_k|`
and, integrating by parts twice in `q`, `sup|g_k| ≤ λ_k^{-2} sup|∂_q² g|` with `g` the source; sum the
absolutely convergent series (`Σ_k k^{-4}`). -/
def CylinderPoissonBound : Prop :=
  ∀ c B : ℝ, 0 < c → ∃ M : ℝ, ∀ (u : Plane → Vec) (q : Plane → ℝ),
    ContDiff ℝ ∞ u → ContDiff ℝ 2 q → Cyl.IsPeriodic c u → Cyl.IsPeriodic c q →
    (∀ z, Cyl.divergence u z = 0) → (∀ k : ℕ, k ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ k u z‖ ≤ B) →
    Tendsto u (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    Tendsto q (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    (∀ z, Train.lapS q z = - poissonSource u z) → ∀ z, |q z| ≤ M

/-- **Uniform energy bound** (source lines 276-282): with `v` and `∇v` bounded and `p` bounded by
`Mp`, the cell energy is bounded on `[0,T]`.  Test the momentum equation with `φ_R v`
(`φ_R = etaCutoff R`, `|∇φ_R| ≤ C/R`, supported in `|η| ≤ 2R`) and integrate over the cell:
`½ d/ds ∫ φ_R |v|² = -ν∫φ_R|∇v|² - ν∫ (∇φ_R·∇)v·v + ½∫|v|² v·∇φ_R + ∫ p v·∇φ_R`; each term but the
first is bounded by a constant times `(1/R)·|{R ≤ |η| ≤ 2R} ∩ cell| ≤ 2c C`, so
`∫ φ_R |v(s)|² ≤ ∫|v(0)|² + C s` with `C` independent of `R`; let `R → ∞` (monotone convergence;
`v 0 = trainDatum c` has finite energy). -/
def ClassicalEnergyBound : Prop :=
  ∀ (ν c T Mp : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → HasBoundedDerivsOn T v → (∀ s ∈ Icc (0 : ℝ) T, ∀ z, |p s z| ≤ Mp) →
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 ≤ M

/-- **Cutoff energy inequality for the difference of two classical solutions** (the classical-class
analogue of `TrainCutoffEnergyIneq`, `Short/PartI/Sub/T05.lean`).  With `w = v - v'` and
`π = p - p'`: `w_s + v·∇w + w·∇v' - νΔw + ∇π = 0`, `w(0) = 0`, `div w = 0`.  Testing with
`φ_R w`, `φ_R = ζ²`: the viscous cross term is absorbed by `-ν∫φ_R|∇w|²` (Young) up to
`ν C R^{-2} M`; the stretching term is `≤ ‖∇v'‖_∞ F_R`; the transport term is `O(M²/R)`; the pressure
term is `≤ (C/R)·2M·∫_{R≤|η|≤2R}|w| = O(R^{-1/2})` by Cauchy-Schwarz on a strip of measure `≤ 2cR`
and `∫_cell |w|² ≤ 4M`.  Integrate in `s`. -/
def ClassicalCutoffEnergyIneq : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → IsClassicalOn ν c T v' p' →
    HasBoundedDerivsOn T v → HasBoundedDerivsOn T v' →
    ClassicalBoundedBy c T M v p → ClassicalBoundedBy c T M v' p' →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (classicalCutoffEnergy c v v' R) (Icc 0 T) ∧
      ∀ s ∈ Icc (0 : ℝ) T,
        classicalCutoffEnergy c v v' R s ≤
          C * (∫ r in (0 : ℝ)..s, classicalCutoffEnergy c v v' R r) + C / Real.sqrt R

/-- **Uniqueness of bounded classical solutions** with the same datum (source lines 276-288). -/
def ClassicalUniquenessBounded : Prop :=
  ∀ (ν c T M : ℝ) (v v' : ℝ → Plane → Vec) (p p' : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c → 0 < T →
    IsClassicalOn ν c T v p → IsClassicalOn ν c T v' p' →
    HasBoundedDerivsOn T v → HasBoundedDerivsOn T v' →
    ClassicalBoundedBy c T M v p → ClassicalBoundedBy c T M v' p' →
    ∀ s ∈ Icc (0 : ℝ) T, v s = v' s

/-! ### The conditional theorem -/

/-- A uniform bound on `‖v s z‖` from `HasBoundedDerivsOn` (order `0`). -/
theorem exists_sup_bound_of_hasBoundedDerivsOn {T : ℝ} {v : ℝ → Plane → Vec}
    (h : HasBoundedDerivsOn T v) : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖v s z‖ ≤ M := by
  obtain ⟨M, hM⟩ := h 0
  refine ⟨M, fun s hs z => ?_⟩
  have := hM s hs z
  rwa [norm_iteratedFDeriv_zero] at this

/-- Bounds on `‖D^k v‖`, `k ≤ 4`, by one constant, from `HasBoundedDerivsOn`. -/
theorem exists_deriv_bound_le_four {T : ℝ} {v : ℝ → Plane → Vec} (h : HasBoundedDerivsOn T v) :
    ∃ B : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ k : ℕ, k ≤ 4 → ∀ z : Plane,
      ‖iteratedFDeriv ℝ k (v s) z‖ ≤ B := by
  choose Mk hMk using h
  refine ⟨∑ k ∈ Finset.range 5, |Mk k|, fun s hs k hk z => ?_⟩
  have h1 : Mk k ≤ |Mk k| := le_abs_self _
  have h2 : |Mk k| ≤ ∑ k ∈ Finset.range 5, |Mk k| :=
    Finset.single_le_sum (f := fun k => |Mk k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  exact (hMk k s hs z).trans (h1.trans h2)

/-- **`ClassicalPressureBound` from the three pressure leaves.** -/
theorem classicalPressureBound_of (h1 : SlicePoisson) (h2 : VelocityDecayOfEnergy)
    (h3 : CylinderPoissonBound) : ClassicalPressureBound := by
  intro ν c T v p hν hc hT hcl hb hp
  have hc0 : 0 < c := by linarith
  obtain ⟨B, hB⟩ := exists_deriv_bound_le_four hb
  obtain ⟨M, hM⟩ := h3 c B hc0
  refine ⟨M, fun s hs z => ?_⟩
  have hvs : ContDiff ℝ ∞ (v s) := by
    have h := hcl.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => (⟨hs, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
    exact contDiffOn_univ.1 h
  have hps : ContDiff ℝ 2 (p s) := by
    have hp2 : ContDiffOn ℝ 2 (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ) :=
      hcl.smooth_p.of_le (by simp)
    have h := hp2.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
      (fun z _ => (⟨hs, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
    exact contDiffOn_univ.1 h
  exact hM (v s) (p s) hvs hps (hcl.periodic_v s hs) (hcl.periodic_p s hs) (hcl.solenoidal s hs)
    (fun k hk w => hB s hs k hk w) (h2 ν c T v p hν hc hT hcl hb s hs) (hp s hs)
    (h1 ν c T v p hν hc hT hcl s hs) z

/-- **`ClassicalOdd` from the six leaves.** -/
theorem classicalOdd_of (h1 : ReflectClassical) (h2 : ReflectBoundedDerivs)
    (h3 : ReflectPressureDecay) (hP : ClassicalPressureBound) (hE : ClassicalEnergyBound)
    (hU : ClassicalUniquenessBounded) : ClassicalOdd := by
  intro ν c T v p hν hc hT hcl hb hp s hs z
  have hcl' := h1 ν c T v p hν hc hT hcl
  have hb' := h2 T v hb
  have hp' := h3 T p hp
  obtain ⟨Mp, hMp⟩ := hP ν c T v p hν hc hT hcl hb hp
  obtain ⟨Mp', hMp'⟩ := hP ν c T (reflV v) (reflP p) hν hc hT hcl' hb' hp'
  obtain ⟨Me, hMe⟩ := hE ν c T Mp v p hν hc hT hcl hb hMp
  obtain ⟨Me', hMe'⟩ := hE ν c T Mp' (reflV v) (reflP p) hν hc hT hcl' hb' hMp'
  obtain ⟨Mv, hMv⟩ := exists_sup_bound_of_hasBoundedDerivsOn hb
  obtain ⟨Mv', hMv'⟩ := exists_sup_bound_of_hasBoundedDerivsOn hb'
  set M : ℝ := max (max Mv Mv') (max (max Mp Mp') (max Me Me')) with hM
  have hB : ClassicalBoundedBy c T M v p := fun r hr =>
    ⟨fun w => (hMv r hr w).trans (by simp [hM]), fun w => (hMp r hr w).trans (by simp [hM]),
      (hMe r hr).trans (by simp [hM])⟩
  have hB' : ClassicalBoundedBy c T M (reflV v) (reflP p) := fun r hr =>
    ⟨fun w => (hMv' r hr w).trans (by simp [hM]), fun w => (hMp' r hr w).trans (by simp [hM]),
      (hMe' r hr).trans (by simp [hM])⟩
  have key := hU ν c T M v (reflV v) p (reflP p) hν hc hT hcl hcl' hb hb' hB hB' s hs
  have h := congrFun key (-z)
  simp only [reflV, neg_neg] at h
  exact h

end UnforcedLeray.Short.PartI
