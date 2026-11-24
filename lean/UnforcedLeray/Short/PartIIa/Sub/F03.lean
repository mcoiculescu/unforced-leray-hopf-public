import UnforcedLeray.Units.B0423
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Lib.PhaseSpace.Graph
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Part II-a, task `PartII-a:F03`: the fixed-window local graph estimate (conditional)

Source of record: `the November 2 reference manuscript`, lines 1431-1441 (the
paragraph starting "On `|t| < 2`, set `v(t,x) = e^{-t/2} w(τ₀+t, e^{-t/2}x)`"; the task spec cites
1451-1471, which is the later averaging paragraph). Old-manuscript counterpart: `paper/main.tex`
lines 7479-7517 (blueprint unit B0424), whose `q = 2` case is
`Cons/L2/FreeLaplacianRegularity/Window.lean`.

## Statement (`LocalWindowEstimate`)

For a distributional solution `w, f ∈ Y_r` of `(μ + L₀)w = f` (`HasPhaseOp (μ + L₀ᵗ) w f`) there is,
for every center `τ₀`, a field `Λ` on `ℝ × ℝ³` (the weak Laplacian `νΔw` on the window
`|τ - τ₀| < 1`, `IsWindowLaplacian`) with

`∫_{τ₀-1}^{τ₀+1} ‖Λ(τ)‖_r^r dτ ≤ C_r^r ∫_{τ₀-2}^{τ₀+2} [‖f(τ)‖_r^r + (1+|μ|)^r ‖w(τ)‖_r^r] dτ`,

`C_r` independent of `P ≤ 1`, `ν`, `μ`, `τ₀`. The task text puts `∃ C` before `∀ r`; that is
impossible (the constant depends on `r`, source line 1433 "C_r"), so the quantifiers are
`∀ r, ∃ C`. `νΔw` is not assumed to exist in `Y_r`: the window Laplacian is produced by the
proof ("the same reasoning applies to any distributional `Y_r` solution", line 1447), which is
what the maximal-domain step (task `PartII-a:F04`, averaging over centers) needs. A global
Laplacian `a` of `w` in `Y_r` (if one is known) equals `Λ` on the window almost everywhere (the
uniqueness of the weak Laplacian), so the estimate also bounds `‖νΔw‖` locally.

## Proof (the leaves)

With a fixed cutoff `χ ∈ C_c^∞(-2,2)`, `χ = 1` on `[-1,1]`, put for each component `c`
`u_c(θ,x) = χ(log θ) θ^{-1/2} W_c(τ₀ + log θ, θ^{-1/2}x)` for `θ > 0` (`0` otherwise),
`F_c(θ,x) = θ^{-3/2}[(χ'-μχ)W_c + χ f_c](τ₀ + log θ, θ^{-1/2}x)`.

* `WindowEquation` (task `PartII-a:F03/1`): `(∂_θ - νΔ_x)u_c = F_c` weakly on `ℝ × ℝ³`.
* `WindowNorms` (task `PartII-a:F03/2`): `u_c, F_c ∈ L^r(ℝ × ℝ³)` and the `L^r` norm of `F_c` is
  bounded by the weighted window integrals (Jacobians `dx = e^{3t/2}dy`, `dθ = e^t dt`
  bounded on `|t| < 2`).
* The heat maximal regularity `B0423.heat_estimate_complex_laplacian` (proved) gives weak
  second derivatives `D2_c i j ∈ L^r` with `‖νΣ_i D2_c i i‖_r ≤ C_h ‖F_c‖_r`.
* `WindowBackEquation` (task `PartII-a:F03/3`): the field `windowLap` built from
  `ν Σ_i D2_c i i` is a weak Laplacian of `w` on the window.
* `WindowBackNorm` (task `PartII-a:F03/4`): the `L^r` norm of `windowLap` on the window is bounded
  by the `L^r` norms of the `ν Σ_i D2_c i i` (change of variables back).

Import note: `Units/B0424/Rep.lean` does not compile (`lintegral_rep`, `Lp.enorm_ne_top`); the
repaired copy `Sub/F03Rep.lean` (namespace `UnforcedLeray.Short.PartIIa.Rep`: `IsRep`, `exists_isRep`,
`lintegral_window_lt_top`, `vfun`, `lintegral_rep`, ...) is used instead.

Proved here: the cutoff exists (`windowCutoff_exists`) and the assembly `localWindowEstimate_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- The time cutoff of line 1434 ("a fixed cutoff equal to one on `|t| < 1`"): smooth, compactly
supported in `(-2, 2)`, equal to `1` on `[-1, 1]`. -/
structure WindowCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  compact : HasCompactSupport χ
  support : tsupport χ ⊆ Ioo (-2 : ℝ) 2
  one : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1

/-- A window cutoff exists. -/
theorem windowCutoff_exists : ∃ χ : ℝ → ℝ, WindowCutoff χ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport, ?_, fun t ht => ?_⟩⟩
  · rw [b.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    have : |t| ≤ 3 / 2 := ht
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  · refine b.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩

/-- The cutoff pull-back (lines 1431-1434): component `c` of
`u(θ, x) = χ(log θ) θ^{-1/2} W(τ₀ + log θ, θ^{-1/2} x)` for `θ > 0`, `0` otherwise. For `|t| < 1`,
`θ = e^t`, `x = e^{t/2} y`: `u(e^t, e^{t/2} y) = e^{-t/2} W(τ₀ + t, y)`. -/
def windowField (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3) (X : PS 3) : ℂ :=
  if 0 < X.1 then
    ((χ (Real.log X.1) * Real.exp (-(Real.log X.1 / 2)) : ℝ) : ℂ) *
      W (τ₀ + Real.log X.1, Real.exp (-(Real.log X.1 / 2)) • X.2) c
  else 0

/-- The right side of the transformed equation (line 1432-1434): component `c` of
`F(θ, x) = θ^{-3/2} [(χ' - μχ) W + χ f](τ₀ + log θ, θ^{-1/2} x)` for `θ > 0`, `0` otherwise
(`W`, `Fr` representatives of `w`, `f`; the equation is `(μ + L₀)w = f`). -/
def windowForce (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3) (c : Fin 3)
    (X : PS 3) : ℂ :=
  if 0 < X.1 then
    ((Real.exp (-(3 * Real.log X.1 / 2)) : ℝ) : ℂ) *
      ((((deriv χ (Real.log X.1) : ℝ) : ℂ) - μ * (χ (Real.log X.1) : ℂ)) *
          W (τ₀ + Real.log X.1, Real.exp (-(Real.log X.1 / 2)) • X.2) c +
        (χ (Real.log X.1) : ℂ) *
          Fr (τ₀ + Real.log X.1, Real.exp (-(Real.log X.1 / 2)) • X.2) c)
  else 0

/-- The transport back (lines 1435-1436, "all Jacobians on the window are bounded"): given the
Laplacians `D c = Δ_x u_c` on `ℝ × ℝ³`, the field
`Λ_c(τ₀ + t, y) = ν e^{3t/2} (Δ_x u_c)(e^t, e^{t/2} y)` for `|t| < 1` (and `0` otherwise); on
`|t| < 1`, `W_c(τ₀+t, y) = e^{t/2} u_c(e^t, e^{t/2}y)` gives `ν Δ_y W_c = Λ_c`. -/
def windowLap (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ) (p : ℝ × Space) : CVec3 :=
  if |p.1 - τ₀| < 1 then
    WithLp.toLp 2 fun c => (ν : ℂ) * ((Real.exp (3 * (p.1 - τ₀) / 2) : ℝ) : ℂ) *
        D c (Real.exp (p.1 - τ₀), Real.exp ((p.1 - τ₀) / 2) • p.2)
  else 0

/-- `Λ` is a weak Laplacian `νΔW` on the window `(τ₀-1, τ₀+1) × ℝ³`: against every smooth
compactly supported `ℂ³`-valued `ψ` with support in the window, `∫ W · νΔψ = ∫ Λ · ψ` (bilinear
dot product), both integrands being integrable. -/
def IsWindowLaplacian (ν τ₀ : ℝ) (W Λ : ℝ × Space → CVec3) : Prop :=
  ∀ ψ : ℝ × Space → CVec3, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) →
      Integrable (fun p => dotL (W p) (ν • lapT ψ p)) ∧ Integrable (fun p => dotL (Λ p) (ψ p)) ∧
        ∫ p, dotL (W p) (ν • lapT ψ p) = ∫ p, dotL (Λ p) (ψ p)

/-- **The fixed-window local graph estimate** (lines 1431-1441). -/
def LocalWindowEstimate : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∀ τ₀ : ℝ, ∃ Λ : ℝ × Space → CVec3, IsWindowLaplacian ν τ₀ W Λ ∧
          ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **Leaf `PartII-a:F03/1` (the transformed equation).** For a distributional solution of
`(μ + L₀)w = f` and jointly measurable representatives `W`, `Fr` of `w`, `f`, each
`u_c = windowField` is a weak solution of `(∂_θ - νΔ_x)u_c = windowForce` on `ℝ × ℝ³`
(`B0423.IsWeakHeatSolC`). Proof: periodize a test supported in time to a phase test; transport
phase tests along `D(t,y) = (t, e^{t/2}y)` and `E(t,x) = (e^t, x)` using the calculus of
`Units/B0424/Calc.lean` (`L0T_phaseTest`, `L0S_phaseScal`) and the tests of `Units/B0424/Tests.lean`;
the Jacobians are `Units/B0424/Chart.lean`. -/
def WindowEquation : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (μ : ℂ)
    (f w : Yq P r), HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f →
      ∀ W Fr : ℝ × Space → CVec3, IsRep w W → IsRep f Fr →
        ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ (τ₀ : ℝ) (c : Fin 3),
          B0423.IsWeakHeatSolC (d := 3) ν (windowField χ τ₀ W c)
            (windowForce μ χ τ₀ W Fr c)

/-- **Leaf `PartII-a:F03/2` (membership and the force bound).** `u_c`, `F_c` are in
`L^r(ℝ × ℝ³)` and `‖F_c‖_r^r ≤ K^r ∫_{τ₀-2}^{τ₀+2}[‖f(τ)‖_r^r + (1+|μ|)^r ‖w(τ)‖_r^r] dτ`, with
`K` depending only on `r` and `χ`. (Jacobians `Units/B0424/Chart.lean`, representatives and
slice integrals `Short/PartII-a/Sub/F03Rep.lean`: `lintegral_rep`, `lintegral_dilChart'`,
`lintegral_expChart'`; the weights `e^{±3t/2}`, `e^{t}` are bounded on `|t| ≤ 2`, and
`|χ'| + |χ| ≤ K_χ`.) -/
def WindowNorms : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∀ χ : ℝ → ℝ, WindowCutoff χ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ) (f w : Yq P r)
      (W Fr : ℝ × Space → CVec3), IsRep w W → IsRep f Fr → ∀ (τ₀ : ℝ) (c : Fin 3),
        MemLp (windowField χ τ₀ W c) (ENNReal.ofReal r.toReal) volume ∧
        MemLp (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ∧
        eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^ r.toReal ≤
          ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
            (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
              ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **Leaf `PartII-a:F03/3` (the Laplacian of `w` on the window).** If the components `u_c` of the
cutoff pull-back have weak second derivatives `D2 c i j ∈ L^r`, then `windowLap` of the Laplacians
`Σ_i D2 c i i` is a weak Laplacian of `w` on the window (transfer the complex test `ψ` through
`lapTest`, `sLap_lapTest` of `Units/B0424/Tests.lean`, on `|t| < 1` where `χ = 1`; split into real
and imaginary parts since `HasWeakSpaceDeriv2C` tests against real tests). -/
def WindowBackEquation : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ τ₀ : ℝ,
      ∀ D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ,
        (∀ c i j, MemLp (D2 c i j) (ENNReal.ofReal r.toReal) volume ∧
          B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) i j (D2 c i j)) →
        IsWindowLaplacian ν τ₀ W (windowLap ν τ₀ fun c X => ∑ i, D2 c i i X)

/-- **Leaf `PartII-a:F03/4` (the norm of the transported Laplacian).** For `q > 1` there is `K`
(depending only on `q`) with `∫_{τ₀-1}^{τ₀+1}∫ |windowLap(τ,y)|^q dy dτ ≤ K^q Σ_c ‖ν D_c‖_q^q`, for
every measurable family `D` (`dy = e^{-3t/2}dx` and `dt = dθ/θ` on `|t| < 1`, so the weights
`e^{3(q-1)t/2}` and `θ^{-1}` are bounded; `‖v‖^q ≤ 3^{q-1}Σ_c |v_c|^q` on `ℂ³`;
`lintegral_dilChart'`, `lintegral_expChart'` of `Units/B0424/Chart.lean`). -/
def WindowBackNorm : Prop :=
  ∀ q : ℝ, 1 < q → ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ),
    (∀ c, AEStronglyMeasurable (D c) volume) →
      ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖windowLap ν τ₀ D (τ, y)‖ₑ ^ q ≤
        ENNReal.ofReal K ^ q *
          ∑ c, eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q

/-- **`PartII-a:F03`, conditional on the four leaves.** -/
theorem localWindowEstimate_of (h1 : WindowEquation) (h2 : WindowNorms)
    (h3 : WindowBackEquation) (h4 : WindowBackNorm) : LocalWindowEstimate := by
  intro r _ hr1 hrt
  have hq : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hq0 : 0 ≤ r.toReal := by linarith
  have hqr : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrt
  obtain ⟨χ, hχ⟩ := windowCutoff_exists
  obtain ⟨K, hK0, hK⟩ := h2 r hr1 hrt χ hχ
  obtain ⟨K', hK'0, hK'⟩ := h4 r.toReal hq
  obtain ⟨Ch, hCh⟩ := B0423.heat_estimate_complex_laplacian (d := 3) hq
  set q := r.toReal with hqdef
  -- the constant
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / q) := by positivity
  refine ⟨(3 : ℝ) ^ (1 / q) * K' * Ch * K, by positivity, ?_⟩
  intro P _ hP1 ν hν μ f w hw W hW τ₀
  obtain ⟨Fr, hFr⟩ := exists_isRep hrt f
  have heq := h1 r hrt P ν μ f w hw W Fr hW hFr χ hχ τ₀
  have hmem := fun c => hK P μ f w W Fr hW hFr τ₀ c
  have hheat := fun c => hCh ν hν (windowField χ τ₀ W c) (windowForce μ χ τ₀ W Fr c)
    (hmem c).1 (hmem c).2.1 (heq c)
  choose D2 Dt hD2 hDt hDtw hb hbt using hheat
  refine ⟨windowLap ν τ₀ fun c X => ∑ i, D2 c i i X,
    h3 r hrt P ν w W hW χ hχ τ₀ D2 fun c i j => hD2 c i j, ?_⟩
  set R : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
    (‖f (τ : AddCircle P)‖ₑ ^ q + ENNReal.ofReal (1 + ‖μ‖) ^ q * ‖w (τ : AddCircle P)‖ₑ ^ q)
    with hR
  have hmeas : ∀ c, AEStronglyMeasurable (fun X : PS 3 => ∑ i, D2 c i i X) volume := fun c =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD2 c i i).1.1
  refine (hK' ν τ₀ (fun c X => ∑ i, D2 c i i X) hmeas).trans ?_
  have hterm : ∀ c, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q)
      volume ^ q ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) := fun c => by
    calc eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q) volume ^ q
        ≤ ((Ch : ℝ≥0∞) * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume) ^ q :=
          ENNReal.rpow_le_rpow (hb c) hq0
      _ = (Ch : ℝ≥0∞) ^ q * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) :=
          mul_le_mul' le_rfl (hmem c).2.2
  have hsum : ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
      (ENNReal.ofReal q) volume ^ q ≤ 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R)) := by
    calc ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
          (ENNReal.ofReal q) volume ^ q
        ≤ ∑ _c : Fin 3, (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R)) := by
          simp [Finset.sum_const]
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  -- the constant identity
  have hC : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K) ^ q =
      ENNReal.ofReal K' ^ q * (3 * ((Ch : ℝ≥0∞) ^ q * ENNReal.ofReal K ^ q)) := by
    have h1' : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K) =
        ENNReal.ofReal ((3 : ℝ) ^ (1 / q)) * ENNReal.ofReal K' * (Ch : ℝ≥0∞) *
          ENNReal.ofReal K := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul h3pos, ENNReal.ofReal_coe_nnreal]
    rw [h1', ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.mul_rpow_of_nonneg _ _ hq0,
      ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_nonneg h3pos hq0,
      ← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have h33 : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [h33]
    ring
  rw [hC]
  ring

end UnforcedLeray.Short.PartIIa
