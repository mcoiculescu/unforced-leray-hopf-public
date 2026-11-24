import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapAEMeas
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowRhsFinite
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapUnique
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapGlue
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPoU
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.PeriodAverageBound
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.SliceIntegralYq
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.LaplacianFieldToYRep
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.YqRepNorm
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.NormFromPower

/-!
# Part II-a, task `PartII-a:F09/3/1`: the time-reversed diffusion bound, reduced to four leaves

Source `the November 2 reference manuscript`
lines 1426-1442 and 1431-1480 ("At `r = 2`, reverse the phase window and use `θ = 1 - e^{-t}` for
`L^* = -𝒯 - νΔ + 1`").

The distributional equation `HasPhaseOp (μ̄ + L₀) w f` says `(μ̄ - ∂_τ + ½ y·∇ + 1 - νΔ) w = f`.
For a centre `τ₀` and `t = τ₀ - τ`, put `v(t,x) = W(τ₀ - t, e^{t/2} x)`; then
`∂_t v - ν e^{-t} Δ_x v = f(τ₀-t, e^{t/2}x) - (1+μ̄) v`.  With the cutoff `χ(t)` and
`θ = 1 - e^{-t}` (`∂_θ = e^{t} ∂_t`) the cutoff field `u(θ,x) = χ(t) v(t,x)` (zero for `θ ≥ 1`)
solves `(∂_θ - νΔ_x) u = e^{t}[(χ' - (1+μ̄)χ) v + χ f(τ₀-t, e^{t/2}x)]`.
Back on `|t| < 1`: `W(τ,y) = u(1 - e^{-t}, e^{-t/2} y)` and
`νΔ_y W = ν e^{-t} (Δ_x u)(1 - e^{-t}, e^{-t/2} y)`.

The four leaves are the exact adjoint analogues of `WindowEquation`, `WindowNorms`,
`WindowBackEquation`, `WindowBackNorm` of `Sub/F03.lean`; the assembly
`adjointLocalWindowEstimate_of` is the adjoint analogue of `localWindowEstimate_of`, and
`adjointLaplacianBound_of` is `bodyLaplacianBound_of` with the global gluing
(`globalFieldWindowBound`) run against the adjoint window estimate.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- The reversed-window cutoff pull-back (line 1442, `θ = 1 - e^{-t}`): component `c` of
`u(θ,x) = χ(t) W(τ₀ - t, e^{t/2} x)`, `t = -log(1-θ)`, for `θ < 1`, and `0` for `θ ≥ 1`. -/
def adjWindowField (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3) (X : PS 3) : ℂ :=
  if X.1 < 1 then
    ((χ (-Real.log (1 - X.1)) : ℝ) : ℂ) *
      W (τ₀ + Real.log (1 - X.1), Real.exp (-Real.log (1 - X.1) / 2) • X.2) c
  else 0

/-- The right side of the transformed adjoint equation: component `c` of
`F(θ,x) = e^{t}[(χ'(t) - (1+μ̄)χ(t)) W + χ(t) f](τ₀ - t, e^{t/2}x)`, `t = -log(1-θ)`, `θ < 1`
(`W`, `Fr` representatives of `w`, `f`; the equation is `(μ̄ + L₀ᵗ) w = f`). -/
def adjWindowForce (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3) (c : Fin 3)
    (X : PS 3) : ℂ :=
  if X.1 < 1 then
    ((Real.exp (-Real.log (1 - X.1)) : ℝ) : ℂ) *
      ((((deriv χ (-Real.log (1 - X.1)) : ℝ) : ℂ) -
            (1 + (starRingEnd ℂ) μ) * (χ (-Real.log (1 - X.1)) : ℂ)) *
          W (τ₀ + Real.log (1 - X.1), Real.exp (-Real.log (1 - X.1) / 2) • X.2) c +
        (χ (-Real.log (1 - X.1)) : ℂ) *
          Fr (τ₀ + Real.log (1 - X.1), Real.exp (-Real.log (1 - X.1) / 2) • X.2) c)
  else 0

/-- The transport back: from Laplacians `D c = Δ_x u_c`, the field
`Λ_c(τ, y) = ν e^{-t} (Δ_x u_c)(1 - e^{-t}, e^{-t/2} y)`, `t = τ₀ - τ`, for `|τ - τ₀| < 1`
(and `0` otherwise); on that window `νΔ_y W_c = Λ_c` since `W(τ,y) = u(1-e^{-t}, e^{-t/2}y)`. -/
def adjWindowLap (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ) (p : ℝ × Space) : CVec3 :=
  if |p.1 - τ₀| < 1 then
    WithLp.toLp 2 fun c => (ν : ℂ) * ((Real.exp (-(τ₀ - p.1)) : ℝ) : ℂ) *
        D c (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2)
  else 0

/-- **The reversed fixed-window local graph estimate** (lines 1426-1442, 1431-1441 reversed). -/
def AdjointLocalWindowEstimate : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
        ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∀ τ₀ : ℝ, ∃ Λ : ℝ × Space → CVec3, IsWindowLaplacian ν τ₀ W Λ ∧
          ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **Leaf A (the transformed adjoint equation).** For a distributional solution of
`(μ̄ + L₀ᵗ) w = f` and representatives `W`, `Fr`, each `u_c = adjWindowField` is a weak solution of
`(∂_θ - νΔ_x) u_c = adjWindowForce` on `ℝ × ℝ³`. Analogue of `WindowEquation`
(`Tasks/F03aWindowEquation*`): periodize a time-supported test to a phase test, transport it along
`(t,y) ↦ (t, e^{t/2}y)` and the time change `θ = 1 - e^{-t}`, and use the identity
`μ̄Φ + L₀Φ = μ̄Φ - driftTΦ - νΔΦ + Φ` (`L0_eq_adjoint`). -/
def AdjointWindowEquation : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (μ : ℂ)
    (f w : Yq P r), HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
      ∀ W Fr : ℝ × Space → CVec3, IsRep w W → IsRep f Fr →
        ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ (τ₀ : ℝ) (c : Fin 3),
          B0423.IsWeakHeatSolC (d := 3) ν (adjWindowField χ τ₀ W c)
            (adjWindowForce μ χ τ₀ W Fr c)

/-- **Leaf B (membership and the force bound).** `u_c`, `F_c` are in `L^r(ℝ × ℝ³)` and
`‖F_c‖_r^r ≤ K^r ∫_{τ₀-2}^{τ₀+2}[‖f(τ)‖_r^r + (1+|μ|)^r ‖w(τ)‖_r^r] dτ`, `K` depending only on
`r` and `χ` (Jacobians `dx = e^{-3t/2} dy`, `dθ = e^{-t} dt` and the weight `e^{t}` bounded on
`|t| ≤ 2`). Analogue of `WindowNorms`. -/
def AdjointWindowNorms : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∀ χ : ℝ → ℝ, WindowCutoff χ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ) (f w : Yq P r)
      (W Fr : ℝ × Space → CVec3), IsRep w W → IsRep f Fr → ∀ (τ₀ : ℝ) (c : Fin 3),
        MemLp (adjWindowField χ τ₀ W c) (ENNReal.ofReal r.toReal) volume ∧
        MemLp (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ∧
        eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^ r.toReal ≤
          ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
            (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
              ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **Leaf C (the Laplacian of `w` on the window).** If the components `u_c` have weak second
derivatives `D2 c i j ∈ L^r`, then `adjWindowLap` of `Σ_i D2 c i i` is a weak Laplacian of `w` on
`|τ - τ₀| < 1` (where `χ = 1`; `Δ_y W = e^{-t} Δ_x u`). Analogue of `WindowBackEquation`. -/
def AdjointWindowBackEquation : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ τ₀ : ℝ,
      ∀ D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ,
        (∀ c i j, MemLp (D2 c i j) (ENNReal.ofReal r.toReal) volume ∧
          B0423.HasWeakSpaceDeriv2C (d := 3) (adjWindowField χ τ₀ W c) i j (D2 c i j)) →
        IsWindowLaplacian ν τ₀ W (adjWindowLap ν τ₀ fun c X => ∑ i, D2 c i i X)

/-- **Leaf D (the norm of the transported Laplacian).** For `q > 1` there is `K` (depending only
on `q`) with `∫_{τ₀-1}^{τ₀+1}∫ |adjWindowLap(τ,y)|^q dy dτ ≤ K^q Σ_c ‖ν D_c‖_q^q` for every
measurable family `D` (`dy = e^{3t/2} dx`, `dτ = dθ/(1-θ)`, weights bounded on `|t| < 1`).
Analogue of `WindowBackNorm`. -/
def AdjointWindowBackNorm : Prop :=
  ∀ q : ℝ, 1 < q → ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ),
    (∀ c, AEStronglyMeasurable (D c) volume) →
      ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖adjWindowLap ν τ₀ D (τ, y)‖ₑ ^ q ≤
        ENNReal.ofReal K ^ q *
          ∑ c, eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q

/-- **Adjoint local window estimate, conditional on the four leaves.** -/
theorem adjointLocalWindowEstimate_of (h1 : AdjointWindowEquation) (h2 : AdjointWindowNorms)
    (h3 : AdjointWindowBackEquation) (h4 : AdjointWindowBackNorm) : AdjointLocalWindowEstimate := by
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
  have hheat := fun c => hCh ν hν (adjWindowField χ τ₀ W c) (adjWindowForce μ χ τ₀ W Fr c)
    (hmem c).1 (hmem c).2.1 (heq c)
  choose D2 Dt hD2 hDt hDtw hb hbt using hheat
  refine ⟨adjWindowLap ν τ₀ fun c X => ∑ i, D2 c i i X,
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
        ≤ ((Ch : ℝ≥0∞) * eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume) ^ q :=
          ENNReal.rpow_le_rpow (hb c) hq0
      _ = (Ch : ℝ≥0∞) ^ q * eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume ^ q :=
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


theorem adjointGlobalFieldWindowBound (hloc : AdjointLocalWindowEstimate)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r) (hrt : r ≠ ⊤) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∃ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ ∧
          (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) ∧
          (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) ∧
          ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
  obtain ⟨C, hC0, hC⟩ := hloc r hr1 hrt
  refine ⟨C, hC0, ?_⟩
  intro P hP hP1 ν hν μ f w hf W hW
  have hCP := hC P hP1 ν hν μ f w hf W hW
  choose Λk hΛk hbd using fun k : ℤ => hCP (k : ℝ)
  have hfin2 : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λk k (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro k
    refine lt_of_le_of_lt (hbd k) (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w (k : ℝ)))
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (Λk k) (volume.restrict (winSet (k : ℝ))) :=
    fun k => windowLapAEMeas ν (k : ℝ) W (Λk k) (hΛk k)
  have hli : ∀ k : ℤ, LocallyIntegrableOn (Λk k) (winSet (k : ℝ)) :=
    fun k => windowLapLocInt r hrt _ _ (Λk k) (hmeas k) (hfin2 k)
  have hover : ∀ k l : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))] Λk l := by
    intro k l
    have hset : winSet (k : ℝ) ∩ winSet (l : ℝ) =
        Ioo (max ((k : ℝ) - 1) ((l : ℝ) - 1)) (min ((k : ℝ) + 1) ((l : ℝ) + 1)) ×ˢ
          (univ : Set Space) := by
      unfold winSet
      rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioo_inter_Ioo]
    rw [hset]
    exact windowLapUnique ν k l _ _ W (Λk k) (Λk l) (le_max_left _ _) (min_le_left _ _)
      (le_max_right _ _) (min_le_right _ _) (hΛk k) (hΛk l)
      ((hli k).mono_set (by rw [← hset]; exact Set.inter_subset_left))
      ((hli l).mono_set (by rw [← hset]; exact Set.inter_subset_right))
  obtain ⟨Λ, hΛm, hΛeq⟩ := windowLapGlue Λk hmeas hover
  have hwin : ∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ := windowLapPoU ν W Λ Λk hΛk hΛeq
  have hli' : ∀ k : ℤ, LocallyIntegrableOn Λ (winSet (k : ℝ)) :=
    fun k => (hli k).congr (hΛeq k).symm
  have hWper : ∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y) := by
    filter_upwards [hW.slice, hW.slice_shift P] with t h1 h2
    have e : ((P + t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [add_comm]; exact AddCircle.coe_add_period P t
    rw [e] at h2
    rw [add_comm t P]
    exact h2.trans h1.symm
  have hperΛ : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y) :=
    windowLapPeriodic_of windowLapUnique P ν hP.out W Λ hW.meas hΛm hWper hwin hli'
  -- equal integrals over a window when the fields agree a.e. on that window
  have hcongrW : ∀ (a b : ℝ) (Λ₁ Λ₂ : ℝ × Space → CVec3),
      Λ₁ =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] Λ₂ →
      ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₁ (τ, y)‖ₑ ^ r.toReal =
        ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₂ (τ, y)‖ₑ ^ r.toReal := by
    intro a b Λ₁ Λ₂ h
    have h' : Λ₁ =ᵐ[((volume : Measure ℝ).restrict (Ioo a b)).prod (volume : Measure Space)] Λ₂ := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact h
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod h'] with τ hτ
    apply lintegral_congr_ae
    filter_upwards [hτ] with y hy
    rw [hy]
  have hfinW : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    intro k
    rw [hcongrW ((k : ℝ) - 1) ((k : ℝ) + 1) Λ (Λk k) (hΛeq k)]
    exact hfin2 k
  -- local integrability of `Λ` on every real window, from two integer windows
  have hLIΛ : ∀ τ₀ : ℝ, LocallyIntegrableOn Λ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    intro τ₀
    apply windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ hΛm.aestronglyMeasurable
    have hk1 := Int.floor_le τ₀
    have hk2 := Int.lt_floor_add_one τ₀
    have hsub : Ioo (τ₀ - 1) (τ₀ + 1) ⊆
        Ioo (((⌊τ₀⌋ : ℤ) : ℝ) - 1) (((⌊τ₀⌋ : ℤ) : ℝ) + 1) ∪
          Ioo ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) - 1) ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) + 1) := by
      intro t ht
      simp only [Set.mem_union, Set.mem_Ioo, Int.cast_add, Int.cast_one] at ht ⊢
      by_cases hkt : t < ((⌊τ₀⌋ : ℤ) : ℝ) + 1
      · left
        constructor <;> linarith [ht.1, ht.2]
      · right
        push_neg at hkt
        constructor <;> linarith [ht.1, ht.2]
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
    exact ENNReal.add_lt_top.2 ⟨hfinW _, hfinW _⟩
  refine ⟨Λ, hΛm, hwin, hperΛ, ?_⟩
  intro τ₀
  obtain ⟨Λ₀, hΛ₀, hbd₀⟩ := hCP τ₀
  have hli₀ : LocallyIntegrableOn Λ₀ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    refine windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ₀ (windowLapAEMeas ν τ₀ W Λ₀ hΛ₀) ?_
    exact lt_of_le_of_lt hbd₀ (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w τ₀))
  have hae : Λ =ᵐ[volume.restrict (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space))] Λ₀ :=
    windowLapUnique ν τ₀ τ₀ (τ₀ - 1) (τ₀ + 1) W Λ Λ₀ le_rfl le_rfl le_rfl le_rfl (hwin τ₀) hΛ₀
      (hLIΛ τ₀) hli₀
  rw [hcongrW (τ₀ - 1) (τ₀ + 1) Λ Λ₀ hae]
  exact hbd₀


/-- `BodyLaplacianBound` from the leaves (given the local window estimate). -/
theorem adjointLaplacianBound_r (hloc : AdjointLocalWindowEstimate)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r) (hrt : r ≠ ⊤) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
        ∃ a : Yq P r, HasPhaseOp (nuLapT ν) w a ∧ ‖a‖ ≤ C * (‖f‖ + (1 + ‖μ‖) * ‖w‖) := by
  have h2 : PeriodAverageBound := periodAverageBound
  have h3 : SliceIntegralYq := sliceIntegralYq
  have h4 : LaplacianFieldToYRep := laplacianFieldToYRep
  have h5 : YqRepNorm := yqRepNorm
  have h6 : NormFromPower := normFromPower
  obtain ⟨C, hC0, hC⟩ := adjointGlobalFieldWindowBound hloc r hr1 hrt
  have hs : 1 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hrt).2 hr1
    simpa using this
  obtain ⟨K', hK0, hK'⟩ := h6 r.toReal hs C hC0
  refine ⟨K', hK0, ?_⟩
  intro P _ hP ν hν μ f w hf
  obtain ⟨W, hW⟩ := exists_isRep hrt w
  obtain ⟨Λ, hm, hwin, hper, hbd⟩ := hC P hP ν hν μ f w hf W hW
  have hav := h2 r hrt P C μ f w Λ hm hper hbd
  have hP3 := h3 r hrt P μ f w
  set R : ℝ≥0∞ := ‖f‖ₑ ^ r.toReal +
    ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w‖ₑ ^ r.toReal with hR
  have hRtop : R < ⊤ := by
    rw [hR]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top, ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        ENNReal.ofReal_ne_top) (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top)⟩
  have hfin : ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    refine lt_of_le_of_lt hav ?_
    rw [hP3]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRtop)
  obtain ⟨a, haR, haOp⟩ := h4 r hrt P ν w W hW Λ hm hwin hper hfin
  refine ⟨a, haOp, ?_⟩
  have h5' := h5 r hrt P a Λ haR
  have key : ‖a‖ₑ ^ r.toReal ≤ 2 * ENNReal.ofReal C ^ r.toReal * R := by
    have hle : ENNReal.ofReal P * ‖a‖ₑ ^ r.toReal ≤
        ENNReal.ofReal P * (2 * ENNReal.ofReal C ^ r.toReal * R) := by
      rw [h5']
      calc _ ≤ 2 * ENNReal.ofReal C ^ r.toReal * (ENNReal.ofReal P * R) := by
            rw [← hP3]; exact hav
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right
      (by simpa using Fact.out (p := 0 < P)) ENNReal.ofReal_ne_top).1 hle
  have := hK' ‖a‖ ‖f‖ ‖w‖ (1 + ‖μ‖) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (by positivity)
  refine this ?_
  simp only [ofReal_norm]
  exact key


/-- **The time-reversed diffusion bound from the reversed local window estimate** (1426-1442,
1470-1480): centre averaging with no inverse-period factor, at `r = 2`. -/
theorem adjointLaplacianBound_of (hloc : AdjointLocalWindowEstimate) : AdjointLaplacianBound := by
  obtain ⟨C, hC0, hC⟩ := adjointLaplacianBound_r hloc (2 : ℝ≥0∞) (by norm_num) (by simp)
  exact ⟨C, hC0, fun P _ hP ν hν μ f w hw => hC P hP ν hν μ f w hw⟩

end UnforcedLeray.Short.PartIIa
