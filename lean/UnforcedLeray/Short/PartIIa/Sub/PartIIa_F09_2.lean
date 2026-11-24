import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_2.ReflHeat
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03bWindowNorms
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm

/-!
# Part II-a, task `PartII-a:F09/2`: the adjoint maximal domain at `r = 2`

Source `the November 2 reference manuscript`:
lemma `bg:common-body-graph`, lines 1356-1366 ("At `r = 2` the adjoint has the same maximal
graph"); the window paragraph 1426-1443 (the pull-back `v(t,x) = e^{-t/2} w(τ₀+t, e^{-t/2}x)`, the
cutoff, `θ = e^t`, the local heat estimate, "the same reasoning applies to any distributional
`Y_r` solution"); the local heat estimate 1377-1382 and "the reflected kernel has the same
bounds", 1417-1418; and 1467-1471 ("At `r = 2`, reverse the phase window and use `θ = 1 - e^{-t}`
for `L^* = -𝒯 - νΔ + 1` ... this reversed-window estimate places it in `D_2`").

## The adjoint equation is the forward equation with the viscosity reversed

`AdjointMaximalDomain` (`Sub/PartII-a_F09.lean`) is about a distributional solution
`HasPhaseOp (fun Φ => μ̄ • Φ + L₀ Φ) w f`, i.e. `(μ̄ - 𝒯 - νΔ + 1) w = f` (`L^* = -𝒯 - νΔ + 1`,
line 1469). On tests `L₀Φ = -driftT Φ - νΔΦ + Φ` (`L0_eq_adjoint`) and
`L₀ᵗ_{-ν}Φ = driftT Φ + νΔΦ - Φ/2` (`B0411.L0T` at viscosity `-ν`), hence
(`adjoint_test_eq_forward`)

  `μ̄Φ + L₀Φ = -(μ'Φ + L₀ᵗ_{-ν}Φ)`,  `μ' = adjMu μ = -μ̄ - 1/2`,

and `HasPhaseOp (μ̄ + L₀) w f` gives `HasPhaseOp (μ' + L₀ᵗ_{-ν}) w (-f)`
(`hasPhaseOp_forward_of_adjoint`): `w` solves the *forward* body equation `(μ' + L)w = -f` of
line 1345 with viscosity `-ν`. The radial drift keeps its sign; only the diffusion is reversed.
This is the time reversal of lines 1467-1468 read in the heat time: with `s = -t` the forward
chart `(τ₀ + t, y) ↦ (θ, x) = (e^t, e^{t/2} y)` reads `(τ₀ - s, y) ↦ (e^{-s}, e^{-s/2} y)`, so after
the reflection `σ = -θ` it is the reversed-window chart `(τ₀ - s, y) ↦ (1 - e^{-s}, e^{-s/2} y)` of
lines 1467-1468 shifted by `1` in the heat time; the two windows differ only by this shift and the
amplitude `e^{-t/2}`, both harmless on `|t| < 2`.

## The reversed window estimate from the forward window leaves

The four window leaves of `Sub/F03.lean` (accepted: `windowEquation`, `windowNorms`,
`windowBackEquation`, `windowBackNorm`) are stated for every real viscosity; only the heat
estimate needs `ν > 0`. So, with the same pull-back `u_c = windowField χ τ₀ W c` (window of lines
1426-1430, `θ = e^t`, `x = e^{t/2} y`):

* `WindowEquation` at `(-ν, μ', -f)`: `(∂_θ + νΔ_x) u_c = windowForce μ' χ τ₀ W (-Fr) c`
  weakly, a *backward* heat equation (`IsWeakHeatSolC (-ν)`);
* `WindowNorms`: `u_c` and the force are in `L^r`, with the force bound of lines 1432-1436 and
  `1 + |μ'| ≤ (3/2)(1 + |μ|)` (`norm_adjMu_le`), `‖(-f)(τ)‖ = ‖f(τ)‖` (`adj_window_rhs_le`);
* the reflected heat estimate `heat_estimate_complex_laplacian_neg`
  (`Sub/PartII-a_F09_2/ReflHeat.lean`: `θ ↦ -θ`, then `B0423.heat_estimate_complex_laplacian`;
  lines 1417-1418, 1467-1469) gives weak second derivatives `D2 c i j ∈ L^r` of `u_c` with
  `‖ν Σ_i D2 c i i‖_r ≤ C‖F_c‖_r`;
* `WindowBackEquation`, `WindowBackNorm` at `+ν`: `windowLap ν τ₀ (Σ_i D2 c i i)` is a weak
  Laplacian `νΔW` on `|τ - τ₀| < 1` with the window bound.

This is `adjointLocalWindowEstimate_of_forward`, which proves the reversed-window estimate
`AdjointLocalWindowEstimate` of `Sub/PartII-a_F09_3_1.lean` (lines 1426-1442 reversed) with no
new chart: `adjointLocalWindowEstimate_viaForward` is unconditional.

## Gluing, the drift step and the maximal domain

The gluing of the window Laplacians does not see the drift (`IsWindowLaplacian ν τ₀ W Λ` involves
only `W` and `νΔ`), so the drift-free forward leaves apply verbatim: the role of an adjoint
`GlobalLaplacianField` is played by `adjointGlobalFieldWindowBound` (`Sub/PartII-a_F09_3_1.lean`,
from the accepted F04a leaves `windowLapAEMeas` ... `windowLapPeriodic_of`) and that of an
adjoint `LaplacianFieldToY` by the accepted drift-free `LaplacianFieldToYRep`; both are packaged
in `adjointLaplacianBound_of` (centre averaging with no inverse period factor, lines 1437-1441),
which gives `νΔw = a ∈ Y_2`. The equation then gives the drift (lines 1441-1442):
`T₀ w = (μ̄ + 1) w - a - f` (`hasPhaseOp_adjDrift_of`), and `w ∈ D P ν 2` by `mem_D`
(`adjointMaximalDomain_of`). The adjoint existence (`AdjointExistence`) is not used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- The forward parameter of the adjoint equation: `μ' = -μ̄ - 1/2`, so that
`μ̄ + L^* = -(μ' + L_{-ν})` (`adjoint_test_eq_forward`). -/
def adjMu (μ : ℂ) : ℂ := -(starRingEnd ℂ) μ - 1 / 2

theorem norm_adjMu_le (μ : ℂ) : 1 + ‖adjMu μ‖ ≤ 3 / 2 * (1 + ‖μ‖) := by
  have h : ‖adjMu μ‖ ≤ ‖μ‖ + 1 / 2 := by
    unfold adjMu
    calc ‖-(starRingEnd ℂ) μ - 1 / 2‖ ≤ ‖-(starRingEnd ℂ) μ‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖μ‖ + 1 / 2 := by
          rw [norm_neg, Complex.norm_conj]
          norm_num
  linarith [norm_nonneg μ]

/-- On test fields, `μ̄Φ + L₀Φ = -((-μ̄ - 1/2)Φ + L₀ᵗ_{-ν}Φ)`: the adjoint test operator is minus
the forward test operator with viscosity `-ν` and parameter `adjMu μ`. -/
theorem adjoint_test_eq_forward (μ : ℂ) (ν : ℝ) (Φ : ℝ × Space → CVec3) :
    adjMu μ • Φ + L0T (-ν) Φ = -((starRingEnd ℂ) μ • Φ + L0 ν Φ) := by
  rw [L0_eq_adjoint]
  funext p
  simp only [adjMu, L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
  have h1 : ((1 / 2 : ℝ) • Φ p : CVec3) = (1 / 2 : ℂ) • Φ p := by
    rw [← Complex.coe_smul]; norm_num
  have h2 : (-ν) • lapT Φ p = -(ν • lapT Φ p) := neg_smul ν (lapT Φ p)
  rw [h1, h2]
  module

/-- The adjoint equation is the forward body equation with viscosity `-ν`, parameter `adjMu μ`
and right side `-f`. -/
theorem hasPhaseOp_forward_of_adjoint {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {ν : ℝ}
    {μ : ℂ} {w f : Yq P r} (hf : HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f) :
    HasPhaseOp (fun Φ => adjMu μ • Φ + L0T (-ν) Φ) w (-f) := by
  intro Φ hΦ
  have hT : IsPhaseTest P ((starRingEnd ℂ) μ • Φ + L0 ν Φ) := by
    rw [L0_eq_adjoint]
    exact (hΦ.const_smul _).add ((hΦ.driftT.neg.sub (isPhaseTest_nuLapT hΦ ν)).add hΦ)
  show phasePair P r (adjMu μ • Φ + L0T (-ν) Φ) w = phasePair P r Φ (-f)
  rw [adjoint_test_eq_forward, phasePair_neg hT, map_neg]
  congr 1
  exact hf Φ hΦ

/-- A representative of `-f` is `-Fr`. -/
theorem isRep_neg {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {f : Yq P r}
    {Fr : ℝ × Space → CVec3} (hFr : IsRep f Fr) : IsRep (-f) (-Fr) where
  meas := hFr.meas.neg
  slice := by
    have h1 : ∀ᵐ τ : ℝ, ((-f : Yq P r) (τ : AddCircle P)) = -(f (τ : AddCircle P)) :=
      UnforcedLeray.PhaseTrace.ae_comp_mk (Lp.coeFn_neg f)
    filter_upwards [h1, hFr.slice] with τ hτ hs
    rw [hτ]
    filter_upwards [hs, Lp.coeFn_neg (f (τ : AddCircle P))] with y hy hn
    rw [hn, Pi.neg_apply, Pi.neg_apply, ← hy]

/-- The right side of the window bound for `(-f, adjMu μ)` is at most `(3/2)^r` times that for
`(f, μ)`. -/
theorem adj_window_rhs_le {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 0 < r.toReal)
    (μ : ℂ) (f w : Yq P r) (a b : ℝ) :
    ∫⁻ τ in Ioo a b, (‖(-f) (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖adjMu μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) ≤
      ENNReal.ofReal (3 / 2) ^ r.toReal * ∫⁻ τ in Ioo a b, (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
  have hq0 : 0 ≤ r.toReal := hr.le
  have h1 : ∀ᵐ τ : ℝ, ((-f : Yq P r) (τ : AddCircle P)) = -(f (τ : AddCircle P)) :=
    UnforcedLeray.PhaseTrace.ae_comp_mk (Lp.coeFn_neg f)
  have hc1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2) ^ r.toReal :=
    ENNReal.one_le_rpow (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      hr
  have hc2 : ENNReal.ofReal (1 + ‖adjMu μ‖) ^ r.toReal ≤
      ENNReal.ofReal (3 / 2) ^ r.toReal * ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_adjMu_le μ)) hq0
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae h1] with τ hτ
  rw [hτ, enorm_neg]
  calc ‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖adjMu μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal
      ≤ ENNReal.ofReal (3 / 2) ^ r.toReal * ‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        (ENNReal.ofReal (3 / 2) ^ r.toReal * ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal) *
          ‖w (τ : AddCircle P)‖ₑ ^ r.toReal := by
        gcongr
        exact le_mul_of_one_le_left zero_le hc1
    _ = ENNReal.ofReal (3 / 2) ^ r.toReal * (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by ring

/-- **The reversed fixed-window estimate from the forward window leaves** (lines 1426-1443,
1467-1471): the adjoint equation is the forward equation at viscosity `-ν`
(`hasPhaseOp_forward_of_adjoint`), the forward pull-back solves a backward heat equation
(`WindowEquation` at `-ν`), and the reflected heat estimate (`heat_estimate_complex_laplacian_neg`)
replaces the forward one. -/
theorem adjointLocalWindowEstimate_of_forward (h1 : WindowEquation) (h2 : WindowNorms)
    (h3 : WindowBackEquation) (h4 : WindowBackNorm) : AdjointLocalWindowEstimate := by
  intro r _ hr1 hrt
  have hq : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hqpos : 0 < r.toReal := by linarith
  have hq0 : 0 ≤ r.toReal := hqpos.le
  obtain ⟨χ, hχ⟩ := windowCutoff_exists
  obtain ⟨K, hK0, hK⟩ := h2 r hr1 hrt χ hχ
  obtain ⟨K', hK'0, hK'⟩ := h4 r.toReal hq
  obtain ⟨Ch, hCh⟩ := heat_estimate_complex_laplacian_neg (d := 3) hq
  set q := r.toReal with hqdef
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / q) := by positivity
  set K₂ : ℝ := 3 / 2 * K with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨(3 : ℝ) ^ (1 / q) * K' * Ch * K₂, by positivity, ?_⟩
  intro P _ hP1 ν hν μ f w hw W hW τ₀
  obtain ⟨Fr, hFr⟩ := exists_isRep hrt f
  have hFr' : IsRep (-f) (-Fr) := isRep_neg hFr
  have hw' := hasPhaseOp_forward_of_adjoint hw
  have heq := h1 r hrt P (-ν) (adjMu μ) (-f) w hw' W (-Fr) hW hFr' χ hχ τ₀
  have hmem := fun c => hK P (adjMu μ) (-f) w W (-Fr) hW hFr' τ₀ c
  have hheat := fun c => hCh ν hν (windowField χ τ₀ W c)
    (windowForce (adjMu μ) χ τ₀ W (-Fr) c) (hmem c).1 (hmem c).2.1 (heq c)
  choose D2 hD2 hb using hheat
  refine ⟨windowLap ν τ₀ fun c X => ∑ i, D2 c i i X,
    h3 r hrt P ν w W hW χ hχ τ₀ D2 fun c i j => hD2 c i j, ?_⟩
  set R : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
    (‖f (τ : AddCircle P)‖ₑ ^ q + ENNReal.ofReal (1 + ‖μ‖) ^ q * ‖w (τ : AddCircle P)‖ₑ ^ q)
    with hR
  have hforce : ∀ c, eLpNorm (windowForce (adjMu μ) χ τ₀ W (-Fr) c) (ENNReal.ofReal q)
      volume ^ q ≤ ENNReal.ofReal K₂ ^ q * R := fun c => by
    refine (hmem c).2.2.trans ?_
    calc ENNReal.ofReal K ^ q * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
          (‖(-f) (τ : AddCircle P)‖ₑ ^ q +
            ENNReal.ofReal (1 + ‖adjMu μ‖) ^ q * ‖w (τ : AddCircle P)‖ₑ ^ q)
        ≤ ENNReal.ofReal K ^ q * (ENNReal.ofReal (3 / 2) ^ q * R) :=
          mul_le_mul' le_rfl (adj_window_rhs_le hqpos μ f w _ _)
      _ = ENNReal.ofReal K₂ ^ q * R := by
          rw [hK₂, ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hq0]
          ring
  have hmeas : ∀ c, AEStronglyMeasurable (fun X : PS 3 => ∑ i, D2 c i i X) volume := fun c =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD2 c i i).1.1
  refine (hK' ν τ₀ (fun c X => ∑ i, D2 c i i X) hmeas).trans ?_
  have hterm : ∀ c, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q)
      volume ^ q ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K₂ ^ q * R) := fun c => by
    calc eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q) volume ^ q
        ≤ ((Ch : ℝ≥0∞) * eLpNorm (windowForce (adjMu μ) χ τ₀ W (-Fr) c) (ENNReal.ofReal q)
            volume) ^ q :=
          ENNReal.rpow_le_rpow (hb c) hq0
      _ = (Ch : ℝ≥0∞) ^ q * eLpNorm (windowForce (adjMu μ) χ τ₀ W (-Fr) c) (ENNReal.ofReal q)
            volume ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K₂ ^ q * R) :=
          mul_le_mul' le_rfl (hforce c)
  have hsum : ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
      (ENNReal.ofReal q) volume ^ q ≤ 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K₂ ^ q * R)) := by
    calc ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
          (ENNReal.ofReal q) volume ^ q
        ≤ ∑ _c : Fin 3, (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K₂ ^ q * R) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K₂ ^ q * R)) := by
          simp [Finset.sum_const]
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  have hC : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K₂) ^ q =
      ENNReal.ofReal K' ^ q * (3 * ((Ch : ℝ≥0∞) ^ q * ENNReal.ofReal K₂ ^ q)) := by
    have h1' : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K₂) =
        ENNReal.ofReal ((3 : ℝ) ^ (1 / q)) * ENNReal.ofReal K' * (Ch : ℝ≥0∞) *
          ENNReal.ofReal K₂ := by
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

/-- **The reversed fixed-window estimate, unconditional**: the accepted forward window leaves
(`PartII-a:F03/1`-`/4`) and the reflected heat estimate. -/
theorem adjointLocalWindowEstimate_viaForward : AdjointLocalWindowEstimate :=
  adjointLocalWindowEstimate_of_forward windowEquation windowNorms windowBackEquation
    windowBackNorm

/-- **The adjoint drift step** (lines 1441-1442, "the equation gives the drift bound"): from the
adjoint equation and `νΔw = a`, `T₀ w = (μ̄ + 1) w - a - f` in distributions
(`L₀Φ = -driftT Φ - νΔΦ + Φ`, so `⟪driftT Φ, w⟫ = (μ̄ + 1)⟪Φ, w⟫ - ⟪Φ, a⟫ - ⟪Φ, f⟫`). -/
theorem hasPhaseOp_adjDrift_of {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {ν : ℝ} {μ : ℂ}
    {w f a : Yq P r} (hf : HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f)
    (ha : HasPhaseOp (nuLapT ν) w a) :
    HasPhaseOp driftT w (((starRingEnd ℂ) μ + 1) • w - a - f) := by
  intro Φ hΦ
  have h1 : phasePair P r ((starRingEnd ℂ) μ • Φ + L0 ν Φ) w = phasePair P r Φ f := hf Φ hΦ
  have h2 := ha Φ hΦ
  have hd := hΦ.driftT
  have hn := isPhaseTest_nuLapT hΦ ν
  have hc : IsPhaseTest P ((starRingEnd ℂ) μ • Φ) := hΦ.const_smul _
  rw [L0_eq_adjoint, phasePair_add hc ((hd.neg.sub hn).add hΦ), phasePair_add (hd.neg.sub hn) hΦ,
    phasePair_sub hd.neg hn, phasePair_neg hd, phasePair_const_smul hΦ, h2] at h1
  simp only [map_sub, map_smul, smul_eq_mul]
  linear_combination -h1

/-- **`PartII-a:F09/2`, conditional on the reversed window estimate**: every distributional `Y_2`
solution of the adjoint equation lies in `D_2` (`adjointLaplacianBound_of` for `νΔw ∈ Y_2`, the
drift step for `T₀w ∈ Y_2`, `mem_D`). -/
theorem adjointMaximalDomain_of (hloc : AdjointLocalWindowEstimate) : AdjointMaximalDomain := by
  intro P _ hP ν hν μ _ w f hf
  obtain ⟨C, -, hC⟩ := adjointLaplacianBound_of hloc
  obtain ⟨a, ha, -⟩ := hC P hP ν hν μ f w hf
  exact mem_D.2 ⟨⟨a, ha⟩, ⟨_, hasPhaseOp_adjDrift_of hf ha⟩⟩

/-- Probe of the final assembly of task `PartII-a:F09/2`. -/
example : AdjointMaximalDomain := adjointMaximalDomain_of adjointLocalWindowEstimate_viaForward

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.adjointLocalWindowEstimate_viaForward
#print axioms UnforcedLeray.Short.PartIIa.adjointMaximalDomain_of
