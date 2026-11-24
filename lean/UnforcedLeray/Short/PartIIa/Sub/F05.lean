import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# Part II-a, task `PartII-a:F05`: homogeneous uniqueness (conditional on the adjoint resolvent)

Source of record: `the November 2 reference manuscript`, lines 1403-1423
("uniqueness does not require an a priori graph"). The argument: for a smooth compact spatial
(here: phase) test `Φ₀`, the adjoint resolvent `Ψ` of `Φ₀` solves `(μ + L₀ᵗ)Ψ = Φ₀` and has
`Ψ`, `∂ⱼΨ`, `ΔΨ`, `T₀ᵗΨ` in `Y_{r'}` (line 1411-1413: "by the gap and the extra factor
`e^{-t/2}` per derivative"). A homogeneous distributional solution `w` is tested against `Ψ`
times a radial cutoff; the cutoff commutators vanish in the limit (line 1414-1417), so
`⟨(μ + L₀ᵗ)Ψ, w⟩ = 0` for the Schwartz-type test `Ψ`, i.e. `⟨Φ₀, w⟩ = 0` for all tests `Φ₀`, so
`w = 0` (phase tests separate the points of `Y_r`, `B0411.eq_zero_of_forall_phasePair`).

Decomposition (the analytic core is the only unproved input):

* `AdjResolventSolution` (task `PartII-a:F05/1`): the adjoint resolvent of a phase test exists as a
  smooth periodic solution with polynomial decay `|y|^{-2(Re μ + 1)}` of `Ψ, ∂ⱼΨ, ΔΨ`.
* `SliceContOfDecay` (task `PartII-a:F05/2`): continuous functions with polynomial decay of
  exponent `s`, `s q > 3`, are slice continuous into `L^q(ℝ³)`.

Proved here (no hypotheses): the extension of the homogeneous equation to Schwartz-type tests
(`hasPhaseOp_body_extend`, from `HasPhaseOp.extend_of_tendsto` and the cutoff convergence of
`Lib/PhaseSpace/ExtendedTest.lean`), the exponent arithmetic `s (r')_ℝ > 3`
(`decay_exponent`), the assembly `adjointResolventSchwartz_of` of the two leaves into
`AdjointResolventSchwartz`, and `bodyOp_uniqueness_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Leaf `PartII-a:F05/1` (adjoint resolvent of a phase test; lines 1403-1413).** For `ν > 0`,
`Re μ + 1 > 0`, and a phase test `Φ₀`, there is a smooth `P`-periodic `Ψ` with
`(μ + L₀ᵗ)Ψ = Φ₀` pointwise, and with polynomial decay `|y|^{-2(Re μ + 1)}` of `Ψ`, `∂ⱼΨ`,
`ΔΨ` uniformly in the phase.

Proof idea: `Ψ(τ, y) = ∫₀^∞ e^{-(μ+1)t} [e^{ν(1-e^{-t})Δ} Φ₀(τ + t, ·)](e^{-t/2} y) dt` (the
adjoint semigroup `S(t)*h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)` of line 1405 composed with the
phase shift and `e^{-μ t}`). The integrand and all its `(τ, y)`-derivatives are bounded by
`C e^{-(Re μ + 1)t}` (heat flow of a smooth compactly supported field has uniformly bounded
derivatives, with Gaussian-times-compact tails), so one differentiates under the integral;
`d/dt` of the integrand is `-(μ+1)·integrand + ∂_τ - ½ y·∇ + ν Δ` of it, which gives
`-∂_τΨ + ½ y·∇Ψ + (μ+1)Ψ - νΔΨ = Φ₀` after `∫₀^∞ d/dt = -(value at t = 0) = -Φ₀`. For the decay,
`|(e^{sΔ}Φ₀)(z)| ≤ C_N (1+|z|)^{-N}` uniformly in `s ∈ [0, ν]` for every `N`, and the
substitution `u = e^{-t/2}|y|` bounds the integral by `C |y|^{-2(Re μ + 1)}`; each `∂ⱼ` adds a
factor `e^{-t/2}`, hence decay `|y|^{-2(Re μ+1)-1}`, and `Δ` a factor `e^{-t}`. -/
def AdjResolventSolution : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 →
    ∀ Φ₀ : ℝ × Space → CVec3, IsPhaseTest P Φ₀ →
      ∃ Ψ : ℝ × Space → CVec3, ContDiff ℝ ∞ Ψ ∧ (∀ τ y, Ψ (τ + P, y) = Ψ (τ, y)) ∧
        (∀ p, (μ • Ψ + L0T ν Ψ) p = Φ₀ p) ∧
        ∃ C : ℝ, ∀ (τ : ℝ) (y : Space),
          ‖Ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 * (μ.re + 1))) ∧
          (∀ j, ‖dy j Ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 * (μ.re + 1)))) ∧
          ‖lapT Ψ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 * (μ.re + 1)))

/-- **Leaf `PartII-a:F05/2` (slice continuity from polynomial decay).** A continuous `ℂ³`-valued
function on `ℝ × ℝ³` with `|G(τ, y)| ≤ C (1 + |y|)^{-s}`, `s q > 3`, `q < ∞`, has all slices in
`L^q(ℝ³)` and depends continuously on the phase there (dominated convergence with the dominating
function `C (1+|y|)^{-s} ∈ L^q`). -/
def SliceContOfDecay : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ⊤ → ∀ (s C : ℝ), 3 < s * q.toReal →
    ∀ G : ℝ × Space → CVec3, Continuous G →
      (∀ (τ : ℝ) (y : Space), ‖G (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-s)) → SliceCont q G

/-- **The adjoint resolvent of a phase test is a Schwartz-type phase test in `Y_{r'}`**
(lines 1411-1413): for `1 < r < 3`, `a_r = Re μ + γ_r > 0`, `ν > 0`, every phase test `Φ₀` is
`(μ + L₀ᵗ)Ψ` for a Schwartz-type phase test `Ψ` (smooth, periodic, with `Ψ, ∂ⱼΨ, ΔΨ, T₀ᵗΨ`
slice continuous into `L^{r'}`). -/
def AdjointResolventSchwartz : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν →
    ∀ μ : ℂ, 0 < μ.re + gammaR r → ∀ Φ₀ : ℝ × Space → CVec3, IsPhaseTest P Φ₀ →
      ∃ Ψ : ℝ × Space → CVec3, IsPhaseSchwartz P (conjExp r) Ψ ∧
        ∀ p, (μ • Ψ + L0T ν Ψ) p = Φ₀ p

/-! ### Exponent arithmetic -/

theorem one_lt_toReal {r : ℝ≥0∞} (h1 : 1 < r) (hr : r ≠ ⊤) : 1 < r.toReal := by
  have := ENNReal.toReal_strict_mono hr h1
  simpa using this

theorem toReal_conjExp {r : ℝ≥0∞} (h1 : 1 < r) (hr : r ≠ ⊤) :
    (conjExp r).toReal = r.toReal / (r.toReal - 1) := by
  have ht := one_lt_toReal h1 hr
  have hinv : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 h1.le
  have h2 : (1 - r⁻¹).toReal = 1 - r.toReal⁻¹ := by
    rw [ENNReal.toReal_sub_of_le hinv ENNReal.one_ne_top, ENNReal.toReal_inv]
    simp
  have h3 : conjExp r = (1 - r⁻¹)⁻¹ := rfl
  rw [h3, ENNReal.toReal_inv, h2]
  have ht0 : r.toReal ≠ 0 := by positivity
  have ht1 : r.toReal - 1 ≠ 0 := by linarith
  field_simp

/-- The decay exponent `s = 2 (Re μ + 1)` satisfies `s · (r')_ℝ > 3` when `a_r > 0`. -/
theorem decay_exponent {r : ℝ≥0∞} (h1 : 1 < r) (hr : r ≠ ⊤) {μ : ℂ}
    (hμ : 0 < μ.re + gammaR r) : 3 < 2 * (μ.re + 1) * (conjExp r).toReal := by
  have ht := one_lt_toReal h1 hr
  rw [toReal_conjExp h1 hr]
  set t := r.toReal with htdef
  have ht1 : 0 < t - 1 := by linarith
  have ht0 : 0 < t := by linarith
  have hg : gammaR r = (3 / t - 1) / 2 := rfl
  rw [hg] at hμ
  have h3t : 3 / t * t = 3 := by field_simp
  have hs : 3 - 3 / t < 2 * (μ.re + 1) := by linarith
  rw [← mul_div_assoc, lt_div_iff₀ ht1]
  nlinarith

/-- `0 < Re μ + γ_r` implies `0 < Re μ + 1` for `r > 1`. -/
theorem re_add_one_pos {r : ℝ≥0∞} (h1 : 1 < r) (hr : r ≠ ⊤) {μ : ℂ}
    (hμ : 0 < μ.re + gammaR r) : 0 < μ.re + 1 := by
  have ht := one_lt_toReal h1 hr
  have hg : gammaR r = (3 / r.toReal - 1) / 2 := rfl
  have : 3 / r.toReal < 3 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  linarith

/-! ### Assembly of the adjoint resolvent -/

theorem adjointResolventSchwartz_of (h1 : AdjResolventSolution) (h2 : SliceContOfDecay) :
    AdjointResolventSchwartz := by
  intro r _ hr1 hr3 P _ ν hν μ hμ Φ₀ hΦ₀
  have hrt : r ≠ ⊤ := ne_top_of_lt hr3
  obtain ⟨Ψ, hsm, hper, heq, C, hC⟩ :=
    h1 P ν hν μ (re_add_one_pos hr1 hrt hμ) Φ₀ hΦ₀
  have hs := decay_exponent hr1 hrt hμ
  have hq : conjExp r ≠ ⊤ := conjExp_ne_top hr1
  have hS := fun G (hG : Continuous G) (hb : ∀ (τ : ℝ) (y : Space),
      ‖G (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 * (μ.re + 1)))) =>
    h2 (conjExp r) hq (2 * (μ.re + 1)) C hs G hG hb
  have hΨ : SliceCont (conjExp r) Ψ := hS Ψ hsm.continuous fun τ y => (hC τ y).1
  have hdy : ∀ j, SliceCont (conjExp r) (dy j Ψ) := fun j =>
    hS _ (contDiff_dy hsm j).continuous fun τ y => (hC τ y).2.1 j
  have hlap : SliceCont (conjExp r) (lapT Ψ) :=
    hS _ (continuous_finsetSum _ fun j _ => (contDiff_dy (contDiff_dy hsm j) j).continuous)
      fun τ y => (hC τ y).2.2
  have hdrift : driftT Ψ = Φ₀ + (-μ + (1 / 2 : ℂ)) • Ψ + (ν : ℂ) • lapT Ψ := by
    funext p
    have := heq p
    simp only [L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at this
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [← this]
    have h1' : ((ν : ℂ)) • lapT Ψ p = ν • lapT Ψ p := Complex.coe_smul _ _
    have h2' : ((1 / 2 : ℂ)) • Ψ p = (1 / 2 : ℝ) • Ψ p := by
      rw [← Complex.coe_smul]; norm_num
    rw [h1', add_smul, neg_smul, h2']
    abel
  refine ⟨Ψ, ⟨hsm, hper, hΨ, hdy, hlap, ?_⟩, heq⟩
  rw [hdrift]
  exact ((hΦ₀.sliceCont (conjExp r)).add (hΨ.const_smul _)).add (hlap.const_smul _)

/-! ### Extension of the homogeneous equation to Schwartz-type tests -/

theorem body_eq (μ : ℂ) (ν : ℝ) (Ψ : ℝ × Space → CVec3) :
    μ • Ψ + L0T ν Ψ = (μ - 1 / 2) • Ψ + driftT Ψ + (-(ν : ℂ)) • lapT Ψ := by
  funext p
  simp only [L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have h1' : ((ν : ℂ)) • lapT Ψ p = ν • lapT Ψ p := Complex.coe_smul _ _
  have h2' : ((1 / 2 : ℂ)) • Ψ p = (1 / 2 : ℝ) • Ψ p := by
    rw [← Complex.coe_smul]; norm_num
  rw [neg_smul, h1', sub_smul, h2']
  abel

section Extend

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {Ψ : ℝ × Space → CVec3}

theorem testElem_body (μ : ℂ) (ν : ℝ) (hΨ : IsPhaseSchwartz P q Ψ) :
    testElem P q (μ • Ψ + L0T ν Ψ) =
      (μ - 1 / 2) • testElem P q Ψ + testElem P q (driftT Ψ) +
        (-(ν : ℂ)) • testElem P q (lapT Ψ) := by
  rw [body_eq]
  have hA := hΨ.sliceTest.const_smul (μ - 1 / 2)
  have hB := hΨ.sliceTest_driftT
  have hC := hΨ.sliceTest_lapT.const_smul (-(ν : ℂ))
  rw [testElem_add (hA.add hB) hC, testElem_add hA hB, testElem_const_smul hΨ.sliceTest,
    testElem_const_smul hΨ.sliceTest_lapT]

/-- **Extension of `⟨(μ + L₀ᵗ)Φ, w⟩ = ⟨Φ, g⟩` from phase tests to Schwartz-type tests**
(radial cutoff `χ_N Ψ`; lines 1414-1417). -/
theorem hasPhaseOp_body_extend (hq : 1 < q) (μ : ℂ) (ν : ℝ) {w g : Yq P q}
    (h : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w g)
    (hΨ : IsPhaseSchwartz P (conjExp q) Ψ) :
    phasePair P q (μ • Ψ + L0T ν Ψ) w = phasePair P q Ψ g := by
  refine h.extend_of_tendsto (Lt := fun Φ => μ • Φ + L0T ν Φ) hΨ.isPhaseTest_cut
    (tendsto_cut (conjExp_ne_top hq) hΨ) ?_
  have hn : ∀ n, testElem P (conjExp q) (μ • mulT (cutχ n) Ψ + L0T ν (mulT (cutχ n) Ψ)) =
      (μ - 1 / 2) • testElem P (conjExp q) (mulT (cutχ n) Ψ) +
        testElem P (conjExp q) (driftT (mulT (cutχ n) Ψ)) +
        (-(ν : ℂ)) • testElem P (conjExp q) (lapT (mulT (cutχ n) Ψ)) := fun n =>
    testElem_body μ ν ((hΨ.isPhaseTest_cut n).isPhaseSchwartz (conjExp q))
  have hlim := testElem_body (P := P) (q := conjExp q) μ ν hΨ
  simp only [hn]
  show Tendsto _ atTop (𝓝 (testElem P (conjExp q) (μ • Ψ + L0T ν Ψ)))
  rw [hlim]
  exact (((tendsto_cut (conjExp_ne_top hq) hΨ).const_smul _).add
    (tendsto_cut_driftT (conjExp_ne_top hq) hΨ)).add
    ((tendsto_cut_lapT (conjExp_ne_top hq) hΨ).const_smul _)

end Extend

/-! ### The conditional theorem -/

/-- **`PartII-a:F05`, conditional on the adjoint resolvent**: a distributional solution of the
homogeneous body equation `(μ + L₀)w = 0` in `Y_r`, `1 < r < 3`, `Re μ + γ_r > 0`, vanishes. -/
theorem bodyOp_uniqueness_of (hA : AdjointResolventSchwartz)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (nu : ℝ)
    (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r) (w : Yq P r)
    (hw : HasPhaseOp (fun Phi => mu • Phi + L0T nu Phi) w 0) : w = 0 := by
  refine eq_zero_of_forall_phasePair fun Φ₀ hΦ₀ => ?_
  obtain ⟨Ψ, hΨ, heq⟩ := hA r h1 h3 P nu hnu mu hmu Φ₀ hΦ₀
  have hfun : mu • Ψ + L0T nu Ψ = Φ₀ := funext heq
  have := hasPhaseOp_body_extend h1 mu nu hw hΨ
  rw [hfun] at this
  simpa using this

end UnforcedLeray.Short.PartIIa
