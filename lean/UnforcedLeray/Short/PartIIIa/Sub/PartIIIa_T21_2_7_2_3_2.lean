import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# `PartIII-a:T21/2/7/2/3/2`: the bound of the cut rate, decomposed

Source: `the November 2 reference manuscript` (SP) lines 3062-3071, 3044-3049.

`CutRateBound` is split into: a pointwise Young bound on the cell (`CutRatePointwise`), the
integrability of every piece of the integrand (`CutRateIntegrable`), and the weighted `L²` bound of
`χ` (`CutWeightX2`). `cutRateBound_of` integrates the pointwise bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- The pointwise integrand of `cutRate` (the sum of its two integrands). -/
def cutRateIntegrand (c m R : ℝ) (Φ F : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℝ :=
  -(2 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re))) -
    2 * ∑ k : Fin 2, B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
        ((starRingEnd ℂ) (pdCx k Φ x) * F x).re

/-- **Leaf 1: the pointwise Young bound** (SP 3062-3071, 3044-3049). With `ζ = χ_R ∈ [0,1]`,
`w = ⟨x⟩^{-2m}`, `D = |ΔΦ|`, `G_k = |∂_kΦ|`, `X = |χ|`, `T = |V·∇Φ| ≤ |C_V|(G_0 + G_1)`:
`|∂_k(ζ²w)| ≤ K₂ ζ w` (from `ladCutProps`: `|∂_kζ| ≤ K₁/R`, `R ≥ 1`, and `adjWeightGrad`:
`|∂_k w| ≤ 2|m| w`, `K₂ = 2K₁ + 2|m|`, `ζ² ≤ ζ`); `ζ ≠ 0 → x.2² < 2R² → χ_{2R}(x) = 1`;
`-2ζ²w Re(conj(ΔΦ)F) = 2νζ²wD² - 2ζ²w Re(conj(ΔΦ)(χ - V·∇Φ))`; Young
`|2 Re(conj(ΔΦ)(χ - V·∇Φ))| ≤ (ν/2)D² + (4/ν)(X² + T²)`;
`|2 ∂_k(ζ²w) Re(conj(∂_kΦ)F)| ≤ 2K₂ζw G_k(X + νD + T) ≤ (ν/8)ζ²wD² + K₃ w (G_k² + X² + T²)`
(the `ζ`-free terms carry the indicator of `{ζ ≠ 0}`, i.e. `χ_{2R}²`). Result on the cell:
`νζ²wD² - K'(wX² + χ_{2R}² w (G_0² + G_1²)) ≤ A(x) ≤ 3νζ²wD² + K'(…)`, `A` = `cutRateIntegrand`. -/
def CutRatePointwise : Prop :=
  ∀ (m ν CV : ℝ), 0 < ν → ∃ K' : ℝ, 0 ≤ K' ∧
    ∀ (c R : ℝ) (Φ χ F : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ), 0 < c → 1 ≤ R →
      ContDiff ℝ ∞ Φ →
      (∀ x ∈ B0579.cell c, ∀ j : Fin 2, |V x j| ≤ CV) →
      (∀ x : ℝ × ℝ, F x = χ x - (ν : ℂ) * ladLapCx Φ x -
        ((V x 0 : ℂ) * pdCx 0 Φ x + (V x 1 : ℂ) * pdCx 1 Φ x)) →
      ∀ x ∈ B0579.cell c,
        ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ladLapCx Φ x‖ ^ 2)) -
            K' * (B0579.jb x ^ (-m) * ‖χ x‖ ^ 2 +
              ∑ k : Fin 2, ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)) ≤
          cutRateIntegrand c m R Φ F x ∧
        cutRateIntegrand c m R Φ F x ≤
          3 * ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ladLapCx Φ x‖ ^ 2)) +
            K' * (B0579.jb x ^ (-m) * ‖χ x‖ ^ 2 +
              ∑ k : Fin 2, ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))

/-- **Leaf 2: integrability on the cell** of the pieces of the integrand. All of them are continuous
and vanish for `x.2² ≥ 2R²` (resp. `8R²` for `χ_{2R}`) (`ladCutProps`), so they are integrable on the
cell (`Ico × univ` meets the band in a bounded set); the piece `w‖χ‖²` is integrable by
`MemLp χ 2` (`integral_cellMeasure_eq`, `MemLp.integrable_norm_pow`). -/
def CutRateIntegrable : Prop :=
  ∀ (m : ℝ) (c R : ℝ) (Φ χ F : ℝ × ℝ → ℂ), 0 < c → 0 < R →
    ContDiff ℝ ∞ Φ → Continuous χ → Continuous F →
    MemLp χ 2 (B0579.cellMeasure c (-m)) →
    IntegrableOn (fun x => ladCut R x ^ 2 *
      (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re)) (B0579.cell c) ∧
    (∀ k : Fin 2, IntegrableOn (fun x =>
      B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
        ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) (B0579.cell c)) ∧
    IntegrableOn (fun x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ladLapCx Φ x‖ ^ 2))
      (B0579.cell c) ∧
    (∀ k : Fin 2, IntegrableOn (fun x => ladCut (2 * R) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)) (B0579.cell c)) ∧
    IntegrableOn (fun x => B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) (B0579.cell c)

/-- **Leaf 3: the weighted `L²` norm of `χ`.** `∫_cell ⟨x⟩^{-2m}|χ|² = ‖χ‖²_{X_{-m,c}} ≤ M²`
(`integral_cellMeasure_eq`, `sq_toReal_eLpNorm` from `Sub/T21_2_2_1_F1/WtCore`). -/
def CutWeightX2 : Prop :=
  ∀ (c m M : ℝ) (χ : ℝ × ℝ → ℂ), MemLp χ 2 (B0579.cellMeasure c (-m)) →
    eLpNorm χ 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M →
    ∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2 ≤ M ^ 2

theorem measurableSet_cell' (c : ℝ) : MeasurableSet (B0579.cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- `CutRateBound` from its three leaves. -/
theorem cutRateBound_of (hP : CutRatePointwise) (hI : CutRateIntegrable) (hX : CutWeightX2) :
    CutRateBound := by
  intro m ν CV M hν
  obtain ⟨K', hK', hP'⟩ := hP m ν CV hν
  refine ⟨K' * (1 + M ^ 2), by positivity, ?_⟩
  intro c R Φ χ F V hc hR hΦ hχ hF hV hFe hmem hM
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI m c R Φ χ F hc (by linarith) hΦ hχ hF hmem
  have hX2 := hX c m M χ hmem hM
  have hmeas := measurableSet_cell' c
  have i2s : IntegrableOn (fun x => ∑ k : Fin 2, B0579.pd k
      (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
        ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) (B0579.cell c) :=
    integrable_finset_sum _ (fun k _ => i2 k)
  have a1 : IntegrableOn (fun x => -(2 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re)))) (B0579.cell c) := (i1.const_mul 2).neg
  have a2 : IntegrableOn (fun x => 2 * ∑ k : Fin 2, B0579.pd k
      (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
        ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) (B0579.cell c) := i2s.const_mul 2
  have hAi : IntegrableOn (cutRateIntegrand c m R Φ F) (B0579.cell c) := a1.sub a2
  have hrate : cutRate c m R Φ F = ∫ x in B0579.cell c, cutRateIntegrand c m R Φ F x := by
    unfold cutRate cutRateIntegrand
    rw [integral_sub a1 a2, integral_neg, integral_const_mul, integral_const_mul,
      integral_finset_sum _ (fun k _ => i2 k)]
  have i4s : IntegrableOn (fun x => ∑ k : Fin 2, ladCut (2 * R) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)) (B0579.cell c) :=
    integrable_finset_sum _ (fun k _ => i4 k)
  have hE : cutE1 c m (2 * R) Φ = ∫ x in B0579.cell c, ∑ k : Fin 2, ladCut (2 * R) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2) := by
    unfold cutE1
    rw [integral_finset_sum _ (fun k _ => i4 k)]
  have hE0 : 0 ≤ cutE1 c m (2 * R) Φ := by
    unfold cutE1
    refine Finset.sum_nonneg fun k _ => setIntegral_nonneg hmeas fun x _ => ?_
    have := B0579.jb_pos x
    positivity
  have hS : IntegrableOn (fun x => (B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
      ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)) (B0579.cell c) := i5.add i4s
  have l1 : IntegrableOn (fun x => ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2))) (B0579.cell c) := i3.const_mul ν
  have l3 : IntegrableOn (fun x => 3 * ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2))) (B0579.cell c) := i3.const_mul (3 * ν)
  have l2 : IntegrableOn (fun x => K' * ((B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
      ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))) (B0579.cell c) :=
    hS.const_mul K'
  have hint1 : ∫ x in B0579.cell c, (ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2)) - K' * ((B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
        ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))) =
      ν * cutLap c m R Φ - K' * ((∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) +
        cutE1 c m (2 * R) Φ) := by
    rw [integral_sub l1 l2, integral_const_mul, integral_const_mul, integral_add i5 i4s, ← hE]
    rfl
  have hint2 : ∫ x in B0579.cell c, (3 * ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2)) + K' * ((B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
        ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))) =
      3 * ν * cutLap c m R Φ + K' * ((∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) +
        cutE1 c m (2 * R) Φ) := by
    rw [integral_add l3 l2, integral_const_mul, integral_const_mul, integral_add i5 i4s, ← hE]
    rfl
  have hpt := fun x (hx : x ∈ B0579.cell c) =>
    hP' c R Φ χ F V hc hR hΦ hV hFe x hx
  have hlo : ∫ x in B0579.cell c, (ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2)) - K' * ((B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
        ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))) ≤
      ∫ x in B0579.cell c, cutRateIntegrand c m R Φ F x :=
    setIntegral_mono_on (l1.sub l2) hAi hmeas (fun x hx => (hpt x hx).1)
  have hhi : ∫ x in B0579.cell c, cutRateIntegrand c m R Φ F x ≤
      ∫ x in B0579.cell c, (3 * ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ‖ladLapCx Φ x‖ ^ 2)) + K' * ((B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) + ∑ k : Fin 2,
        ladCut (2 * R) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2))) :=
    setIntegral_mono_on hAi (l3.add l2) hmeas (fun x hx => (hpt x hx).2)
  rw [hint1, ← hrate] at hlo
  rw [hint2, ← hrate] at hhi
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hcmp : K' * ((∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) +
      cutE1 c m (2 * R) Φ) ≤ K' * (1 + M ^ 2) * (1 + cutE1 c m (2 * R) Φ) := by
    have : (∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2) +
        cutE1 c m (2 * R) Φ ≤ (1 + M ^ 2) * (1 + cutE1 c m (2 * R) Φ) := by
      nlinarith
    calc _ ≤ K' * ((1 + M ^ 2) * (1 + cutE1 c m (2 * R) Φ)) := mul_le_mul_of_nonneg_left this hK'
      _ = _ := by ring
  constructor <;> linarith

end UnforcedLeray.Short.IIIa
