import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Ftc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Scale

/-!
# `PartIII-a:T21/2/2/3/5/3/1` (`E1PhysDiff`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864
(`x = √a y`, `d = c/√a`), 3036-3037, 3044 (the periodic weight), 3060-3073 (`E_1` is used as a
classical, differentiable quantity of the reverse time).

On the fixed physical cell `C_c`, `physE1 r = a(r)⁻² Σ_k I_k(r)`,
`I_k(r) = ∫_{C_c} physW(r, x) |∂_kφ(r, x)|² dx`, `physW(r, x) = p_{c/√a}⁻¹(x/√a)`, `a = a(r)`.

* `e1PhysDiff_of`: `E1PhysDiff` from `E1PhysTerm` (the derivative of each `I_k`) by the product
  rule with `(a⁻²)'` (`a(r) > 0` at `r = revAge ν s ζ ∈ (t, s)`).
* `e1PhysTerm_of`: `E1PhysTerm` from the weighted product rule `weightedProductRule`
  (`Sub/T21_2_2/E0/Reynolds/R1/ProductRule.lean`, compiled, used for `E_0` with `w = []`) applied to
  `f r = ∂_kφ(r)`, `f' = ∂_k∂_rφ(r)`, and three leaves:
  - `PhysWBound` (calculus): local uniform bounds of `physW` and its `r`-derivative by `physW(r)`;
  - `PhysE1L2Diff` (from `adjXDiff`, `w = [k]`, and `physW ≤ K⟨x⟩^{-2m}` on the cell): the
    difference quotient of `∂_kφ` converges to `∂_k∂_rφ` in `L²(physW(r) dx)`;
  - `WPRSplit` (abstract measure theory): `∫ ∂_r(w|f|²) = ∫ ∂_r w |f|² + 2∫ w Re(conj f f')`.
  The pointwise facts (`∂_r∂_kφ = ∂_k∂_rφ` by joint smoothness, measurability) are proved here
  with the lemmas of `Sub/T21_2_2/AdjXDiff/Ftc.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- The fixed-cell weight `physW(r, x) = p_{c/√a}⁻¹(x/√a)`, `a = a(r)`, `p_d⁻¹ = periodicWeight (-m) d`
(SP 3036-3037, 3044): the weight of `physE1` (`Sub/PartIIIa_T21_2_2_3_5.lean`). -/
def physW (ν c m r : ℝ) (x : ℝ × ℝ) : ℝ :=
  periodicWeight (-m) (cellLen c (clockA ν r))
    (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r))

/-- **The derivative of one gradient term on the fixed cell** (SP 3060-3073): at the age
`r₀ = revAge ν s ζ`, `r ↦ ∫_{C_c} physW(r)|∂_kφ(r)|²` has derivative
`∫ ∂_r physW(r₀)|∂_kφ(r₀)|² + 2 ∫ physW(r₀) Re(conj ∂_kφ(r₀) · ∂_k∂_rφ(r₀))`. -/
def E1PhysTerm (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ → ∀ k : Fin 2,
      HasDerivAt (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          physW ν (ν ^ (-2 : ℝ)) m r x * ‖pdCx k (φ r) x‖ ^ 2)
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r' x) (revAge ν s ζ) *
              ‖pdCx k (φ (revAge ν s ζ)) x‖ ^ 2) +
          2 * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ) x *
              ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ)) x) *
                pdCx k (adjDt t s φ (revAge ν s ζ)) x).re)
        (revAge ν s ζ)

/-- The age `revAge ν s ζ` of the flow window lies in `(t, s)` and has `a > 0`. -/
theorem adjFlowAt_age {m ν : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t s : ℝ}
    {φ : ℝ → ℝ × ℝ → ℂ} {ζ : ℝ} (hζ : AdjFlowAt m ν tr t s φ ζ) :
    revAge ν s ζ ∈ Ioo t s ∧ 0 < clockA ν (revAge ν s ζ) := by
  obtain ⟨hν, ht0, hts, _, hz⟩ := hζ
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hz
  refine ⟨hr, ?_⟩
  have h0 : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν.le (by linarith [hr.1])
  unfold clockA
  linarith

/-- **`E1PhysDiff` from `E1PhysTerm`** (product rule with `(a⁻²)'`, SP 2860-2864, 3060-3062). -/
theorem e1PhysDiff_of (m : ℝ) (h : E1PhysTerm m) : E1PhysDiff m := by
  intro ν tr t s φ ζ hζ
  obtain ⟨_, ha⟩ := adjFlowAt_age hζ
  have hA : DifferentiableAt ℝ (fun r => clockA ν r) (revAge ν s ζ) := by
    unfold clockA
    fun_prop
  have hdiff : DifferentiableAt ℝ (fun r => (clockA ν r)⁻¹ ^ 2) (revAge ν s ζ) :=
    (hA.inv ha.ne').pow 2
  have hg := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => h ν tr t s φ ζ hζ k)
  have hfg := hdiff.hasDerivAt.mul hg
  exact hfg

/-! ## The leaves of `E1PhysTerm` -/

/-- **Leaf (calculus, as `WtPhysBound` for `E_0`)**: local uniform bounds of the fixed-cell weight
and of its `r`-derivative by the weight at `r`, for `c > 0`, `a(r) > 0`
(`physW(r', x) = (1 + P(x)/a(r'))^{-m}`, `P = x₂² + (c/π)² sin²(π x₁/c)`). -/
def PhysWBound (m : ℝ) : Prop :=
  ∀ ν c r : ℝ, 0 < c → 0 < clockA ν r →
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ × ℝ, ∀ r' ∈ ball r δ,
      DifferentiableAt ℝ (fun q => physW ν c m q x) r' ∧ 0 ≤ physW ν c m r' x ∧
      physW ν c m r' x ≤ C * physW ν c m r x ∧
      |deriv (fun q => physW ν c m q x) r'| ≤ C * physW ν c m r x

/-- **Leaf (from `AdjXDiff`, `w = [k]`)**: for `r ∈ (t, s)` the difference quotient of `∂_kφ`
converges to `∂_k∂_rφ(r)` in `L²(physW(r) dx)` on the cell, and `∫ physW(r)|∂_kφ(r)|²`,
`∫ physW(r)|∂_k∂_rφ(r)|²` are finite (`IsAdjointFlow.memH1`, `higherCont`; `physW(r) ≤ K⟨x⟩^{-2m}`
on the cell by `wtRatio_le`, `wtF0_eq_periodicWeight`). -/
def PhysE1L2Diff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ∀ r ∈ Ioo t s, ∀ k : Fin 2,
        Tendsto (fun r' => ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (physW ν (ν ^ (-2 : ℝ)) m r x) *
              ‖(r' - r)⁻¹ • (pdCx k (φ r') x - pdCx k (φ r) x) -
                pdCx k (adjDt t s φ r) x‖ₑ ^ 2)
          (𝓝[≠] r) (𝓝 0) ∧
        (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (physW ν (ν ^ (-2 : ℝ)) m r x) * ‖pdCx k (φ r) x‖ₑ ^ 2) < ⊤ ∧
        (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (physW ν (ν ^ (-2 : ℝ)) m r x) *
              ‖pdCx k (adjDt t s φ r) x‖ₑ ^ 2) < ⊤

/-- **Leaf (abstract measure theory)**: under the hypotheses `E0.WPRHyp` of the weighted product
rule, the integrated pointwise derivative splits as
`∫ ∂_r(w‖f‖²) = ∫ ∂_r w ‖f‖² + 2 ∫ w Re(conj f · f')` (pointwise product rule with
`HasDerivAt.norm_sq`, `⟪z, v⟫_ℝ = Re(conj z · v)`; integrability as in `wprInteg`). -/
def WPRSplit : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (w : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (f' : ℝ × ℝ → ℂ) (r : ℝ),
    E0.WPRHyp μ w f f' r →
    ∫ x, deriv (fun q => w q x * ‖f q x‖ ^ 2) r ∂μ =
      (∫ x, deriv (fun q => w q x) r * ‖f r x‖ ^ 2 ∂μ) +
        2 * ∫ x, w r x * ((starRingEnd ℂ) (f r x) * f' x).re ∂μ

/-- `∂_r ∂_kφ(r, x) = ∂_k ∂_rφ(r, x)` at an interior age (joint smoothness, SP 3060-3073). -/
theorem hasDerivAt_pdCx_age {ν m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {t s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hF : IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ) {r : ℝ} (hr : r ∈ Ioo t s) (k : Fin 2)
    (x : ℝ × ℝ) :
    HasDerivAt (fun q => pdCx k (φ q) x) (pdCx k (adjDt t s φ r) x) r := by
  have hj : ContDiffOn ℝ ∞ (jF φ) (Ioo t s ×ˢ univ) :=
    hF.jointSmooth.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have h1 := hasDerivAt_fderiv_jF_slice hj hr x ((0 : ℝ), B0579.dir k)
  have hsy := symm_jF hj hr x ((1 : ℝ), (0 : ℝ × ℝ)) ((0 : ℝ), B0579.dir k)
  rw [pdCx_adjDt_eq hj hr k x]
  rw [hsy] at h1
  refine h1.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2) (fun σ hσ => pdCx_slice_eq hj hσ k x)

/-- **`E1PhysTerm` from the leaves** and the compiled weighted product rule. -/
theorem e1PhysTerm_of (m : ℝ) (h1 : PhysWBound m) (h2 : PhysE1L2Diff m) (h3 : WPRSplit) :
    E1PhysTerm m := by
  intro ν tr t s φ ζ hζ k
  obtain ⟨hr, ha⟩ := adjFlowAt_age hζ
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, _⟩ := hζ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hwm : ∀ r', Measurable (physW ν (ν ^ (-2 : ℝ)) m r') := by
    intro r'
    unfold physW periodicWeight
    fun_prop
  have hm : ∀ᶠ r' in 𝓝 (revAge ν s ζ), AEStronglyMeasurable (pdCx k (φ r'))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) := by
    filter_upwards [Ico_mem_nhds hr.1 hr.2] with r' hr'
    exact (contDiff_pdCx k (hF.smooth r' hr')).continuous.aestronglyMeasurable
  have hd : ∀ x : ℝ × ℝ, HasDerivAt (fun q => pdCx k (φ q) x)
      (pdCx k (adjDt t s φ (revAge ν s ζ)) x) (revAge ν s ζ) :=
    fun x => hasDerivAt_pdCx_age hF hr k x
  obtain ⟨hT, hf0, hf1⟩ := h2 ν hν tr t s ht0 hts _ φ hF (revAge ν s ζ) hr k
  have hC := h1 ν (ν ^ (-2 : ℝ)) (revAge ν s ζ) hc ha
  have hH : E0.WPRHyp (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) (physW ν (ν ^ (-2 : ℝ)) m)
      (fun q => pdCx k (φ q)) (pdCx k (adjDt t s φ (revAge ν s ζ))) (revAge ν s ζ) :=
    ⟨hwm, hm, hC, hd, hT, hf0, hf1⟩
  have key := weightedProductRule _ (physW ν (ν ^ (-2 : ℝ)) m) (fun q => pdCx k (φ q))
    (pdCx k (adjDt t s φ (revAge ν s ζ))) (revAge ν s ζ) hwm hm hC hd hT hf0 hf1
  rw [h3 _ _ _ _ _ hH] at key
  exact key

/-- **`E1PhysDiff` from the three leaves.** -/
theorem e1PhysDiff_of_leaves (m : ℝ) (h1 : PhysWBound m) (h2 : PhysE1L2Diff m)
    (h3 : WPRSplit) : E1PhysDiff m :=
  e1PhysDiff_of m (e1PhysTerm_of m h1 h2 h3)

end UnforcedLeray.Short.IIIa.AdjE1
