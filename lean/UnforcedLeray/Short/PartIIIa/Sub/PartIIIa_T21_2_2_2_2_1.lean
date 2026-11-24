import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.Defs

/-!
# `PartIII-a:T21/2/2/2/2/1`: differentiation of the fixed-cell energy, decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.

`physE0 r = ∫_{C_c} wt(r, x) ‖φ(r, x)‖²`, `wt(r, x) = a(r)⁻³ p_d⁻¹(x/√a)`. The derivative is the
weighted product rule. Leaves:

* `WtPhysBound` (pure calculus on `periodicWeight`): `wt(·, x)` is differentiable near `r` with
  `wt(r', x) ≤ C wt(r, x)` and `|∂_r wt(r', x)| ≤ C wt(r, x)` for `|r' - r| < δ`;
* `PhysE0Pointwise` (from `IsAdjointFlow.smooth`/`jointSmooth`): measurability of `φ(r')`, and
  pointwise `∂_r φ(r, x) = adjDt t s φ r x`;
* `PhysE0L2Diff` (from `AdjXDiff` and the equivalence `AdjWeightEquiv` of `wt(r)` with
  `periodicWeight (-m) c`, SP 3044-3047): the difference quotient of `φ` converges to `∂_rφ(r)`
  in `L²(wt(r) dx)` (written with `lintegral`, so finiteness is part of the statement);
* `WeightedProductRule` (abstract measure theory): the product rule for `∫ w(r,x) ‖f(r,x)‖²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The weight `wt(r, x) = a(r)⁻³ p_d⁻¹(x/√a)`, `d = c/√a` (SP 3036-3037, 3060). -/
def wtPhys (ν c m : ℝ) (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  ((clockA ν r ^ 3)⁻¹) *
    periodicWeight (-m) (cellLen c (clockA ν r)) (x.1 / Real.sqrt (clockA ν r),
      x.2 / Real.sqrt (clockA ν r))

/-- **Leaf (calculus)**: local uniform bounds of the weight and its `r`-derivative by the weight
at `r`, for `c > 0`, `a(r) > 0`. -/
def WtPhysBound (m : ℝ) : Prop :=
  ∀ ν c r : ℝ, 0 < c → 0 < clockA ν r →
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ × ℝ, ∀ r' ∈ ball r δ,
      DifferentiableAt ℝ (fun q => wtPhys ν c m q x) r' ∧ 0 ≤ wtPhys ν c m r' x ∧
      wtPhys ν c m r' x ≤ C * wtPhys ν c m r x ∧
      |deriv (fun q => wtPhys ν c m q x) r'| ≤ C * wtPhys ν c m r x

/-- **Leaf (pointwise facts of the flow)**: for `r ∈ (t, s)`, `φ(·, x)` has derivative
`adjDt t s φ r x` at `r`, each `φ(r')` (`r'` near `r`) is a.e.-strongly measurable on the cell,
and `wtPhys ν c m r'` is measurable for every `r'`. -/
def PhysE0Pointwise (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → ∀ r ∈ Ioo t s,
        (∀ x : ℝ × ℝ, HasDerivAt (fun q => φ q x) (adjDt t s φ r x) r) ∧
        (∀ᶠ r' in 𝓝 r, AEStronglyMeasurable (φ r') (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
        (∀ r', Measurable (wtPhys ν (ν ^ (-2 : ℝ)) m r'))

/-- **Leaf (from `AdjXDiff`)**: `L²(wt(r) dx)`-differentiability of `φ` at `r ∈ (t, s)`, with the
finiteness of `∫ wt(r)|φ(r)|²` and `∫ wt(r)|∂_rφ(r)|²`. -/
def PhysE0L2Diff (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ),
    0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjXDiff m → ∀ r ∈ Ioo t s,
        Tendsto (fun r' => ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (wtPhys ν (ν ^ (-2 : ℝ)) m r x) *
              ‖(r' - r)⁻¹ • (φ r' x - φ r x) - adjDt t s φ r x‖ₑ ^ 2)
          (𝓝[≠] r) (𝓝 0) ∧
        (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (wtPhys ν (ν ^ (-2 : ℝ)) m r x) * ‖φ r x‖ₑ ^ 2) < ⊤ ∧
        (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
            ENNReal.ofReal (wtPhys ν (ν ^ (-2 : ℝ)) m r x) * ‖adjDt t s φ r x‖ₑ ^ 2) < ⊤

/-- **Leaf (abstract measure theory)**: the product rule for `r ↦ ∫ w(r, x) ‖f(r, x)‖² dμ`, for a
family of weights controlled by the weight at `r` and a family `f` differentiable in
`L²(w(r) dμ)` and pointwise. -/
def WeightedProductRule : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (w : ℝ → ℝ × ℝ → ℝ) (f : ℝ → ℝ × ℝ → ℂ) (f' : ℝ × ℝ → ℂ) (r : ℝ),
    (∀ r', Measurable (w r')) → (∀ᶠ r' in 𝓝 r, AEStronglyMeasurable (f r') μ) →
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : ℝ × ℝ, ∀ r' ∈ ball r δ,
      DifferentiableAt ℝ (fun q => w q x) r' ∧ 0 ≤ w r' x ∧ w r' x ≤ C * w r x ∧
      |deriv (fun q => w q x) r'| ≤ C * w r x) →
    (∀ x : ℝ × ℝ, HasDerivAt (fun q => f q x) (f' x) r) →
    Tendsto (fun r' => ∫⁻ x, ENNReal.ofReal (w r x) *
        ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ) (𝓝[≠] r) (𝓝 0) →
    (∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ) < ⊤ →
    (∫⁻ x, ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2 ∂μ) < ⊤ →
    HasDerivAt (fun r' => ∫ x, w r' x * ‖f r' x‖ ^ 2 ∂μ)
      (∫ x, deriv (fun q => w q x * ‖f q x‖ ^ 2) r ∂μ) r

/-- `ReyPhysDeriv` from the four leaves. -/
theorem reyPhysDeriv_of (m : ℝ) (h1 : WtPhysBound m) (h2 : PhysE0Pointwise m)
    (h3 : PhysE0L2Diff m) (h4 : WeightedProductRule) (hX : AdjXDiff m) : ReyPhysDeriv m := by
  intro ν hν tr t s ht hts g φ hφ r hr
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν r := by
    have : 0 < r := lt_of_le_of_lt ht hr.1
    unfold clockA; nlinarith
  obtain ⟨hd, hm, hwm⟩ := h2 ν hν tr t s ht hts g φ hφ r hr
  obtain ⟨hl, hf0, hf1⟩ := h3 ν hν tr t s ht hts g φ hφ hX r hr
  have key := h4 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) (wtPhys ν (ν ^ (-2 : ℝ)) m) φ
    (adjDt t s φ r) r hwm hm (h1 ν _ r hc ha) hd hl hf0 hf1
  exact key

end UnforcedLeray.Short.IIIa.E0
