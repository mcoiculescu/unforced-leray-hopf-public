import UnforcedLeray.Short.PartIIIa.Clock.Stages
import UnforcedLeray.Units.B0285.Circulation

/-!
# Part III-a full clock: zero circulation is preserved (SP 3100-3101), leaves

Source of record: `the November 2 reference manuscript` (SP), lines 3100-3101:
"Zero mass is preserved by the conservative physical equation and then by continuous extension
in the actual weighted dual source norm."

How the statement `ZeroCirculationPreserved` (`Clock/Stages.lean`) is reached. The velocity of a
weak linearised flow is, at every age `s ≥ t`, the zero-circulation Biot-Savart field
`u(s) = K_c ω(s)` (`IsLinearisedFlow.biotSavart`, `IsBiotSavart` in `Defs.lean`; SP 2081-2085, and
SP 3497-3504: the zero-circulation reconstruction of `K_c ω` in `L²`, where the horizontal mean of
`u_q` is the zero-endpoint primitive of the mean vorticity and zero circulation removes both
endpoint terms). Conversely an `L²(cell)` velocity with `curl u = ω` forces `∫_cell ω = 0`:
testing `curl u = ω` with the `q`-independent cutoff `φ_n(q, η) = χ(η/(n+1))` (`B0285.cutT n`)
gives `∫_cell ω φ_n = ∫_cell u_q ∂_η φ_n`, which is `O((n+1)^{-1/2})` by Cauchy-Schwarz
(`∂_η φ_n` is `O(1/(n+1))` on a band of height `4(n+1)`), while `∫_cell ω φ_n → ∫_cell ω` by
dominated convergence, `ω(s) ∈ X_{m,c}` with `m > 1` being integrable on the cell
(SP 2823-2827). Hence zero mass at age `s` follows from the flow's own Biot-Savart velocity at
age `s`: no regularity of the train and no sign condition on the initial age `t` is used.

Leaves (each a `Prop`, proved in `Clock/Sub/ZeroCirc/*.lean`):
* `ZCCellIntegrable`: `X_{m,c} ⊂ L¹(cell)` for `m > 1` (SP 2823-2827);
* `ZCCutoffTest`: `B0285.cutT n` is a `B0579` cylinder test, with its two partial derivatives;
* `ZCChiDeriv`: the profile `B0285.chi0` has bounded derivative, vanishing on `|y| > 2`;
* `ZCBandL2`: the `L²(cell)` bound of a bounded continuous function supported in a band;
* `ZCCauchySchwarz`: `|∫ a g dμ| ≤ ‖a‖₂ ‖g‖₂`;
* `ZCCutoffLimit`: `∫_cell ω φ_n → ∫_cell ω` for `ω` integrable on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 2823-2827: `X_{m,c} = L²(C_c, ⟨x⟩^{2m}dx)`; used with `m > 1`). Every element
of `X_{m,c}` is integrable on the cell: Cauchy-Schwarz with the weight `(1+q²+η²)^{-m}`, which
is integrable on the cell for `m > 1`. -/
def ZCCellIntegrable : Prop :=
  ∀ c m : ℝ, 1 < m → ∀ g : ℝ × ℝ → ℂ, MemLp g 2 (B0579.cellMeasure c m) →
    IntegrableOn g (B0579.cell c)

/-- **Leaf 2** (the cutoff test of SP 3100-3101, as in B0285 `integral_eq_zero_of_isWeakCurl`).
`φ_n(q, η) = χ(η/(n+1))` (`B0285.cutT n`) is a cylinder test in the sense of `B0579`, with
`∂_q φ_n = 0` and `∂_η φ_n = χ'(η/(n+1))/(n+1)`. -/
def ZCCutoffTest : Prop :=
  ∀ (c : ℝ) (n : ℕ), B0579.IsCylTest c (B0285.cutT n) ∧
    (∀ x : ℝ × ℝ, B0579.pd 0 (B0285.cutT n) x = 0) ∧
    ∀ x : ℝ × ℝ, B0579.pd 1 (B0285.cutT n) x =
      deriv B0285.chi0 (((n : ℝ) + 1)⁻¹ * x.2) * ((n : ℝ) + 1)⁻¹

/-- **Leaf 3** (the cutoff profile of leaf 2). The bump `χ = B0285.chi0` (`1` on `[-1, 1]`,
`0` outside `(-2, 2)`) has bounded derivative, and its derivative vanishes on `|y| > 2`. -/
def ZCChiDeriv : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, |deriv B0285.chi0 y| ≤ M ∧ (2 < |y| → deriv B0285.chi0 y = 0)

/-- **Leaf 4** (the size of `∂_η φ_n` in `L²(cell)`, SP 3100-3101). A continuous `g` with
`|g| ≤ M` vanishing on `|η| > L` has `‖g‖_{L²(cell c)} ≤ M (c · 2L)^{1/2}` (the band
`[-c/2, c/2) × [-L, L]` has area `2cL`). -/
def ZCBandL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (g : ℝ × ℝ → ℝ) (M L : ℝ), 0 ≤ M → 0 ≤ L → Continuous g →
    (∀ x, |g x| ≤ M) → (∀ x : ℝ × ℝ, L < |x.2| → g x = 0) →
    eLpNorm g 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal (M * Real.sqrt (c * (2 * L)))

/-- **Leaf 5** (Cauchy-Schwarz, used for the pairing `∫_cell u_q ∂_η φ_n` of SP 3100-3101). For
`a ∈ L²(μ)` complex and `g ∈ L²(μ)` real, `‖∫ a g dμ‖ ≤ ‖a‖₂ ‖g‖₂`. -/
def ZCCauchySchwarz : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ → ℂ) (g : ℝ × ℝ → ℝ), MemLp a 2 μ → MemLp g 2 μ →
    ‖∫ x, a x * (g x : ℂ) ∂μ‖ ≤ (eLpNorm a 2 μ).toReal * (eLpNorm g 2 μ).toReal

/-- **Leaf 6** (dominated convergence for the cutoff, SP 3100-3101). For `ω` integrable on the
cell, `∫_cell ω φ_n → ∫_cell ω` (`|φ_n| ≤ 1`, `φ_n → 1` pointwise). -/
def ZCCutoffLimit : Prop :=
  ∀ (c : ℝ) (ω : ℝ × ℝ → ℂ), IntegrableOn ω (B0579.cell c) →
    Tendsto (fun n : ℕ => ∫ x in B0579.cell c, ω x * (B0285.cutT n x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, ω x))

/-- `M/x · (c · 2 · 2x)^{1/2} = M (4c/x)^{1/2}` for `x > 0`. -/
theorem zc_bound_eq (M c x : ℝ) (hx : 0 < x) :
    M / x * Real.sqrt (c * (2 * (2 * x))) = M * Real.sqrt (4 * c * (1 / x)) := by
  have e : c * (2 * (2 * x)) = x ^ 2 * (4 * c * (1 / x)) := by
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  field_simp

/-- **An `L²(cell)` Biot-Savart velocity forces zero circulation** (SP 3100-3101, 3497-3504),
from leaves 2-6: if `ω` is integrable on the cell and `curl u = ω`, `div u = 0` with
`u ∈ L²(cell)`, then `∫_cell ω = 0`. -/
theorem integral_cell_eq_zero_of_isBiotSavart_of (h2 : ZCCutoffTest) (h3 : ZCChiDeriv)
    (h4 : ZCBandL2) (h5 : ZCCauchySchwarz) (h6 : ZCCutoffLimit) {c : ℝ} (hc : 0 < c)
    {ω : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ} (hω : IntegrableOn ω (B0579.cell c))
    (hu : IsBiotSavart c ω u) : ∫ x in B0579.cell c, ω x = 0 := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c) with hμ
  obtain ⟨M, hM0, hM⟩ := h3
  set A : ℝ := (eLpNorm (fun x => u x 0) 2 μ).toReal with hA
  set B : ℕ → ℝ := fun n => M * Real.sqrt (4 * c * (1 / ((n : ℝ) + 1))) with hB
  have hbound : ∀ n : ℕ, ‖∫ x in B0579.cell c, ω x * (B0285.cutT n x : ℂ)‖ ≤ A * B n := by
    intro n
    obtain ⟨htest, hpd0, hpd1⟩ := h2 c n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hid : ∫ x in B0579.cell c, ω x * (B0285.cutT n x : ℂ) =
        ∫ x in B0579.cell c, u x 0 * (B0579.pd 1 (B0285.cutT n) x : ℂ) := by
      rw [hu.2.2 _ htest]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hpd0 x, Complex.ofReal_zero, mul_zero, sub_zero]
    have hgb : ∀ x : ℝ × ℝ, |B0579.pd 1 (B0285.cutT n) x| ≤ M / ((n : ℝ) + 1) := by
      intro x
      rw [hpd1 x, abs_mul, abs_inv, abs_of_pos hpos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM _).1 (inv_nonneg.2 hpos.le)
    have hgv : ∀ x : ℝ × ℝ, 2 * ((n : ℝ) + 1) < |x.2| → B0579.pd 1 (B0285.cutT n) x = 0 := by
      intro x hx
      have hy : 2 < |((n : ℝ) + 1)⁻¹ * x.2| := by
        rw [abs_mul, abs_inv, abs_of_pos hpos, lt_inv_mul_iff₀ hpos]
        linarith
      rw [hpd1 x, (hM _).2 hy, zero_mul]
    have hL2 := h4 c hc _ (M / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) (div_nonneg hM0 hpos.le)
      (by positivity) (htest.pd 1).continuous hgb hgv
    have hmemg : MemLp (B0579.pd 1 (B0285.cutT n)) 2 μ :=
      ⟨(htest.pd 1).continuous.aestronglyMeasurable, hL2.trans_lt ENNReal.ofReal_lt_top⟩
    have hCS := h5 μ (fun x => u x 0) _ (hu.1 0) hmemg
    have hgle : (eLpNorm (B0579.pd 1 (B0285.cutT n)) 2 μ).toReal ≤ B n := by
      have heq := zc_bound_eq M c ((n : ℝ) + 1) hpos
      simp only [hB]
      rw [← heq]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL2
    rw [hid]
    calc _ ≤ A * (eLpNorm (B0579.pd 1 (B0285.cutT n)) 2 μ).toReal := hCS
      _ ≤ A * B n := mul_le_mul_of_nonneg_left hgle ENNReal.toReal_nonneg
  have hlim : Tendsto (fun n : ℕ => A * B n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcont : Continuous fun ε : ℝ => A * (M * Real.sqrt (4 * c * ε)) := by fun_prop
    have := (hcont.tendsto 0).comp h1
    simpa [Function.comp_def, hB] using this
  exact tendsto_nhds_unique (h6 c ω hω) (squeeze_zero_norm hbound hlim)

/-- **Zero circulation is preserved** (SP 3100-3101), from the six leaves: at every age
`s ≥ t` the flow `w s ∈ X_{m,c}` (`m > 1`) is integrable on the cell (leaf 1) and has the
`L²(cell)` Biot-Savart velocity `u s`, which forces `∫_cell w s = 0`. -/
theorem zeroCirculationPreserved_of (h1 : ZCCellIntegrable) (h2 : ZCCutoffTest)
    (h3 : ZCChiDeriv) (h4 : ZCBandL2) (h5 : ZCCauchySchwarz) (h6 : ZCCutoffLimit) :
    ZeroCirculationPreserved := by
  intro ν c m hc hm tr t f w u hw _ s hs
  have hint := h1 c m hm (w s) (hw.memX s hs)
  exact ⟨hint,
    integral_cell_eq_zero_of_isBiotSavart_of h2 h3 h4 h5 h6 hc hint (hw.biotSavart s hs)⟩

end UnforcedLeray.Short.IIIa
