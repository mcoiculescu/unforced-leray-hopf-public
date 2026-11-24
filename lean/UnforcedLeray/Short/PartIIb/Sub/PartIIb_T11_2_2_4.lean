import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4` (`DualRemainderLimit`): decomposition

Source: `the November 2 reference manuscript`
lines 1923-1927 (flat equation tested against `φ(η/L) σ^{μ-1} χ(σ) H(s-σ,·)`).

The remainder `Rem_L = T(∇^⊥ψ_L) - φ_L T(∇^⊥ψ_∞)` is, by the product rule, a finite sum of terms
carrying `L^{-1}φ'`, `L^{-2}φ''`, `L^{-3}φ'''` times `σ^{μ-1}χ` (and its derivatives) times
derivatives of order `≤ 3` of `g(σ,·) = H(s-σ,·)`, supported in `σ ∈ supp χ`.  So a pointwise
bound `|Rem_L| ≤ C (L⁻¹+L⁻²+L⁻³) G` with `G` the order-`≤3` jet of `g` on `supp χ`; Hölder
bounds `∫ |b| G`; measurability; then the squeeze (proved here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The order-`≤ 3` jet of `g(σ,·) = H(s-σ,·)`, restricted to `σ ∈ tsupport χ`. -/
def dualG (χ : ℝ → ℝ) (H : Coord → ℝ) (s : ℝ) (x : Coord) : ℝ :=
  (tsupport χ).indicator (fun _ => (1 : ℝ)) x.1 *
    ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖

/-- Leaf `T11/2/2/4/1` (pointwise commutator bound; SP 1923-1927).  Product rule: `ψ_L = φ(η/L)ψ_∞`,
`ψ_∞ = σ^{μ-1}χ(σ)g`; `flatTransposeC (perpC ·)` involves derivatives of total order `≤ 3`
(one in `q`/`η` from `perpC`, then `σ`-derivative or two more in `q`/`η`); a derivative landing on
`φ(η/L)` produces `L^{-k}φ^{(k)}(η/L)`, `k = 1,2,3`, bounded by `sup|φ^{(k)}|` (`DFPhi`: smooth with
compact support).  `σ^{μ-1}` and its `σ`-derivatives are bounded on the compact `tsupport χ ⊂ (0,s)`;
outside `tsupport χ × ℝ²` both `ψ_L, ψ_∞` vanish near `x`, so `Rem_L x = 0`. -/
def DualRemPointwise : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (H : Coord → ℝ) (s r' : ℝ) (χ φ : ℝ → ℝ),
    0 < c → 0 < ν → 0 < s → HeatSol c ν r' H → DFChi s χ → DFPhi φ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ (x : Coord) (i : Fin 2),
      ‖dualRem ν μ χ φ H s L x i‖ ≤ C * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) * dualG χ H s x

/-- Leaf `T11/2/2/4/2` (Hölder; SP 1923-1927).  `∫ |b| G d(ageμ c 0) < ∞`: `G` vanishes outside
`σ ∈ tsupport χ ⊂ [a,a'] ⊂ (0,s)`, where the weights `σ^{r/2-5/2}` are bounded above and below, so
Hölder `(r, r/(r-1))` against `b ∈ L^r(ageμ c (r/2-5/2))` and
`HeatSol.deriv_memLp` (`n ≤ 3`, on `[s-a', s-a] × cell × ℝ`) applies; `ageμ c 0 = dσ ⊗ avgμ c`
and `q`-periodicity (`HeatSol.periodic`) reduce the integral to the cell. -/
def DualGWeightedInt : Prop :=
  ∀ (c r ν : ℝ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b →
    HeatSol c ν (r / (r - 1)) H → DFChi s χ →
    Integrable (fun x => ‖b x‖ * dualG χ H s x) (Axi.ageμ c 0)

/-- Leaf `T11/2/2/4/3` (measurability).  `dualRem` is built from `fderiv`s (measurable in `x`), so
`x ↦ pairC b (dualRem …) x` is a.e. strongly measurable for `ageμ c 0` once `b` is
(`InHr` gives it for `ageμ c (r/2-5/2)`, which has the same null sets as `ageμ c 0`:
equivalent densities `σ^{r/2-5/2}` on `σ > 0`; use `measurable_fderiv`,
`measurable_fderiv_apply_const`). -/
def DualRemMeasurable : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ φ : ℝ → ℝ) (L : ℝ),
    0 < c → 0 < ν → 0 < s → 1 < r → InHr c r b → HeatSol c ν (r / (r - 1)) H →
    DFChi s χ → DFPhi φ →
    AEStronglyMeasurable (fun x => pairC b (dualRem ν μ χ φ H s L) x) (Axi.ageμ c 0) ∧
    AEStronglyMeasurable (fun x => ‖b x‖ * dualG χ H s x) (Axi.ageμ c 0)

/-- `DualRemainderLimit` from the three leaves (integrable domination, then squeeze). -/
theorem dualRemainderLimit_of (h1 : DualRemPointwise) (h2 : DualGWeightedInt)
    (h3 : DualRemMeasurable) : DualRemainderLimit := by
  intro c r ν μ b H s χ φ hc hν hr hs hb hfl hH hχ hφ
  obtain ⟨C, hC0, hC⟩ := h1 c ν μ H s (r / (r - 1)) χ φ hc hν hs hH hχ hφ
  have hI := h2 c r ν b H s χ hc hν hr hs hb hH hχ
  set K : ℝ → ℝ := fun L => L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 with hK
  -- pointwise bound
  have hpt : ∀ L : ℝ, 0 < L → ∀ x : Coord,
      ‖pairC b (dualRem ν μ χ φ H s L) x‖ ≤ (2 * C * K L) * (‖b x‖ * dualG χ H s x) := by
    intro L hL x
    have hG : 0 ≤ dualG χ H s x := by
      unfold dualG
      refine mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) ?_
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hKL : 0 ≤ K L := by
      have : 0 < L⁻¹ := inv_pos.2 hL
      simp only [hK]; positivity
    unfold pairC
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i : Fin 2, ‖b x i * dualRem ν μ χ φ H s L x i‖ ≤
        (C * K L) * (‖b x‖ * dualG χ H s x) := by
      intro i
      rw [norm_mul]
      have hb' : ‖b x i‖ ≤ ‖b x‖ := by
        have := PiLp.norm_apply_le (b x) i
        simpa using this
      have hr' := hC L hL x i
      calc ‖b x i‖ * ‖dualRem ν μ χ φ H s L x i‖
          ≤ ‖b x‖ * (C * K L * dualG χ H s x) :=
            mul_le_mul hb' hr' (norm_nonneg _) (norm_nonneg _)
        _ = (C * K L) * (‖b x‖ * dualG χ H s x) := by ring
    calc ∑ i : Fin 2, ‖b x i * dualRem ν μ χ φ H s L x i‖
        ≤ ∑ _i : Fin 2, (C * K L) * (‖b x‖ * dualG χ H s x) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (2 * C * K L) * (‖b x‖ * dualG χ H s x) := by
          simp [Finset.sum_const]; ring
  have hint : ∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualRem ν μ χ φ H s L) x) (Axi.ageμ c 0) := by
    intro L hL
    refine Integrable.mono' (hI.const_mul (2 * C * K L)) (h3 c r ν μ b H s χ φ L hc hν hs hr hb hH hχ hφ).1 ?_
    exact Filter.Eventually.of_forall (fun x => hpt L hL x)
  refine ⟨hint, ?_⟩
  set I : ℝ := ∫ x, ‖b x‖ * dualG χ H s x ∂(Axi.ageμ c 0) with hIdef
  have hKlim : Tendsto K atTop (𝓝 0) := by
    have h1' : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have := (h1'.add (h1'.pow 2)).add (h1'.pow 3)
    simpa [hK] using this
  have hbound : ∀ᶠ L in atTop, ‖∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)‖ ≤
      (2 * C * I) * K L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    calc ‖∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)‖
        ≤ ∫ x, (2 * C * K L) * (‖b x‖ * dualG χ H s x) ∂(Axi.ageμ c 0) :=
          norm_integral_le_of_norm_le (hI.const_mul _) (Filter.Eventually.of_forall (hpt L hL))
      _ = (2 * C * I) * K L := by
          rw [integral_const_mul, hIdef]; ring
  have hlim : Tendsto (fun L : ℝ => (2 * C * I) * K L) atTop (𝓝 0) := by
    simpa using hKlim.const_mul (2 * C * I)
  exact squeeze_zero_norm' hbound hlim

end UnforcedLeray.Short.IIb
