import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.Defs
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLiftJet
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest

/-!
# `BgYoungW2` from its leaves (source 1206-1222, 2347-2387, 2525-2562, 2575-2609, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `PartIII-b:C/ward/12/org`.  `BgYoungW2` (`Ward/Bg/Defs.lean`) bounds `U = V + r_b` and its
first and second Cartesian partials on the young support `ϱ ≥ R√ν` (`s ≤ 1/ν`) at the levels of
the Part II regime.  By `IIb.ExactSplitII.state`, `V = U_raw + Σᵢ αᵢ E_i` and `r_b = w`, so `U` is
the sum of the raw lift, the two inlet columns (coefficients `αᵢ = coord z i`) and the repair.
The three pieces are bounded separately, in the form `‖D^n F(y)‖ ≤ M` for `n ≤ 2`
(`iteratedFDeriv`), and the sum rule is applied at the young point (which is off the axis, where the
raw lift is `C²`; the inlet columns are `C^∞` on `ℝ³`; the repair is `U - V` with `U` jointly `C^∞`
by `IsExactProfile.smoothU`).  `physPd` and `physPd2` are bounded by the first and second iterated
derivatives (`norm_physPd_le_iter`, `norm_physPd2_le_iter`).

## The three pieces (the first two level leaves)

* `BgRawYoungJets` (source 1206-1222 `sct:lift`: "globally bounded fixed spatial derivatives";
  5461-5464: `DU_raw = s(D_flat v + εC₁)`, `D²U_raw = s^{3/2}(D²_flat v + εC₂)` with "finite
  weighted train bounds"): the raw lift is `C²` off the axis and bounded with its first two
  derivatives on the young support.  Proved here (`bgRawYoungJets_of`) from
  - `BgRawProfileSmooth`: the raw profile `b_raw = (v₁, v₂ + εH)` is `C^∞` on `s > 0`;
  - `BgRawProfileYoungJets`: its chart jets of order `≤ 2` are bounded on `0 < s ≤ 1/ν` with the
    transverse weight `(1+|η|)²` (from `BgTrainStreamYoungJets`, the weighted jets of the train
    stream, Part I `sct:fluctuation` 439-446 and `sct:expansion` 447-459);
  - `BgRingLiftYoung`: the ring-chart calculus at off-axis points of age `≤ S` for a profile that is
    only `C^∞` on `s > 0` (a localized `IIb.RingLiftOffAxis`; from `BgCompChartJetsYoung`, the
    localized Faà di Bruno step `IIb.CompChartJets`).
* `BgInletColumnJets` (source 2347-2369, 2385-2387 `‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`): each inlet
  column is `C²` on `ℝ³` with bounded value and first two derivatives.  Proved here
  (`bgInletColumnJets_of`) from `BgInletProfileJetsAt` (the weighted jets of the inlet profile,
  at a single level, without the slow-age quantifier of `IIb.InletProfileWeightedJets`) and the
  accepted `IIb.ringLiftJet`, `IIb.NicePT.contDiff_Nv`.
* `BgCorrYoungJets` (source 2525-2562: the qualitative bootstrap "This proves all spatial orders",
  "all factors through order `k` are bounded"; 2607-2609 "their uniform supremum bounds"): the
  repair `r_b = w` of an exact split is bounded with its first two derivatives on the young support.

The ages: the inlet constants depend on the slow age `Σ = p.ageCut`, but `BgYoungW2` fixes `ν₀`
before the level, so the inlet leaf is stated at one level with `ν ≤ 1` (all that the inlet
smoothness and jet bounds use: `c = ν⁻² ≥ 1`, `R ≥ 1`), and its bound `M` is chosen after the
level.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-! ## 1. The leaves -/

/-- **Composite jets at an off-axis point of a profile smooth on `s > 0`** (the Faà di Bruno step of
the ring lift, source 2360-2366, 2386-2387, 5461-5464; localized form of `IIb.CompChartJets`): if
`b` is `C^∞` on `{s > 0}` and its jets of order `≤ j` at the chart point `chart R τ y` satisfy
`(1+|η(y)|)^j ‖D^l b‖ ≤ M`, then at the off-axis point `y` of age `< S` the composite
`z ↦ b(chart R τ z)` has `‖D^n(b ∘ chart)(y)‖ ≤ C_j(1+S)^{k_j} M` for `n ≤ j` (the `l`-th chart
derivative carries one factor `1+|η|`, `IIb.ChartJets`). -/
def BgCompChartJetsYoung : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ M : ℝ) (b : ℝ × (ℝ × ℝ) → Merid), 0 < S → 1 ≤ R → 0 ≤ M →
      ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      ∀ y : Space, y ∉ axis → age R y < S →
      (∀ l ≤ j, (1 + |trans R y|) ^ j * ‖iteratedFDeriv ℝ l b (chart R τ y)‖ ≤ M) →
      ∀ n ≤ j, ‖iteratedFDeriv ℝ n (fun z => b (chart R τ z)) y‖ ≤ C * (1 + S) ^ k * M

/-- **Jets of the ring lift at off-axis points of age `≤ S`, for a profile smooth on `s > 0`**
(source 2360-2366, 2386-2387, 5461-5464; localized form of `IIb.RingLiftOffAxis`, which needs a
profile `C^∞` on all of `ℝ × ℝ²` and vanishing for `s > S`): if `b` is `C^∞` on `{s > 0}` and its
jets of order `≤ j` satisfy `(1+|η|)^j ‖D^l b(x)‖ ≤ M` at every `x` with `0 < s ≤ S`, then
`‖D^j N_v b(τ, y)‖ ≤ C_j(1+S)^{k_j} M` at every off-axis `y` of age `≤ S`. -/
def BgRingLiftYoung : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ M : ℝ) (b : ℝ × (ℝ × ℝ) → Merid), 0 < S → 1 ≤ R → 0 ≤ M →
      ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      (∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ S →
        (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l b x‖ ≤ M) →
      ∀ y : Space, y ∉ axis → age R y ≤ S →
        ‖iteratedFDeriv ℝ j (Nv R b τ) y‖ ≤ C * (1 + S) ^ k * M

/-- **The raw profile is smooth for positive age** (source 1206-1222 `sct:lift`, 397 and 2049:
the train and its decaying stream are smooth; `b_raw = (v₁, v₂ + εH)`, `H = (1-K)ψ`,
`K = η∂_η + 2s∂_s`): at every level of the regime, `rawProfile ε v ψ` is `C^∞` on `{s > 0}`
(`v = ∇^⊥ψ` is `IsTrain.smooth_v`, `ψ` is `BgRegime.train_stream_smooth`). -/
def BgRawProfileSmooth : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (Ioi 0 ×ˢ univ)

/-- **Weighted jets of the train stream on the young band** (Part I `sct:fluctuation` 439-446:
`‖⟨η⟩^m ∂_s^ℓ D^j ψ̃(s)‖_∞ ≤ P e^{-κνs/c²}` at every age `s > 0`; `sct:expansion` 447-459:
`‖η^m ∂_η^b ∂_s^ℓ S(s)‖_∞ ≤ P(1+s)^{(m-b-1)/2-ℓ}` for the mean stream `S = ψ̄` at all `s ≥ 0`; source
5461-5464 "finite weighted train bounds"): at every level of the regime with `ν` small, the stream
`Ψ(s, (q, η)) = ψ(s, (q, η))` has `(1+|η|)³ ‖D^l Ψ(x)‖ ≤ M` for `l ≤ 3` and `0 < s ≤ 1/ν`. -/
def BgTrainStreamYoungJets : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ M : ℝ, ∀ l ≤ 3, ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ p.ν⁻¹ →
        (1 + |x.2.2|) ^ 3 *
          ‖iteratedFDeriv ℝ l (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) x‖ ≤ M

/-- **Weighted jets of the raw profile on the young band** (source 1206-1222, 5461-5464: `H`,
`C₁`, `C₂` "have the finite weighted train bounds supplied by the explicit chart differentiation
and the young train construction"): at every level of the regime with `ν` small, the raw profile
`b_raw = v + εH e_z` (`v = ∇^⊥ψ`, `H = ψ - η∂_ηψ - 2s∂_sψ`) has `(1+|η|)² ‖D^l b_raw(x)‖ ≤ M` for
`l ≤ 2` and `0 < s ≤ 1/ν`. -/
def BgRawProfileYoungJets : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ M : ℝ, ∀ l ≤ 2, ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ p.ν⁻¹ →
        (1 + |x.2.2|) ^ 2 *
          ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x‖ ≤ M

/-- **Weighted jets of the inlet profile at one level** (source 2347-2369: the periodized
eigenstream and every fixed derivative have exponential transverse decay with polynomial `c`
costs; the normalized lift `e_ε = e₀ + εe₁` of the cut stream `χ(s)ψ`, with `χ` zero before the
terminal age; 2385-2387): at every level of the regime with `ν ≤ 1` and `p.mode = q` (a growing
eigenpair), each inlet profile `e_ε = ringStreamProfile R (χψᵢ)` is `C^∞`, vanishes for `s > H/2`,
and has `(1+|η|)² ‖D^l e_ε(x)‖ ≤ M` for `l ≤ 2` and all `x`.  (The single-level form of
`IIb.InletProfileWeightedJets`, whose threshold `ν₀` depends on the slow age `Σ`.) -/
def BgInletProfileJetsAt : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ 1 →
    p.mode = q → ∀ i : Fin 2,
      ContDiff ℝ ∞ (p.inletProfile i) ∧
      (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
      ∃ M : ℝ, ∀ l ≤ 2, ∀ x : ℝ × (ℝ × ℝ),
        (1 + |x.2.2|) ^ 2 * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M

/-- **The raw lift on the young support** (source 1206-1222 `sct:lift`: `U_R` has "globally
bounded fixed spatial derivatives"; 5461-5464 `U_raw = √s(v + εHe_z)`, `DU_raw = s(D_flat v + εC₁)`,
`D²U_raw = s^{3/2}(D²_flat v + εC₂)`): at every level of the regime with `ν` small, each phase slice
of `U_raw` is `C²` off the axis, and `‖D^n U_raw(τ, y)‖ ≤ M` for `n ≤ 2` at every phase and every
`y` with `ϱ ≥ R√ν`. -/
def BgRawYoungJets : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      (∀ τ : ℝ, ContDiffOn ℝ 2 (p.raw τ) axisᶜ) ∧
      ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), p.R * Real.sqrt p.ν ≤ ϱ y → ∀ n : ℕ, n ≤ 2 →
        ‖iteratedFDeriv ℝ n (p.raw τ) y‖ ≤ M

/-- **The inlet columns are `W^{2,∞}`** (source 2347-2369, 2385-2387:
`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`): at every level of the regime with `ν ≤ 1` and `p.mode = q` (a
growing eigenpair), each inlet column `E_i(τ, ·)` is `C²` on `ℝ³` and `‖D^n E_i(τ, y)‖ ≤ M` for
`n ≤ 2`, every phase and every `y`. -/
def BgInletColumnJets : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ 1 →
    p.mode = q → ∀ i : Fin 2,
      (∀ τ : ℝ, ContDiff ℝ 2 (p.inlet i τ)) ∧
      ∃ M : ℝ, ∀ (τ : ℝ) (y : Space) (n : ℕ), n ≤ 2 → ‖iteratedFDeriv ℝ n (p.inlet i τ) y‖ ≤ M

/-- **The repair is `W^{2,∞}` on the young support** (source 2525-2562: the qualitative bootstrap
`A₀D_jw = f_j + ½D_jw` with the maximal graph at shift zero, "This proves all spatial orders",
"if derivatives through order `k` are in the graph, all factors through order `k` are bounded";
2538-2541 `short-bg:strong`; 2607-2609 "interpolation between its `C_per L^p` derivatives and their
uniform supremum bounds"): for the growing eigenpair `q = p.mode` there is `ν₀ > 0` such that at
every level of the regime with `ν ≤ ν₀`, every exact split `U = V + r_b` (`IIb.ExactSplitII`, so
`r_b = w = corr z` for a solution `z` of the projected equation, with `sup_τ ‖r_b‖_∞ ≤ ρ_b`) whose
sum is an exact profile (`IsExactProfile`) has `‖D^n r_b(τ, y)‖ ≤ M` for `n ≤ 2` at every phase and
every `y` with `ϱ ≥ R√ν`. -/
def BgCorrYoungJets : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d ρb S_in : ℝ) (V rb : ℝ → SpatialField) (pres : ℝ → Space → ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      UnforcedLeray.Short.IIb.ExactSplitII p ρb S_in V rb →
      IsExactProfile p.ν p.period (fun τ y => V τ y + rb τ y) pres →
      ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), p.R * Real.sqrt p.ν ≤ ϱ y → ∀ n : ℕ, n ≤ 2 →
        ‖iteratedFDeriv ℝ n (rb τ) y‖ ≤ M

/-! ## 2. Elementary facts -/

/-- A young point `ϱ ≥ R√ν` (`R, ν > 0`) is off the axis. -/
theorem young_not_mem_axis {R ν : ℝ} (hR : 0 < R) (hν : 0 < ν) {y : Space}
    (hy : R * Real.sqrt ν ≤ ϱ y) : y ∉ axis := by
  intro hax
  have hax' : y 0 = 0 ∧ y 1 = 0 := hax
  have h0 : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hϱ : ϱ y = 0 := by
    simp only [ϱ, hax'.1, hax'.2]
    norm_num
  linarith

/-- A young point `ϱ ≥ R√ν` has age `s = R²/ϱ² ≤ 1/ν`. -/
theorem young_age_le {R ν : ℝ} (hR : 0 < R) (hν : 0 < ν) {y : Space}
    (hy : R * Real.sqrt ν ≤ ϱ y) : age R y ≤ ν⁻¹ := by
  have h0 : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hϱ : 0 < ϱ y := h0.trans_le hy
  have hsq : (R * Real.sqrt ν) ^ 2 ≤ ϱ y ^ 2 := pow_le_pow_left₀ h0.le hy 2
  have e : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by rw [mul_pow, Real.sq_sqrt hν.le]
  rw [e] at hsq
  unfold age
  rw [div_le_iff₀ (pow_pos hϱ 2)]
  calc R ^ 2 = ν⁻¹ * (R ^ 2 * ν) := by field_simp
    _ ≤ ν⁻¹ * ϱ y ^ 2 := mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 hν.le)

/-- In the regime `ε = e^{-d/ν} ≤ 1`, so `R = ε⁻¹ ≥ 1`. -/
theorem bgRegime_one_le_R {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) : 1 ≤ p.R := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hε : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
    rw [neg_div]
    linarith
  show 1 ≤ p.ε⁻¹
  exact (one_le_inv₀ p.ε_pos).mpr hε

/-- The ring lift of a profile `C^∞` on `{s > 0}` is `C^∞` off the axis. -/
theorem contDiffOn_Nv_of {R : ℝ} (hR : R ≠ 0) {b : ℝ × (ℝ × ℝ) → Merid}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ)) (τ : ℝ) :
    ContDiffOn ℝ ∞ (Nv R b τ) axisᶜ := by
  have hc : ContDiffOn ℝ ∞ (fun z => b (chart R τ z)) axisᶜ :=
    hb.comp (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_chart hR τ)
      (fun z hz => ⟨age_pos hR hz, mem_univ _⟩)
  rw [UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun]
  exact (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_sqrt_age hR).smul
    (UnforcedLeray.Short.IIb.ChartJetsAux.contDiffOn_frameL.clm_apply hc)

theorem norm_coordinateVector_bg (j : Fin 3) : ‖UnforcedLeray.coordinateVector j‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

/-- `|∂_j F| ≤ ‖DF‖`. -/
theorem norm_physPd_le_iter (F : Space → Space) (j : Fin 3) (y : Space) :
    ‖physPd F j y‖ ≤ ‖iteratedFDeriv ℝ 1 F y‖ := by
  rw [norm_iteratedFDeriv_one]
  unfold physPd
  calc ‖fderiv ℝ F y (UnforcedLeray.coordinateVector j)‖
      ≤ ‖fderiv ℝ F y‖ * ‖UnforcedLeray.coordinateVector j‖ := (fderiv ℝ F y).le_opNorm _
    _ = ‖fderiv ℝ F y‖ := by rw [norm_coordinateVector_bg, mul_one]

/-- `|∂_j∂_l F| ≤ ‖D²F‖` for a `C²` field. -/
theorem norm_physPd2_le_iter {F : Space → Space} (hF : ContDiff ℝ 2 F) (j l : Fin 3)
    (y : Space) : ‖physPd2 F j l y‖ ≤ ‖iteratedFDeriv ℝ 2 F y‖ := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y := (hF1.differentiable (by norm_num)) y
  have hfd : HasFDerivAt (fun y' => fderiv ℝ F y' (UnforcedLeray.coordinateVector l))
      ((fderiv ℝ F y).comp (0 : Space →L[ℝ] Space) +
        (fderiv ℝ (fderiv ℝ F) y).flip (UnforcedLeray.coordinateVector l)) y :=
    hd.hasFDerivAt.clm_apply (hasFDerivAt_const (UnforcedLeray.coordinateVector l) y)
  have e : physPd2 F j l y = iteratedFDeriv ℝ 2 F y
      ![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector l] := by
    rw [iteratedFDeriv_two_apply]
    simp only [physPd2, physPd]
    rw [hfd.fderiv]
    simp
  rw [e]
  refine ((iteratedFDeriv ℝ 2 F y).le_opNorm _).trans ?_
  simp [Fin.prod_univ_two, norm_coordinateVector_bg]

/-! ## 3. The raw lift and the inlet columns from their leaves -/

/-- **`BgRawYoungJets`** from the smoothness and the weighted young jets of the raw profile and the
localized ring-lift calculus: off the axis `U_raw = N_v b_raw` (`Params.raw_eq_off_axis`); a young
point is off the axis with age `≤ 1/ν` (`young_not_mem_axis`, `young_age_le`), and `R ≥ 1`. -/
theorem bgRawYoungJets_of (h1 : BgRawProfileSmooth) (h2 : BgRawProfileYoungJets)
    (h3 : BgRingLiftYoung) : BgRawYoungJets := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, h2'⟩ := h2 dm dp hdm
  obtain ⟨C0, k0, hC0, H0⟩ := h3 0
  obtain ⟨C1, k1, hC1, H1⟩ := h3 1
  obtain ⟨C2, k2, hC2, H2⟩ := h3 2
  refine ⟨ν₀, hν₀, fun p d hreg hν => ?_⟩
  have hbs : ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      (Ioi 0 ×ˢ univ) := h1 p d dm dp hreg
  have hR0 : p.R ≠ 0 := p.R_pos.ne'
  have hR1 : 1 ≤ p.R := bgRegime_one_le_R hreg
  have hopen : IsOpen (axisᶜ : Set Space) := isOpen_compl_axis
  have heq : ∀ τ : ℝ, EqOn (p.raw τ)
      (Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) axisᶜ :=
    fun τ y hy => p.raw_eq_off_axis τ y hy
  refine ⟨fun τ => ((contDiffOn_Nv_of hR0 hbs τ).of_le
    (by simp)).congr (heq τ), ?_⟩
  obtain ⟨M, hM⟩ := h2' p d hreg hν
  have hS : 0 < p.ν⁻¹ := inv_pos.2 p.ν_pos
  have hM'0 : 0 ≤ max M 0 := le_max_right _ _
  have hw : ∀ j ≤ 2, ∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ p.ν⁻¹ →
      (1 + |x.2.2|) ^ j *
        ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x‖ ≤
          max M 0 := by
    intro j hj l hl x hx0 hxS
    have h := hM l (hl.trans hj) x hx0 hxS
    have hpow : (1 + |x.2.2|) ^ j ≤ (1 + |x.2.2|) ^ 2 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg x.2.2]) hj
    calc _ ≤ (1 + |x.2.2|) ^ 2 *
          ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ M := h
      _ ≤ max M 0 := le_max_left _ _
  have t0 : 0 ≤ C0 * (1 + p.ν⁻¹) ^ k0 * max M 0 := by positivity
  have t1 : 0 ≤ C1 * (1 + p.ν⁻¹) ^ k1 * max M 0 := by positivity
  have t2 : 0 ≤ C2 * (1 + p.ν⁻¹) ^ k2 * max M 0 := by positivity
  refine ⟨C0 * (1 + p.ν⁻¹) ^ k0 * max M 0 + C1 * (1 + p.ν⁻¹) ^ k1 * max M 0 +
    C2 * (1 + p.ν⁻¹) ^ k2 * max M 0, fun τ y hy n hn => ?_⟩
  have hyax : y ∉ axis := young_not_mem_axis p.R_pos p.ν_pos hy
  have hage : age p.R y ≤ p.ν⁻¹ := young_age_le p.R_pos p.ν_pos hy
  have hev : p.raw τ =ᶠ[𝓝 y]
      Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hyax) (heq τ)
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
  interval_cases n
  · have h := H0 p.ν⁻¹ p.R τ (max M 0) _ hS hR1 hM'0 hbs (hw 0 (by norm_num)) y hyax hage
    linarith
  · have h := H1 p.ν⁻¹ p.R τ (max M 0) _ hS hR1 hM'0 hbs (hw 1 (by norm_num)) y hyax hage
    linarith
  · have h := H2 p.ν⁻¹ p.R τ (max M 0) _ hS hR1 hM'0 hbs (hw 2 le_rfl) y hyax hage
    linarith

/-- **`BgInletColumnJets`** from the single-level weighted jets of the inlet profile, the accepted
ring-lift jet bound `IIb.ringLiftJet` (`R ≥ 1`, profile vanishing for `s > H/2`) and the accepted
smoothness of the ring lift `IIb.NicePT.contDiff_Nv`. -/
theorem bgInletColumnJets_of (h : BgInletProfileJetsAt) : BgInletColumnJets := by
  intro lam q hq p d dm dp hreg hν hmode i
  obtain ⟨hsm, hvan, M, hM⟩ := h lam q hq p d dm dp hreg hν hmode i
  have hR1 : 1 ≤ p.R := bgRegime_one_le_R hreg
  have hH : 0 < p.H / 2 := half_pos p.H_pos
  refine ⟨fun τ => ?_, ?_⟩
  · have hN := UnforcedLeray.Short.IIb.NicePT.contDiff_Nv p.R_pos hsm hvan
    have hc := hN.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ (fun y : Space => ((τ, y) : ℝ × Space)))
    exact hc.of_le (by simp)
  obtain ⟨C0, k0, hC0, H0⟩ := UnforcedLeray.Short.IIb.ringLiftJet 0
  obtain ⟨C1, k1, hC1, H1⟩ := UnforcedLeray.Short.IIb.ringLiftJet 1
  obtain ⟨C2, k2, hC2, H2⟩ := UnforcedLeray.Short.IIb.ringLiftJet 2
  have hM'0 : 0 ≤ max M 0 := le_max_right _ _
  have hw : ∀ j ≤ 2, ∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ),
      (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ max M 0 := by
    intro j hj l hl x
    have h := hM l (hl.trans hj) x
    have hpow : (1 + |x.2.2|) ^ j ≤ (1 + |x.2.2|) ^ 2 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg x.2.2]) hj
    calc _ ≤ (1 + |x.2.2|) ^ 2 * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ M := h
      _ ≤ max M 0 := le_max_left _ _
  have t0 : 0 ≤ C0 * (1 + p.H / 2) ^ k0 * max M 0 := by positivity
  have t1 : 0 ≤ C1 * (1 + p.H / 2) ^ k1 * max M 0 := by positivity
  have t2 : 0 ≤ C2 * (1 + p.H / 2) ^ k2 * max M 0 := by positivity
  refine ⟨C0 * (1 + p.H / 2) ^ k0 * max M 0 + C1 * (1 + p.H / 2) ^ k1 * max M 0 +
    C2 * (1 + p.H / 2) ^ k2 * max M 0, fun τ y n hn => ?_⟩
  interval_cases n
  · have h := H0 (p.H / 2) p.R τ (max M 0) (p.inletProfile i) hH hR1 hM'0 hsm hvan
      (hw 0 (by norm_num)) y
    exact h.trans (by linarith)
  · have h := H1 (p.H / 2) p.R τ (max M 0) (p.inletProfile i) hH hR1 hM'0 hsm hvan
      (hw 1 (by norm_num)) y
    exact h.trans (by linarith)
  · have h := H2 (p.H / 2) p.R τ (max M 0) (p.inletProfile i) hH hR1 hM'0 hsm hvan
      (hw 2 le_rfl) y
    exact h.trans (by linarith)

/-! ## 4. The combination -/

/-- **`BgYoungW2` from the three pieces** (source 2525-2562, 2607-2609, 4155, 4194-4195): at a
young point `y` (off the axis), `U(τ, ·) = U_raw + α₀E₀ + α₁E₁ + r_b` with `U` jointly `C^∞`
(`IsExactProfile.smoothU`), `U_raw` `C²` near `y`, `E_i` `C²`, hence `r_b = U - V` `C²` near `y`;
so `D^nU(y) = D^nU_raw(y) + α₀D^nE₀(y) + α₁D^nE₁(y) + D^nr_b(y)` for `n ≤ 2`, and `U`, `∂_jU`,
`∂_j∂_lU` are bounded by `|U|`, `‖DU‖`, `‖D²U‖`. -/
theorem bgYoungW2_of (hR : BgRawYoungJets) (hI : BgInletColumnJets) (hC : BgCorrYoungJets) :
    BgYoungW2 := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, hR'⟩ := hR dm dp hdm
  obtain ⟨ν₂, hν₂, hC'⟩ := hC lam q hq dm dp hdm
  refine ⟨min (min ν₁ ν₂) 1, lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro p d ρb S_in V rb pres hreg hν hmode hsplit hex
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνc : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  obtain ⟨hrawC, Mr, hMr⟩ := hR' p d hreg hνa
  obtain ⟨Mw, hMw⟩ := hC' p d ρb S_in V rb pres hreg hνb hmode hsplit hex
  obtain ⟨hI0C, M0, hM0⟩ := hI lam q hq p d dm dp hreg hνc hmode 0
  obtain ⟨hI1C, M1, hM1⟩ := hI lam q hq p d dm dp hreg hνc hmode 1
  obtain ⟨z, -, hV, -, -⟩ := hsplit.state
  refine ⟨Mr + (‖p.coord z 0‖ * M0 + ‖p.coord z 1‖ * M1) + Mw, fun τ y hy => ?_⟩
  have hyax : y ∈ (axisᶜ : Set Space) := young_not_mem_axis p.R_pos p.ν_pos hy
  have hopen : IsOpen (axisᶜ : Set Space) := isOpen_compl_axis
  have hFs : ContDiff ℝ 2 (fun y' => V τ y' + rb τ y') := by
    have h := hex.smoothU.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => ((τ, y') : ℝ × Space)))
    exact h.of_le (by simp)
  have hVfun : V τ = fun y' => p.raw τ y' +
      (p.coord z 0 • p.inlet 0 τ y' + p.coord z 1 • p.inlet 1 τ y') := by
    funext y'
    rw [hV, Fin.sum_univ_two]
  have hrA : ContDiffAt ℝ 2 (p.raw τ) y := (hrawC τ).contDiffAt (hopen.mem_nhds hyax)
  have h0A : ContDiffAt ℝ 2 (p.inlet 0 τ) y := (hI0C τ).contDiffAt
  have h1A : ContDiffAt ℝ 2 (p.inlet 1 τ) y := (hI1C τ).contDiffAt
  have hSA : ContDiffAt ℝ 2
      (fun y' => p.coord z 0 • p.inlet 0 τ y' + p.coord z 1 • p.inlet 1 τ y') y :=
    (h0A.const_smul _).add (h1A.const_smul _)
  have hVA : ContDiffAt ℝ 2 (V τ) y := by
    rw [hVfun]
    exact hrA.add hSA
  have hrbfun : rb τ = fun y' => (V τ y' + rb τ y') - V τ y' := by
    funext y'
    abel
  have hrbA : ContDiffAt ℝ 2 (rb τ) y := by
    rw [hrbfun]
    exact hFs.contDiffAt.sub hVA
  have key : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => V τ y' + rb τ y') y‖ ≤
      Mr + (‖p.coord z 0‖ * M0 + ‖p.coord z 1‖ * M1) + Mw := by
    intro n hn
    have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
    have eF : iteratedFDeriv ℝ n (fun y' => V τ y' + rb τ y') y =
        iteratedFDeriv ℝ n (V τ) y + iteratedFDeriv ℝ n (rb τ) y :=
      iteratedFDeriv_add_apply (f := V τ) (g := rb τ) (hVA.of_le hn') (hrbA.of_le hn')
    have eS : iteratedFDeriv ℝ n
        (fun y' => p.coord z 0 • p.inlet 0 τ y' + p.coord z 1 • p.inlet 1 τ y') y =
        p.coord z 0 • iteratedFDeriv ℝ n (p.inlet 0 τ) y +
          p.coord z 1 • iteratedFDeriv ℝ n (p.inlet 1 τ) y := by
      have e1 := iteratedFDeriv_add_apply (f := fun y' => p.coord z 0 • p.inlet 0 τ y')
        (g := fun y' => p.coord z 1 • p.inlet 1 τ y')
        ((h0A.of_le hn').const_smul (p.coord z 0)) ((h1A.of_le hn').const_smul (p.coord z 1))
      rw [iteratedFDeriv_const_smul_apply' (h0A.of_le hn'),
        iteratedFDeriv_const_smul_apply' (h1A.of_le hn')] at e1
      exact e1
    have eV : iteratedFDeriv ℝ n (V τ) y = iteratedFDeriv ℝ n (p.raw τ) y +
        (p.coord z 0 • iteratedFDeriv ℝ n (p.inlet 0 τ) y +
          p.coord z 1 • iteratedFDeriv ℝ n (p.inlet 1 τ) y) := by
      rw [hVfun, ← eS]
      exact iteratedFDeriv_add_apply (f := p.raw τ)
        (g := fun y' => p.coord z 0 • p.inlet 0 τ y' + p.coord z 1 • p.inlet 1 τ y')
        (hrA.of_le hn') (hSA.of_le hn')
    have b1 := hMr τ y hy n hn
    have b2 := hM0 τ y n hn
    have b3 := hM1 τ y n hn
    have b4 := hMw τ y hy n hn
    rw [eF, eV]
    calc _ ≤ ‖iteratedFDeriv ℝ n (p.raw τ) y‖ +
          (‖p.coord z 0‖ * ‖iteratedFDeriv ℝ n (p.inlet 0 τ) y‖ +
            ‖p.coord z 1‖ * ‖iteratedFDeriv ℝ n (p.inlet 1 τ) y‖) +
          ‖iteratedFDeriv ℝ n (rb τ) y‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add ?_ ?_)))) le_rfl)
          · exact norm_smul_le _ _
          · exact norm_smul_le _ _
      _ ≤ Mr + (‖p.coord z 0‖ * M0 + ‖p.coord z 1‖ * M1) + Mw := by gcongr
  refine ⟨?_, fun j => ?_, fun j l => ?_⟩
  · have h0 := key 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at h0
  · exact (norm_physPd_le_iter _ j y).trans (key 1 (by norm_num))
  · exact (norm_physPd2_le_iter hFs j l y).trans (key 2 le_rfl)

#print axioms bgYoungW2_of

end UnforcedLeray.Short.PartIIIb.Concrete

