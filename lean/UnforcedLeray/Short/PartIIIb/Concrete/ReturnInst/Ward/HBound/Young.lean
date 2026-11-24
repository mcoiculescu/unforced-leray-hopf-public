import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardYoungPointwise

/-!
# The Ward fields on the young support: chart readings, the leaves, the change of measure
(shared by `PartIII-b:C/ward/9`, `/10`, `/11`)

Source of record: `the November 2 reference manuscript` (73 pages).

## The young chart reading

At the chart point `q = (s, (q, η))`, `s > 0`, the similarity point `y = chartY R q` has
`ϱ y = R/√s` and `age R y = s` (source 2666-2668).  The young region `νs ≤ 1` of the chart is the
young receiver region `ϱ ≥ R√ν` (`χ_y(ν·age) = 0` for `ϱ ≤ R√ν`, source 4164-4167).  For a physical
field `F(τ, y)` the chart reading `s^{-1/2}|F(τ, y)|` at `τ = chartTau R q` is the coefficient
convention `b = s^{-1/2}·(physical field)` of `coefOf` (source 2683), and its `L²(s^{-3/2}dς)` norm
is `R⁻¹π^{-1/2}` times the `Y₂ = L²_τL²` norm of the (axisymmetric) field over one period
`P = 2c/R` (lift identity 2684-2689).  `wardYoungRead ν R F` is this reading restricted to `νs ≤ 1`,
and `YoungL2Le c ν R C F g` says that it is measurable with norm at most `C‖g‖_{L²(s^{-1/2}dς)}`:
"`1_young F ∈ Y₂` with the fixed-parameter bound".

## Leaves (the analytic content, stated here)

* `WardXYoungL2` : `X` and `∂_jX` (source 4194-4196 "`X, DX, Y ∈ Y₂`"; `sep:young` 3633-3648 with
  `p = q = 2`, `b = 1`; the stream-cutoff majorant 3687-3713);
* `WardD2XYoungL2` : `∂_j∂_lX` (same, `j = 2`);
* `WardYYoungL2`, `WardDYYoungL2` : `Y = D_{μ+1}X` and `∂_jY` (`ward:cutoff-source` 4202-4216:
  `Y = 𝒞_yW_μ + [D_{μ+1}, 𝒞_y]X₀`; `sep:young` 3633-3648; the commutator lives on the annulus
  `R√ν ≤ ϱ ≤ R√(1.25ν)`, 3707-3713);
* `WardDXYoungSup` : the ordinary `L^∞_τL^∞_y` bound of `∂_jX` on `ϱ ≥ R√ν` (source 5238-5244;
  Cauchy-Schwarz in `sep:resolvent` 3611-3629 with the kernel bound `sep:kernel` 3603-3611 and the
  periodic geometric sum, `Re μ > -1/4`; the stream cutoff 3687-3713).

## Proved here

* `wyl_coefOf_norm_le`, `wyl_coefOf_le`: the chart coefficient is dominated by the chart reading,
  case split young / old / `s ≤ 0`;
* `wyl_X_zero_nhds`, `wyl_Y_zero_nhds`: on `νs > 1` the Ward fields vanish near the chart point at
  every phase (source 4306-4311, `wyp_at`);
* `wyl_eLpNorm_body_le` (Lemma A): on fields vanishing off `νs ≤ 1`, the gained body norm is at
  most `√(π e^{2|γ|/ν})` times the `L²(s^{-3/2}dς)` norm (`g⁻¹ ≤ e^{|γ|/ν}` on `νs ≤ 1`, source
  3875, 5117);
* `wyl_eLpNorm_src`: `‖·‖_{L²(srcMeasure)} = √π ‖·‖_{L²(s^{-3/2}dς)}`;
* `WylBd` and its closure under sums and real multiples (bookkeeping of the bounds `K‖g‖`);
* `wyl_fderiv_apply_norm_le`: `|Df(y)v| ≤ Σ_k |v_k| |∂_kf(y)|` (linearity of `fderiv`, no
  differentiability needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. The young chart reading -/

/-- The young chart region `νs ≤ 1` (source 4164-4167, 4306-4311). -/
def wardYoungSet (ν : ℝ) : Set Chart := {q : Chart | ν * q.1 ≤ 1}

/-- The chart reading `s^{-1/2}|F(chartTau R q, chartY R q)|` of a physical field, restricted to
the young chart region `νs ≤ 1` (source 2683-2689: `R⁻¹π^{-1/2}‖1_{young}F‖_{Y₂}` is its
`L²(s^{-3/2}dς)` norm). -/
def wardYoungRead (ν R : ℝ) (F : ℝ → Space → Space) : Chart → ℝ :=
  (wardYoungSet ν).indicator fun q =>
    (Real.sqrt q.1)⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖

/-- **`1_young F ∈ Y₂` with the bound `C‖g‖`**: the young chart reading of `F` is measurable and
its `L²(s^{-3/2}dς)` norm is at most `C‖g‖_{L²(s^{-1/2}dς)}` (source 4194-4196, 2683-2689). -/
def YoungL2Le (c ν R C : ℝ) (F : ℝ → Space → Space) (g : Chart → Ten3) : Prop :=
  AEStronglyMeasurable (wardYoungRead ν R F) (ageμ c (-3 / 2)) ∧
    eLpNorm (wardYoungRead ν R F) 2 (ageμ c (-3 / 2)) ≤
      ENNReal.ofReal C * eLpNorm g 2 (ageμ c (-1 / 2))

/-! ## 2. Leaves -/

/-- **`X, ∂_jX ∈ Y₂` on the young support** (source 4187-4196 "`X, DX, Y ∈ Y₂` … fixed-parameter
bounds"; `sep:young` 3633-3648 with `p = q = 2`, `b = 1`:
`‖1_young D^jW_μ‖_{L²_τL²} ≤ C D^{-1-j}‖T‖_{L²_τL²}`, `D = R√ν(1 - √(5/6))`,
`inf_K(2μ + 3/2) > 0` for `μ > -1/4`, applied to `W_μ` and `W_{μ+1}` of the cut old source
`oldCutSrc` (`oldSourceReg_of`, lift identity 2684-2687); the stream cutoff
`𝒞_yZ = χ_yZ + (χ_y'/r)Ψ_Ze_z` has the translation-invariant majorant
`CD^{-2}(D² + |z - z_src|²)^{-1}1_{|y' - z'_src| ≤ CD}`, whose `L¹` norm is `CD^{-1}`, 3687-3713):
for old `L²` data the young chart readings of `X = 𝒞_y(W_μ - W_{μ+1})` and of its first partials are
bounded by `C‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardXYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R C (wardX ν μ R c χy g) g ∧
        ∀ j : Fin 3, YoungL2Le c ν R C (fun τ => physPd (wardX ν μ R c χy g τ) j) g

/-- **`D²X ∈ Y₂` on the young support** (source 4194-4196, 5225-5235 "`D²X`" in
`(U⊗U):D²X` and `C_diff`; `sep:young` 3633-3648 with `j = 2`, `p = q = 2`, `b = 1`; after `j`
derivatives the stream-cutoff majorant costs `D^{-j}`, 3696-3697). -/
def WardD2XYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ j l : Fin 3, YoungL2Le c ν R C (fun τ => physPd2 (wardX ν μ R c χy g τ) j l) g

/-- **`Y ∈ Y₂` on the young support** (source 4194-4196; `ward:cutoff-source` 4202-4216:
`Y = D_{μ+1}X = 𝒞_yW_μ + [D_{μ+1}, 𝒞_y]X₀`, no `y·∇` falls on `X₀`, the commutator carries only
derivatives of `χ_y`, which live on the bounded annulus `R√ν ≤ ϱ ≤ R√(1.25ν)`, and
`Bχ = -ϱχ'(ϱ)/2` is bounded; `sep:young` 3633-3648 for `W_μ` and the `X`-type bound for the
commutator, 3707-3713). -/
def WardYYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → YoungL2Le c ν R C (wardY ν μ R c χy g) g

/-- **`DY ∈ Y₂` on the young support** (source 5225-5235, the term `2U·∇Y` of `Ẽ_μ`; the
`y`-derivative of the cutoff-source identity 4202-4216; `sep:young` 3633-3648 with `j = 1`). -/
def WardDYYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ j : Fin 3, YoungL2Le c ν R C (fun τ => physPd (wardY ν μ R c χy g τ) j) g

/-- **The ordinary `L^∞_τL^∞_y` bound of `DX` on the young support** (source 5238-5244: the
pressure term `(DX + DXᵀ)∇p` pairs the `Y₂` bound of `∇p` with this bound; for old `L²` data it is
Cauchy-Schwarz in `sep:resolvent` 3621-3629 over `(λ, z)`: the gradient kernel
`|D∇K_t| ≤ C|y - λz|^{-5}` (`sep:kernel` 3603-3611) is square integrable across the radial gap
`D = R√ν(1 - √(5/6))`, and `∫_0^∞ e^{-at}‖T(τ - t)‖²_{L²}dt` is a geometric sum of one-period
`L²_τL²` norms since `T` is `P`-periodic, `a > 0` for `μ > -1/4`; the stream cutoff and the
primitive `Ψ` are bounded the same way, 3687-3713). -/
def WardDXYoungSup : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y → ∀ j : Fin 3,
        ‖physPd (wardX ν μ R c χy g τ) j y‖ ≤ C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal

/-! ## 3. Chart points -/

theorem wyl_ϱ_chartY {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    ϱ (NearInst.chartY R q) = R / Real.sqrt q.1 := by
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.mpr hs
  have hy0 : (NearInst.chartY R q) 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
  have hy1 : (NearInst.chartY R q) 1 = 0 := by simp [NearInst.chartY]
  unfold ϱ
  rw [hy0, hy1, show (R / Real.sqrt q.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt q.1) ^ 2 by ring]
  exact Real.sqrt_sq (div_pos hR hsq).le

theorem wyl_age_chartY {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    age R (NearInst.chartY R q) = q.1 := by
  unfold age
  rw [wyl_ϱ_chartY hR hs, div_pow, Real.sq_sqrt hs.le]
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  field_simp

/-- A young chart point lies in the young receiver region `ϱ ≥ R√ν`. -/
theorem wyl_young_ϱ {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {q : Chart} (hs : 0 < q.1)
    (hq : ν * q.1 ≤ 1) : R * Real.sqrt ν ≤ ϱ (NearInst.chartY R q) := by
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.mpr hs
  rw [wyl_ϱ_chartY hR hs, le_div_iff₀ hsq, mul_assoc, ← Real.sqrt_mul hν.le]
  have h1 : Real.sqrt (ν * q.1) ≤ 1 := Real.sqrt_le_one.mpr hq
  nlinarith

theorem wyl_youngRead_of_young {ν R : ℝ} (F : ℝ → Space → Space) {q : Chart}
    (hq : ν * q.1 ≤ 1) :
    wardYoungRead ν R F q =
      (Real.sqrt q.1)⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ := by
  unfold wardYoungRead
  rw [indicator_of_mem (show q ∈ wardYoungSet ν from hq)]

theorem wyl_youngRead_nonneg (ν R : ℝ) (F : ℝ → Space → Space) (q : Chart) :
    0 ≤ wardYoungRead ν R F q := by
  unfold wardYoungRead
  refine indicator_nonneg (fun q _ => ?_) q
  exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (norm_nonneg _)

theorem wyl_youngRead_zero_of_nonpos {ν R : ℝ} (F : ℝ → Space → Space) {q : Chart}
    (hs : q.1 ≤ 0) : wardYoungRead ν R F q = 0 := by
  unfold wardYoungRead
  have h0 : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 hs
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, h0, inv_zero, zero_mul]
  · rw [indicator_of_notMem hq]

/-! ## 4. The chart coefficient against the chart reading -/

theorem wyl_merid_norm_le (v : Space) : ‖(!₂[v 0, v 2] : Merid)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [sq_nonneg (v 1)]

/-- `|coefOf R F q| ≤ s^{-1/2}|F(chartTau R q, chartY R q)|`. -/
theorem wyl_coefOf_norm_le (R : ℝ) (F : ℝ → Space → Space) (q : Chart) :
    ‖coefOf R F q‖ ≤
      (Real.sqrt q.1)⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ := by
  unfold coefOf
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left (wyl_merid_norm_le _) (inv_nonneg.2 (Real.sqrt_nonneg _))

/-- **Domination of the chart coefficient** (case split): if the physical field vanishes at the
chart points with `νs > 1` and is dominated on the young chart points, then the chart coefficient
is dominated everywhere (for `s ≤ 0` the prefactor `(√s)⁻¹` vanishes). -/
theorem wyl_coefOf_le {ν R : ℝ} {F : ℝ → Space → Space} {B : Chart → ℝ} (hB0 : ∀ q, 0 ≤ B q)
    (hzero : ∀ q : Chart, 1 < ν * q.1 → F (NearInst.chartTau R q) (NearInst.chartY R q) = 0)
    (hyoung : ∀ q : Chart, 0 < q.1 → ν * q.1 ≤ 1 →
      (Real.sqrt q.1)⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ ≤ B q)
    (q : Chart) : ‖coefOf R F q‖ ≤ B q := by
  refine le_trans (wyl_coefOf_norm_le R F q) ?_
  by_cases hs : 0 < q.1
  · by_cases hq : ν * q.1 ≤ 1
    · exact hyoung q hs hq
    · rw [hzero q (not_le.1 hq), norm_zero, mul_zero]
      exact hB0 q
  · have h0 : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hs)
    rw [h0, inv_zero, zero_mul]
    exact hB0 q

/-! ## 5. Young support of the Ward fields at chart points -/

section Support

variable {ν μ R c : ℝ} {χy : ℝ → ℝ}

theorem wyl_old_pos (hν : 0 < ν) {q : Chart} (hq : 1 < ν * q.1) : 0 < q.1 := by
  by_contra h
  have h' : q.1 ≤ 0 := not_lt.mp h
  nlinarith

/-- On `νs > 1`, near the chart point the displacement vanishes at every phase (source
4306-4311). -/
theorem wyl_X_zero_nhds (hν : 0 < ν) (hR : 0 < R) (hχy : IsYoungCutoff χy) (g : Chart → Ten3)
    {q : Chart} (hq : 1 < ν * q.1) :
    ∀ᶠ y in 𝓝 (NearInst.chartY R q), ∀ t : ℝ,
      wardX ν μ R c χy g t =ᶠ[𝓝 y] fun _ => (0 : Space) := by
  have hs := wyl_old_pos hν hq
  set y₀ := NearInst.chartY R q
  have hϱ : 0 < ϱ y₀ := by
    rw [wyl_ϱ_chartY hR hs]
    exact div_pos hR (Real.sqrt_pos.mpr hs)
  have hage : 1 < ν * age R y₀ := by rw [wyl_age_chartY hR hs]; exact hq
  have hc1 : ContinuousAt (fun y => ν * age R y) y₀ := by
    unfold age
    exact continuousAt_const.mul
      (continuousAt_const.div (continuous_ϱ.continuousAt.pow 2) (pow_pos hϱ 2).ne')
  have hev1 : ∀ᶠ y in 𝓝 y₀, 1 < ν * age R y := continuousAt_const.eventually_lt hc1 hage
  have hev2 : ∀ᶠ y in 𝓝 y₀, 0 < ϱ y :=
    continuousAt_const.eventually_lt continuous_ϱ.continuousAt hϱ
  filter_upwards [hev1, hev2] with y hy1 hy2 t
  exact wyp_at ν μ R c hχy g hy2 hy1 t

/-- On `νs > 1`, near the chart point `Y = D_{μ+1}X` vanishes at every phase. -/
theorem wyl_Y_zero_nhds (hν : 0 < ν) (hR : 0 < R) (hχy : IsYoungCutoff χy) (g : Chart → Ten3)
    {q : Chart} (hq : 1 < ν * q.1) (τ : ℝ) :
    wardY ν μ R c χy g τ =ᶠ[𝓝 (NearInst.chartY R q)] fun _ => (0 : Space) := by
  filter_upwards [wyl_X_zero_nhds (μ := μ) (c := c) hν hR hχy g hq] with y hy
  exact wyp_physDmu_zero ν (μ + 1) hy τ

end Support

/-! ## 6. Change of measure (Lemma A) -/

/-- **Lemma A** (source 2683-2689, 3875, 5117): for a chart field vanishing on `νs > 1`, the gained
body norm `L²(π g⁻²s^{-3/2}dς)` is at most `√(π e^{2|γ|/ν})` times the `L²(s^{-3/2}dς)` norm. -/
theorem wyl_eLpNorm_body_le {E : Type*} [NormedAddCommGroup E] (c γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    {F : Chart → E} (hF : ∀ q : Chart, 1 < ν * q.1 → F q = 0) :
    eLpNorm F 2 (bodyMeasure c γ ν) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * Real.exp (2 * |γ| / ν))) *
        eLpNorm F 2 (ageμ c (-3 / 2)) := by
  set S : Set Chart := wardYoungSet ν with hSdef
  have hSm : MeasurableSet S := by
    have hf : Measurable fun p : Chart => ν * p.1 := measurable_fst.const_mul ν
    exact measurableSet_le hf measurable_const
  have hsupp : Function.support F ⊆ S := by
    intro q hq
    by_contra h
    exact hq (hF q (not_le.1 h))
  set K : ℝ := Real.pi * Real.exp (2 * |γ| / ν) with hK
  have hK0 : 0 ≤ K := mul_nonneg Real.pi_pos.le (Real.exp_pos _).le
  -- the restricted body measure is dominated by `K` times the restricted age measure
  have hle : (bodyMeasure c γ ν).restrict S ≤ ENNReal.ofReal K • (ageμ c (-3 / 2)).restrict S := by
    refine Measure.le_iff.2 fun A hA => ?_
    have hdens : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
      have hg : Measurable (ginv γ ν) := by
        have h1 : Measurable fun p : Chart => max p.1 0 := measurable_fst.max measurable_const
        have h2 : Measurable fun p : Chart => γ * max p.1 0 / (1 + ν * max p.1 0) :=
          (measurable_const.mul h1).div (measurable_const.add (measurable_const.mul h1))
        have h3 : Measurable fun p : Chart => UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) :=
          Real.continuous_exp.measurable.comp h2
        exact h3.inv
      exact (measurable_const.mul (hg.pow_const 2)).ennreal_ofReal
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
      bodyMeasure, withDensity_apply _ (hA.inter hSm)]
    calc ∫⁻ p in A ∩ S, ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ _ in A ∩ S, ENNReal.ofReal K ∂(ageμ c (-3 / 2)) := by
          refine setLIntegral_mono measurable_const fun p hp => ?_
          have hp' : ν * p.1 ≤ 1 := hp.2
          have hm0 : 0 ≤ max p.1 0 := le_max_right _ _
          have hνm : ν * max p.1 0 ≤ 1 := by
            rcases le_total 0 p.1 with h | h
            · rw [max_eq_left h]; exact hp'
            · rw [max_eq_right h, mul_zero]; exact zero_le_one
          have hpos : 0 < 1 + ν * max p.1 0 := by nlinarith [mul_nonneg hν.le hm0]
          have hden : 1 ≤ 1 + ν * max p.1 0 := by nlinarith [mul_nonneg hν.le hm0]
          have ht : |γ * max p.1 0 / (1 + ν * max p.1 0)| ≤ |γ| / ν := by
            rw [abs_div, abs_mul, abs_of_nonneg hm0, abs_of_pos hpos]
            refine le_trans (div_le_self (mul_nonneg (abs_nonneg γ) hm0) hden) ?_
            rw [le_div_iff₀ hν]
            nlinarith [abs_nonneg γ, mul_le_mul_of_nonneg_left hνm (abs_nonneg γ)]
          have hE : ginv γ ν p = Real.exp (-(γ * max p.1 0 / (1 + ν * max p.1 0))) := by
            simp only [ginv, UnforcedLeray.Short.IIIa.gainG, Real.exp_neg]
          have h1 : Real.exp (-(γ * max p.1 0 / (1 + ν * max p.1 0))) ≤ Real.exp (|γ| / ν) :=
            Real.exp_le_exp.mpr (le_trans (neg_le_abs _) ht)
          have h2 : ginv γ ν p ^ 2 ≤ Real.exp (2 * |γ| / ν) := by
            rw [hE]
            calc Real.exp (-(γ * max p.1 0 / (1 + ν * max p.1 0))) ^ 2
                ≤ Real.exp (|γ| / ν) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le h1 2
              _ = Real.exp (2 * |γ| / ν) := by
                rw [sq, ← Real.exp_add]; congr 1; ring
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 Real.pi_pos.le)
      _ = ENNReal.ofReal K * (ageμ c (-3 / 2)) (A ∩ S) := setLIntegral_const _ _
  calc eLpNorm F 2 (bodyMeasure c γ ν)
      = eLpNorm F 2 ((bodyMeasure c γ ν).restrict S) :=
        (eLpNorm_restrict_eq_of_support_subset hsupp).symm
    _ ≤ eLpNorm F 2 (ENNReal.ofReal K • (ageμ c (-3 / 2)).restrict S) :=
        eLpNorm_mono_measure F hle
    _ = ENNReal.ofReal K ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm F 2 ((ageμ c (-3 / 2)).restrict S) :=
        eLpNorm_smul_measure_of_ne_top (by norm_num) F _
    _ = ENNReal.ofReal (Real.sqrt K) * eLpNorm F 2 (ageμ c (-3 / 2)) := by
        rw [eLpNorm_restrict_eq_of_support_subset hsupp, smul_eq_mul]
        congr 1
        rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]
        norm_num

/-- `‖·‖_{L²(srcMeasure c)} = √π ‖·‖_{L²(s^{-3/2}dς)}`. -/
theorem wyl_eLpNorm_src {E : Type*} [NormedAddCommGroup E] (c : ℝ) (F : Chart → E) :
    eLpNorm F 2 (srcMeasure c) =
      ENNReal.ofReal (Real.sqrt Real.pi) * eLpNorm F 2 (ageμ c (-3 / 2)) := by
  rw [srcMeasure, eLpNorm_smul_measure_of_ne_top (by norm_num) F _, smul_eq_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg Real.pi_pos.le (by norm_num)]
  norm_num

/-! ## 7. Bookkeeping of the bounds `K‖g‖` -/

/-- `f` is measurable with `‖f‖_{L²(m)} ≤ K·N`. -/
def WylBd (m : Measure Chart) (N : ℝ≥0∞) (f : Chart → ℝ) (K : ℝ) : Prop :=
  AEStronglyMeasurable f m ∧ eLpNorm f 2 m ≤ ENNReal.ofReal K * N

theorem WylBd.add {m : Measure Chart} {N : ℝ≥0∞} {f g : Chart → ℝ} {K₁ K₂ : ℝ}
    (h1 : WylBd m N f K₁) (h2 : WylBd m N g K₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    WylBd m N (fun q => f q + g q) (K₁ + K₂) := by
  refine ⟨h1.1.add h2.1, ?_⟩
  calc eLpNorm (fun q => f q + g q) 2 m = eLpNorm (f + g) 2 m := rfl
    _ ≤ eLpNorm f 2 m + eLpNorm g 2 m := eLpNorm_add_le h1.1 h2.1 one_le_two
    _ ≤ ENNReal.ofReal K₁ * N + ENNReal.ofReal K₂ * N := add_le_add h1.2 h2.2
    _ = ENNReal.ofReal (K₁ + K₂) * N := by rw [← add_mul, ENNReal.ofReal_add hK₁ hK₂]

theorem WylBd.const_mul {m : Measure Chart} {N : ℝ≥0∞} {f : Chart → ℝ} {K : ℝ}
    (h : WylBd m N f K) (a : ℝ) :
    WylBd m N (fun q => a * f q) (|a| * K) := by
  refine ⟨h.1.const_mul a, ?_⟩
  calc eLpNorm (fun q => a * f q) 2 m = eLpNorm (a • f) 2 m := rfl
    _ = ‖a‖ₑ * eLpNorm f 2 m := eLpNorm_const_smul a f 2 m
    _ ≤ ‖a‖ₑ * (ENNReal.ofReal K * N) := mul_le_mul' le_rfl h.2
    _ = ENNReal.ofReal (|a| * K) * N := by
        rw [← mul_assoc, ENNReal.ofReal_mul (abs_nonneg a), Real.enorm_eq_ofReal_abs]

theorem WylBd.mono_K {m : Measure Chart} {N : ℝ≥0∞} {f : Chart → ℝ} {K K' : ℝ}
    (h : WylBd m N f K) (hK : K ≤ K') : WylBd m N f K' :=
  ⟨h.1, h.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hK) le_rfl)⟩

theorem WylBd.sum {m : Measure Chart} {N : ℝ≥0∞} {ι : Type*} (s : Finset ι)
    {f : ι → Chart → ℝ} {K : ι → ℝ} (hK : ∀ i, 0 ≤ K i) (h : ∀ i ∈ s, WylBd m N (f i) (K i)) :
    WylBd m N (fun q => ∑ i ∈ s, f i q) (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨aestronglyMeasurable_const, ?_⟩
    simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h3 := h1.add h2 (hK a) (Finset.sum_nonneg fun i _ => hK i)
    simp only [Finset.sum_insert ha]
    exact h3

/-- From `YoungL2Le` to `WylBd` with a nonnegative constant. -/
theorem wyl_bd_of_young {c ν R C : ℝ} {F : ℝ → Space → Space} {g : Chart → Ten3}
    (h : YoungL2Le c ν R C F g) :
    WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2))) (wardYoungRead ν R F) (max C 0) :=
  ⟨h.1, h.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)⟩

/-! ## 8. Pointwise calculus -/

theorem wyl_vec_expand (v : Space) : v = ∑ k : Fin 3, v k • coordinateVector k := by
  ext i
  simp [coordinateVector, Pi.single_apply]

theorem wyl_norm_coordinateVector (k : Fin 3) : ‖coordinateVector k‖ = 1 := by
  simp [coordinateVector]

theorem wyl_abs_apply_le (v : Space) (k : Fin 3) : |v k| ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le v k
  simpa [Real.norm_eq_abs] using h

/-- `Df(y)v = Σ_k v_k ∂_kf(y)` (linearity of `fderiv ℝ f y`). -/
theorem wyl_fderiv_apply_eq (f : Space → Space) (y v : Space) :
    fderiv ℝ f y v = ∑ k : Fin 3, v k • physPd f k y := by
  conv_lhs => rw [wyl_vec_expand v]
  rw [map_sum]
  simp only [map_smul, physPd]

/-- `|Df(y)v| ≤ Σ_k |v_k||∂_kf(y)|`. -/
theorem wyl_fderiv_apply_norm_le (f : Space → Space) (y v : Space) :
    ‖fderiv ℝ f y v‖ ≤ ∑ k : Fin 3, |v k| * ‖physPd f k y‖ := by
  rw [wyl_fderiv_apply_eq]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_smul, Real.norm_eq_abs]

/-- `|v| ≤ Σ_k |v_k|`. -/
theorem wyl_norm_le_sum_abs (v : Space) : ‖v‖ ≤ ∑ k : Fin 3, |v k| := by
  conv_lhs => rw [wyl_vec_expand v]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_smul, wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs]

end UnforcedLeray.Short.PartIIIb.Concrete
