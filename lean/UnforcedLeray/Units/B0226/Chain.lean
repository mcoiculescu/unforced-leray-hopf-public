import UnforcedLeray.Units.B0226.Defs

/-!
# B0226, part 2: the chain rule `∇ₓ(Φ ∘ chart) = (εr)⁻¹ (D_εΦ e_r + ∂_ηΦ e_z)`

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline: with
`s = r⁻²`, `q = ε⁻¹ log r + τ/(2ε)`, `η = z/(εr)` (B0220, tex lines 3283–3287),
`∂_r = (εr)⁻¹ (∂_q − εK)` and `∂_z = (εr)⁻¹ ∂_η` on profiles, and the chart does not depend on
the azimuth. Hence for a profile `Φ`,
`∇ₓ(Φ ∘ chart) = (εr)⁻¹ (D_εΦ e_r + ∂_ηΦ e_z) = ε⁻¹ a (D_εΦ e_r + ∂_ηΦ e_z)` off the axis
(`gradX_comp_chart`).

* A profile test `Φ` composed with the chart is a physical test of `ℝ³ × period`
  (`isPhysTest_comp_chart`, `physTestOfProfile`): it is smooth (it vanishes near the axis), it is
  `2εc`-periodic in `τ` (one period shifts `q` by one cell, B0220 `chart_add_period`), and it
  vanishes for large `|x|`.
* Its gradient is a multiple of the lift of the profile gradient:
  `∇ₓ(Φ ∘ chart) = (ε c_J)⁻¹ J_ε (D_εΦ, ∂_ηΦ)` in `L²(dx dτ)`, where `c_J = (√(2π) ε)⁻¹` is the
  constant of `J_ε` (`physGrad_physTestOfProfile`). Since `J_ε` is an isometry,
  `⟪J_ε b, ∇ₓ(Φ ∘ chart)⟫_{L²(dx dτ)} = (ε c_J)⁻¹ ⟪b, (D_εΦ, ∂_ηΦ)⟫_H`
  (`inner_J_physGrad`): this is the change of variables of the distributional divergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

theorem radius_eq_ϱ (x : Space) : radius x = Axi.ϱ x := rfl

theorem notMem_axis {x : Space} (hx : radius x ≠ 0) : x ∉ Axi.axis := by
  rw [Axi.mem_axis_iff]
  exact hx

/-- The chart written with products and inverses only. -/
def chartM (ε : ℝ) (y : Space × ℝ) : Profile :=
  ((radius y.1 ^ 2)⁻¹, ε⁻¹ * Real.log (radius y.1) + y.2 * (2 * ε)⁻¹,
    y.1 2 * (ε * radius y.1)⁻¹)

theorem chart_eq_chartM (ε : ℝ) : chart ε = chartM ε := by
  funext y
  simp only [chart, chartM, ageS, cellQ, etaCoord, div_eq_mul_inv]

/-- The `x`-derivative of the chart, `Dchart(x,τ)(w, 0)`, against a profile derivative. -/
theorem fderiv_comp_chart_apply {ε : ℝ} (hε : ε ≠ 0) {Φ : Profile → ℝ} {y : Space × ℝ}
    (hr : radius y.1 ≠ 0) (hΦ : DifferentiableAt ℝ Φ (chart ε y)) (w : Space) :
    fderiv ℝ (fun y => Φ (chart ε y)) y (w, 0) =
      (-(2 * radius y.1 * Axi.ϱD y.1 w) / (radius y.1 ^ 2) ^ 2) * Axi.dS Φ (chart ε y) +
      (ε⁻¹ * ((radius y.1)⁻¹ * Axi.ϱD y.1 w)) * Axi.dQ Φ (chart ε y) +
      (w 2 * (ε * radius y.1)⁻¹ +
        y.1 2 * (-((ε * radius y.1) ^ 2)⁻¹ * (ε * Axi.ϱD y.1 w))) * Axi.dEta Φ (chart ε y) := by
  rw [chart_eq_chartM] at hΦ ⊢
  have hρ : HasFDerivAt (fun y : Space × ℝ => radius y.1)
      ((Axi.ϱD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) y :=
    (Axi.hasFDerivAt_ϱ (notMem_axis hr)).comp y hasFDerivAt_fst
  have hs : HasFDerivAt (fun y : Space × ℝ => (radius y.1 ^ 2)⁻¹)
      ((-((radius y.1 ^ 2) ^ 2)⁻¹) • ((2 • radius y.1 ^ (2 - 1)) •
        (Axi.ϱD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))) y :=
    (hasDerivAt_inv (pow_ne_zero 2 hr)).comp_hasFDerivAt y (hρ.pow 2)
  have hq : HasFDerivAt (fun y : Space × ℝ => ε⁻¹ * Real.log (radius y.1) + y.2 * (2 * ε)⁻¹)
      (ε⁻¹ • ((radius y.1)⁻¹ • (Axi.ϱD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) +
        (2 * ε)⁻¹ • ContinuousLinearMap.snd ℝ Space ℝ) y :=
    ((hρ.log hr).const_mul ε⁻¹).add (hasFDerivAt_snd.mul_const _)
  have hz : HasFDerivAt (fun y : Space × ℝ => y.1 2)
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ Space ℝ)) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hasFDerivAt_fst
  have hinv : HasFDerivAt (fun y : Space × ℝ => (ε * radius y.1)⁻¹)
      ((-((ε * radius y.1) ^ 2)⁻¹) •
        (ε • (Axi.ϱD y.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))) y :=
    (hasDerivAt_inv (mul_ne_zero hε hr)).comp_hasFDerivAt y (hρ.const_mul ε)
  have hη := hz.mul hinv
  have hchart : HasFDerivAt (chartM ε) _ y := hs.prodMk (hq.prodMk hη)
  have hcomp := hΦ.hasFDerivAt.comp y hchart
  rw [show (fun y => Φ (chartM ε y)) = Φ ∘ chartM ε from rfl, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', EuclideanSpace.coe_proj,
    smul_eq_mul, mul_zero, add_zero, nsmul_eq_mul]
  rw [Axi.clm_triple]
  simp only [Axi.dS, Axi.dQ, Axi.dEta, smul_eq_mul]
  simp only [Nat.cast_ofNat]
  ring

theorem inner_unitR (x : Space) (w : Space) :
    ⟪unitR x, w⟫_ℝ = x 0 / radius x * w 0 + x 1 / radius x * w 1 := by
  simp only [unitR, inner_add_left, inner_smul_left, EuclideanSpace.inner_single_left,
    conj_trivial, one_mul]

theorem inner_unitZ (w : Space) : ⟪unitZ, w⟫_ℝ = w 2 := by
  simp only [unitZ, EuclideanSpace.inner_single_left, conj_trivial, one_mul]

/-- **Chain rule** (tex lines 3394–3402, proof outline): off the axis,
`∇ₓ(Φ ∘ chart)(x,τ) = ε⁻¹ a (D_εΦ e_r + ∂_ηΦ e_z)` at `(s,q,η) = chart(x,τ)`, `a = 1/r`. -/
theorem gradX_comp_chart {ε : ℝ} (hε : ε ≠ 0) {Φ : Profile → ℝ} {y : Space × ℝ}
    (hr : radius y.1 ≠ 0) (hΦ : DifferentiableAt ℝ Φ (chart ε y)) :
    gradX (fun y => Φ (chart ε y)) y =
      (ε⁻¹ * liftA y.1) • frame y.1 (profileGrad ε Φ (chart ε y)) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradX, fderiv_comp_chart_apply hε hr hΦ w, real_inner_smul_left, frame_apply,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_unitR, inner_unitZ,
    profileGrad_zero, profileGrad_one, Axi.ϱD_apply]
  rw [← radius_eq_ϱ]
  simp only [Deps, Kop, liftA, chart, ageS, etaCoord]
  field_simp
  ring

/-! ### Profile tests give physical tests -/

theorem continuous_radius_fst : Continuous fun y : Space × ℝ => radius y.1 :=
  continuous_radius.comp continuous_fst

theorem contDiffOn_chart {ε : ℝ} (hε : ε ≠ 0) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (chart ε) {y : Space × ℝ | radius y.1 ≠ 0} := by
  rw [chart_eq_chartM]
  have hρ : ContDiffOn ℝ n (fun y : Space × ℝ => radius y.1) {y | radius y.1 ≠ 0} :=
    Axi.contDiffOn_ϱ.comp contDiff_fst.contDiffOn fun y hy => notMem_axis hy
  have hs : ContDiffOn ℝ n (fun y : Space × ℝ => (radius y.1 ^ 2)⁻¹) {y | radius y.1 ≠ 0} :=
    (hρ.pow 2).inv fun y hy => pow_ne_zero 2 hy
  have hq : ContDiffOn ℝ n
      (fun y : Space × ℝ => ε⁻¹ * Real.log (radius y.1) + y.2 * (2 * ε)⁻¹)
      {y | radius y.1 ≠ 0} :=
    (contDiffOn_const.mul (hρ.log fun y hy => hy)).add
      (contDiff_snd.contDiffOn.mul contDiffOn_const)
  have hz : ContDiff ℝ n (fun y : Space × ℝ => y.1 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_fst
  have hη : ContDiffOn ℝ n (fun y : Space × ℝ => y.1 2 * (ε * radius y.1)⁻¹)
      {y | radius y.1 ≠ 0} :=
    hz.contDiffOn.mul ((contDiffOn_const.mul hρ).inv fun y hy => mul_ne_zero hε hy)
  exact hs.prodMk (hq.prodMk hη)

/-- A profile test composed with the chart is smooth on `ℝ³ × ℝ`: near the axis it vanishes. -/
theorem contDiff_comp_chart {ε c : ℝ} (hε : ε ≠ 0) {Φ : Profile → ℝ}
    (hΦ : IsProfileTest c Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Φ (chart ε y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hr : radius y.1 = 0
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
    set M : ℝ := max s0 s1 with hM
    have hMpos : 0 < M := lt_max_of_lt_left hs0
    have hW : IsOpen {y' : Space × ℝ | radius y'.1 ^ 2 < M⁻¹} :=
      isOpen_lt (continuous_radius_fst.pow 2) continuous_const
    have hyW : y ∈ {y' : Space × ℝ | radius y'.1 ^ 2 < M⁻¹} := by
      simp only [mem_setOf_eq, hr]
      norm_num
      exact hMpos
    refine contDiffAt_const (c := (0 : ℝ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [hW.mem_nhds hyW] with y' hy'
    by_contra hne
    obtain ⟨⟨h1, h2⟩, -⟩ := hb _ hne
    simp only [chart, ageS] at h1 h2
    have hpos : 0 < radius y'.1 ^ 2 := by
      rcases (sq_nonneg (radius y'.1)).lt_or_eq with h | h
      · exact h
      · rw [← h, inv_zero] at h1
        linarith
    have hle : (radius y'.1 ^ 2)⁻¹ ≤ M := h2.trans (le_max_right _ _)
    rw [inv_le_comm₀ hpos hMpos] at hle
    exact absurd hy' (not_lt.2 hle)
  · exact (hΦ.smooth.comp_contDiffOn (contDiffOn_chart hε)).contDiffAt
      ((isOpen_ne_fun continuous_radius_fst continuous_const).mem_nhds hr)

theorem bounded_comp_chart {ε c : ℝ} (hε : ε ≠ 0) {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) :
    ∃ R : ℝ, ∀ y : Space × ℝ, Φ (chart ε y) ≠ 0 → ‖y.1‖ ≤ R := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  refine ⟨√(s0⁻¹ * (1 + ε ^ 2 * L ^ 2)), fun y hy => ?_⟩
  obtain ⟨⟨h1, -⟩, h3⟩ := hb _ hy
  simp only [chart, ageS, etaCoord] at h1 h3
  have hpos : 0 < radius y.1 ^ 2 := by
    rcases (sq_nonneg (radius y.1)).lt_or_eq with h | h
    · exact h
    · rw [← h, inv_zero] at h1
      linarith
  have hr : radius y.1 ≠ 0 := fun h => by simp [h] at hpos
  have hr2 : radius y.1 ^ 2 ≤ s0⁻¹ := by
    rwa [le_inv_comm₀ hs0 hpos] at h1
  have hη2 : (y.1 2 / (ε * radius y.1)) ^ 2 ≤ L ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hz2 : y.1 2 ^ 2 ≤ ε ^ 2 * radius y.1 ^ 2 * L ^ 2 := by
    have : y.1 2 = ε * radius y.1 * (y.1 2 / (ε * radius y.1)) := by
      field_simp
    rw [this, mul_pow]
    calc (ε * radius y.1) ^ 2 * (y.1 2 / (ε * radius y.1)) ^ 2
          ≤ (ε * radius y.1) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hη2 (by positivity)
      _ = ε ^ 2 * radius y.1 ^ 2 * L ^ 2 := by ring
  have hn : ‖y.1‖ ^ 2 = radius y.1 ^ 2 + y.1 2 ^ 2 := Axi.norm_sq_eq_ϱ_sq_add y.1
  rw [← abs_norm]
  refine Real.abs_le_sqrt ?_
  rw [hn]
  nlinarith [sq_nonneg ε, sq_nonneg L, mul_le_mul_of_nonneg_left hr2 (by positivity :
    (0 : ℝ) ≤ ε ^ 2 * L ^ 2)]

end UnforcedLeray.B0226
