import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.HeatTaylor2
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.DilationTaylor1
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.DilationTaylor2

/-!
# Part II-a, task `PartII-a:F02/7`: quantitative second-order generator bound for the adjoint

Source of record: `the November 2 reference manuscript`, lines 1363-1370.

This file proves the Prop `AdjointTaylor` of `Sub/F02.lean`. With `e = e^{-r}`,
`δ = e^{-r/2}`, `σ = ν(1-e)`, `w = e^{σΔ}u`, the pointwise identity

`S'(r)u - u - r A^t u = e·(w - u - σΔu)(δ·) + (eσ)(Δu(δ·) - Δu) + (eσ - rν)Δu
  + e(u(δ·) - u - (δ-1)∇u·y) + (e(δ-1) + r/2)∇u·y + (e-1+r)u`

splits the remainder into six terms. Each is bounded in `L^p` by `C M r²`: the first by
`heatTaylor2` and the dilation scaling, the second and fourth by `dilationTaylor1` and
`dilationTaylor2`, and the rest by scalar Taylor bounds and the ball bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Scaling of an `L^p` norm by a dilation with factor `δ ∈ [1/2, 1]`. -/
theorem at_scale {g : SpatialField} {δ : ℝ} (hδ1 : 1 / 2 ≤ δ) (hδ2 : δ ≤ 1) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    eLpNorm (fun y : Space => g (δ • y)) p volume ≤ ENNReal.ofReal 8 * eLpNorm g p volume := by
  have hδpos : 0 < δ := by linarith
  have hδ0 : δ ≠ 0 := hδpos.ne'
  rw [B0418.eLpNorm_comp_dilation hp hδ0 g]
  refine mul_le_mul' ?_ le_rfl
  have hd2 : 1 / 4 ≤ δ ^ 2 := by nlinarith
  have h3 : 1 / 8 ≤ δ ^ 3 := by nlinarith
  have hinv : (δ ^ 3)⁻¹ ≤ 8 := by
    rw [inv_eq_one_div, div_le_iff₀ (pow_pos hδpos 3)]
    linarith
  have hA : ENNReal.ofReal |(δ ^ 3)⁻¹| ≤ ENNReal.ofReal 8 := by
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (inv_nonneg.2 (pow_pos hδpos 3).le)]
    exact hinv
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 8 := ENNReal.one_le_ofReal.2 (by norm_num)
  have ht1 : (1 / p).toReal ≤ 1 := by
    have h1 : 1 / p ≤ 1 := by
      rw [one_div]
      exact ENNReal.inv_le_one.2 hp1
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    simpa using this
  calc (ENNReal.ofReal |(δ ^ 3)⁻¹|) ^ (1 / p).toReal
      ≤ (ENNReal.ofReal 8) ^ (1 / p).toReal :=
        ENNReal.rpow_le_rpow hA ENNReal.toReal_nonneg
    _ ≤ (ENNReal.ofReal 8) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hone ht1
    _ = ENNReal.ofReal 8 := ENNReal.rpow_one _

/-- The `L^p` norm of a function vanishing off a ball, bounded by its sup bound. -/
theorem at_ball {g : SpatialField} {Rp eta : ℝ} (p : ℝ≥0∞)
    (hsupp : ∀ y : Space, Rp < ‖y‖ → g y = 0) (hb : ∀ y : Space, ‖y‖ ≤ Rp → ‖g y‖ ≤ eta) :
    eLpNorm g p volume ≤
      ENNReal.ofReal ((volume (Metric.closedBall (0 : Space) Rp) ^ p.toReal⁻¹).toReal * eta) := by
  have h := dilationTaylor1_ball_bound g Rp eta hsupp hb p
  have hne : volume (Metric.closedBall (0 : Space) Rp) ^ p.toReal⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) measure_closedBall_lt_top.ne
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]
  exact h

/-- Scalar multiples: `‖c f‖_p ≤ X Y` when `|c| ≤ X` and `‖f‖_p ≤ Y`. -/
theorem at_smul {f : SpatialField} {p : ℝ≥0∞} {c X Y : ℝ} (hX : 0 ≤ X) (hc : |c| ≤ X)
    (hf : eLpNorm f p volume ≤ ENNReal.ofReal Y) :
    eLpNorm (fun y : Space => c • f y) p volume ≤ ENNReal.ofReal (X * Y) := by
  have h2 : ‖c‖ₑ ≤ ENNReal.ofReal X := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hc
  calc eLpNorm (fun y : Space => c • f y) p volume = ‖c‖ₑ * eLpNorm f p volume :=
        eLpNorm_const_smul c f p volume
    _ ≤ ENNReal.ofReal X * ENNReal.ofReal Y := mul_le_mul' h2 hf
    _ = ENNReal.ofReal (X * Y) := (ENNReal.ofReal_mul hX).symm

/-- A six-term sum of nonnegative real bounds. -/
theorem at_ofReal_add6 {a1 a2 a3 a4 a5 a6 : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) :
    ENNReal.ofReal a1 + ENNReal.ofReal a2 + ENNReal.ofReal a3 + ENNReal.ofReal a4 +
      ENNReal.ofReal a5 + ENNReal.ofReal a6 =
    ENNReal.ofReal (a1 + a2 + a3 + a4 + a5 + a6) := by
  have s2 := add_nonneg h1 h2
  have s3 := add_nonneg s2 h3
  have s4 := add_nonneg s3 h4
  have s5 := add_nonneg s4 h5
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add s2 h3, ← ENNReal.ofReal_add s3 h4,
    ← ENNReal.ofReal_add s4 h5, ← ENNReal.ofReal_add s5 h6]

/-- A function vanishing off the ball of radius `R` has zero support outside it. -/
theorem at_tsupport_sub {h : SpatialField} {R : ℝ} (hsupp : ∀ y : Space, R < ‖y‖ → h y = 0) :
    tsupport h ⊆ Metric.closedBall (0 : Space) R := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hc
  exact Function.mem_support.mp hy (hsupp y (not_le.mp hc))

theorem at_compact {h : SpatialField} {R : ℝ} (hsupp : ∀ y : Space, R < ‖y‖ → h y = 0) :
    HasCompactSupport h :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) R) (isClosed_tsupport h)
    (at_tsupport_sub hsupp)

theorem at_lap_zero {h : SpatialField} {R : ℝ} (hsupp : ∀ y : Space, R < ‖y‖ → h y = 0)
    {x : Space} (hx : R < ‖x‖) : B0418.vecLaplacian h x = 0 := by
  apply B0418.vecLaplacian_eq_zero
  intro hmem
  have := at_tsupport_sub hsupp hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

set_option maxHeartbeats 1600000 in
/-- **Quantitative second-order generator bound for the adjoint** (task `PartII-a:F02/7`):
proves the Prop `AdjointTaylor`. -/
theorem adjointTaylor : UnforcedLeray.Short.PartIIa.AdjointTaylor := by
  intro ν R p hν hp1 hp
  obtain ⟨C1, hC1, hD1⟩ := dilationTaylor1 R p hp1 hp
  obtain ⟨C2, hC2, hD2⟩ := dilationTaylor2 R p hp1 hp
  obtain ⟨Rp, hRp_def⟩ : ∃ Rp : ℝ, Rp = max R 0 := ⟨_, rfl⟩
  have hRp0 : 0 ≤ Rp := by rw [hRp_def]; exact le_max_right _ _
  have hRR : R ≤ Rp := by rw [hRp_def]; exact le_max_left _ _
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ,
      K = (volume (Metric.closedBall (0 : Space) Rp) ^ p.toReal⁻¹).toReal := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK_def]; exact ENNReal.toReal_nonneg
  have a1 : 0 ≤ ν ^ 2 * K := mul_nonneg (sq_nonneg ν) hK0
  have a2 : 0 ≤ ν * C1 := mul_nonneg hν.le hC1
  have a3 : 0 ≤ ν * K := mul_nonneg hν.le hK0
  have a4 : 0 ≤ K * Rp := mul_nonneg hK0 hRp0
  refine ⟨4 * ν ^ 2 * K + ν * C1 / 2 + 2 * ν * K + C2 / 4 + K * Rp + K, ?_, ?_⟩
  · linarith
  intro M u hu hsupp hbd r hr0 hr1
  have hu0 : ∀ y : Space, ‖u y‖ ≤ M := fun y => (hbd y).1
  have hDu1 : ∀ y : Space, ‖fderiv ℝ u y‖ ≤ M := fun y => (hbd y).2.1
  have hD2bd : ∀ y : Space, ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M := fun y => (hbd y).2.2.1
  have hL0 : ∀ y : Space, ‖B0418.vecLaplacian u y‖ ≤ M := fun y => (hbd y).2.2.2.1
  have hL1 : ∀ y : Space, ‖fderiv ℝ (B0418.vecLaplacian u) y‖ ≤ M := fun y => (hbd y).2.2.2.2.1
  have hL2 : ∀ y : Space, ‖B0418.vecLaplacian (B0418.vecLaplacian u) y‖ ≤ M :=
    fun y => (hbd y).2.2.2.2.2
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hu0 0)
  have hΔc : ContDiff ℝ ∞ (B0418.vecLaplacian u) := hT2_contDiff_vecLaplacian hu
  have hcomp : HasCompactSupport u := at_compact hsupp
  -- supports at radius `R` and at radius `Rp`
  have hΔR : ∀ y : Space, R < ‖y‖ → B0418.vecLaplacian u y = 0 :=
    fun y hy => at_lap_zero hsupp hy
  have hDuR : ∀ y : Space, R < ‖y‖ → fderiv ℝ u y y = 0 := by
    intro y hy
    rw [dilationTaylor2_fderiv_zero u R hsupp y hy]
    simp
  have hu_Rp : ∀ y : Space, Rp < ‖y‖ → u y = 0 :=
    fun y hy => hsupp y (lt_of_le_of_lt hRR hy)
  have hΔ_Rp : ∀ y : Space, Rp < ‖y‖ → B0418.vecLaplacian u y = 0 :=
    fun y hy => hΔR y (lt_of_le_of_lt hRR hy)
  have hΔ2_Rp : ∀ y : Space, Rp < ‖y‖ → B0418.vecLaplacian (B0418.vecLaplacian u) y = 0 :=
    fun y hy => at_lap_zero hΔR (lt_of_le_of_lt hRR hy)
  have hDu_Rp : ∀ y : Space, Rp < ‖y‖ → fderiv ℝ u y y = 0 :=
    fun y hy => hDuR y (lt_of_le_of_lt hRR hy)
  -- ball bounds
  have hub : eLpNorm u p volume ≤ ENNReal.ofReal (K * M) := by
    rw [hK_def]; exact at_ball p hu_Rp (fun y _ => hu0 y)
  have hΔb : eLpNorm (B0418.vecLaplacian u) p volume ≤ ENNReal.ofReal (K * M) := by
    rw [hK_def]; exact at_ball p hΔ_Rp (fun y _ => hL0 y)
  have hΔ2b : eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian u)) p volume
      ≤ ENNReal.ofReal (K * M) := by
    rw [hK_def]; exact at_ball p hΔ2_Rp (fun y _ => hL2 y)
  have hDb : eLpNorm (fun y : Space => fderiv ℝ u y y) p volume
      ≤ ENNReal.ofReal (K * (M * Rp)) := by
    rw [hK_def]
    refine at_ball (g := fun y : Space => fderiv ℝ u y y) p hDu_Rp (fun y hy => ?_)
    calc ‖fderiv ℝ u y y‖ ≤ ‖fderiv ℝ u y‖ * ‖y‖ := (fderiv ℝ u y).le_opNorm y
      _ ≤ M * Rp := mul_le_mul (hDu1 y) hy (norm_nonneg y) hM0
  -- scalar facts
  obtain ⟨e, he⟩ : ∃ e : ℝ, Real.exp (-r) = e := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, Real.exp (-r / 2) = δ := ⟨_, rfl⟩
  have hE0 : 0 < e := by rw [← he]; exact Real.exp_pos _
  have hE1 : e ≤ 1 := by rw [← he]; exact Real.exp_le_one_iff.2 (by linarith)
  have hEl : 1 - r ≤ e := by rw [← he]; linarith [Real.add_one_le_exp (-r)]
  have hδl : 1 - r / 2 ≤ δ := by rw [← hδ]; linarith [Real.add_one_le_exp (-r / 2)]
  have hδ1 : δ ≤ 1 := by rw [← hδ]; exact Real.exp_le_one_iff.2 (by linarith)
  have hδ_half : 1 / 2 ≤ δ := by linarith
  have hEx : |e - 1 + r| ≤ r ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -r)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [he, show e - 1 - -r = e - 1 + r by ring, neg_sq] at h
    exact h
  have hDx : |δ - 1 + r / 2| ≤ r ^ 2 / 4 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -r / 2)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hδ, show δ - 1 - -r / 2 = δ - 1 + r / 2 by ring,
      show (-r / 2) ^ 2 = r ^ 2 / 4 by ring] at h
    exact h
  have hσ0 : 0 ≤ ν * (1 - e) := mul_nonneg hν.le (by linarith)
  have hσr : ν * (1 - e) ≤ ν * r := mul_le_mul_of_nonneg_left (by linarith) hν.le
  have hEσ0 : 0 ≤ e * (ν * (1 - e)) := mul_nonneg hE0.le hσ0
  have hEσr : e * (ν * (1 - e)) ≤ ν * r :=
    le_trans (mul_le_of_le_one_left hσ0 hE1) hσr
  have hS5 : |e * (ν * (1 - e)) - r * ν| ≤ 2 * ν * r ^ 2 := by
    have key : e * (ν * (1 - e)) - r * ν = ν * (-(e * (e - 1 + r)) - r * (1 - e)) := by ring
    have hB : |e * (e - 1 + r)| ≤ r ^ 2 := by
      rw [abs_mul, abs_of_pos hE0]
      calc e * |e - 1 + r| ≤ 1 * |e - 1 + r| := mul_le_mul_of_nonneg_right hE1 (abs_nonneg _)
        _ ≤ r ^ 2 := by linarith
    have hB' := abs_le.mp hB
    have hC1' : 0 ≤ r * (1 - e) := mul_nonneg hr0.le (by linarith)
    have hC2' : r * (1 - e) ≤ r ^ 2 := by nlinarith
    have hX : |-(e * (e - 1 + r)) - r * (1 - e)| ≤ 2 * r ^ 2 := by
      rw [abs_le]
      constructor <;> linarith [hB'.1, hB'.2]
    rw [key, abs_mul, abs_of_nonneg hν.le]
    calc ν * |-(e * (e - 1 + r)) - r * (1 - e)| ≤ ν * (2 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hX hν.le
      _ = 2 * ν * r ^ 2 := by ring
  have hS6 : |e * (δ - 1) + r / 2| ≤ r ^ 2 := by
    have key6 : e * (δ - 1) + r / 2 = e * (δ - 1 + r / 2) + (r / 2) * (1 - e) := by ring
    have hD := abs_le.mp hDx
    have hDD1 : e * (δ - 1 + r / 2) ≤ r ^ 2 / 4 := by
      nlinarith [mul_nonneg hE0.le (sub_nonneg.2 hD.2), mul_nonneg (sub_nonneg.2 hE1) (sq_nonneg r)]
    have hDD2 : -(r ^ 2 / 4) ≤ e * (δ - 1 + r / 2) := by
      nlinarith [mul_nonneg hE0.le (by linarith [hD.1] : (0:ℝ) ≤ δ - 1 + r / 2 + r ^ 2 / 4),
        mul_nonneg (sub_nonneg.2 hE1) (sq_nonneg r)]
    have hR1 : (r / 2) * (1 - e) ≤ r ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (show 1 - e ≤ r by linarith)
        (by linarith : (0:ℝ) ≤ r / 2)]
    have hR0 : 0 ≤ (r / 2) * (1 - e) := mul_nonneg (by linarith) (by linarith)
    rw [key6, abs_le]
    constructor <;> nlinarith [sq_nonneg r]
  have h1δ : 1 - δ ≤ r / 2 := by linarith
  have h1δ0 : 0 ≤ 1 - δ := by linarith
  have h2δ : (1 - δ) ^ 2 ≤ r ^ 2 / 4 := by
    calc (1 - δ) ^ 2 = (1 - δ) * (1 - δ) := by ring
      _ ≤ (r / 2) * (r / 2) := mul_le_mul h1δ h1δ h1δ0 (by linarith)
      _ = r ^ 2 / 4 := by ring
  have hδm : Measurable (fun y : Space => δ • y) := (continuous_const_smul δ).measurable
  have hu_m : Measurable u := hu.continuous.measurable
  have hΔm : Measurable (B0418.vecLaplacian u) := (B0418.continuous_vecLaplacian hu).measurable
  have hDu_m : Measurable (fun y : Space => fderiv ℝ u y y) :=
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_id).measurable
  have hH_m : ∀ σ : ℝ, Measurable (fun y : Space => Heat.flow u σ y) := fun σ =>
    (B0418.measurable_flow_uncurry hu.continuous).comp (measurable_id.prodMk measurable_const)
  -- the six terms
  have e1 : eLpNorm (fun y : Space => e • (Heat.flow u (ν * (1 - e)) (δ • y) - u (δ • y) -
      (ν * (1 - e)) • B0418.vecLaplacian u (δ • y))) p volume ≤
      ENNReal.ofReal ((4 * ν ^ 2 * K) * M * r ^ 2) := by
    have hG : eLpNorm (fun x : Space => Heat.flow u (ν * (1 - e)) x - u x -
        (ν * (1 - e)) • B0418.vecLaplacian u x) p volume ≤
        ENNReal.ofReal ((ν * (1 - e)) ^ 2 / 2 * (K * M)) := by
      calc _ ≤ ENNReal.ofReal ((ν * (1 - e)) ^ 2 / 2) *
            eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian u)) p volume :=
              heatTaylor2 p hp1 hp u hu hcomp _ hσ0
        _ ≤ ENNReal.ofReal ((ν * (1 - e)) ^ 2 / 2) * ENNReal.ofReal (K * M) :=
              mul_le_mul' le_rfl hΔ2b
        _ = ENNReal.ofReal ((ν * (1 - e)) ^ 2 / 2 * (K * M)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
    have hf : eLpNorm (fun y : Space => Heat.flow u (ν * (1 - e)) (δ • y) - u (δ • y) -
        (ν * (1 - e)) • B0418.vecLaplacian u (δ • y)) p volume ≤
        ENNReal.ofReal (8 * ((ν * (1 - e)) ^ 2 / 2 * (K * M))) := by
      calc _ ≤ ENNReal.ofReal 8 * eLpNorm (fun x : Space => Heat.flow u (ν * (1 - e)) x - u x -
              (ν * (1 - e)) • B0418.vecLaplacian u x) p volume :=
            at_scale (g := fun x : Space => Heat.flow u (ν * (1 - e)) x - u x -
              (ν * (1 - e)) • B0418.vecLaplacian u x) hδ_half hδ1 hp1 hp
        _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal ((ν * (1 - e)) ^ 2 / 2 * (K * M)) :=
            mul_le_mul' le_rfl hG
        _ = ENNReal.ofReal (8 * ((ν * (1 - e)) ^ 2 / 2 * (K * M))) :=
            (ENNReal.ofReal_mul (by norm_num)).symm
    have h := at_smul (f := fun y : Space => Heat.flow u (ν * (1 - e)) (δ • y) - u (δ • y) -
        (ν * (1 - e)) • B0418.vecLaplacian u (δ • y)) (c := e) (X := 1)
        (Y := 8 * ((ν * (1 - e)) ^ 2 / 2 * (K * M))) zero_le_one
        (by rw [abs_of_pos hE0]; exact hE1) hf
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_self_le_mul_self hσ0 hσr, mul_nonneg hK0 hM0]
  have e2 : eLpNorm (fun y : Space => (e * (ν * (1 - e))) •
      (B0418.vecLaplacian u (δ • y) - B0418.vecLaplacian u y)) p volume ≤
      ENNReal.ofReal ((ν * C1 / 2) * M * r ^ 2) := by
    have hΔD := hD1 M (B0418.vecLaplacian u) hΔc hΔR hL1 δ hδ_half hδ1
    refine (at_smul (f := fun y : Space => B0418.vecLaplacian u (δ • y) -
        B0418.vecLaplacian u y) (c := e * (ν * (1 - e))) (X := ν * r) (Y := C1 * M * (1 - δ))
        (mul_nonneg hν.le hr0.le) (by rw [abs_of_nonneg hEσ0]; exact hEσr) hΔD).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hnn : 0 ≤ ν * r * (C1 * M) := mul_nonneg (mul_nonneg hν.le hr0.le) (mul_nonneg hC1 hM0)
    nlinarith [mul_le_mul_of_nonneg_left h1δ hnn]
  have e3 : eLpNorm (fun y : Space => (e * (ν * (1 - e)) - r * ν) • B0418.vecLaplacian u y)
      p volume ≤ ENNReal.ofReal ((2 * ν * K) * M * r ^ 2) := by
    refine (at_smul (f := B0418.vecLaplacian u) (c := e * (ν * (1 - e)) - r * ν)
        (X := 2 * ν * r ^ 2) (Y := K * M)
        (mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg r)) hS5 hΔb).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have e4 : eLpNorm (fun y : Space => e • (u (δ • y) - u y - (δ - 1) • fderiv ℝ u y y)) p volume
      ≤ ENNReal.ofReal ((C2 / 4) * M * r ^ 2) := by
    have hD2' := hD2 M u hu hsupp hD2bd δ hδ_half hδ1
    refine (at_smul (f := fun y : Space => u (δ • y) - u y - (δ - 1) • fderiv ℝ u y y)
        (c := e) (X := 1) (Y := C2 * M * (1 - δ) ^ 2) zero_le_one
        (by rw [abs_of_pos hE0]; exact hE1) hD2').trans (ENNReal.ofReal_le_ofReal ?_)
    have hCM : 0 ≤ C2 * M := mul_nonneg hC2 hM0
    nlinarith [mul_le_mul_of_nonneg_left h2δ hCM]
  have e5 : eLpNorm (fun y : Space => (e * (δ - 1) + r / 2) • fderiv ℝ u y y) p volume
      ≤ ENNReal.ofReal ((K * Rp) * M * r ^ 2) := by
    refine (at_smul (f := fun y : Space => fderiv ℝ u y y) (c := e * (δ - 1) + r / 2)
        (X := r ^ 2) (Y := K * (M * Rp)) (sq_nonneg r) hS6 hDb).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have e6 : eLpNorm (fun y : Space => (e - 1 + r) • u y) p volume
      ≤ ENNReal.ofReal (K * M * r ^ 2) := by
    refine (at_smul (f := u) (c := e - 1 + r) (X := r ^ 2) (Y := K * M) (sq_nonneg r) hEx
        hub).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  -- measurability of the six terms
  have m1 : AEStronglyMeasurable (fun y : Space => e • (Heat.flow u (ν * (1 - e)) (δ • y) -
      u (δ • y) - (ν * (1 - e)) • B0418.vecLaplacian u (δ • y))) volume :=
    (((((hH_m (ν * (1 - e))).comp hδm).sub (hu_m.comp hδm)).sub
      ((hΔm.comp hδm).const_smul (ν * (1 - e)))).const_smul e).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun y : Space => (e * (ν * (1 - e))) •
      (B0418.vecLaplacian u (δ • y) - B0418.vecLaplacian u y)) volume :=
    (((hΔm.comp hδm).sub hΔm).const_smul (e * (ν * (1 - e)))).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun y : Space => (e * (ν * (1 - e)) - r * ν) •
      B0418.vecLaplacian u y) volume :=
    (hΔm.const_smul (e * (ν * (1 - e)) - r * ν)).aestronglyMeasurable
  have m4 : AEStronglyMeasurable (fun y : Space => e • (u (δ • y) - u y -
      (δ - 1) • fderiv ℝ u y y)) volume :=
    ((((hu_m.comp hδm).sub hu_m).sub (hDu_m.const_smul (δ - 1))).const_smul e).aestronglyMeasurable
  have m5 : AEStronglyMeasurable (fun y : Space => (e * (δ - 1) + r / 2) • fderiv ℝ u y y)
      volume :=
    (hDu_m.const_smul (e * (δ - 1) + r / 2)).aestronglyMeasurable
  have m6 : AEStronglyMeasurable (fun y : Space => (e - 1 + r) • u y) volume :=
    (hu_m.const_smul (e - 1 + r)).aestronglyMeasurable
  -- pointwise identity
  have hF : (fun y : Space => adjFree ν r u y - u y - r • adjGen ν u y) =
      (fun y : Space => e • (Heat.flow u (ν * (1 - e)) (δ • y) - u (δ • y) -
        (ν * (1 - e)) • B0418.vecLaplacian u (δ • y))) +
      (fun y : Space => (e * (ν * (1 - e))) •
        (B0418.vecLaplacian u (δ • y) - B0418.vecLaplacian u y)) +
      (fun y : Space => (e * (ν * (1 - e)) - r * ν) • B0418.vecLaplacian u y) +
      (fun y : Space => e • (u (δ • y) - u y - (δ - 1) • fderiv ℝ u y y)) +
      (fun y : Space => (e * (δ - 1) + r / 2) • fderiv ℝ u y y) +
      (fun y : Space => (e - 1 + r) • u y) := by
    funext y
    simp only [Pi.add_apply, adjFree, adjGen, SpatialScaling.spatialScale, he, hδ]
    module
  have nn : ∀ c : ℝ, 0 ≤ c → 0 ≤ c * M * r ^ 2 := fun c hc =>
    mul_nonneg (mul_nonneg hc hM0) (sq_nonneg r)
  have hc1 : 0 ≤ 4 * ν ^ 2 * K := by linarith
  have hc2 : 0 ≤ ν * C1 / 2 := by linarith
  have hc3 : 0 ≤ 2 * ν * K := by linarith
  have hc4 : 0 ≤ C2 / 4 := by linarith
  have hc5 : 0 ≤ K * Rp := a4
  have hc6 : 0 ≤ K := hK0
  refine (B0418.eLpNorm_le_of_sum6 hp1 hF m1 m2 m3 m4 m5 m6 e1 e2 e3 e4 e5).trans ?_
  refine (add_le_add_right e6 _).trans ?_
  rw [at_ofReal_add6 (nn _ hc1) (nn _ hc2) (nn _ hc3) (nn _ hc4) (nn _ hc5) (nn _ hc6)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIa
