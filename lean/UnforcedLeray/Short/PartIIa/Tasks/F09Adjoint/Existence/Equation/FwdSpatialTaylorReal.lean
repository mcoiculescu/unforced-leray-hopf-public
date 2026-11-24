import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.AdjointTaylor

/-!
# Part II-a, task `PartII-a:F09/1/3/1/1/1`: real forward second-order Taylor bound

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
Mirror of `AdjointTaylor` for `freeEvolution` (dilation factor `d = e^{r/2} ∈ [1, 2]`).
With `e = e^r`, `σ = ν(e-1)`, `w = e^{σΔ}u`:
`S(r)u - u - rGu = d(w-u-σΔu)(d·) + dσ(Δu(d·)-Δu) + (dσ-rν)Δu
  + d(u(d·)-u-(d-1)∇u·y) + (d(d-1)-r/2)∇u·y + (d-1-r/2)u`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem fwd_dil1_pointwise (M b : ℝ) (w : SpatialField) (hw : ContDiff ℝ ∞ w)
    (hM : ∀ y : Space, ‖fderiv ℝ w y‖ ≤ M) (hb : 1 ≤ b) (y : Space) :
    ‖w (b • y) - w y‖ ≤ M * (b - 1) * ‖y‖ := by
  have hdiff : ∀ x : Space, DifferentiableAt ℝ w x := fun x => (hw.differentiable (by simp)) x
  have hmvt : ‖w (b • y) - w y‖ ≤ M * ‖b • y - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x : ∀ x ∈ (Set.univ : Set Space), DifferentiableAt ℝ w x)
      (fun x _ => hM x : ∀ x ∈ (Set.univ : Set Space), ‖fderiv ℝ w x‖ ≤ M)
      convex_univ (Set.mem_univ y) (Set.mem_univ (b • y))
  have hnorm : ‖b • y - y‖ = (b - 1) * ‖y‖ := by
    rw [show b • y - y = (b - 1) • y by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ b - 1 by linarith)]
  rw [hnorm] at hmvt
  linarith

theorem fwd_dil2_pointwise (M b : ℝ) (w : SpatialField) (hw : ContDiff ℝ ∞ w)
    (hM : ∀ y : Space, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) (hM0 : 0 ≤ M) (hb : 1 ≤ b)
    (y : Space) :
    ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖ ≤ M * (b - 1) ^ 2 * ‖y‖ ^ 2 := by
  have hdiff : ∀ x : Space, DifferentiableAt ℝ w x := fun x => (hw.differentiable (by simp)) x
  have hdiff1 : ∀ x : Space, DifferentiableAt ℝ (fderiv ℝ w) x := fun x =>
    ((ContDiff.fderiv_right (m := ∞) hw (by simp)).differentiable (by simp)) x
  have hlip : ∀ z : Space, ‖fderiv ℝ w z - fderiv ℝ w y‖ ≤ M * ‖z - y‖ := fun z =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff1 x)
      (fun x _ => hM x) convex_univ (Set.mem_univ y) (Set.mem_univ z)
  have hr0 : 0 ≤ ‖b • y - y‖ := norm_nonneg _
  have hs : ∀ z ∈ Metric.closedBall y ‖b • y - y‖,
      ‖fderiv ℝ w z - fderiv ℝ w y‖ ≤ M * ‖b • y - y‖ := by
    intro z hz
    have hzy : ‖z - y‖ ≤ ‖b • y - y‖ := by
      have h := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    exact (hlip z).trans (mul_le_mul_of_nonneg_left hzy hM0)
  have hbmem : b • y ∈ Metric.closedBall y ‖b • y - y‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' (f := w) (φ := fderiv ℝ w y)
    (s := Metric.closedBall y ‖b • y - y‖) (C := M * ‖b • y - y‖)
    (fun x _ => hdiff x) hs (convex_closedBall y _) (Metric.mem_closedBall_self hr0) hbmem
  have hlin : fderiv ℝ w y (b • y - y) = (b - 1) • fderiv ℝ w y y := by
    rw [show b • y - y = (b - 1) • y by rw [sub_smul, one_smul], map_smul]
  have hnorm : ‖b • y - y‖ = (b - 1) * ‖y‖ := by
    rw [show b • y - y = (b - 1) • y by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ b - 1 by linarith)]
  rw [hlin, hnorm] at hmv
  calc ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖
      ≤ M * ((b - 1) * ‖y‖) * ((b - 1) * ‖y‖) := hmv
    _ = M * (b - 1) ^ 2 * ‖y‖ ^ 2 := by ring

/-- First-order dilation bound for a factor `b ∈ [1, 2]`. -/
theorem fwdDilation1 (R : ℝ) (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (w : SpatialField), ContDiff ℝ ∞ w → (∀ y, R < ‖y‖ → w y = 0) →
      (∀ y, ‖fderiv ℝ w y‖ ≤ M) → ∀ b : ℝ, 1 ≤ b →
        eLpNorm (fun y => w (b • y) - w y) p volume ≤ ENNReal.ofReal (C * M * (b - 1)) := by
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  have hR1 : R ≤ max R 0 := le_max_left R 0
  refine ⟨max R 0 * (volume (Metric.closedBall (0 : Space) (max R 0)) ^
      p.toReal⁻¹).toReal, mul_nonneg hR0 ENNReal.toReal_nonneg, ?_⟩
  intro M w hw hsupp hM b hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsupp2 : ∀ y : Space, max R 0 < ‖y‖ → w (b • y) - w y = 0 := by
    intro y hy
    have hyR : R < ‖y‖ := by linarith
    have hbyR : R < ‖b • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith [norm_nonneg y]
    simp [hsupp y hyR, hsupp (b • y) hbyR]
  have hbound : ∀ y : Space, ‖y‖ ≤ max R 0 →
      ‖w (b • y) - w y‖ ≤ M * (b - 1) * max R 0 := fun y hy =>
    (fwd_dil1_pointwise M b w hw hM hb y).trans
      (mul_le_mul_of_nonneg_left hy (mul_nonneg hM0 (by linarith)))
  refine (at_ball (g := fun y => w (b • y) - w y) p hsupp2 hbound).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))

/-- Second-order dilation bound for a factor `b ∈ [1, 2]`. -/
theorem fwdDilation2 (R : ℝ) (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (w : SpatialField), ContDiff ℝ ∞ w → (∀ y, R < ‖y‖ → w y = 0) →
      (∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) → ∀ b : ℝ, 1 ≤ b →
        eLpNorm (fun y => w (b • y) - w y - (b - 1) • fderiv ℝ w y y) p volume ≤
          ENNReal.ofReal (C * M * (b - 1) ^ 2) := by
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  have hR1 : R ≤ max R 0 := le_max_left R 0
  refine ⟨(max R 0) ^ 2 * (volume (Metric.closedBall (0 : Space) (max R 0)) ^
      p.toReal⁻¹).toReal, mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg, ?_⟩
  intro M w hw hsupp hM b hb
  have hM0 : 0 ≤ M := by
    have h0 := hM 0
    have hn := norm_nonneg (fderiv ℝ (fderiv ℝ w) 0)
    linarith
  have hsupp2 : ∀ y : Space, max R 0 < ‖y‖ →
      w (b • y) - w y - (b - 1) • fderiv ℝ w y y = 0 := by
    intro y hy
    have hyR : R < ‖y‖ := by linarith
    have hbyR : R < ‖b • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith [norm_nonneg y]
    simp [hsupp y hyR, hsupp (b • y) hbyR, dilationTaylor2_fderiv_zero w R hsupp y hyR]
  have hbound : ∀ y : Space, ‖y‖ ≤ max R 0 →
      ‖w (b • y) - w y - (b - 1) • fderiv ℝ w y y‖ ≤ M * (b - 1) ^ 2 * (max R 0) ^ 2 := by
    intro y hy
    have hsq : ‖y‖ ^ 2 ≤ (max R 0) ^ 2 := by nlinarith [norm_nonneg y]
    exact (fwd_dil2_pointwise M b w hw hM hM0 hb y).trans
      (mul_le_mul_of_nonneg_left hsq (mul_nonneg hM0 (sq_nonneg _)))
  refine (at_ball (g := fun y => w (b • y) - w y - (b - 1) • fderiv ℝ w y y) p hsupp2
    hbound).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))

/-- Scaling of an `L^p` norm by a dilation with factor `b ≥ 1`. -/
theorem fwdScale {p : ℝ≥0∞} (hp : p ≠ ⊤) {b : ℝ} (hb : 1 ≤ b) (g : SpatialField) :
    eLpNorm (fun y : Space => g (b • y)) p volume ≤ eLpNorm g p volume := by
  have h := B0418.eLpNorm_spatialScale_le hp 1 hb g
  have he : SpatialScaling.spatialScale 1 b g = fun y : Space => g (b • y) := by
    funext y; simp [SpatialScaling.spatialScale]
  rw [he] at h
  simpa using h

set_option maxHeartbeats 1600000 in
/-- **Real forward second-order Taylor bound** (task `PartII-a:F09/1/3/1/1/1`). -/
theorem fwdSpatialTaylorReal : FwdSpatialTaylorReal := by
  intro ν R p hν hp1 hp
  obtain ⟨C1, hC1, hD1⟩ := fwdDilation1 R p
  obtain ⟨C2, hC2, hD2⟩ := fwdDilation2 R p
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
  refine ⟨4 * ν ^ 2 * K + 4 * (ν * C1) + 3 * (ν * K) + 2 * C2 + K * Rp + K, ?_, ?_⟩
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
  obtain ⟨e, he⟩ : ∃ e : ℝ, Real.exp r = e := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, Real.exp (r / 2) = d := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by rw [← hd]; linarith [Real.add_one_le_exp (r / 2)]
  have he1 : 1 ≤ e := by rw [← he]; linarith [Real.add_one_le_exp r]
  have hEx : |e - 1 - r| ≤ r ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := r) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rwa [he] at h
  have hDx : |d - 1 - r / 2| ≤ r ^ 2 / 4 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := r / 2)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [hd, show (r / 2) ^ 2 = r ^ 2 / 4 by ring] at h
    exact h
  have hEx' := abs_le.mp hEx
  have hDx' := abs_le.mp hDx
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hrr : 0 ≤ r ^ 2 := sq_nonneg r
  have hd_up : d - 1 ≤ 3 * r / 4 := by nlinarith [hDx'.2]
  have hd2 : d ≤ 2 := by linarith
  have he_up : e - 1 ≤ 2 * r := by nlinarith [hEx'.2]
  have hσ0 : 0 ≤ ν * (e - 1) := mul_nonneg hν.le (by linarith)
  have hσr : ν * (e - 1) ≤ 2 * ν * r := by nlinarith [mul_le_mul_of_nonneg_left he_up hν.le]
  have hdσ0 : 0 ≤ d * (ν * (e - 1)) := mul_nonneg (by linarith) hσ0
  have hdσr : d * (ν * (e - 1)) ≤ 4 * ν * r := by
    have := mul_le_mul hd2 hσr hσ0 (by norm_num : (0:ℝ) ≤ 2)
    nlinarith
  have hS3 : |d * (ν * (e - 1)) - r * ν| ≤ 3 * ν * r ^ 2 := by
    have key : d * (ν * (e - 1)) - r * ν = ν * (d * (e - 1 - r) + (d - 1) * r) := by ring
    have h1 : |d * (e - 1 - r)| ≤ 2 * r ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ d)]
      nlinarith [abs_nonneg (e - 1 - r)]
    have h2 : 0 ≤ (d - 1) * r := mul_nonneg (by linarith) hr0.le
    have h3 : (d - 1) * r ≤ r ^ 2 := by nlinarith
    have h1' := abs_le.mp h1
    have hX : |d * (e - 1 - r) + (d - 1) * r| ≤ 3 * r ^ 2 := by
      rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2]
    rw [key, abs_mul, abs_of_nonneg hν.le]
    calc ν * |d * (e - 1 - r) + (d - 1) * r| ≤ ν * (3 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hX hν.le
      _ = 3 * ν * r ^ 2 := by ring
  have hS5 : |d * (d - 1) - r / 2| ≤ r ^ 2 := by
    have key : d * (d - 1) - r / 2 = (d - 1) ^ 2 + (d - 1 - r / 2) := by ring
    have hs : (d - 1) ^ 2 ≤ 9 * r ^ 2 / 16 := by
      have h0 : 0 ≤ d - 1 := by linarith
      nlinarith
    have hs0 : 0 ≤ (d - 1) ^ 2 := sq_nonneg _
    rw [key, abs_le]
    constructor <;> nlinarith [hDx'.1, hDx'.2]
  have hS6 : |d - 1 - r / 2| ≤ r ^ 2 := by nlinarith [hDx'.1, hDx'.2]
  have h1d : d - 1 ≤ r := by linarith
  have h2d : (d - 1) ^ 2 ≤ r ^ 2 := by
    have h0 : 0 ≤ d - 1 := by linarith
    nlinarith
  have hdm : Measurable (fun y : Space => d • y) := (continuous_const_smul d).measurable
  have hu_m : Measurable u := hu.continuous.measurable
  have hΔm : Measurable (B0418.vecLaplacian u) := (B0418.continuous_vecLaplacian hu).measurable
  have hDu_m : Measurable (fun y : Space => fderiv ℝ u y y) :=
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_id).measurable
  have hH_m : ∀ σ : ℝ, Measurable (fun y : Space => Heat.flow u σ y) := fun σ =>
    (B0418.measurable_flow_uncurry hu.continuous).comp (measurable_id.prodMk measurable_const)
  have e1 : eLpNorm (fun y : Space => d • (Heat.flow u (ν * (e - 1)) (d • y) - u (d • y) -
      (ν * (e - 1)) • B0418.vecLaplacian u (d • y))) p volume ≤
      ENNReal.ofReal ((4 * ν ^ 2 * K) * M * r ^ 2) := by
    have hG : eLpNorm (fun x : Space => Heat.flow u (ν * (e - 1)) x - u x -
        (ν * (e - 1)) • B0418.vecLaplacian u x) p volume ≤
        ENNReal.ofReal ((ν * (e - 1)) ^ 2 / 2 * (K * M)) := by
      calc _ ≤ ENNReal.ofReal ((ν * (e - 1)) ^ 2 / 2) *
            eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian u)) p volume :=
              heatTaylor2 p hp1 hp u hu hcomp _ hσ0
        _ ≤ ENNReal.ofReal ((ν * (e - 1)) ^ 2 / 2) * ENNReal.ofReal (K * M) :=
              mul_le_mul' le_rfl hΔ2b
        _ = ENNReal.ofReal ((ν * (e - 1)) ^ 2 / 2 * (K * M)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
    have hf : eLpNorm (fun y : Space => Heat.flow u (ν * (e - 1)) (d • y) - u (d • y) -
        (ν * (e - 1)) • B0418.vecLaplacian u (d • y)) p volume ≤
        ENNReal.ofReal ((ν * (e - 1)) ^ 2 / 2 * (K * M)) :=
      (fwdScale hp hd1 (fun x : Space => Heat.flow u (ν * (e - 1)) x - u x -
        (ν * (e - 1)) • B0418.vecLaplacian u x)).trans hG
    have h := at_smul (f := fun y : Space => Heat.flow u (ν * (e - 1)) (d • y) - u (d • y) -
        (ν * (e - 1)) • B0418.vecLaplacian u (d • y)) (c := d) (X := 2)
        (Y := (ν * (e - 1)) ^ 2 / 2 * (K * M)) (by norm_num)
        (by rw [abs_of_nonneg (by linarith)]; exact hd2) hf
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_self_le_mul_self hσ0 hσr, mul_nonneg hK0 hM0]
  have e2 : eLpNorm (fun y : Space => (d * (ν * (e - 1))) •
      (B0418.vecLaplacian u (d • y) - B0418.vecLaplacian u y)) p volume ≤
      ENNReal.ofReal ((4 * (ν * C1)) * M * r ^ 2) := by
    have hΔD := hD1 M (B0418.vecLaplacian u) hΔc hΔR hL1 d hd1
    refine (at_smul (f := fun y : Space => B0418.vecLaplacian u (d • y) -
        B0418.vecLaplacian u y) (c := d * (ν * (e - 1))) (X := 4 * ν * r) (Y := C1 * M * (d - 1))
        (by positivity) (by rw [abs_of_nonneg hdσ0]; exact hdσr) hΔD).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hnn : 0 ≤ 4 * ν * r * (C1 * M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1d hnn]
  have e3 : eLpNorm (fun y : Space => (d * (ν * (e - 1)) - r * ν) • B0418.vecLaplacian u y)
      p volume ≤ ENNReal.ofReal ((3 * (ν * K)) * M * r ^ 2) := by
    refine (at_smul (f := B0418.vecLaplacian u) (c := d * (ν * (e - 1)) - r * ν)
        (X := 3 * ν * r ^ 2) (Y := K * M) (by positivity) hS3 hΔb).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have e4 : eLpNorm (fun y : Space => d • (u (d • y) - u y - (d - 1) • fderiv ℝ u y y)) p volume
      ≤ ENNReal.ofReal ((2 * C2) * M * r ^ 2) := by
    have hD2' := hD2 M u hu hsupp hD2bd d hd1
    refine (at_smul (f := fun y : Space => u (d • y) - u y - (d - 1) • fderiv ℝ u y y)
        (c := d) (X := 2) (Y := C2 * M * (d - 1) ^ 2) (by norm_num)
        (by rw [abs_of_nonneg (by linarith)]; exact hd2) hD2').trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hCM : 0 ≤ C2 * M := mul_nonneg hC2 hM0
    nlinarith [mul_le_mul_of_nonneg_left h2d hCM]
  have e5 : eLpNorm (fun y : Space => (d * (d - 1) - r / 2) • fderiv ℝ u y y) p volume
      ≤ ENNReal.ofReal ((K * Rp) * M * r ^ 2) := by
    refine (at_smul (f := fun y : Space => fderiv ℝ u y y) (c := d * (d - 1) - r / 2)
        (X := r ^ 2) (Y := K * (M * Rp)) (sq_nonneg r) hS5 hDb).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have e6 : eLpNorm (fun y : Space => (d - 1 - r / 2) • u y) p volume
      ≤ ENNReal.ofReal (K * M * r ^ 2) := by
    refine (at_smul (f := u) (c := d - 1 - r / 2) (X := r ^ 2) (Y := K * M) (sq_nonneg r) hS6
        hub).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have m1 : AEStronglyMeasurable (fun y : Space => d • (Heat.flow u (ν * (e - 1)) (d • y) -
      u (d • y) - (ν * (e - 1)) • B0418.vecLaplacian u (d • y))) volume :=
    (((((hH_m (ν * (e - 1))).comp hdm).sub (hu_m.comp hdm)).sub
      ((hΔm.comp hdm).const_smul (ν * (e - 1)))).const_smul d).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun y : Space => (d * (ν * (e - 1))) •
      (B0418.vecLaplacian u (d • y) - B0418.vecLaplacian u y)) volume :=
    (((hΔm.comp hdm).sub hΔm).const_smul (d * (ν * (e - 1)))).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun y : Space => (d * (ν * (e - 1)) - r * ν) •
      B0418.vecLaplacian u y) volume :=
    (hΔm.const_smul (d * (ν * (e - 1)) - r * ν)).aestronglyMeasurable
  have m4 : AEStronglyMeasurable (fun y : Space => d • (u (d • y) - u y -
      (d - 1) • fderiv ℝ u y y)) volume :=
    ((((hu_m.comp hdm).sub hu_m).sub (hDu_m.const_smul (d - 1))).const_smul d).aestronglyMeasurable
  have m5 : AEStronglyMeasurable (fun y : Space => (d * (d - 1) - r / 2) • fderiv ℝ u y y)
      volume :=
    (hDu_m.const_smul (d * (d - 1) - r / 2)).aestronglyMeasurable
  have m6 : AEStronglyMeasurable (fun y : Space => (d - 1 - r / 2) • u y) volume :=
    (hu_m.const_smul (d - 1 - r / 2)).aestronglyMeasurable
  have hF : (fun y : Space => AncientLocalization.freeEvolution ν r u y - u y -
      r • fwdGen ν u y) =
      (fun y : Space => d • (Heat.flow u (ν * (e - 1)) (d • y) - u (d • y) -
        (ν * (e - 1)) • B0418.vecLaplacian u (d • y))) +
      (fun y : Space => (d * (ν * (e - 1))) •
        (B0418.vecLaplacian u (d • y) - B0418.vecLaplacian u y)) +
      (fun y : Space => (d * (ν * (e - 1)) - r * ν) • B0418.vecLaplacian u y) +
      (fun y : Space => d • (u (d • y) - u y - (d - 1) • fderiv ℝ u y y)) +
      (fun y : Space => (d * (d - 1) - r / 2) • fderiv ℝ u y y) +
      (fun y : Space => (d - 1 - r / 2) • u y) := by
    funext y
    simp only [Pi.add_apply, AncientLocalization.freeEvolution,
      AncientLocalization.similarityDilation, fwdGen, SpatialScaling.spatialScale, he, hd]
    module
  have nn : ∀ c : ℝ, 0 ≤ c → 0 ≤ c * M * r ^ 2 := fun c hc =>
    mul_nonneg (mul_nonneg hc hM0) (sq_nonneg r)
  have hc1 : 0 ≤ 4 * ν ^ 2 * K := by linarith
  have hc2 : 0 ≤ 4 * (ν * C1) := by linarith
  have hc3 : 0 ≤ 3 * (ν * K) := by linarith
  have hc4 : 0 ≤ 2 * C2 := by linarith
  refine (B0418.eLpNorm_le_of_sum6 hp1 hF m1 m2 m3 m4 m5 m6 e1 e2 e3 e4 e5).trans ?_
  refine (add_le_add_right e6 _).trans ?_
  rw [at_ofReal_add6 (nn _ hc1) (nn _ hc2) (nn _ hc3) (nn _ hc4) (nn _ a4) (nn _ hK0)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIa
