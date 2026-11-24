import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Lin.Basic

/-!
# Integrability core for `FullOutSubLin` (source 3611-3621, 3604-3610)

The `z`-integrand of `sepW` is dominated by `M₀ · Σ|∂K|` on a fixed ball; the `l`-integral is
bounded by `A + B (1-l²)^{-1/2}` (small `l`: sup bound of the kernel; `l ≥ 1/2`: `GradKL1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

open UnforcedLeray
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LinAux

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
  UnforcedLeray.Short.PartIIIb.Concrete.T8_1

/-- The `z`-envelope `Σ_{j,k} |∂_k (K_t)_{ij}(y - l z)|` at `t = ν(1-l²)`. -/
def envE (ν : ℝ) (i : Fin 3) (y : Space) (l : ℝ) (z : Space) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, |Gm k i j (ν * (1 - l ^ 2), y - l • z)|

theorem psi_pointwise (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (M0 ρ : ℝ)
    (hM0 : 0 ≤ M0) (hM : ∀ (τ' : ℝ) (z : Space) (a b : Fin 3), |T τ' z a b| ≤ M0)
    (τ : ℝ) (y : Space) (l : ℝ) (z : Space) :
    ‖PsiM ν i T ((τ, y), l) z‖ ≤ M0 * envE ν i y l z := by
  dsimp only [PsiM, envE]
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, ((Gm k i j (ν * (1 - l ^ 2), y - l • z) : ℝ) : ℂ) *
        ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖
      ≤ ∑ j : Fin 3, ∑ k : Fin 3, M0 * |Gm k i j (ν * (1 - l ^ 2), y - l • z)| := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |Gm k i j (ν * (1 - l ^ 2), y - l • z)| * |T (τ + 2 * Real.log l) z j k|
            ≤ |Gm k i j (ν * (1 - l ^ 2), y - l • z)| * M0 :=
              mul_le_mul_of_nonneg_left (hM _ z j k) (abs_nonneg _)
          _ = M0 * |Gm k i j (ν * (1 - l ^ 2), y - l • z)| := mul_comm _ _
    _ = M0 * ∑ j : Fin 3, ∑ k : Fin 3, |Gm k i j (ν * (1 - l ^ 2), y - l • z)| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

theorem psi_zero (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (ρ : ℝ)
    (hρ : ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → T τ' z = 0)
    (τ : ℝ) (y : Space) (l : ℝ) (z : Space) (hz : z ∉ Metric.closedBall (0 : Space) ρ) :
    PsiM ν i T ((τ, y), l) z = 0 := by
  have h0 : T (τ + 2 * Real.log l) z = 0 :=
    hρ _ z (not_le.mp (fun h => hz (mem_closedBall_zero_iff.2 h)))
  dsimp only [PsiM]
  simp [h0]

theorem psi_lint_le (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (M0 ρ : ℝ) (hM0 : 0 ≤ M0) (hM : ∀ (τ' : ℝ) (z : Space) (a b : Fin 3), |T τ' z a b| ≤ M0)
    (hρ : ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → T τ' z = 0) (τ : ℝ) (y : Space) (l : ℝ) :
    ∫⁻ z, ENNReal.ofReal ‖PsiM ν i T ((τ, y), l) z‖ ≤
      ENNReal.ofReal M0 * ∫⁻ z in Metric.closedBall (0 : Space) ρ,
        ENNReal.ofReal (envE ν i y l z) := by
  have hball : MeasurableSet (Metric.closedBall (0 : Space) ρ) := measurableSet_closedBall
  calc ∫⁻ z, ENNReal.ofReal ‖PsiM ν i T ((τ, y), l) z‖
      ≤ ∫⁻ z, (Metric.closedBall (0 : Space) ρ).indicator
          (fun z => ENNReal.ofReal M0 * ENNReal.ofReal (envE ν i y l z)) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ Metric.closedBall (0 : Space) ρ
        · rw [indicator_of_mem hz, ← ENNReal.ofReal_mul hM0]
          exact ENNReal.ofReal_le_ofReal (psi_pointwise ν i T M0 ρ hM0 hM τ y l z)
        · rw [indicator_of_notMem hz, psi_zero ν i T ρ hρ τ y l z hz, norm_zero,
            ENNReal.ofReal_zero]
    _ = ∫⁻ z in Metric.closedBall (0 : Space) ρ,
          ENNReal.ofReal M0 * ENNReal.ofReal (envE ν i y l z) := lintegral_indicator hball _
    _ = ENNReal.ofReal M0 * ∫⁻ z in Metric.closedBall (0 : Space) ρ,
          ENNReal.ofReal (envE ν i y l z) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem J_bound (ν : ℝ) (hν : 0 < ν) (ρ : ℝ) (i : Fin 3) (y : Space) :
    ∃ A B : ENNReal, A ≠ ⊤ ∧ B ≠ ⊤ ∧ ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫⁻ z in Metric.closedBall (0 : Space) ρ, ENNReal.ofReal (envE ν i y l z) ≤
        A + B * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hsup⟩ := gk1_sup
  obtain ⟨C, hC, hgrad⟩ := gradKL1
  refine ⟨ENNReal.ofReal (K * ((3 * ν / 4) ^ 2)⁻¹) * volume (Metric.closedBall (0 : Space) ρ),
    ENNReal.ofReal 8 * (ENNReal.ofReal C * ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)))),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ?_⟩
  intro l hl
  have hl0 : 0 < l := hl.1
  have hl1 : l < 1 := hl.2
  have hl2 : 0 < 1 - l ^ 2 := by nlinarith
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν hl2
  have hsub : ∀ z : Space, envE ν i y l z ≤ gk1Sum (ν * (1 - l ^ 2)) (y - l • z) :=
    fun z => Gm_sum_le (ν * (1 - l ^ 2)) (y - l • z) i
  rcases le_total l (1 / 2) with hle | hge
  · have hcst : ∀ z : Space, envE ν i y l z ≤ K * ((3 * ν / 4) ^ 2)⁻¹ := by
      intro z
      have hl4 : l ^ 2 ≤ 1 / 4 := by nlinarith
      have h4 : (3 / 4 : ℝ) ≤ 1 - l ^ 2 := by linarith
      have h3 : 3 * ν / 4 ≤ ν * (1 - l ^ 2) := by
        have := mul_le_mul_of_nonneg_left h4 hν.le
        linarith
      have hK2 : (3 * ν / 4) ^ 2 ≤ (ν * (1 - l ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      calc envE ν i y l z ≤ gk1Sum (ν * (1 - l ^ 2)) (y - l • z) := hsub z
        _ ≤ K * ((ν * (1 - l ^ 2)) ^ 2)⁻¹ := (hsup _ ht _).2
        _ ≤ K * ((3 * ν / 4) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hK2) hK
    calc ∫⁻ z in Metric.closedBall (0 : Space) ρ, ENNReal.ofReal (envE ν i y l z)
        ≤ ∫⁻ z in Metric.closedBall (0 : Space) ρ, ENNReal.ofReal (K * ((3 * ν / 4) ^ 2)⁻¹) :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hcst z)
      _ = ENNReal.ofReal (K * ((3 * ν / 4) ^ 2)⁻¹) *
            volume (Metric.closedBall (0 : Space) ρ) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := le_self_add
  · have h8real : (l ^ 3)⁻¹ ≤ 8 := by
      have h1 : (1 / 8 : ℝ) ≤ l ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hge 3
        norm_num at this
        linarith
      have h2 := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 8) h1
      norm_num at h2 ⊢
      linarith
    have hsplit : (ν * (1 - l ^ 2)) ^ (-(1 / 2 : ℝ)) =
        ν ^ (-(1 / 2 : ℝ)) * (1 - l ^ 2) ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hν.le hl2.le
    calc ∫⁻ z in Metric.closedBall (0 : Space) ρ, ENNReal.ofReal (envE ν i y l z)
        ≤ ∫⁻ z, gradKNorm (ν * (1 - l ^ 2)) (y - l • z) :=
          (setLIntegral_le_lintegral _ _).trans'
            (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hsub z))
      _ = ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ v, gradKNorm (ν * (1 - l ^ 2)) v :=
          lint_affine y l hl0 _ (measurable_gradKNorm _ ht)
      _ ≤ ENNReal.ofReal 8 * (ENNReal.ofReal C * ENNReal.ofReal ((ν * (1 - l ^ 2)) ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal h8real) (hgrad _ ht)
      _ = ENNReal.ofReal 8 * (ENNReal.ofReal C * ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)))) *
            ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) := by
          rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hν.le _)]
          ring
      _ ≤ _ := le_add_self

theorem lint_inv_sqrt_lt_top :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) < ⊤ := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := h1.comp_sub_left 1
  simp only [sub_zero, sub_self] at h2
  rw [intervalIntegrable_iff, Set.uIoc_of_ge zero_le_one] at h2
  have h3 : IntegrableOn (fun l : ℝ => (1 - l) ^ (-(1 / 2 : ℝ))) (Ioo (0 : ℝ) 1) :=
    h2.mono_set Set.Ioo_subset_Ioc_self
  have h4 : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - l) ^ (-(1 / 2 : ℝ))) < ⊤ :=
    h3.lintegral_lt_top
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioo fun l hl => ?_) h4
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hl.2]) (by nlinarith [hl.1, hl.2])
    (by norm_num)

theorem core_inner (ν : ℝ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hm : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k)
    (M0 ρ : ℝ) (hM0 : 0 ≤ M0)
    (hM : ∀ (τ' : ℝ) (z : Space) (a b : Fin 3), |T τ' z a b| ≤ M0)
    (hρ : ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → T τ' z = 0)
    (τ : ℝ) (y : Space) (i : Fin 3) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun z : Space => PsiM ν i T ((τ, y), l) z) := by
  obtain ⟨A, B, hA, hB, hJ⟩ := J_bound ν hν ρ i y
  refine ⟨((measurable_PsiM ν i T hm).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).2 ?_⟩
  calc ∫⁻ z, ENNReal.ofReal ‖PsiM ν i T ((τ, y), l) z‖
      ≤ ENNReal.ofReal M0 * ∫⁻ z in Metric.closedBall (0 : Space) ρ,
          ENNReal.ofReal (envE ν i y l z) := psi_lint_le ν i T M0 ρ hM0 hM hρ τ y l
    _ ≤ ENNReal.ofReal M0 * (A + B * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hJ l hl) bot_le
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hA.lt_top, ENNReal.mul_lt_top hB.lt_top ENNReal.ofReal_lt_top⟩)

theorem core_outer (ν : ℝ) (μ : ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hm : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k)
    (M0 ρ : ℝ) (hM0 : 0 ≤ M0)
    (hM : ∀ (τ' : ℝ) (z : Space) (a b : Fin 3), |T τ' z a b| ≤ M0)
    (hρ : ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → T τ' z = 0)
    (τ : ℝ) (y : Space) (i : Fin 3) :
    Integrable (fun l : ℝ => (l : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T ((τ, y), l) z)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hP := measurable_PsiM ν i T hm
  have hI : StronglyMeasurable fun r : (ℝ × Space) × ℝ => ∫ z : Space, PsiM ν i T r z :=
    StronglyMeasurable.integral_prod_right' (ν := volume)
      (f := fun p : ((ℝ × Space) × ℝ) × Space => PsiM ν i T p.1 p.2) hP.stronglyMeasurable
  have hO : Measurable fun r : (ℝ × Space) × ℝ =>
      (r.2 : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T r z :=
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul hI.measurable
  refine ⟨(hO.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).2 ?_⟩
  obtain ⟨A, B, hA, hB, hJ⟩ := J_bound ν hν ρ i y
  have hcov : ∀ l ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T ((τ, y), l) z‖ ≤
        ENNReal.ofReal M0 * (A + B * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have hl1 : l < 1 := hl.2
    have hpow : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hl0]
      have hre : (2 * (μ : ℂ) + 2).re = 2 * μ + 2 := by simp
      rw [hre]
      exact Real.rpow_le_one hl0.le hl1.le (by linarith)
    have hint : ENNReal.ofReal ‖∫ z : Space, PsiM ν i T ((τ, y), l) z‖ ≤
        ∫⁻ z, ENNReal.ofReal ‖PsiM ν i T ((τ, y), l) z‖ := by
      simpa only [ofReal_norm_eq_enorm] using
        enorm_integral_le_lintegral_enorm (fun z => PsiM ν i T ((τ, y), l) z)
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    calc ENNReal.ofReal ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ *
          ENNReal.ofReal ‖∫ z : Space, PsiM ν i T ((τ, y), l) z‖
        ≤ 1 * ENNReal.ofReal ‖∫ z : Space, PsiM ν i T ((τ, y), l) z‖ :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.2 hpow) bot_le
      _ ≤ ∫⁻ z, ENNReal.ofReal ‖PsiM ν i T ((τ, y), l) z‖ := by rw [one_mul]; exact hint
      _ ≤ ENNReal.ofReal M0 * ∫⁻ z in Metric.closedBall (0 : Space) ρ,
            ENNReal.ofReal (envE ν i y l z) := psi_lint_le ν i T M0 ρ hM0 hM hρ τ y l
      _ ≤ ENNReal.ofReal M0 * (A + B * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hJ l hl) bot_le
  have hvol : (volume.restrict (Ioo (0 : ℝ) 1)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2) *
          ∫ z : Space, PsiM ν i T ((τ, y), l) z‖
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal M0 *
          (A + B * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) :=
        setLIntegral_mono' measurableSet_Ioo hcov
    _ = ENNReal.ofReal M0 * (A * (volume.restrict (Ioo (0 : ℝ) 1)) univ +
          B * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, lintegral_const_mul' _ _ hB]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hA.lt_top hvol,
          ENNReal.mul_lt_top hB.lt_top lint_inv_sqrt_lt_top⟩)

/-- A tensor field with the three structural properties used in the integrability argument. -/
structure GoodT (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  meas : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k
  bd : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ (τ' : ℝ) (z : Space) (a b : Fin 3), |T τ' z a b| ≤ M0
  supp : ∃ ρ : ℝ, ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → T τ' z = 0

theorem goodT_of_box (R c : ℝ) (hR : 0 < R) (f : Chart → Ten3) (hf : IsBoxTensor f) :
    GoodT (NearInst.cartLift R c f) := by
  obtain ⟨hm, ⟨M0, hM0⟩, ⟨ρ, hρ⟩⟩ := cartLift_good R c hR f hf
  exact ⟨hm, ⟨|M0|, abs_nonneg _, fun τ z a b => (hM0 τ z a b).trans (le_abs_self _)⟩,
    ⟨ρ, fun τ z hz => hρ τ z hz⟩⟩

theorem sepW_sub_good (ν μ : ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ)
    (T1 T2 : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (h1 : GoodT T1) (h2 : GoodT T2)
    (y : Space) (τ : ℝ) (i : Fin 3) :
    UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (fun τ' z => T1 τ' z - T2 τ' z) y τ i =
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T1 y τ i -
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T2 y τ i := by
  obtain ⟨M1, hM1nn, hM1⟩ := h1.bd
  obtain ⟨ρ1, hρ1⟩ := h1.supp
  obtain ⟨M2, hM2nn, hM2⟩ := h2.bd
  obtain ⟨ρ2, hρ2⟩ := h2.supp
  have hI1 := core_outer ν μ hν hμ T1 h1.meas M1 ρ1 hM1nn hM1 hρ1 τ y i
  have hI2 := core_outer ν μ hν hμ T2 h2.meas M2 ρ2 hM2nn hM2 hρ2 τ y i
  have hin : ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫ z : Space, PsiM ν i (fun τ' w => T1 τ' w - T2 τ' w) ((τ, y), l) z =
        (∫ z : Space, PsiM ν i T1 ((τ, y), l) z) - ∫ z : Space, PsiM ν i T2 ((τ, y), l) z := by
    intro l hl
    have e : ∀ z : Space, PsiM ν i (fun τ' w => T1 τ' w - T2 τ' w) ((τ, y), l) z =
        PsiM ν i T1 ((τ, y), l) z - PsiM ν i T2 ((τ, y), l) z :=
      fun z => psiM_sub ν i T1 T2 ((τ, y), l) z
    simp only [e]
    refine (integral_sub (core_inner ν hν T1 h1.meas M1 ρ1 hM1nn hM1 hρ1 τ y i l hl)
      (core_inner ν hν T2 h2.meas M2 ρ2 hM2nn hM2 hρ2 τ y i l hl)).trans ?_
    rfl
  have hout : ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
        ∫ z : Space, PsiM ν i (fun τ' w => T1 τ' w - T2 τ' w) ((τ, y), l) z =
      (∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T1 ((τ, y), l) z) -
        ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T2 ((τ, y), l) z := by
    rw [← integral_sub hI1 hI2]
    refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
    show _ = _
    rw [hin l hl, mul_sub]
  have e : ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T y τ i = -2 * ∫ l in Ioo (0 : ℝ) 1,
        (l : ℂ) ^ (2 * (μ : ℂ) + 2) * ∫ z : Space, PsiM ν i T ((τ, y), l) z :=
    fun T => sepW_eq_PsiM ν (μ : ℂ) T i (τ, y)
  rw [e, e T1, e T2, hout]
  ring

theorem sepW_sub_fun (ν μ : ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ)
    (T1 T2 : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (h1 : GoodT T1) (h2 : GoodT T2)
    (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (fun τ' z => T1 τ' z - T2 τ' z) y τ =
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T1 y τ -
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T2 y τ :=
  funext fun i => sepW_sub_good ν μ hν hμ T1 T2 h1 h2 y τ i

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LinAux
