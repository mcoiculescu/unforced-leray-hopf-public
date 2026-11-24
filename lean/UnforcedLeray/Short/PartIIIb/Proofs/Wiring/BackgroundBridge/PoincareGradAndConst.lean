import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.BackgroundBridge.PoincareSmooth
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pointwise gradient recovery and `L²` constant shift (`PartIII-b:IIIb-D5/bridge/2`)

Source of record: `the November 2 reference manuscript`, lines 117-118,
2641-2642, 4139-4141.

Proves `ShortBgExactProfileAux.WeakGradPoincareRecovery`: if `G : SpatialField` is smooth and
equals the distributional gradient of `P₀ ∈ L²(ℝ³)`, then its radial Poincaré potential
`radialPoincare G` satisfies `physGrad (radialPoincare G) = G` everywhere and
`radialPoincare G - c ∈ L²(ℝ³)` for some constant `c : ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

open UnforcedLeray

private theorem space_eq_sum_coord (v : Space) :
    v = ∑ i : Fin 3, v i • coordinateVector i := by
  apply PiLp.ext
  intro k
  simp [coordinateVector, Pi.single_apply]

private theorem inner_coordinateVector_right (w : Space) (j : Fin 3) :
    inner ℝ w (coordinateVector j) = w j := by
  rw [real_inner_comm, coordinateVector, EuclideanSpace.inner_single_left]
  simp

private theorem fderiv_coord_apply {G : SpatialField} (hG : ContDiff ℝ ∞ G)
    (z v : Space) (j : Fin 3) :
    fderiv ℝ (fun y => G y j) z v = (fderiv ℝ G z v) j := by
  have h : HasFDerivAt (fun y => G y j)
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).comp (fderiv ℝ G z)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).hasFDerivAt.comp z
      (hG.differentiable (by simp) z).hasFDerivAt
  rw [h.fderiv]
  rfl

private theorem isSpatialTest_derivative {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (i : Fin 3) :
    IsSpatialTest (spatialTestDerivative i Φ) :=
  ⟨UnforcedLeray.Sob.contDiff_dirDeriv hΦ.smooth (coordinateVector i),
    hΦ.compact.fderiv_apply ℝ (coordinateVector i)⟩

private theorem spatialTestDerivative_comm {Φ : Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i j : Fin 3) :
    spatialTestDerivative i (spatialTestDerivative j Φ) =
      spatialTestDerivative j (spatialTestDerivative i Φ) :=
  UnforcedLeray.Sob.dirDeriv_comm hΦ (coordinateVector i) (coordinateVector j)

private theorem integral_smooth_mul_fderiv_test {u φ : Space → ℝ}
    (hu : ContDiff ℝ ∞ u) (hφ : IsSpatialTest φ) (v : Space) :
    (∫ y : Space, u y * fderiv ℝ φ y v) = -∫ y : Space, fderiv ℝ u y v * φ y := by
  have hu_d : Differentiable ℝ u := hu.differentiable (by simp)
  have hφ_d : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hdu_cont : Continuous (fun y => fderiv ℝ u y v) :=
    (UnforcedLeray.Sob.contDiff_dirDeriv hu v).continuous
  have hdφ_cont : Continuous (fun y => fderiv ℝ φ y v) :=
    (UnforcedLeray.Sob.contDiff_dirDeriv hφ.smooth v).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdu_cont.mul hφ.smooth.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left)
    ((hu.continuous.mul hdφ_cont).integrable_of_hasCompactSupport
      (hφ.compact.fderiv_apply ℝ v).mul_left)
    ((hu.continuous.mul hφ.smooth.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left)
    (fun x _ => hu_d x) (fun x _ => hφ_d x)

private theorem fderiv_symm_of_weakGrad {G : SpatialField} {P₀ : Space → ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hweak : ∀ (j : Fin 3) (φ : Space → ℝ), IsSpatialTest φ →
      (∫ y : Space, G y j * φ y) = -∫ y : Space, P₀ y * spatialTestDerivative j φ y)
    (z u v : Space) :
    inner ℝ (fderiv ℝ G z u) v = inner ℝ (fderiv ℝ G z v) u := by
  have hcoord : ∀ i j : Fin 3,
      (fderiv ℝ G z (coordinateVector i)) j = (fderiv ℝ G z (coordinateVector j)) i := by
    intro i j
    let gj : Space → ℝ := fun y => G y j
    let gi : Space → ℝ := fun y => G y i
    have hgj : ContDiff ℝ ∞ gj :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).contDiff.comp hG
    have hgi : ContDiff ℝ ∞ gi :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp hG
    let q : Space → ℝ := fun y =>
      fderiv ℝ gj y (coordinateVector i) - fderiv ℝ gi y (coordinateVector j)
    have hq_cont : Continuous q :=
      (UnforcedLeray.Sob.contDiff_dirDeriv hgj (coordinateVector i)).continuous.sub
        (UnforcedLeray.Sob.contDiff_dirDeriv hgi (coordinateVector j)).continuous
    have hq_ae : q =ᵐ[volume] (0 : Space → ℝ) := by
      refine (UnforcedLeray.Sob.wholeSpace 3).ae_zero q hq_cont.locallyIntegrable ?_
      intro Φ hΦ_adm
      have hΦ : IsSpatialTest Φ := ⟨hΦ_adm.1, hΦ_adm.2⟩
      have hw1 : (∫ y : Space, gj y * spatialTestDerivative i Φ y) =
          -∫ y : Space, P₀ y * spatialTestDerivative j (spatialTestDerivative i Φ) y :=
        hweak j (spatialTestDerivative i Φ) (isSpatialTest_derivative hΦ i)
      have hw2 : (∫ y : Space, gi y * spatialTestDerivative j Φ y) =
          -∫ y : Space, P₀ y * spatialTestDerivative i (spatialTestDerivative j Φ) y :=
        hweak i (spatialTestDerivative j Φ) (isSpatialTest_derivative hΦ j)
      rw [spatialTestDerivative_comm hΦ.smooth j i] at hw1
      have heq_test : (∫ y : Space, gj y * fderiv ℝ Φ y (coordinateVector i)) =
          ∫ y : Space, gi y * fderiv ℝ Φ y (coordinateVector j) :=
        hw1.trans hw2.symm
      rw [integral_smooth_mul_fderiv_test hgj hΦ (coordinateVector i),
        integral_smooth_mul_fderiv_test hgi hΦ (coordinateVector j)] at heq_test
      have heq_pos : (∫ y : Space, fderiv ℝ gj y (coordinateVector i) * Φ y) =
          ∫ y : Space, fderiv ℝ gi y (coordinateVector j) * Φ y :=
        neg_injective heq_test
      have hint1 : Integrable (fun y => Φ y * fderiv ℝ gj y (coordinateVector i)) volume :=
        (hΦ.smooth.continuous.mul
          (UnforcedLeray.Sob.contDiff_dirDeriv hgj (coordinateVector i)).continuous
          ).integrable_of_hasCompactSupport hΦ.compact.mul_right
      have hint2 : Integrable (fun y => Φ y * fderiv ℝ gi y (coordinateVector j)) volume :=
        (hΦ.smooth.continuous.mul
          (UnforcedLeray.Sob.contDiff_dirDeriv hgi (coordinateVector j)).continuous
          ).integrable_of_hasCompactSupport hΦ.compact.mul_right
      have hsub : (fun y => Φ y * q y) =
          fun y => Φ y * fderiv ℝ gj y (coordinateVector i) -
            Φ y * fderiv ℝ gi y (coordinateVector j) :=
        funext fun y => mul_sub (Φ y) _ _
      rw [UnforcedLeray.Sob.wholeSpace_μ, hsub, integral_sub hint1 hint2]
      simp_rw [mul_comm (Φ _)]
      exact sub_eq_zero.mpr heq_pos
    have hq_eq : q = 0 := (hq_cont.ae_eq_iff_eq volume continuous_zero).mp hq_ae
    have hqz : q z = 0 := congrFun hq_eq z
    have h_eq : fderiv ℝ gj z (coordinateVector i) = fderiv ℝ gi z (coordinateVector j) :=
      sub_eq_zero.mp hqz
    rw [← fderiv_coord_apply hG z (coordinateVector i) j,
      ← fderiv_coord_apply hG z (coordinateVector j) i]
    exact h_eq
  have hu := space_eq_sum_coord u
  have hv := space_eq_sum_coord v
  conv_lhs => rw [hu, hv]
  conv_rhs => rw [hv, hu]
  simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    inner_coordinateVector_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcoord j i]
  ring

private theorem contDiff_radialPoincare {G : SpatialField} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ShortBgExactProfileAux.radialPoincare G) := by
  have h1 := poincareIntervalSmooth_proof (fun _ : ℝ => G) (hG.comp contDiff_snd)
  exact h1.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)

private theorem physGrad_radialPoincare_eq {G : SpatialField} {P₀ : Space → ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hweak : ∀ (j : Fin 3) (φ : Space → ℝ), IsSpatialTest φ →
      (∫ y : Space, G y j * φ y) = -∫ y : Space, P₀ y * spatialTestDerivative j φ y)
    (y₀ : Space) :
    physGrad (ShortBgExactProfileAux.radialPoincare G) y₀ = G y₀ := by
  have hpr : ContDiff ℝ ∞ (ShortBgExactProfileAux.radialPoincare G) :=
    contDiff_radialPoincare hG
  have hG_diff : Differentiable ℝ G := hG.differentiable (by simp)
  have hfderiv_apply : ∀ v : Space,
      fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀ v = inner ℝ (G y₀) v := by
    intro v
    let γ : ℝ → Space := fun s => y₀ + s • v
    have hγ : ∀ s : ℝ, HasDerivAt γ v s := fun s => by
      dsimp only [γ]
      simpa using (hasDerivAt_id s).smul_const v
    have hγ_cont : Continuous γ :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hpr_γ : HasDerivAt (fun s : ℝ => ShortBgExactProfileAux.radialPoincare G (γ s))
        (fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀ v) 0 := by
      have hγ0_eq : γ 0 = y₀ := by simp [γ]
      have h0 : HasFDerivAt (ShortBgExactProfileAux.radialPoincare G)
          (fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀) (γ 0) := by
        rw [hγ0_eq]
        exact (hpr.differentiable (by simp) y₀).hasFDerivAt
      have hcomp := (h0.comp (0 : ℝ) (hγ 0).hasFDerivAt).hasDerivAt
      have hval : ((fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀).comp
          (ContinuousLinearMap.toSpanSingleton ℝ v)) 1 =
          fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀ v := by simp
      rwa [hval] at hcomp
    let F : ℝ → ℝ → ℝ := fun s t => inner ℝ (G (t • γ s)) (γ s)
    let F' : ℝ → ℝ → ℝ := fun s t =>
      inner ℝ (G (t • γ s)) v + inner ℝ (fderiv ℝ G (t • γ s) (t • v)) (γ s)
    have hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
      (hG.continuous.comp (continuous_snd.smul (hγ_cont.comp continuous_fst))).inner
        (hγ_cont.comp continuous_fst)
    have hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
      have h1 : Continuous (fun p : ℝ × ℝ => inner ℝ (G (p.2 • γ p.1)) v) :=
        (hG.continuous.comp (continuous_snd.smul (hγ_cont.comp continuous_fst))).inner
          continuous_const
      have h2 : Continuous (fun p : ℝ × ℝ => fderiv ℝ G (p.2 • γ p.1) (p.2 • v)) :=
        ((hG.continuous_fderiv (by simp)).comp
          (continuous_snd.smul (hγ_cont.comp continuous_fst))).clm_apply
          (continuous_snd.smul continuous_const)
      exact h1.add (h2.inner (hγ_cont.comp continuous_fst))
    have hK : IsCompact (Metric.closedBall (0 : ℝ) 1 ×ˢ Set.uIcc (0 : ℝ) 1) :=
      (isCompact_closedBall (0 : ℝ) 1).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'_cont.continuousOn
    have hparam : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..1, F s t)
        (∫ t in (0 : ℝ)..1, F' 0 t) 0 := by
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (s := Metric.closedBall (0 : ℝ) 1) (bound := fun _ => C)
        (Metric.closedBall_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
      · exact Eventually.of_forall fun s =>
          (hF_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hF_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
      · exact (hF'_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun t ht s hs =>
          hC (s, t) ⟨hs, Set.uIoc_subset_uIcc ht⟩
      · refine Eventually.of_forall fun t _ s _ => ?_
        have hGt : HasDerivAt (fun r : ℝ => G (t • γ r))
            (fderiv ℝ G (t • γ s) (t • v)) s :=
          (hG_diff (t • γ s)).hasFDerivAt.comp_hasDerivAt s ((hγ s).const_smul t)
        exact HasDerivAt.inner ℝ hGt (hγ s)
    have hderiv_eq : fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀ v =
        ∫ t in (0 : ℝ)..1, F' 0 t :=
      hpr_γ.unique hparam
    rw [hderiv_eq]
    let ψ : ℝ → ℝ := fun t => t * inner ℝ (G (t • y₀)) v
    have hψ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (F' 0 t) t := by
      intro t _
      have hty : HasDerivAt (fun r : ℝ => r • y₀) y₀ t := by
        simpa using (hasDerivAt_id t).smul_const y₀
      have hGt : HasDerivAt (fun r : ℝ => G (r • y₀)) (fderiv ℝ G (t • y₀) y₀) t :=
        (hG_diff (t • y₀)).hasFDerivAt.comp_hasDerivAt t hty
      have hin : HasDerivAt (fun r : ℝ => inner ℝ (G (r • y₀)) v)
          (inner ℝ (fderiv ℝ G (t • y₀) y₀) v) t := by
        simpa using HasDerivAt.inner ℝ hGt (hasDerivAt_const t v)
      have hmul : HasDerivAt ψ
          (1 * inner ℝ (G (t • y₀)) v + t * inner ℝ (fderiv ℝ G (t • y₀) y₀) v) t :=
        (hasDerivAt_id t).mul hin
      have hF'0 : 1 * inner ℝ (G (t • y₀)) v + t * inner ℝ (fderiv ℝ G (t • y₀) y₀) v =
          F' 0 t := by
        dsimp only [F', γ]
        rw [zero_smul, add_zero, map_smul, real_inner_smul_left, one_mul,
          fderiv_symm_of_weakGrad hG hweak (t • y₀) y₀ v]
      rwa [hF'0] at hmul
    have hint : IntervalIntegrable (F' 0) volume 0 1 :=
      (hF'_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hψ hint]
    simp [ψ]
  apply PiLp.ext
  intro j
  change fderiv ℝ (ShortBgExactProfileAux.radialPoincare G) y₀ (coordinateVector j) = G y₀ j
  rw [hfderiv_apply (coordinateVector j), inner_coordinateVector_right]

private def mollBumpSeq (k : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((k : ℝ) + 3)
  rOut := 1 / ((k : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

private theorem tendsto_mollBumpSeq_rOut :
    Tendsto (fun k : ℕ => (mollBumpSeq k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun k => ?_
  dsimp [mollBumpSeq]
  push_cast
  ring

private theorem mollBumpSeq_rOut_le_one (k : ℕ) : (mollBumpSeq k).rOut ≤ 1 := by
  dsimp [mollBumpSeq]
  exact div_le_one_of_le₀ (by linarith) (by positivity)

private theorem moll_const_of_weakGradZero {h : Space → ℝ}
    (hh_loc : LocallyIntegrable h volume)
    (hw : ∀ j : Fin 3,
      UnforcedLeray.Sob.HasWeakDeriv
        (UnforcedLeray.Sob.wholeSpaceOf Space volume coordinateVector)
        [coordinateVector j] h (0 : Space → ℝ))
    (b : ContDiffBump (0 : Space)) (x : Space) :
    UnforcedLeray.Sob.moll b volume h x = UnforcedLeray.Sob.moll b volume h 0 := by
  have hm_smooth : ContDiff ℝ ∞ (UnforcedLeray.Sob.moll b volume h) :=
    UnforcedLeray.Sob.contDiff_moll b hh_loc
  have hm_diff : Differentiable ℝ (UnforcedLeray.Sob.moll b volume h) :=
    hm_smooth.differentiable (by simp)
  have hf0 : ∀ z : Space, fderiv ℝ (UnforcedLeray.Sob.moll b volume h) z = 0 := by
    intro z
    have hcoord0 : ∀ j : Fin 3,
        fderiv ℝ (UnforcedLeray.Sob.moll b volume h) z (coordinateVector j) = 0 := by
      intro j
      have hid := congrFun
        (UnforcedLeray.Sob.iterDD_cv_of_hasWeakDeriv (hw j)
          (b.contDiff_normed (μ := volume)) (b.hasCompactSupport_normed (μ := volume)) hh_loc) z
      simpa [UnforcedLeray.Sob.moll, UnforcedLeray.Sob.cv_apply] using hid
    ext v
    rw [space_eq_sum_coord v, map_sum]
    simp [map_smul, hcoord0]
  exact is_const_of_fderiv_eq_zero hm_diff hf0 x 0

private theorem ae_eq_const_of_weakGradZero {h : Space → ℝ}
    (hh_loc : LocallyIntegrable h volume)
    (hw : ∀ j : Fin 3,
      UnforcedLeray.Sob.HasWeakDeriv
        (UnforcedLeray.Sob.wholeSpaceOf Space volume coordinateVector)
        [coordinateVector j] h (0 : Space → ℝ)) :
    ∃ c : ℝ, h =ᵐ[volume] fun _ : Space => c := by
  let cSeq : ℕ → ℝ := fun k => UnforcedLeray.Sob.moll (mollBumpSeq k) volume h 0
  have hcSeq_eq : ∀ (k : ℕ) (x : Space),
      UnforcedLeray.Sob.moll (mollBumpSeq k) volume h x = cSeq k :=
    fun k x => moll_const_of_weakGradZero hh_loc hw (mollBumpSeq k) x
  have hball_lim : ∀ R : ℝ, 0 < R →
      Tendsto (fun k : ℕ =>
        eLpNorm (fun x : Space => h x - cSeq k) 1
          (volume.restrict (Metric.closedBall (0 : Space) R))) atTop (𝓝 0) := by
    intro R _
    let B : Set Space := Metric.closedBall (0 : Space) R
    let B1 : Set Space := Metric.closedBall (0 : Space) (R + 1)
    let hR : Space → ℝ := B1.indicator h
    have hhR_int : Integrable hR volume :=
      (integrable_indicator_iff measurableSet_closedBall).mpr
        (hh_loc.integrableOn_isCompact (isCompact_closedBall (0 : Space) (R + 1)))
    have hhR_mem : MemLp hR 1 volume := memLp_one_iff_integrable.mpr hhR_int
    have hmoll_lim : Tendsto (fun k : ℕ =>
        eLpNorm (hR - UnforcedLeray.Sob.moll (mollBumpSeq k) volume hR) 1 volume)
        atTop (𝓝 0) :=
      UnforcedLeray.Sob.tendsto_eLpNorm_moll_sub ENNReal.one_ne_top hhR_mem
        tendsto_mollBumpSeq_rOut
    have hmoll_eq_on : ∀ (k : ℕ) {x : Space}, x ∈ B →
        UnforcedLeray.Sob.moll (mollBumpSeq k) volume hR x = cSeq k := by
      intro k x hx
      rw [← hcSeq_eq k x, UnforcedLeray.Sob.moll_apply_swap, UnforcedLeray.Sob.moll_apply_swap]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ Metric.ball (0 : Space) (mollBumpSeq k).rOut
      · have hxt : x - t ∈ B1 := by
          rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
          rw [Metric.mem_ball, dist_zero_right] at ht
          have ht1 : ‖t‖ ≤ 1 := ht.le.trans (mollBumpSeq_rOut_le_one k)
          calc ‖x - t‖ ≤ ‖x‖ + ‖t‖ := norm_sub_le x t
            _ ≤ R + 1 := add_le_add hx ht1
        simp [hR, Set.indicator_of_mem hxt]
      · have h0 : (mollBumpSeq k).normed volume t = 0 := by
          rw [← Function.notMem_support, (mollBumpSeq k).support_normed_eq (μ := volume)]
          exact ht
        simp [h0]
    have hle : ∀ k : ℕ,
        eLpNorm (fun x : Space => h x - cSeq k) 1 (volume.restrict B) ≤
          eLpNorm (hR - UnforcedLeray.Sob.moll (mollBumpSeq k) volume hR) 1 volume := by
      intro k
      have hae : (fun x : Space => h x - cSeq k) =ᵐ[volume.restrict B]
          (hR - UnforcedLeray.Sob.moll (mollBumpSeq k) volume hR) := by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        have hx1 : x ∈ B1 :=
          Metric.closedBall_subset_closedBall (by linarith : R ≤ R + 1) hx
        simp [Pi.sub_apply, hR, Set.indicator_of_mem hx1, hmoll_eq_on k hx]
      rw [eLpNorm_congr_ae hae]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmoll_lim
      (fun _ => zero_le) hle
  let B₀ : Set Space := Metric.closedBall (0 : Space) 1
  let μ₀ : Measure Space := volume.restrict B₀
  let V : ℝ≥0∞ := volume B₀
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos volume (0 : Space) one_pos).ne'
  have hVtop : V ≠ ⊤ := (isCompact_closedBall (0 : Space) 1).measure_lt_top.ne
  have he₀ := hball_lim 1 one_pos
  have hd_lim : Tendsto (fun k : ℕ =>
      eLpNorm (fun x : Space => h x - cSeq k) 1 μ₀ * V⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const he₀ (Or.inr (ENNReal.inv_ne_top.mpr hV0))
  have hcauchy : CauchySeq cSeq := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    let δ : ℝ≥0∞ := min ε 1 / 2
    have hδ_pos : 0 < δ := ENNReal.div_pos (lt_min hε zero_lt_one).ne' (by norm_num)
    obtain ⟨K, hK⟩ := (hd_lim.eventually (gt_mem_nhds hδ_pos)).exists_forall_of_atTop
    refine ⟨K, fun m hm n hn => ?_⟩
    have hconst_eq : eLpNorm (fun _ : Space => cSeq m - cSeq n) 1 μ₀ =
        ‖cSeq m - cSeq n‖ₑ * V := by
      dsimp [μ₀, V]
      rw [eLpNorm_const' (cSeq m - cSeq n) one_ne_zero ENNReal.one_ne_top,
        Measure.restrict_apply_univ]
      simp
    have hdiff_eq : (fun _ : Space => cSeq m - cSeq n) =
        (fun x : Space => h x - cSeq n) - (fun x : Space => h x - cSeq m) :=
      funext fun x => by dsimp; ring
    have hmeas_n : AEStronglyMeasurable (fun x : Space => h x - cSeq n) μ₀ :=
      hh_loc.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const
    have hmeas_m : AEStronglyMeasurable (fun x : Space => h x - cSeq m) μ₀ :=
      hh_loc.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const
    have htri : ‖cSeq m - cSeq n‖ₑ * V ≤
        eLpNorm (fun x : Space => h x - cSeq n) 1 μ₀ +
          eLpNorm (fun x : Space => h x - cSeq m) 1 μ₀ := by
      rw [← hconst_eq, hdiff_eq]
      exact eLpNorm_sub_le hmeas_n hmeas_m le_rfl
    have hmul : ‖cSeq m - cSeq n‖ₑ ≤
        eLpNorm (fun x : Space => h x - cSeq n) 1 μ₀ * V⁻¹ +
          eLpNorm (fun x : Space => h x - cSeq m) 1 μ₀ * V⁻¹ := by
      calc ‖cSeq m - cSeq n‖ₑ
          = ‖cSeq m - cSeq n‖ₑ * V * V⁻¹ :=
            (ENNReal.mul_inv_cancel_right hV0 hVtop).symm
        _ ≤ (eLpNorm (fun x : Space => h x - cSeq n) 1 μ₀ +
              eLpNorm (fun x : Space => h x - cSeq m) 1 μ₀) * V⁻¹ := by
            gcongr
        _ = eLpNorm (fun x : Space => h x - cSeq n) 1 μ₀ * V⁻¹ +
              eLpNorm (fun x : Space => h x - cSeq m) 1 μ₀ * V⁻¹ := add_mul _ _ _
    have hed : edist (cSeq m) (cSeq n) = ‖cSeq m - cSeq n‖ₑ := by
      rw [edist_dist, dist_eq_norm, ofReal_norm]
    calc edist (cSeq m) (cSeq n)
        ≤ eLpNorm (fun x : Space => h x - cSeq n) 1 μ₀ * V⁻¹ +
            eLpNorm (fun x : Space => h x - cSeq m) 1 μ₀ * V⁻¹ := by
          rw [hed]; exact hmul
      _ < δ + δ := ENNReal.add_lt_add (hK n hn) (hK m hm)
      _ = min ε 1 := ENNReal.add_halves (min ε 1)
      _ ≤ ε := min_le_left ε 1
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨c, ?_⟩
  have hae_ball : ∀ N : ℕ,
      ∀ᵐ x : Space ∂volume, x ∈ Metric.closedBall (0 : Space) ((N : ℝ) + 1) → h x = c := by
    intro N
    let R : ℝ := (N : ℝ) + 1
    have hR : 0 < R := by positivity
    let BN : Set Space := Metric.closedBall (0 : Space) R
    let μN : Measure Space := volume.restrict BN
    have hVN_top : volume BN ≠ ⊤ := (isCompact_closedBall (0 : Space) R).measure_lt_top.ne
    have hc_enorm : Tendsto (fun k : ℕ => ‖cSeq k - c‖ₑ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => cSeq k - c) atTop (𝓝 (c - c)) :=
        hc.sub tendsto_const_nhds
      rw [sub_self] at h1
      have h2 : Tendsto (fun k : ℕ => ‖cSeq k - c‖ₑ) atTop (𝓝 ‖(0 : ℝ)‖ₑ) :=
        (continuous_enorm.tendsto (0 : ℝ)).comp h1
      rwa [enorm_zero] at h2
    have hconst_lim : Tendsto (fun k : ℕ =>
        eLpNorm (fun _ : Space => cSeq k - c) 1 μN) atTop (𝓝 0) := by
      have heq : (fun k : ℕ => eLpNorm (fun _ : Space => cSeq k - c) 1 μN) =
          fun k : ℕ => ‖cSeq k - c‖ₑ * volume BN := by
        funext k
        dsimp [μN]
        rw [eLpNorm_const' (cSeq k - c) one_ne_zero ENNReal.one_ne_top,
          Measure.restrict_apply_univ]
        simp
      rw [heq]
      simpa using ENNReal.Tendsto.mul_const hc_enorm (Or.inr hVN_top)
    have hsum_lim : Tendsto (fun k : ℕ =>
        eLpNorm (fun x : Space => h x - cSeq k) 1 μN +
          eLpNorm (fun _ : Space => cSeq k - c) 1 μN) atTop (𝓝 0) := by
      simpa using (hball_lim R hR).add hconst_lim
    have hle_sum : ∀ k : ℕ,
        eLpNorm (fun x : Space => h x - c) 1 μN ≤
          eLpNorm (fun x : Space => h x - cSeq k) 1 μN +
            eLpNorm (fun _ : Space => cSeq k - c) 1 μN := by
      intro k
      have hsplit : (fun x : Space => h x - c) =
          (fun x : Space => h x - cSeq k) + (fun _ : Space => cSeq k - c) :=
        funext fun x => by dsimp; ring
      rw [hsplit]
      exact eLpNorm_add_le
        (hh_loc.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const)
        aestronglyMeasurable_const le_rfl
    have he0 : eLpNorm (fun x : Space => h x - c) 1 μN ≤ 0 :=
      ge_of_tendsto hsum_lim (Eventually.of_forall hle_sum)
    have he_eq : eLpNorm (fun x : Space => h x - c) 1 μN = 0 :=
      le_antisymm he0 zero_le
    have hae_sub : ∀ᵐ x : Space ∂μN, h x - c = 0 :=
      (eLpNorm_eq_zero_iff
        (hh_loc.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const)
        one_ne_zero).mp he_eq
    have hae_vol : ∀ᵐ x : Space ∂volume, x ∈ BN → h x - c = 0 :=
      (ae_restrict_iff' measurableSet_closedBall).mp hae_sub
    filter_upwards [hae_vol] with x hx hxB
    exact sub_eq_zero.mp (hx hxB)
  rw [← ae_all_iff] at hae_ball
  filter_upwards [hae_ball] with x hx
  have hmem : x ∈ Metric.closedBall (0 : Space) ((⌈‖x‖⌉₊ : ℝ) + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil ‖x‖
    linarith
  exact hx ⌈‖x‖⌉₊ hmem

/-- **Radial Poincaré potential recovery and `L²` constant shift** (`PartIII-b:IIIb-D5/bridge/2`). -/
theorem weakGradPoincareRecovery_proof :
    UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ShortBgExactProfileAux.WeakGradPoincareRecovery := by
  intro G P₀ hG hP₀ hweak
  have hgrad : ∀ y : Space, physGrad (ShortBgExactProfileAux.radialPoincare G) y = G y :=
    physGrad_radialPoincare_eq hG hweak
  refine ⟨hgrad, ?_⟩
  let pr : Space → ℝ := ShortBgExactProfileAux.radialPoincare G
  have hpr : ContDiff ℝ ∞ pr := contDiff_radialPoincare hG
  let h : Space → ℝ := fun y => pr y - P₀ y
  have hh_loc : LocallyIntegrable h volume :=
    hpr.continuous.locallyIntegrable.sub (hP₀.locallyIntegrable one_le_two)
  let D := UnforcedLeray.Sob.wholeSpaceOf Space volume coordinateVector
  have hw : ∀ j : Fin 3,
      UnforcedLeray.Sob.HasWeakDeriv D [coordinateVector j] h (0 : Space → ℝ) := by
    intro j
    refine ⟨?_, ?_, ?_⟩
    · intro φ hφ
      have hdφ : D.Adm (UnforcedLeray.Sob.iterDirDeriv [coordinateVector j] φ) :=
        D.adm_iterDirDeriv hφ [coordinateVector j]
      exact hh_loc.integrable_smul_left_of_hasCompactSupport hdφ.1.continuous hdφ.2
    · intro φ _
      simp only [D, UnforcedLeray.Sob.wholeSpaceOf_μ, Pi.zero_apply, smul_zero]
      exact integrable_zero Space ℝ volume
    · intro φ hφ
      have hφ_test : IsSpatialTest φ := ⟨hφ.1, hφ.2⟩
      have hdφ : D.Adm (spatialTestDerivative j φ) :=
        D.adm_iterDirDeriv hφ [coordinateVector j]
      have hibp : (∫ y : Space, pr y * spatialTestDerivative j φ y) =
          -∫ y : Space, fderiv ℝ pr y (coordinateVector j) * φ y :=
        integral_smooth_mul_fderiv_test hpr hφ_test (coordinateVector j)
      have hfderiv_pr : ∀ y : Space, fderiv ℝ pr y (coordinateVector j) = G y j := by
        intro y
        have hy := hgrad y
        change (physGrad pr y) j = G y j
        rw [hy]
      simp_rw [hfderiv_pr] at hibp
      have hpr_eq : (∫ y : Space, pr y * spatialTestDerivative j φ y) =
          ∫ y : Space, P₀ y * spatialTestDerivative j φ y := by
        rw [hibp, hweak j φ hφ_test, neg_neg]
      have hint_pr : Integrable (fun y : Space => spatialTestDerivative j φ y * pr y) volume :=
        (hdφ.1.continuous.mul hpr.continuous).integrable_of_hasCompactSupport hdφ.2.mul_right
      have hint_P0 : Integrable (fun y : Space => spatialTestDerivative j φ y * P₀ y) volume := by
        simpa [smul_eq_mul] using
          (hP₀.locallyIntegrable one_le_two).integrable_smul_left_of_hasCompactSupport
            hdφ.1.continuous hdφ.2
      change ∫ x : Space, spatialTestDerivative j φ x • (pr x - P₀ x) =
        (-1 : ℝ) ^ [coordinateVector j].length • ∫ x : Space, φ x • (0 : ℝ)
      simp only [smul_eq_mul, mul_zero, integral_zero, mul_sub]
      rw [integral_sub hint_pr hint_P0]
      simp_rw [mul_comm (spatialTestDerivative j φ _)]
      exact sub_eq_zero.mpr hpr_eq
  obtain ⟨c, hc⟩ := ae_eq_const_of_weakGradZero hh_loc hw
  refine ⟨c, hP₀.ae_eq ?_⟩
  filter_upwards [hc] with y hy
  dsimp only [h] at hy
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
