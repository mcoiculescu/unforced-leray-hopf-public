import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3.L3
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lemma 4 (`MollSliceTest`): testing the phase operator with a slice test function

Source of record: `the November 2 reference manuscript`, lines 1415-1424 and 2531.

Test `HasPhaseOp (-dy j) w g` with `Φ(τ, z) = a(τ) ρ_n(y - z) e_c`, where `a` is smooth and
`P`-periodic. The derivative `-dy j Φ` is `a(τ) (∂_j ρ_n)(y - z) e_c`. Both pairings are period
integrals (`phasePair_eq_periodIntegral`); each inner `z`-integral is a component of a spatial
mollification, so the two sides are `∫ a(τ) (Moll (∂_j ρ_n) (rep w τ) y)_c` and
`∫ a(τ) (Moll ρ_n (rep g τ) y)_c`. By `mollFderivApply` the first is the `c`-th component of
`∂_j (Moll ρ_n (rep w τ)) y`, so the integral of `a · mollSliceDiff` vanishes.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (rep)

/-- The slice test function `(τ, z) ↦ a(τ) F(y - z) e_c`. -/
def mstTest (F : UnforcedLeray.Space → ℝ) (a : ℝ → ℝ) (y : UnforcedLeray.Space) (c : Fin 3) :
    ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3 :=
  fun p => (a p.1 * F (y - p.2)) •
    (EuclideanSpace.single c (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)

/-- The spatial partial derivative `x ↦ ∂_j F(x)`. -/
def mstD (F : UnforcedLeray.Space → ℝ) (j : Fin 3) : UnforcedLeray.Space → ℝ :=
  fun x => fderiv ℝ F x (EuclideanSpace.single j 1)

lemma mst_dotL_single (c : Fin 3) (r : ℝ) (v : UnforcedLeray.PhaseSpace.CVec3) :
    dotL (r • (EuclideanSpace.single c (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)) v
      = (r : ℂ) * v c := by
  simp [dotL_apply, Complex.real_smul]

/-- Outside the support radius, `F` and its derivative vanish at `y - z`. -/
lemma mst_far {K : UnforcedLeray.Space → ℝ} {r : ℝ}
    (hsub : tsupport K ⊆ Metric.closedBall (0 : UnforcedLeray.Space) r) (hr : r ≤ 1)
    (y z : UnforcedLeray.Space) (hz : ‖y‖ + 1 < ‖z‖) :
    K (y - z) = 0 ∧ fderiv ℝ K (y - z) = 0 := by
  have hnot : y - z ∉ tsupport K := by
    intro hmem
    have h1 := hsub hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖y - z‖ ≤ 1 := h1.trans hr
    have h3 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := by
      calc ‖z‖ = ‖y - (y - z)‖ := by congr 1; abel
        _ ≤ ‖y‖ + ‖y - z‖ := norm_sub_le _ _
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
  exact image_eq_zero_of_notMem_tsupport (fun h => hnot (tsupport_fderiv_subset (𝕜 := ℝ) h))

lemma mst_isPhaseTest {P : ℝ} {F : UnforcedLeray.Space → ℝ} (hF : ContDiff ℝ ∞ F)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hap : Function.Periodic a P)
    (y : UnforcedLeray.Space) (c : Fin 3)
    (hfar : ∀ z : UnforcedLeray.Space, ‖y‖ + 1 < ‖z‖ → F (y - z) = 0) :
    IsPhaseTest P (mstTest F a y c) where
  smooth := by
    unfold mstTest
    exact ((ha.comp contDiff_fst).mul (hF.comp (contDiff_const.sub contDiff_snd))).smul
      contDiff_const
  periodic := fun τ z => by simp only [mstTest, hap τ]
  bounded_support := ⟨‖y‖ + 1, fun τ z hz => by
    simp only [mstTest, hfar z hz, mul_zero, zero_smul]⟩

/-- The `y`-derivative of the slice test function. -/
lemma mst_dy {K : UnforcedLeray.Space → ℝ} (hK : ContDiff ℝ 1 K) {a : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (y : UnforcedLeray.Space) (c j : Fin 3)
    (p : ℝ × UnforcedLeray.Space) :
    dy j (mstTest K a y c) p = (-(a p.1 * fderiv ℝ K (y - p.2) (EuclideanSpace.single j 1))) •
      (EuclideanSpace.single c (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3) := by
  have hKd : DifferentiableAt ℝ K (y - p.2) := (hK.differentiable (by simp)) _
  have hA : HasFDerivAt (fun q : ℝ × UnforcedLeray.Space => a q.1)
      ((fderiv ℝ a p.1).comp (ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Space)) p :=
    ((ha.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hs : HasFDerivAt (fun q : ℝ × UnforcedLeray.Space => y - q.2)
      (0 - ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space) p :=
    (hasFDerivAt_const y p).sub hasFDerivAt_snd
  have hB : HasFDerivAt (fun q : ℝ × UnforcedLeray.Space => K (y - q.2))
      ((fderiv ℝ K (y - p.2)).comp (0 - ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)) p :=
    hKd.hasFDerivAt.comp p hs
  have hG := (hA.mul hB).smul_const
    (EuclideanSpace.single c (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)
  have key : fderiv ℝ (mstTest K a y c) p =
      ((a p.1) • (fderiv ℝ K (y - p.2)).comp (0 - ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)
        + K (y - p.2) • (fderiv ℝ a p.1).comp (ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Space)).smulRight
          (EuclideanSpace.single c (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3) := hG.fderiv
  unfold dy coordinateVector
  rw [key]
  simp [ContinuousLinearMap.smulRight_apply, neg_smul]

lemma mst_neg_dy {K : UnforcedLeray.Space → ℝ} (hK : ContDiff ℝ 1 K) {a : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (y : UnforcedLeray.Space) (c j : Fin 3) :
    -dy j (mstTest K a y c) = mstTest (mstD K j) a y c := by
  funext p
  rw [Pi.neg_apply, mst_dy hK ha y c j p, neg_smul, neg_neg]
  rfl

/-- The pairing of the slice test with a locally integrable `G` is the `c`-th component of a
spatial mollification. -/
lemma mst_pair {F : UnforcedLeray.Space → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {a : ℝ → ℝ} (y : UnforcedLeray.Space) (c : Fin 3) (t : ℝ)
    (G : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (hG : LocallyIntegrable G volume) :
    ∫ z, dotL (mstTest F a y c (t, z)) (G z) = a t • (Moll F G y) c := by
  have hint : Integrable (fun z => F (y - z) • G z) :=
    hG.integrable_smul_left_of_hasCompactSupport (hFc.comp (continuous_const.sub continuous_id))
      (hFcs.comp_homeomorph (Homeomorph.subLeft y))
  have hpt : ∀ z, dotL (mstTest F a y c (t, z)) (G z) = a t • (F (y - z) • G z) c := by
    intro z
    simp only [mstTest]
    rw [mst_dotL_single]
    simp [PiLp.smul_apply, Complex.real_smul]
    ring
  calc ∫ z, dotL (mstTest F a y c (t, z)) (G z)
      = ∫ z, a t • (F (y - z) • G z) c := integral_congr_ae (ae_of_all _ hpt)
    _ = a t • ∫ z, (F (y - z) • G z) c := integral_smul _ _
    _ = a t • (∫ z, F (y - z) • G z) c := by
        rw [eval_integral_piLp (Integrable.eval_piLp hint) c]
    _ = a t • (Moll F G y) c := rfl

theorem mollSliceTest : MollSliceTest := by
  intro ρ hρ P hP w g j hop n y c a ha hap
  obtain ⟨hdiff, hcs, -, -, hsupp⟩ := hρ n
  have hK1 : ContDiff ℝ 1 (ρ n) := hdiff.of_le (by simp)
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hr : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hfar : ∀ z : UnforcedLeray.Space, ‖y‖ + 1 < ‖z‖ → ρ n (y - z) = 0 :=
    fun z hz => (mst_far hsupp hr y z hz).1
  have hfarD : ∀ z : UnforcedLeray.Space, ‖y‖ + 1 < ‖z‖ → mstD (ρ n) j (y - z) = 0 := by
    intro z hz
    unfold mstD
    rw [(mst_far hsupp hr y z hz).2]
    simp
  have hDsm : ContDiff ℝ ∞ (mstD (ρ n) j) := by
    unfold mstD
    exact (hdiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hΦ : IsPhaseTest P (mstTest (ρ n) a y c) := mst_isPhaseTest hdiff ha hap y c hfar
  have hΨ : IsPhaseTest P (mstTest (mstD (ρ n) j) a y c) :=
    mst_isPhaseTest hDsm ha hap y c hfarD
  have hpair : phasePair P UnforcedLeray.B0412.q0E (-dy j (mstTest (ρ n) a y c)) w
      = phasePair P UnforcedLeray.B0412.q0E (mstTest (ρ n) a y c) g := hop _ hΦ
  rw [mst_neg_dy hK1 (ha.of_le (by simp)) y c j, phasePair_eq_periodIntegral hΨ w,
    phasePair_eq_periodIntegral hΦ g] at hpair
  have hDc : Continuous (mstD (ρ n) j) := by
    unfold mstD
    exact (hdiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs : HasCompactSupport (mstD (ρ n) j) := by
    unfold mstD
    exact (hcs.fderiv ℝ).comp_left
      (g := fun L : UnforcedLeray.Space →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)
  have hwrep : ∀ t : ℝ, ∫ z, dotL (mstTest (mstD (ρ n) j) a y c (t, z))
      ((w (t : AddCircle P) : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) z)
      = a t • (Moll (mstD (ρ n) j) (rep w t) y) c := by
    intro t
    have h1 : ∫ z, dotL (mstTest (mstD (ρ n) j) a y c (t, z))
        ((w (t : AddCircle P) : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) z)
        = ∫ z, dotL (mstTest (mstD (ρ n) j) a y c (t, z)) (rep w t z) :=
      integral_congr_ae (by
        filter_upwards [UnforcedLeray.Cons.C03.Concrete.rep_slice w t] with z hz
        rw [hz])
    rw [h1]
    exact mst_pair hDc hDcs y c t (rep w t) ((memLp_rep_slice w t).locallyIntegrable hq1)
  have hvrep : ∀ t : ℝ, ∫ z, dotL (mstTest (ρ n) a y c (t, z))
      ((g (t : AddCircle P) : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) z)
      = a t • (Moll (ρ n) (rep g t) y) c := by
    intro t
    have h1 : ∫ z, dotL (mstTest (ρ n) a y c (t, z))
        ((g (t : AddCircle P) : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) z)
        = ∫ z, dotL (mstTest (ρ n) a y c (t, z)) (rep g t z) :=
      integral_congr_ae (by
        filter_upwards [UnforcedLeray.Cons.C03.Concrete.rep_slice g t] with z hz
        rw [hz])
    rw [h1]
    exact mst_pair hdiff.continuous hcs y c t (rep g t)
      ((memLp_rep_slice g t).locallyIntegrable hq1)
  rw [zero_add] at hpair
  simp only [hwrep, hvrep] at hpair
  have hEq : ∫ t in Ioc (0 : ℝ) P, a t • (Moll (mstD (ρ n) j) (rep w t) y) c
      = ∫ t in Ioc (0 : ℝ) P, a t • (Moll (ρ n) (rep g t) y) c :=
    smul_right_injective ℂ (inv_ne_zero hP.out.ne') hpair
  -- pointwise: the slice defect against `a`
  have hsd : ∀ t : ℝ, a t • mollSliceDiff (ρ n) w g j y c t
      = a t • (Moll (mstD (ρ n) j) (rep w t) y) c - a t • (Moll (ρ n) (rep g t) y) c := by
    intro t
    unfold mollSliceDiff
    have hfd : fderiv ℝ (Moll (ρ n) (rep w t)) y (EuclideanSpace.single j 1)
        = Moll (mstD (ρ n) j) (rep w t) y :=
      mollFderivApply (ρ n) hK1 hcs (rep w t) ((memLp_rep_slice w t).locallyIntegrable hq1)
        y (EuclideanSpace.single j 1)
    rw [hfd, PiLp.sub_apply, smul_sub]
  -- integrability on one period
  have hUloc := (mollSlice_moll_locInt (mstD (ρ n) j) hDc hDcs w y).2
  have hVloc := (mollSlice_moll_locInt (ρ n) hdiff.continuous hcs g y).2
  have hUI : IntegrableOn (fun t : ℝ => a t • (Moll (mstD (ρ n) j) (rep w t) y) c)
      (Icc (0 : ℝ) P) := by
    have hv : IntegrableOn (fun t : ℝ => (Moll (mstD (ρ n) j) (rep w t) y)) (Icc (0 : ℝ) P) :=
      hUloc.integrableOn_isCompact isCompact_Icc
    have hc : IntegrableOn (fun t : ℝ => (Moll (mstD (ρ n) j) (rep w t) y) c) (Icc (0 : ℝ) P) :=
      Integrable.eval_piLp hv c
    exact IntegrableOn.continuousOn_smul hc (ha.continuous.continuousOn) isCompact_Icc
  have hVI : IntegrableOn (fun t : ℝ => a t • (Moll (ρ n) (rep g t) y) c) (Icc (0 : ℝ) P) := by
    have hv : IntegrableOn (fun t : ℝ => (Moll (ρ n) (rep g t) y)) (Icc (0 : ℝ) P) :=
      hVloc.integrableOn_isCompact isCompact_Icc
    have hc : IntegrableOn (fun t : ℝ => (Moll (ρ n) (rep g t) y) c) (Icc (0 : ℝ) P) :=
      Integrable.eval_piLp hv c
    exact IntegrableOn.continuousOn_smul hc (ha.continuous.continuousOn) isCompact_Icc
  calc ∫ t in Ioc (0 : ℝ) P, a t • mollSliceDiff (ρ n) w g j y c t
      = ∫ t in Ioc (0 : ℝ) P, (a t • (Moll (mstD (ρ n) j) (rep w t) y) c
          - a t • (Moll (ρ n) (rep g t) y) c) :=
        setIntegral_congr_fun measurableSet_Ioc (fun t _ => hsd t)
    _ = (∫ t in Ioc (0 : ℝ) P, a t • (Moll (mstD (ρ n) j) (rep w t) y) c)
          - ∫ t in Ioc (0 : ℝ) P, a t • (Moll (ρ n) (rep g t) y) c :=
        integral_sub (hUI.mono_set Ioc_subset_Icc_self) (hVI.mono_set Ioc_subset_Icc_self)
    _ = 0 := sub_eq_zero.2 hEq

end UnforcedLeray.Short.PartIIIb.Concrete
