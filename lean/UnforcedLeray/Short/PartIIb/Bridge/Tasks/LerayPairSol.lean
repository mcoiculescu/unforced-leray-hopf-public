import UnforcedLeray.Short.PartIIb.Bridge.FieldModel
import UnforcedLeray.Lib.LerayC.Complex
import UnforcedLeray.Lib.LerayC.Phase
import UnforcedLeray.Lib.LerayLp.Duality
import UnforcedLeray.Lib.LerayLp.Helmholtz
import UnforcedLeray.Lib.PhaseSpace.Pairing
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Short.IIb.LerayPairSolAux

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

theorem fderiv_proj_apply {g : Space → Space} (hg : ContDiff ℝ ∞ g) (i : Fin 3)
    (x v : Space) : fderiv ℝ (fun y => g y i) x v = fderiv ℝ g x v i := by
  have hd : HasFDerivAt g (fderiv ℝ g x) x := ((hg.differentiable (by simp)) x).hasFDerivAt
  have hp := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt).comp x hd
  rw [show (fun y => g y i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ g from rfl, hp.fderiv]
  rfl

theorem spatialTestDerivative_continuous {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    Continuous (fun x => spatialTestDerivative i φ x) := by
  unfold spatialTestDerivative
  exact (hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem spatialTestDerivative_compact {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    HasCompactSupport (fun x => spatialTestDerivative i φ x) := by
  unfold spatialTestDerivative
  exact hφ.compact.fderiv_apply ℝ (coordinateVector i)

/-- A smooth compactly supported field with classically vanishing divergence is
distributionally solenoidal. -/
theorem isSolenoidal_of_div_zero {g : Space → Space} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g)
    (hdiv : ∀ x : Space, ∑ i : Fin 3, fderiv ℝ g x (coordinateVector i) i = 0) :
    IsSolenoidal g := by
  have hgi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => g y i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hg
  have hgi_c : ∀ i : Fin 3, HasCompactSupport (fun y => g y i) := fun i =>
    (show HasCompactSupport ((fun v : Space => v i) ∘ g) from hc.comp_left (by simp))
  have hgi_fd : ∀ i : Fin 3, Continuous (fun x => fderiv ℝ (fun y => g y i) x (coordinateVector i)) :=
    fun i => ((hgi i).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply integrable_finsetSum
    intro i _
    exact Continuous.integrable_of_hasCompactSupport
      ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i))
      ((hgi_c i).mul_right)
  · have hint : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x) := by
      intro i
      exact Continuous.integrable_of_hasCompactSupport ((hgi_fd i).mul hφ.smooth.continuous)
        (hφ.compact.mul_left)
    have hbp : ∀ i : Fin 3, ∫ x, g x i * spatialTestDerivative i φ x =
        -∫ x, fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x := by
      intro i
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint i) ?_ ?_ ?_ ?_
      · exact Continuous.integrable_of_hasCompactSupport
          ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i))
          ((hgi_c i).mul_right)
      · exact Continuous.integrable_of_hasCompactSupport
          ((hgi i).continuous.mul hφ.smooth.continuous) ((hgi_c i).mul_right)
      · intro x _
        exact ((hgi i).differentiable (by simp)) x
      · intro x _
        exact (hφ.smooth.differentiable (by simp)) x
    show ∫ x, ∑ i : Fin 3, g x i * spatialTestDerivative i φ x = 0
    have hint0 : ∀ i : Fin 3, Integrable (fun x => g x i * spatialTestDerivative i φ x) := fun i =>
      Continuous.integrable_of_hasCompactSupport
        ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i)) ((hgi_c i).mul_right)
    rw [integral_finsetSum _ (fun i _ => hint0 i)]
    rw [Finset.sum_congr rfl (fun i _ => hbp i), Finset.sum_neg_distrib,
      ← integral_finsetSum _ (fun i _ => hint i)]
    have hz : (fun x => ∑ i : Fin 3, fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x) =
        fun _ => 0 := by
      funext x
      simp only [fderiv_proj_apply hg, ← Finset.sum_mul, hdiv x, zero_mul]
    rw [hz]
    simp

/-- Pointwise decomposition of a complex vector. -/
theorem decomp_CVec3 (z : CVec3) : z = ofReV (reV z) + Complex.I • ofReV (imV z) := by
  rw [I_smul_ofReV, ofReV_reV_add_ofImV_imV]

theorem dotL_ofReV_eq (z : CVec3) (w : Space) :
    dotL z (ofReV w) = ((inner ℝ (reV z) w : ℝ) : ℂ) + Complex.I * ((inner ℝ (imV z) w : ℝ) : ℂ) := by
  simp only [dotL_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    reV_apply, imV_apply, ofReV_apply]
  apply Complex.ext <;> simp <;> ring

/-- Symmetry of the real Leray projection against a smooth solenoidal field. -/
theorem real_inner_lerayLp_eq {a : Space → Space} (hcont : Continuous a)
    (hcs : HasCompactSupport a) (hsol : IsSolenoidal a) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (h1 : 1 < q) (hq : q ≠ ⊤) (x : Lp Space q (volume : Measure Space)) :
    ∫ y, inner ℝ (a y) (lerayLp q h1 hq x y) = ∫ y, inner ℝ (a y) (x y) := by
  have hp1 : 1 < conjExp q := one_lt_of_holderConjugate (p := q) (q := conjExp q) hq
  have hp : conjExp q ≠ ⊤ := conjExp_ne_top h1
  have hA : MemLp a (conjExp q) volume := hcont.memLp_of_hasCompactSupport hcs
  have hae : ((hA.toLp a : Lp Space (conjExp q) (volume : Measure Space)) : Space → Space)
      =ᵐ[volume] a := hA.coeFn_toLp
  have hsolL : IsSolenoidal ((hA.toLp a : Lp Space (conjExp q) (volume : Measure Space)) : Space → Space) := by
    refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
    · exact (hsol.integrable φ hφ).congr (by filter_upwards [hae] with y hy; simp only [hy])
    · exact (integral_congr_ae (by filter_upwards [hae] with y hy; simp only [hy])).trans
        (hsol.identity φ hφ)
  have hLP := lerayLp_eq_self hp1 hp (hA.toLp a) hsolL
  have hsym := integral_inner_lerayLp_symm hp1 hp h1 hq (hA.toLp a) x
  rw [hLP] at hsym
  calc ∫ y, inner ℝ (a y) (lerayLp q h1 hq x y)
      = ∫ y, inner ℝ ((hA.toLp a : Lp Space (conjExp q) (volume : Measure Space)) y)
          (lerayLp q h1 hq x y) := by
        apply integral_congr_ae; filter_upwards [hae] with y hy; rw [hy]
    _ = ∫ y, inner ℝ ((hA.toLp a : Lp Space (conjExp q) (volume : Measure Space)) y) (x y) :=
        hsym.symm
    _ = ∫ y, inner ℝ (a y) (x y) := by
        apply integral_congr_ae; filter_upwards [hae] with y hy; rw [hy]

/-- Core slice identity for a smooth compactly supported solenoidal (in space) test field. -/
theorem core_lerayC {q : ℝ≥0∞} [Fact (1 ≤ q)] (h1 : 1 < q) (hq : q ≠ ⊤)
    (ψ : Space → CVec3) (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hsa : IsSolenoidal (fun y => reV (ψ y))) (hsb : IsSolenoidal (fun y => imV (ψ y)))
    (G : Lp CVec3 q (volume : Measure Space)) :
    ∫ y, dotL (ψ y) (lerayC q h1 hq G y) = ∫ y, dotL (ψ y) (G y) := by
  have hac : Continuous (fun y => reV (ψ y)) := reV.continuous.comp hψs.continuous
  have hbc : Continuous (fun y => imV (ψ y)) := imV.continuous.comp hψs.continuous
  have hacs : HasCompactSupport (fun y => reV (ψ y)) := hψc.comp_left reV.map_zero
  have hbcs : HasCompactSupport (fun y => imV (ψ y)) := hψc.comp_left imV.map_zero
  have hAm : MemLp (fun y => reV (ψ y)) (conjExp q) volume := hac.memLp_of_hasCompactSupport hacs
  have hBm : MemLp (fun y => imV (ψ y)) (conjExp q) volume := hbc.memLp_of_hasCompactSupport hbcs
  have hRa : ∀ x : Lp Space q (volume : Measure Space),
      ∫ y, inner ℝ (reV (ψ y)) (lerayLp q h1 hq x y) = ∫ y, inner ℝ (reV (ψ y)) (x y) :=
    fun x => real_inner_lerayLp_eq hac hacs hsa h1 hq x
  have hRb : ∀ x : Lp Space q (volume : Measure Space),
      ∫ y, inner ℝ (imV (ψ y)) (lerayLp q h1 hq x y) = ∫ y, inner ℝ (imV (ψ y)) (x y) :=
    fun x => real_inner_lerayLp_eq hbc hbcs hsb h1 hq x
  have hint : ∀ x : Lp Space q (volume : Measure Space),
      Integrable (fun y => dotL (ψ y) (ofReV (x y))) volume := by
    intro x
    have i1 := UnforcedLeray.RieszLp.integrable_inner_of_memLp hAm (Lp.memLp x)
    have i2 := UnforcedLeray.RieszLp.integrable_inner_of_memLp hBm (Lp.memLp x)
    exact ((i1.ofReal).add ((i2.ofReal).const_mul Complex.I)).congr
      (ae_of_all _ fun y => (dotL_ofReV_eq (ψ y) (x y)).symm)
  have hΛf : ∀ x : Lp Space q (volume : Measure Space),
      ∫ y, dotL (ψ y) (ofReV (x y)) =
        ((∫ y, inner ℝ (reV (ψ y)) (x y) : ℝ) : ℂ) +
          Complex.I * ((∫ y, inner ℝ (imV (ψ y)) (x y) : ℝ) : ℂ) := by
    intro x
    have i1 := UnforcedLeray.RieszLp.integrable_inner_of_memLp hAm (Lp.memLp x)
    have i2 := UnforcedLeray.RieszLp.integrable_inner_of_memLp hBm (Lp.memLp x)
    have e : ∫ y, dotL (ψ y) (ofReV (x y)) = ∫ y, (((inner ℝ (reV (ψ y)) (x y) : ℝ) : ℂ) +
        Complex.I * ((inner ℝ (imV (ψ y)) (x y) : ℝ) : ℂ)) :=
      integral_congr_ae (ae_of_all _ fun y => dotL_ofReV_eq (ψ y) (x y))
    rw [e, integral_add, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
    all_goals first
      | exact i1.ofReal
      | exact (i2.ofReal).const_mul Complex.I
  have hΛP : ∀ x : Lp Space q (volume : Measure Space),
      ∫ y, dotL (ψ y) (ofReV (lerayLp q h1 hq x y)) = ∫ y, dotL (ψ y) (ofReV (x y)) := by
    intro x
    rw [hΛf, hΛf, hRa x, hRb x]
  have hrG := reV.coeFn_compLpL (μ := volume) (p := q) G
  have hiG := imV.coeFn_compLpL (μ := volume) (p := q) G
  have hGdec : ∫ y, dotL (ψ y) (G y) =
      (∫ y, dotL (ψ y) (ofReV ((reV.compLpL q volume G : Lp Space q (volume : Measure Space)) y)))
        + Complex.I * ∫ y, dotL (ψ y) (ofReV ((imV.compLpL q volume G : Lp Space q (volume : Measure Space)) y)) := by
    rw [← integral_const_mul, ← integral_add (hint _) ((hint _).const_mul Complex.I)]
    apply integral_congr_ae
    filter_upwards [hrG, hiG] with y h1' h2'
    rw [h1', h2']
    conv_lhs => rw [decomp_CVec3 (G y)]
    rw [map_add, map_smul, smul_eq_mul]
  have hL : ∫ y, dotL (ψ y) (lerayC q h1 hq G y) =
      ∫ y, (dotL (ψ y) (ofReV (lerayLp q h1 hq (reV.compLpL q volume G) y)) +
        Complex.I * dotL (ψ y) (ofReV (lerayLp q h1 hq (imV.compLpL q volume G) y))) := by
    apply integral_congr_ae
    filter_upwards [coeFn_lerayC h1 hq G] with y hy
    rw [hy, ← I_smul_ofReV, map_add, map_smul, smul_eq_mul]
  rw [hL, integral_add (hint _) ((hint _).const_mul Complex.I), integral_const_mul, hGdec]
  rw [hΛP, hΛP]


/-- Slice identity: the Leray projection is invisible on a solenoidal phase test, slice by slice. -/
theorem slice_identity {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (h1 : 1 < q)
    (hq : q ≠ ⊤) {Φ : ℝ × Space → CVec3}
    (hΦ : UnforcedLeray.Cons.C03.Concrete.IsSolTest P Φ) (t : ℝ)
    (G : Lp CVec3 q (volume : Measure Space)) :
    ∫ y, dotL (Φ (t, y)) (lerayC q h1 hq G y) = ∫ y, dotL (Φ (t, y)) (G y) := by
  obtain ⟨hPh, hdiv⟩ := hΦ
  have hψs : ContDiff ℝ ∞ (fun y => Φ (t, y)) :=
    hPh.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψc : HasCompactSupport (fun y => Φ (t, y)) := hPh.hasCompactSupport_slice t
  have hfd : ∀ (x v : Space), fderiv ℝ (fun y => Φ (t, y)) x v = fderiv ℝ Φ (t, x) (0, v) := by
    intro x v
    have hφd : HasFDerivAt Φ (fderiv ℝ Φ (t, x)) (t, x) :=
      (hPh.smooth.differentiable (by simp) (t, x)).hasFDerivAt
    have hψd : HasFDerivAt (fun y => Φ (t, y))
        ((fderiv ℝ Φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
      hφd.comp x (hasFDerivAt_prodMk_right t x)
    rw [hψd.fderiv]
    rfl
  have hdiff : ∀ x : Space, DifferentiableAt ℝ (fun y => Φ (t, y)) x := fun x =>
    (hψs.differentiable (by simp)) x
  have hsa : IsSolenoidal (fun y => reV (Φ (t, y))) := by
    refine isSolenoidal_of_div_zero (g := fun y => reV (Φ (t, y))) ?_ ?_ ?_
    · exact reV.contDiff.comp hψs
    · exact hψc.comp_left reV.map_zero
    · intro x
      have hsum : ∑ j : Fin 3, fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector j) j = 0 := by
        simp only [hfd]
        exact hdiv (t, x)
      have hr : ∀ i : Fin 3, fderiv ℝ (fun y => reV (Φ (t, y))) x (coordinateVector i) =
          reV (fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector i)) := by
        intro i
        have hd2 : fderiv ℝ (fun y => reV (Φ (t, y))) x =
            reV.comp (fderiv ℝ (fun y => Φ (t, y)) x) :=
          (reV.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
        rw [hd2]
        rfl
      simp only [hr, reV_apply]
      rw [← Complex.re_sum, hsum]
      simp
  have hsb : IsSolenoidal (fun y => imV (Φ (t, y))) := by
    refine isSolenoidal_of_div_zero (g := fun y => imV (Φ (t, y))) ?_ ?_ ?_
    · exact imV.contDiff.comp hψs
    · exact hψc.comp_left imV.map_zero
    · intro x
      have hsum : ∑ j : Fin 3, fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector j) j = 0 := by
        simp only [hfd]
        exact hdiv (t, x)
      have hr : ∀ i : Fin 3, fderiv ℝ (fun y => imV (Φ (t, y))) x (coordinateVector i) =
          imV (fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector i)) := by
        intro i
        have hd2 : fderiv ℝ (fun y => imV (Φ (t, y))) x =
            imV.comp (fderiv ℝ (fun y => Φ (t, y)) x) :=
          (imV.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
        rw [hd2]
        rfl
      simp only [hr, imV_apply]
      rw [← Complex.im_sum, hsum]
      simp
  exact core_lerayC h1 hq (fun y => Φ (t, y)) hψs hψc hsa hsb G

end UnforcedLeray.Short.IIb.LerayPairSolAux

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

theorem lerayPairSol : UnforcedLeray.Short.IIb.LerayPairSol := by
  unfold UnforcedLeray.Short.IIb.LerayPairSol
  intro q _ h1 hq P _ F Φ hΦ
  rw [phasePair_eq_periodIntegral hΦ.1, phasePair_eq_periodIntegral hΦ.1]
  congr 1
  apply integral_congr_ae
  have hP0 : (0 : ℝ) < P := Fact.out
  have hτv : ∀ᵐ τ ∂(volume : Measure (AddCircle P)),
      lerayY P q h1 hq F τ = lerayC q h1 hq (F τ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 hP0).ne']
    filter_upwards [coeFn_lerayY h1 hq F] with τ hτ
    exact hτ
  have hae := (AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae
    (p := fun τ : AddCircle P => lerayY P q h1 hq F τ = lerayC q h1 hq (F τ)) hτv
  filter_upwards [hae] with t ht
  rw [ht]
  exact LerayPairSolAux.slice_identity h1 hq hΦ t (F (t : AddCircle P))

end UnforcedLeray.Short.IIb
