import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# `PartII-b:S3/1/2/2/1/2` (`BgSolTestOrthEqZero`, `SolTestOrthEqZero.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562.

Proves `bgSolTestOrthEqZero_proof : UnforcedLeray.Short.IIb.BgSolTestOrthEqZero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0414 UnforcedLeray.Blueprint
  UnforcedLeray.RieszLp

namespace SolTestOrthEqZeroAux

open PointwiseDerivSub HigherPhaseSub ProjectedEvolutionSub PhaseDerivStepSub LerayPairSolAux

/-- Compact-support integration by parts on `Space` when the right factor is compactly supported. -/
theorem integral_mul_fderiv_eq_neg_of_hasCompactSupport_right
    {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : Space) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfd : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgc_d : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    hgc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (Continuous.integrable_of_hasCompactSupport (hfd.mul hg.continuous) hgc.mul_left)
    (Continuous.integrable_of_hasCompactSupport (hf.continuous.mul hgd) hgc_d.mul_left)
    (Continuous.integrable_of_hasCompactSupport (hf.continuous.mul hg.continuous) hgc.mul_left)
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)

/-- `IsSolenoidal` is closed under subtraction. -/
theorem isSolenoidal_sub {f g : SpatialField} (hf : IsSolenoidal f) (hg : IsSolenoidal g) :
    IsSolenoidal (f - g) := by
  have hneg : -g = (-1 : ℝ) • g := by
    funext x
    simp
  rw [sub_eq_add_neg, hneg]
  exact UnforcedLeray.Cons.C03.isSolenoidal_add hf
    (UnforcedLeray.Cons.C03.isSolenoidal_const_smul hg (-1 : ℝ))

/-- `IsSolenoidal` is preserved by finite sums. -/
theorem isSolenoidal_sum {ι : Type*} (s : Finset ι) {f : ι → SpatialField}
    (hf : ∀ i ∈ s, IsSolenoidal (f i)) :
    IsSolenoidal (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor <;> intro φ hφ <;> simp
  | @insert a s ha ih =>
      have hsplit : (fun y => ∑ i ∈ insert a s, f i y) =
          f a + (fun y => ∑ i ∈ s, f i y) := by
        funext y
        simp [Finset.sum_insert ha]
      rw [hsplit]
      exact UnforcedLeray.Cons.C03.isSolenoidal_add
        (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Any single-direction spatial derivative `dirSpatialJet F [w]` of a smooth solenoidal field `F`
is solenoidal. -/
theorem isSolenoidal_dirSpatialJet_singleton {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hSol : IsSolenoidal F) (w : Space) :
    IsSolenoidal (dirSpatialJet F [w]) := by
  have hFw : ContDiff ℝ ∞ (dirSpatialJet F [w]) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF [w]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply integrable_finsetSum
    intro i _
    have hFi : Continuous (fun x => dirSpatialJet F [w] x i) :=
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hFw.continuous
    exact Continuous.integrable_of_hasCompactSupport
      (hFi.mul (spatialTestDerivative_continuous hφ i))
      (spatialTestDerivative_compact hφ i).mul_left
  · let φw : Space → ℝ := fun x => fderiv ℝ φ x w
    have hφw_smooth : ContDiff ℝ ∞ φw :=
      (hφ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
    have hφw_compact : HasCompactSupport φw :=
      hφ.compact.fderiv_apply ℝ w
    have hφw : IsSpatialTest φw := ⟨hφw_smooth, hφw_compact⟩
    have hcomm : ∀ (i : Fin 3) (x : Space),
        spatialTestDerivative i φw x = fderiv ℝ (spatialTestDerivative i φ) x w := by
      intro i x
      have hd : Differentiable ℝ (fderiv ℝ φ) :=
        (hφ.smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
      have hd1 : fderiv ℝ φw x =
          (ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ φ) x) :=
        (((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt).comp x (hd x).hasFDerivAt).fderiv
      have hd2 : fderiv ℝ (spatialTestDerivative i φ) x =
          (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).comp (fderiv ℝ (fderiv ℝ φ) x) :=
        (((ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).hasFDerivAt).comp x
          (hd x).hasFDerivAt).fderiv
      change fderiv ℝ φw x (coordinateVector i) = fderiv ℝ (spatialTestDerivative i φ) x w
      rw [hd1, hd2]
      change fderiv ℝ (fderiv ℝ φ) x (coordinateVector i) w =
        fderiv ℝ (fderiv ℝ φ) x w (coordinateVector i)
      exact (hφ.smooth.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)).eq (coordinateVector i) w
    have hint1 : ∀ i : Fin 3,
        Integrable (fun x => dirSpatialJet F [w] x i * spatialTestDerivative i φ x) := by
      intro i
      have hFi : Continuous (fun x => dirSpatialJet F [w] x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hFw.continuous
      exact Continuous.integrable_of_hasCompactSupport
        (hFi.mul (spatialTestDerivative_continuous hφ i))
        (spatialTestDerivative_compact hφ i).mul_left
    have hint2 : ∀ i : Fin 3,
        Integrable (fun x => F x i * spatialTestDerivative i φw x) := by
      intro i
      have hFi : Continuous (fun x => F x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hF.continuous
      exact Continuous.integrable_of_hasCompactSupport
        (hFi.mul (spatialTestDerivative_continuous hφw i))
        (spatialTestDerivative_compact hφw i).mul_left
    have hibp : ∀ i : Fin 3,
        ∫ x, dirSpatialJet F [w] x i * spatialTestDerivative i φ x =
          -∫ x, F x i * spatialTestDerivative i φw x := by
      intro i
      have hFi : ContDiff ℝ ∞ (fun x => F x i) :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hF
      have hsd : ContDiff ℝ ∞ (spatialTestDerivative i φ) :=
        (hφ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
      have hstep := integral_mul_fderiv_eq_neg_of_hasCompactSupport_right
        hFi hsd (spatialTestDerivative_compact hφ i) w
      have hL : (fun x => dirSpatialJet F [w] x i * spatialTestDerivative i φ x) =
          (fun x => fderiv ℝ (fun y => F y i) x w * spatialTestDerivative i φ x) := by
        funext x
        rw [fderiv_proj_apply hF i x w]
        rfl
      have hR : (fun x => F x i * spatialTestDerivative i φw x) =
          (fun x => F x i * fderiv ℝ (spatialTestDerivative i φ) x w) := by
        funext x
        rw [hcomm i x]
      rw [hL, hR]
      linarith [hstep]
    show ∫ x, ∑ i : Fin 3, dirSpatialJet F [w] x i * spatialTestDerivative i φ x = 0
    rw [integral_finsetSum _ (fun i _ => hint1 i),
      Finset.sum_congr rfl (fun i _ => hibp i),
      Finset.sum_neg_distrib,
      ← integral_finsetSum _ (fun i _ => hint2 i)]
    have h0 : ∫ x, ∑ i : Fin 3, F x i * spatialTestDerivative i φw x = 0 :=
      hSol.identity φw hφw
    rw [h0, neg_zero]

/-- `spatialLaplacian F` is solenoidal when `F` is smooth and solenoidal. -/
theorem isSolenoidal_spatialLaplacian {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hSol : IsSolenoidal F) :
    IsSolenoidal (spatialLaplacian F) := by
  unfold spatialLaplacian
  refine isSolenoidal_sum Finset.univ fun j _ => ?_
  have h1 : ContDiff ℝ ∞ (dirSpatialJet F [EuclideanSpace.single j 1]) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF [EuclideanSpace.single j 1]
  have hs1 : IsSolenoidal (dirSpatialJet F [EuclideanSpace.single j 1]) :=
    isSolenoidal_dirSpatialJet_singleton hF hSol (EuclideanSpace.single j 1)
  exact isSolenoidal_dirSpatialJet_singleton h1 hs1 (EuclideanSpace.single j 1)

/-- `spatialRadialDrift F` is solenoidal when `F` is smooth and solenoidal. -/
theorem isSolenoidal_spatialRadialDrift {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hSol : IsSolenoidal F) :
    IsSolenoidal (spatialRadialDrift F) := by
  have hRad : ContDiff ℝ ∞ (spatialRadialDrift F) :=
    contDiff_infty_spatialRadialDrift hF
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply integrable_finsetSum
    intro i _
    have hRi : Continuous (fun x => spatialRadialDrift F x i) :=
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hRad.continuous
    exact Continuous.integrable_of_hasCompactSupport
      (hRi.mul (spatialTestDerivative_continuous hφ i))
      (spatialTestDerivative_compact hφ i).mul_left
  · let ψ : Space → ℝ := fun x => ∑ j : Fin 3, x j * spatialTestDerivative j φ x
    have hsd_smooth : ∀ j : Fin 3, ContDiff ℝ ∞ (spatialTestDerivative j φ) :=
      fun j => (hφ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
    have hψ_smooth : ContDiff ℝ ∞ ψ :=
      ContDiff.sum fun j _ =>
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul (hsd_smooth j)
    have hψ_compact : HasCompactSupport ψ := by
      have heq : ψ = fun x =>
          x 0 * spatialTestDerivative 0 φ x +
          x 1 * spatialTestDerivative 1 φ x +
          x 2 * spatialTestDerivative 2 φ x := by
        funext x
        exact Fin.sum_univ_three _
      rw [heq]
      exact (((spatialTestDerivative_compact hφ 0).mul_left).add
        ((spatialTestDerivative_compact hφ 1).mul_left)).add
        ((spatialTestDerivative_compact hφ 2).mul_left)
    have hψ : IsSpatialTest ψ := ⟨hψ_smooth, hψ_compact⟩
    have hcomm : ∀ (i j : Fin 3) (x : Space),
        fderiv ℝ (spatialTestDerivative j φ) x (coordinateVector i) =
          fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j) := by
      intro i j x
      have hd : Differentiable ℝ (fderiv ℝ φ) :=
        (hφ.smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
      have hd1 : fderiv ℝ (spatialTestDerivative j φ) x =
          (ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).comp (fderiv ℝ (fderiv ℝ φ) x) :=
        (((ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).hasFDerivAt).comp x
          (hd x).hasFDerivAt).fderiv
      have hd2 : fderiv ℝ (spatialTestDerivative i φ) x =
          (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).comp (fderiv ℝ (fderiv ℝ φ) x) :=
        (((ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).hasFDerivAt).comp x
          (hd x).hasFDerivAt).fderiv
      rw [hd1, hd2]
      change fderiv ℝ (fderiv ℝ φ) x (coordinateVector i) (coordinateVector j) =
        fderiv ℝ (fderiv ℝ φ) x (coordinateVector j) (coordinateVector i)
      exact (hφ.smooth.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)).eq
        (coordinateVector i) (coordinateVector j)
    have hproj_coord : ∀ j i : Fin 3,
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (coordinateVector i) =
          if i = j then (1 : ℝ) else 0 := by
      intro j i
      change (coordinateVector i) j = if i = j then (1 : ℝ) else 0
      simp [coordinateVector, eq_comm]
    have hψ_deriv : ∀ (i : Fin 3) (x : Space),
        spatialTestDerivative i ψ x =
          spatialTestDerivative i φ x +
            ∑ j : Fin 3, x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j) := by
      intro i x
      have hterm : ∀ j : Fin 3,
          HasFDerivAt (fun y : Space => y j * spatialTestDerivative j φ y)
            ((x j) • fderiv ℝ (spatialTestDerivative j φ) x +
              (spatialTestDerivative j φ x) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) x := by
        intro j
        exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt).mul
          (((hsd_smooth j).differentiable (by simp)) x).hasFDerivAt
      have hsum_d : HasFDerivAt ψ
          (∑ j : Fin 3, ((x j) • fderiv ℝ (spatialTestDerivative j φ) x +
            (spatialTestDerivative j φ x) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ))) x :=
        HasFDerivAt.fun_sum fun j _ => hterm j
      change fderiv ℝ ψ x (coordinateVector i) = _
      rw [hsum_d.fderiv]
      simp only [FunLike.coe_sum, Finset.sum_apply, add_apply,
        smul_apply, smul_eq_mul, hproj_coord, Finset.sum_add_distrib]
      have hdelta : (∑ j : Fin 3, spatialTestDerivative j φ x * (if i = j then (1 : ℝ) else 0)) =
          spatialTestDerivative i φ x := by
        simp
      have h2 : (∑ j : Fin 3, x j * fderiv ℝ (spatialTestDerivative j φ) x (coordinateVector i)) =
          ∑ j : Fin 3, x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcomm i j x]
      linarith
    have hibp_ij : ∀ (i j : Fin 3),
        ∫ x, (x j * spatialPartial j F x i) * spatialTestDerivative i φ x =
          -∫ x, F x i * (spatialTestDerivative i φ x +
            x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j)) := by
      intro i j
      let g : Space → ℝ := fun x => x j * spatialTestDerivative i φ x
      have hg_smooth : ContDiff ℝ ∞ g :=
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul (hsd_smooth i)
      have hg_compact : HasCompactSupport g :=
        (spatialTestDerivative_compact hφ i).mul_left
      have hFi : ContDiff ℝ ∞ (fun x => F x i) :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hF
      have hstep := integral_mul_fderiv_eq_neg_of_hasCompactSupport_right
        hFi hg_smooth hg_compact (coordinateVector j)
      have hg_d : ∀ x : Space,
          fderiv ℝ g x (coordinateVector j) =
            spatialTestDerivative i φ x +
              x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j) := by
        intro x
        have hd : HasFDerivAt g
            ((x j) • fderiv ℝ (spatialTestDerivative i φ) x +
              (spatialTestDerivative i φ x) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) x :=
          ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt).mul
            (((hsd_smooth i).differentiable (by simp)) x).hasFDerivAt
        rw [hd.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul, hproj_coord, ↓reduceIte]
        ring
      have hL : (fun x => (x j * spatialPartial j F x i) * spatialTestDerivative i φ x) =
          (fun x => fderiv ℝ (fun y => F y i) x (coordinateVector j) * g x) := by
        funext x
        have hp := fderiv_proj_apply hF i x (coordinateVector j)
        change (x j * fderiv ℝ F x (coordinateVector j) i) * spatialTestDerivative i φ x = _
        rw [← hp]
        dsimp [g]
        ring
      have hR : (fun x => F x i * (spatialTestDerivative i φ x +
            x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j))) =
          (fun x => F x i * fderiv ℝ g x (coordinateVector j)) := by
        funext x
        rw [hg_d x]
      rw [hL, hR]
      linarith [hstep]
    have hibp_i : ∀ i : Fin 3,
        ∫ x, spatialRadialDrift F x i * spatialTestDerivative i φ x =
          -∫ x, (2 * (F x i * spatialTestDerivative i φ x) +
            F x i * spatialTestDerivative i ψ x) := by
      intro i
      have hFi : Continuous (fun x => F x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hF.continuous
      have hintL : ∀ j : Fin 3,
          Integrable (fun x => (x j * spatialPartial j F x i) * spatialTestDerivative i φ x) := by
        intro j
        have hPj : ContDiff ℝ ∞ (spatialPartial j F) :=
          JointSmoothSub.contDiff_infty_dirSpatialJet hF [EuclideanSpace.single j 1]
        have hPji : Continuous (fun x => spatialPartial j F x i) :=
          ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hPj.continuous
        have hxj : Continuous (fun x : Space => x j) :=
          (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous
        exact Continuous.integrable_of_hasCompactSupport
          ((hxj.mul hPji).mul (spatialTestDerivative_continuous hφ i))
          (spatialTestDerivative_compact hφ i).mul_left
      have hintR : ∀ j : Fin 3,
          Integrable (fun x => F x i * (spatialTestDerivative i φ x +
            x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j))) := by
        intro j
        have hxj : Continuous (fun x : Space => x j) :=
          (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous
        have hsd2 : Continuous (fun x => fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j)) :=
          ((hsd_smooth i).continuous_fderiv (by simp)).clm_apply continuous_const
        have hcs2 : HasCompactSupport (fun x => fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j)) :=
          (spatialTestDerivative_compact hφ i).fderiv_apply ℝ (coordinateVector j)
        have hsum_c : HasCompactSupport (fun x => spatialTestDerivative i φ x +
            x j * fderiv ℝ (spatialTestDerivative i φ) x (coordinateVector j)) :=
          (spatialTestDerivative_compact hφ i).add hcs2.mul_left
        exact Continuous.integrable_of_hasCompactSupport
          (hFi.mul ((spatialTestDerivative_continuous hφ i).add (hxj.mul hsd2)))
          hsum_c.mul_left
      have hrad_sum : (fun x => spatialRadialDrift F x i * spatialTestDerivative i φ x) =
          fun x => ∑ j : Fin 3, (x j * spatialPartial j F x i) * spatialTestDerivative i φ x := by
        funext x
        rw [spatialRadialDrift_eq_sum_coord_spatialPartial F x]
        simp [Finset.sum_apply, Finset.sum_mul]
      rw [hrad_sum, integral_finsetSum _ (fun j _ => hintL j),
        Finset.sum_congr rfl (fun j _ => hibp_ij i j),
        Finset.sum_neg_distrib,
        ← integral_finsetSum _ (fun j _ => hintR j)]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [hψ_deriv i x]
      simp only [Fin.sum_univ_three]
      ring
    have hint_rad : ∀ i : Fin 3,
        Integrable (fun x => spatialRadialDrift F x i * spatialTestDerivative i φ x) := by
      intro i
      have hRi : Continuous (fun x => spatialRadialDrift F x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hRad.continuous
      exact Continuous.integrable_of_hasCompactSupport
        (hRi.mul (spatialTestDerivative_continuous hφ i))
        (spatialTestDerivative_compact hφ i).mul_left
    have hint_φ : ∀ i : Fin 3,
        Integrable (fun x => F x i * spatialTestDerivative i φ x) := by
      intro i
      have hFi : Continuous (fun x => F x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hF.continuous
      exact Continuous.integrable_of_hasCompactSupport
        (hFi.mul (spatialTestDerivative_continuous hφ i))
        (spatialTestDerivative_compact hφ i).mul_left
    have hint_ψ : ∀ i : Fin 3,
        Integrable (fun x => F x i * spatialTestDerivative i ψ x) := by
      intro i
      have hFi : Continuous (fun x => F x i) :=
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hF.continuous
      exact Continuous.integrable_of_hasCompactSupport
        (hFi.mul (spatialTestDerivative_continuous hψ i))
        (spatialTestDerivative_compact hψ i).mul_left
    have hint_comb : ∀ i : Fin 3,
        Integrable (fun x => 2 * (F x i * spatialTestDerivative i φ x) +
          F x i * spatialTestDerivative i ψ x) :=
      fun i => ((hint_φ i).const_mul 2).add (hint_ψ i)
    show ∫ x, ∑ i : Fin 3, spatialRadialDrift F x i * spatialTestDerivative i φ x = 0
    rw [integral_finsetSum _ (fun i _ => hint_rad i),
      Finset.sum_congr rfl (fun i _ => hibp_i i),
      Finset.sum_neg_distrib,
      ← integral_finsetSum _ (fun i _ => hint_comb i)]
    have hsplit : (fun x => ∑ i : Fin 3, (2 * (F x i * spatialTestDerivative i φ x) +
          F x i * spatialTestDerivative i ψ x)) =
        fun x => 2 * (∑ i : Fin 3, F x i * spatialTestDerivative i φ x) +
          (∑ i : Fin 3, F x i * spatialTestDerivative i ψ x) := by
      funext x
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hint_sum_φ : Integrable (fun x => ∑ i : Fin 3, F x i * spatialTestDerivative i φ x) :=
      integrable_finsetSum _ fun i _ => hint_φ i
    have hint_sum_ψ : Integrable (fun x => ∑ i : Fin 3, F x i * spatialTestDerivative i ψ x) :=
      integrable_finsetSum _ fun i _ => hint_ψ i
    rw [hsplit, integral_add (hint_sum_φ.const_mul 2) hint_sum_ψ, integral_const_mul,
      hSol.identity φ hφ, hSol.identity ψ hψ]
    simp

/-- `spatialProjectedLin ν F` is solenoidal when `F` is smooth and solenoidal. -/
theorem isSolenoidal_spatialProjectedLin (ν : ℝ) {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hSol : IsSolenoidal F) :
    IsSolenoidal (spatialProjectedLin ν F) := by
  unfold spatialProjectedLin spatialDiffReact
  exact UnforcedLeray.Cons.C03.isSolenoidal_add
    (UnforcedLeray.Cons.C03.isSolenoidal_const_smul (isSolenoidal_spatialRadialDrift hF hSol) (1 / 2 : ℝ))
    (UnforcedLeray.Cons.C03.isSolenoidal_add
      (UnforcedLeray.Cons.C03.isSolenoidal_const_smul (isSolenoidal_spatialLaplacian hF hSol) ν)
      (UnforcedLeray.Cons.C03.isSolenoidal_const_smul hSol (1 / 2 : ℝ)))

/-- If `U₀, U₁ ∈ IsUniformSmoothL4SliceFamily`, `HasPhaseJetDeriv U₀ U₁`, and every slice `U₀ τ`
is solenoidal, then every slice `U₁ τ` is solenoidal. -/
theorem isSolenoidal_of_hasPhaseJetDeriv {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasPhaseJetDeriv U₀ U₁)
    (hSol : ∀ τ : ℝ, IsSolenoidal (U₀ τ)) (τ : ℝ) :
    IsSolenoidal (U₁ τ) := by
  have hU₁c : ContDiff ℝ ∞ (U₁ τ) := sliceFamily_contDiff_infty hU₁ τ
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply integrable_finsetSum
    intro i _
    have hFi : Continuous (fun x => U₁ τ x i) :=
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).comp hU₁c.continuous
    exact Continuous.integrable_of_hasCompactSupport
      (hFi.mul (spatialTestDerivative_continuous hφ i))
      (spatialTestDerivative_compact hφ i).mul_left
  · obtain ⟨M, hM⟩ := hU₁.iteratedFDeriv_bounded 0
    set L : ℝ := max M 0
    have hL : ∀ (s : ℝ) (x : Space), ‖U₁ s x‖ ≤ L := by
      intro s x
      have h0 := hM s x
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0.trans (le_max_left M 0)
    let F : ℝ → Space → ℝ := fun s x => ∑ i : Fin 3, U₀ s x i * spatialTestDerivative i φ x
    let F' : ℝ → Space → ℝ := fun s x => ∑ i : Fin 3, U₁ s x i * spatialTestDerivative i φ x
    let bound : Space → ℝ := fun x => ∑ i : Fin 3, L * ‖spatialTestDerivative i φ x‖
    have hbound_int : Integrable bound volume := by
      apply integrable_finsetSum
      intro i _
      exact (Continuous.integrable_of_hasCompactSupport
        (spatialTestDerivative_continuous hφ i).norm
        (spatialTestDerivative_compact hφ i).norm).const_mul L
    have hF_meas : ∀ᶠ s in 𝓝 τ, AEStronglyMeasurable (F s) volume := by
      refine Eventually.of_forall fun s => ?_
      have hU₀s : Continuous (U₀ s) := (sliceFamily_contDiff_infty hU₀ s).continuous
      have hFs : Continuous (F s) :=
        continuous_finsetSum _ fun i _ =>
          (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hU₀s).mul
            (spatialTestDerivative_continuous hφ i))
      exact hFs.aestronglyMeasurable
    have hF_int : Integrable (F τ) volume := (hSol τ).integrable φ hφ
    have hF'_meas : AEStronglyMeasurable (F' τ) volume := by
      have hF's : Continuous (F' τ) :=
        continuous_finsetSum _ fun i _ =>
          (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hU₁c.continuous).mul
            (spatialTestDerivative_continuous hφ i))
      exact hF's.aestronglyMeasurable
    have hF'_le : ∀ᵐ x ∂volume, ∀ s ∈ (univ : Set ℝ), ‖F' s x‖ ≤ bound x := by
      refine ae_of_all _ fun x s _ => ?_
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (U₁ s x) i).trans (hL s x))
        (norm_nonneg _)
    have hF_deriv : ∀ᵐ x ∂volume, ∀ s ∈ (univ : Set ℝ), HasDerivAt (fun t => F t x) (F' s x) s := by
      refine ae_of_all _ fun x s _ => ?_
      have hd : ∀ i : Fin 3,
          HasDerivAt (fun t => U₀ t x i * spatialTestDerivative i φ x)
            (U₁ s x i * spatialTestDerivative i φ x) s := by
        intro i
        have h1 : HasDerivAt (fun t => U₀ t x i) (U₁ s x i) s :=
          ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (hDeriv [] s x))
        exact h1.mul_const (spatialTestDerivative i φ x)
      exact HasDerivAt.fun_sum fun i _ => hd i
    have hIntDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      univ_mem hF_meas hF_int hF'_meas hF'_le hbound_int hF_deriv).2
    have hZero : (fun t : ℝ => ∫ x, F t x) = fun _ => 0 := by
      funext t
      exact (hSol t).identity φ hφ
    rw [hZero] at hIntDeriv
    exact hIntDeriv.unique (hasDerivAt_const τ (0 : ℝ))

/-- Every slice of `U₁ - bgPhaseDerivTower ν U₀ 1` is distributionally solenoidal. -/
theorem isSolenoidal_sub_bgPhaseDerivTower_one (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasPhaseJetDeriv U₀ U₁)
    (hSol : ∀ τ : ℝ, IsSolenoidal (U₀ τ)) (τ : ℝ) :
    IsSolenoidal (U₁ τ - bgPhaseDerivTower ν U₀ 1 τ) := by
  have hSolU₁ : IsSolenoidal (U₁ τ) :=
    isSolenoidal_of_hasPhaseJetDeriv hU₀ hU₁ hDeriv hSol τ
  have hSolLin : IsSolenoidal (spatialProjectedLin ν (U₀ τ)) :=
    isSolenoidal_spatialProjectedLin ν (sliceFamily_contDiff_infty hU₀ τ) (hSol τ)
  have hSolConv : IsSolenoidal (smoothConvectiveLeray U₀ U₀ τ) :=
    PointwiseDerivSub.isSolenoidal_smoothConvectiveLeray hU₀ hU₀ τ
  have hTower : bgPhaseDerivTower ν U₀ 1 τ =
      spatialProjectedLin ν (U₀ τ) - smoothConvectiveLeray U₀ U₀ τ :=
    congrFun (ProjectedEvolutionSub.bgPhaseDerivTower_one ν U₀) τ
  rw [hTower]
  exact isSolenoidal_sub hSolU₁ (isSolenoidal_sub hSolLin hSolConv)

/-- Joint continuity on `ℝ × Space` of `spatialProjectedLin ν (U₀ τ) y` under `HasPhaseJetDeriv U₀ U₁`. -/
theorem continuous_uncurried_spatialProjectedLin (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasPhaseJetDeriv U₀ U₁) :
    Continuous (uncurriedField (fun τ => spatialProjectedLin ν (U₀ τ))) := by
  have h0 : Continuous (uncurriedField U₀) :=
    PointwiseDerivSub.continuous_jet_of_hasPhaseJetDeriv hU₀ hU₁ hDeriv []
  have h1 : ∀ j : Fin 3, Continuous (uncurriedField (fun τ => spatialPartial j (U₀ τ))) :=
    fun j => PointwiseDerivSub.continuous_jet_of_hasPhaseJetDeriv hU₀ hU₁ hDeriv
      [EuclideanSpace.single j 1]
  have h2 : ∀ j : Fin 3, Continuous (uncurriedField (fun τ =>
      dirSpatialJet (U₀ τ) [EuclideanSpace.single j 1, EuclideanSpace.single j 1])) :=
    fun j => PointwiseDerivSub.continuous_jet_of_hasPhaseJetDeriv hU₀ hU₁ hDeriv
      [EuclideanSpace.single j 1, EuclideanSpace.single j 1]
  have hRad : Continuous (uncurriedField (fun τ => spatialRadialDrift (U₀ τ))) := by
    have heq : uncurriedField (fun τ => spatialRadialDrift (U₀ τ)) =
        fun x : ℝ × Space => ∑ j : Fin 3, (x.2 j) • spatialPartial j (U₀ x.1) x.2 := by
      funext x
      exact spatialRadialDrift_eq_sum_coord_spatialPartial (U₀ x.1) x.2
    rw [heq]
    exact continuous_finsetSum _ fun j _ =>
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp continuous_snd).smul (h1 j))
  have hLap : Continuous (uncurriedField (fun τ => spatialLaplacian (U₀ τ))) := by
    have heq : uncurriedField (fun τ => spatialLaplacian (U₀ τ)) =
        fun x : ℝ × Space => ∑ j : Fin 3,
          dirSpatialJet (U₀ x.1) [EuclideanSpace.single j 1, EuclideanSpace.single j 1] x.2 := by
      funext x
      simp [uncurriedField, spatialLaplacian]
    rw [heq]
    exact continuous_finsetSum _ fun j _ => h2 j
  exact (hRad.const_smul (1 / 2 : ℝ)).add ((hLap.const_smul ν).add (h0.const_smul (1 / 2 : ℝ)))

/-- Joint continuity on `ℝ × Space` of `bgPhaseDerivTower ν U₀ 1` under `SmoothLeraySliceRegularity`
and `HasPhaseJetDeriv U₀ U₁`. -/
theorem continuous_uncurried_bgPhaseDerivTower_one
    (hLeray : SmoothLeraySliceRegularity) (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasPhaseJetDeriv U₀ U₁) :
    Continuous (uncurriedField (bgPhaseDerivTower ν U₀ 1)) := by
  have hLin : Continuous (uncurriedField (fun τ => spatialProjectedLin ν (U₀ τ))) :=
    continuous_uncurried_spatialProjectedLin ν hU₀ hU₁ hDeriv
  have hConv : Continuous (uncurriedField (smoothConvectiveLeray U₀ U₀)) :=
    PointwiseDerivSub.continuous_jet_of_hasPhaseJetDeriv
      (sliceFamily_smoothConvectiveLeray hLeray U₀ U₀ hU₀ hU₀)
      (sliceFamily_add
        (sliceFamily_smoothConvectiveLeray hLeray U₁ U₀ hU₁ hU₀)
        (sliceFamily_smoothConvectiveLeray hLeray U₀ U₁ hU₀ hU₁))
      (hasPhaseJetDeriv_smoothConvectiveLeray hLeray U₀ U₁ U₀ U₁ hU₀ hU₁ hU₀ hU₁ hDeriv hDeriv)
      []
  have heq : uncurriedField (bgPhaseDerivTower ν U₀ 1) =
      fun x : ℝ × Space => spatialProjectedLin ν (U₀ x.1) x.2 - smoothConvectiveLeray U₀ U₀ x.1 x.2 := by
    funext x
    exact congrFun (congrFun (ProjectedEvolutionSub.bgPhaseDerivTower_one ν U₀) x.1) x.2
  rw [heq]
  exact hLin.sub hConv

theorem realC_eq_ofReV (x : Space) : realC x = ofReV x := by
  ext i
  simp [realC_apply]

/-- `x ↦ dotL w (realC x)` as a continuous ℝ-linear functional on `Space`. -/
def dotLRealCLM (w : CVec3) : Space →L[ℝ] ℂ :=
  ((dotL w).restrictScalars ℝ).comp ofReV

@[simp] theorem dotLRealCLM_apply (w : CVec3) (x : Space) :
    dotLRealCLM w x = dotL w (realC x) := by
  simp [dotLRealCLM, realC_eq_ofReV]

theorem norm_dotL_realC_le (w : CVec3) (x : Space) :
    ‖dotL w (realC x)‖ ≤ ‖dotL‖ * ‖w‖ * ‖x‖ := by
  rw [realC_eq_ofReV]
  calc ‖dotL w (ofReV x)‖
      ≤ ‖dotL w‖ * ‖ofReV x‖ := (dotL w).le_opNorm (ofReV x)
    _ ≤ (‖dotL‖ * ‖w‖) * ‖x‖ := by
        rw [show ‖ofReV x‖ = ‖x‖ from norm_ofReVLin x]
        exact mul_le_mul_of_nonneg_right (dotL.le_opNorm w) (norm_nonneg x)
    _ = ‖dotL‖ * ‖w‖ * ‖x‖ := by ring

theorem integrable_dotL_realC_of_spatialSolTest {Ψ : Space → CVec3} (hΨ : SpatialSolTest Ψ)
    {F : SpatialField} (hF : Continuous F) :
    Integrable (fun y => dotL (Ψ y) (realC (F y))) volume := by
  have hcont : Continuous (fun y => dotL (Ψ y) (realC (F y))) := by
    have h1 : Continuous (fun y => dotL (Ψ y)) := dotL.continuous.comp (o2Cont hΨ)
    have h2 : Continuous (fun y => realC (F y)) := by
      simp_rw [realC_eq_ofReV]
      exact ofReV.continuous.comp hF
    exact h1.clm_apply h2
  have hcs : HasCompactSupport (fun y => dotL (Ψ y) (realC (F y))) := by
    refine HasCompactSupport.intro hΨ.2.1.isCompact fun y hy => ?_
    have h0 : Ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [h0]
  exact hcont.integrable_of_hasCompactSupport hcs

/-- Derivative of the `n`-th Fourier character `t ↦ fourier n (t : AddCircle P)` on `ℝ`. -/
theorem hasDerivAt_fourier_coe (P : ℝ) (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fourier n (s : AddCircle P))
      ((2 * ↑Real.pi * Complex.I * (n : ℂ) / (P : ℂ)) * fourier n (t : AddCircle P)) t := by
  let c : ℂ := 2 * ↑Real.pi * Complex.I * (n : ℂ) / (P : ℂ)
  have heq : (fun s : ℝ => fourier n (s : AddCircle P)) =
      fun s : ℝ => Complex.exp (c * (s : ℂ)) := by
    funext s
    rw [fourier_coe_apply]
    congr 1
    dsimp [c]
    ring
  have hval : Complex.exp (c * (t : ℂ)) * (c * 1) = c * fourier n (t : AddCircle P) := by
    rw [fourier_coe_apply]
    dsimp [c]
    ring
  rw [heq, ← hval]
  exact (((hasDerivAt_id t).ofReal_comp).const_mul c).cexp

/-- If `K : ℝ → ℂ` is `P`-periodic, everywhere differentiable with derivative `h`, and
`∫ t in (0 : ℝ)..P, fourier n (t : AddCircle P) * h t = 0` for all `n : ℤ`, then `h τ = 0` for all `τ`. -/
theorem deriv_eq_zero_of_periodic_of_fourier_deriv_eq_zero
    {P : ℝ} [hP : Fact (0 < P)] {H h : ℝ → ℂ}
    (hH_per : Function.Periodic H P)
    (hH_deriv : ∀ t : ℝ, HasDerivAt H (h t) t)
    (hh_int : ∀ a b : ℝ, IntervalIntegrable h volume a b)
    (hFourier : ∀ n : ℤ, ∫ t in (0 : ℝ)..P, fourier n (t : AddCircle P) * h t = 0)
    (τ : ℝ) : h τ = 0 := by
  have hH_cont : Continuous H :=
    Differentiable.continuous fun t => (hH_deriv t).differentiableAt
  have hH_lift_cont : Continuous hH_per.lift :=
    continuous_coinduced_dom.mpr hH_cont
  let c : ℂ := ∫ z : AddCircle P, hH_per.lift z ∂AddCircle.haarAddCircle
  let K : ℝ → ℂ := fun t => H t - c
  have hK_per : Function.Periodic K P := fun t => by
    simp [K, hH_per t]
  have hK_deriv : ∀ t : ℝ, HasDerivAt K (h t) t := fun t =>
    (hH_deriv t).sub_const c
  have hK_cont : Continuous K := hH_cont.sub continuous_const
  have hK_lift_cont : Continuous hK_per.lift :=
    continuous_coinduced_dom.mpr hK_cont
  have hK_lift_int : Integrable hK_per.lift AddCircle.haarAddCircle :=
    hK_lift_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace hK_per.lift)
  have hK_lift_eq : hK_per.lift = fun z : AddCircle P => hH_per.lift z - c := by
    funext z
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      simp [Function.Periodic.lift_coe, K]
  have hK_fourier : ∀ n : ℤ,
      ∫ z : AddCircle P, fourier n z * hK_per.lift z ∂AddCircle.haarAddCircle = 0 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [fourier_zero, one_mul, hK_lift_eq]
      have hintH : Integrable hH_per.lift AddCircle.haarAddCircle :=
        hH_lift_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace hH_per.lift)
      rw [integral_sub hintH (integrable_const c), integral_const]
      simp [c]
    · let cn : ℂ := 2 * ↑Real.pi * Complex.I * (n : ℂ) / (P : ℂ)
      have hcn : cn ≠ 0 := by
        dsimp [cn]
        refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_) ?_
        · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        · exact Int.cast_ne_zero.mpr hn
        · exact Complex.ofReal_ne_zero.mpr hP.out.ne'
      have hprod_deriv : ∀ t ∈ uIcc (0 : ℝ) P,
          HasDerivAt (fun s : ℝ => fourier n (s : AddCircle P) * K s)
            (cn * (fourier n (t : AddCircle P) * K t) + fourier n (t : AddCircle P) * h t) t := by
        intro t _
        have hd := (hasDerivAt_fourier_coe P n t).mul (hK_deriv t)
        rwa [show (2 * ↑Real.pi * Complex.I * (n : ℂ) / (P : ℂ)) * fourier n (t : AddCircle P) * K t =
          cn * (fourier n (t : AddCircle P) * K t) from mul_assoc _ _ _] at hd
      have hint1 : IntervalIntegrable (fun t : ℝ => cn * (fourier n (t : AddCircle P) * K t)) volume 0 P := by
        have hc : Continuous (fun t : ℝ => cn * (fourier n (t : AddCircle P) * K t)) :=
          continuous_const.mul (((fourier n).continuous.comp (AddCircle.continuous_mk' P)).mul hK_cont)
        exact hc.intervalIntegrable 0 P
      have hint2 : IntervalIntegrable (fun t : ℝ => fourier n (t : AddCircle P) * h t) volume 0 P := by
        have hc : Continuous (fun t : ℝ => fourier n (t : AddCircle P)) :=
          (fourier n).continuous.comp (AddCircle.continuous_mk' P)
        exact (hh_int 0 P).continuousOn_mul hc.continuousOn
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod_deriv (hint1.add hint2)
      have hend : fourier n (P : AddCircle P) * K P - fourier n ((0 : ℝ) : AddCircle P) * K 0 = 0 := by
        have hp1 : (P : AddCircle P) = ((0 : ℝ) : AddCircle P) := by
          simp
        have hp2 : K P = K 0 := by simpa using hK_per 0
        rw [hp1, hp2, sub_self]
      rw [hend, intervalIntegral.integral_add hint1 hint2, hFourier n, add_zero,
        intervalIntegral.integral_const_mul] at hftc
      have hint_zero : ∫ t in (0 : ℝ)..P, fourier n (t : AddCircle P) * K t = 0 :=
        (mul_eq_zero.mp hftc).resolve_left hcn
      have hpre := AddCircle.intervalIntegral_preimage P 0
        (fun z : AddCircle P => fourier n z * hK_per.lift z)
      rw [zero_add, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
        ENNReal.toReal_ofReal hP.out.le] at hpre
      have hpre' : (∫ t in (0 : ℝ)..P, fourier n (t : AddCircle P) * K t) =
          P • ∫ z : AddCircle P, fourier n z * hK_per.lift z ∂AddCircle.haarAddCircle := by
        simpa [Function.Periodic.lift_coe] using hpre
      rw [hint_zero, Complex.real_smul] at hpre'
      exact (mul_eq_zero.mp hpre'.symm).resolve_left (Complex.ofReal_ne_zero.mpr hP.out.ne')
  have hae := ae_eq_zero_of_fourier hK_lift_int hK_fourier
  have hK_lift_zero : hK_per.lift = 0 :=
    (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle hK_lift_cont continuous_const).mp hae
  have hK_zero : K = fun _ => 0 := by
    funext t
    have := congrFun hK_lift_zero (t : AddCircle P)
    simpa [Function.Periodic.lift_coe] using this
  have h0 : HasDerivAt K 0 τ := by
    rw [hK_zero]
    exact hasDerivAt_const τ 0
  exact (hK_deriv τ).unique h0

/-- Slice-by-slice spatial solenoidal-test orthogonality of `U₁ - bgPhaseDerivTower ν U₀ 1`. -/
theorem integral_dotL_sub_bgPhaseDerivTower_one_eq_zero
    {P : ℝ} [hP : Fact (0 < P)] (ν : ℝ)
    (hLeray : SmoothLeraySliceRegularity)
    {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hT₁_fam : IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ 1))
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hDeriv : HasPhaseJetDeriv U₀ U₁)
    (hPer₀ : Function.Periodic U₀ P)
    (hPair : ∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ →
      pairF P Φ (fun x => realC ((U₁ x.1 - bgPhaseDerivTower ν U₀ 1 x.1) x.2)) = 0)
    (τ : ℝ) (Ψ : Space → CVec3) (hΨ : SpatialSolTest Ψ) :
    ∫ y, dotL (Ψ y) (realC ((U₁ τ - bgPhaseDerivTower ν U₀ 1 τ) y)) = 0 := by
  let T₁ : ℝ → SpatialField := bgPhaseDerivTower ν U₀ 1
  let D : ℝ → SpatialField := fun t => U₁ t - T₁ t
  let F₀ : ℝ → ℂ := fun t => ∫ y, dotL (Ψ y) (realC (U₀ t y))
  let F₁ : ℝ → ℂ := fun t => ∫ y, dotL (Ψ y) (realC (U₁ t y))
  let G₁ : ℝ → ℂ := fun t => ∫ y, dotL (Ψ y) (realC (T₁ t y))
  let h : ℝ → ℂ := fun t => ∫ y, dotL (Ψ y) (realC (D t y))
  have hh_eq : ∀ t : ℝ, h t = F₁ t - G₁ t := by
    intro t
    have hint1 : Integrable (fun y => dotL (Ψ y) (realC (U₁ t y))) volume :=
      integrable_dotL_realC_of_spatialSolTest hΨ (sliceFamily_contDiff_infty hU₁ t).continuous
    have hint2 : Integrable (fun y => dotL (Ψ y) (realC (T₁ t y))) volume :=
      integrable_dotL_realC_of_spatialSolTest hΨ (sliceFamily_contDiff_infty hT₁_fam t).continuous
    have hsub : (fun y => dotL (Ψ y) (realC (D t y))) =
        fun y => dotL (Ψ y) (realC (U₁ t y)) - dotL (Ψ y) (realC (T₁ t y)) := by
      funext y
      simp only [D, Pi.sub_apply, ← dotLRealCLM_apply, map_sub]
    dsimp [h, F₁, G₁]
    rw [hsub, integral_sub hint1 hint2]
  obtain ⟨M₁, hM₁⟩ := hU₁.iteratedFDeriv_bounded 0
  set L₁ : ℝ := max M₁ 0
  have hL₁ : ∀ (s : ℝ) (y : Space), ‖U₁ s y‖ ≤ L₁ := by
    intro s y
    have h0 := hM₁ s y
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left M₁ 0)
  let bound₁ : Space → ℝ := fun y => ‖dotL‖ * ‖Ψ y‖ * L₁
  have hbound₁_int : Integrable bound₁ volume := by
    have hΨ_int : Integrable (fun y => ‖Ψ y‖) volume :=
      (o2Cont hΨ).norm.integrable_of_hasCompactSupport hΨ.2.1.norm
    exact (hΨ_int.const_mul ‖dotL‖).mul_const L₁
  have hF₁_le_bound₁ : ∀ (s : ℝ) (y : Space),
      ‖dotL (Ψ y) (realC (U₁ s y))‖ ≤ bound₁ y := by
    intro s y
    exact (norm_dotL_realC_le (Ψ y) (U₁ s y)).trans
      (mul_le_mul_of_nonneg_left (hL₁ s y) (mul_nonneg (norm_nonneg dotL) (norm_nonneg (Ψ y))))
  have hF₀_deriv : ∀ t : ℝ, HasDerivAt F₀ (F₁ t) t := by
    intro t
    have hF_meas : ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (fun y => dotL (Ψ y) (realC (U₀ s y))) volume := by
      refine Eventually.of_forall fun s => ?_
      exact (integrable_dotL_realC_of_spatialSolTest hΨ
        (sliceFamily_contDiff_infty hU₀ s).continuous).aestronglyMeasurable
    have hF_int : Integrable (fun y => dotL (Ψ y) (realC (U₀ t y))) volume :=
      integrable_dotL_realC_of_spatialSolTest hΨ (sliceFamily_contDiff_infty hU₀ t).continuous
    have hF'_meas : AEStronglyMeasurable (fun y => dotL (Ψ y) (realC (U₁ t y))) volume :=
      (integrable_dotL_realC_of_spatialSolTest hΨ
        (sliceFamily_contDiff_infty hU₁ t).continuous).aestronglyMeasurable
    have hF'_le : ∀ᵐ y ∂volume, ∀ s ∈ (univ : Set ℝ),
        ‖dotL (Ψ y) (realC (U₁ s y))‖ ≤ bound₁ y :=
      ae_of_all _ fun y s _ => hF₁_le_bound₁ s y
    have hF_d : ∀ᵐ y ∂volume, ∀ s ∈ (univ : Set ℝ),
        HasDerivAt (fun r => dotL (Ψ y) (realC (U₀ r y)))
          (dotL (Ψ y) (realC (U₁ s y))) s := by
      refine ae_of_all _ fun y s _ => ?_
      simp only [← dotLRealCLM_apply]
      exact (dotLRealCLM (Ψ y)).hasFDerivAt.comp_hasDerivAt s (hDeriv [] s y)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      univ_mem hF_meas hF_int hF'_meas hF'_le hbound₁_int hF_d).2
  obtain ⟨M₂, hM₂⟩ := hT₁_fam.iteratedFDeriv_bounded 0
  set L₂ : ℝ := max M₂ 0
  have hL₂ : ∀ (s : ℝ) (y : Space), ‖T₁ s y‖ ≤ L₂ := by
    intro s y
    have h0 := hM₂ s y
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left M₂ 0)
  let bound₂ : Space → ℝ := fun y => ‖dotL‖ * ‖Ψ y‖ * L₂
  have hbound₂_int : Integrable bound₂ volume := by
    have hΨ_int : Integrable (fun y => ‖Ψ y‖) volume :=
      (o2Cont hΨ).norm.integrable_of_hasCompactSupport hΨ.2.1.norm
    exact (hΨ_int.const_mul ‖dotL‖).mul_const L₂
  have hG₁_cont : Continuous G₁ := by
    have hT₁_cont : Continuous (uncurriedField T₁) :=
      continuous_uncurried_bgPhaseDerivTower_one hLeray ν hU₀ hU₁ hDeriv
    refine MeasureTheory.continuous_of_dominated
      (fun s => (integrable_dotL_realC_of_spatialSolTest hΨ
        (sliceFamily_contDiff_infty hT₁_fam s).continuous).aestronglyMeasurable)
      (fun s => ae_of_all _ fun y => (norm_dotL_realC_le (Ψ y) (T₁ s y)).trans
        (mul_le_mul_of_nonneg_left (hL₂ s y) (mul_nonneg (norm_nonneg dotL) (norm_nonneg (Ψ y)))))
      hbound₂_int
      (ae_of_all _ fun y => ?_)
    simp_rw [← dotLRealCLM_apply]
    exact (dotLRealCLM (Ψ y)).continuous.comp (hT₁_cont.comp (continuous_id.prodMk continuous_const))
  have hF₁_int : ∀ a b : ℝ, IntervalIntegrable F₁ volume a b := by
    intro a b
    have hF₁_eq : F₁ = deriv F₀ := by
      funext s
      exact (hF₀_deriv s).deriv.symm
    have hF₁_meas : AEStronglyMeasurable F₁ volume := by
      rw [hF₁_eq]
      exact aestronglyMeasurable_deriv F₀ volume
    have hF₁_bdd : ∀ s : ℝ, ‖F₁ s‖ ≤ ∫ y, bound₁ y := fun s =>
      norm_integral_le_of_norm_le hbound₁_int (ae_of_all _ fun y => hF₁_le_bound₁ s y)
    exact (IntegrableOn.of_bound measure_Icc_lt_top hF₁_meas.restrict (∫ y, bound₁ y)
      (ae_of_all _ fun s => hF₁_bdd s)).intervalIntegrable
  have hh_int : ∀ a b : ℝ, IntervalIntegrable h volume a b := by
    intro a b
    have heq : h = fun s => F₁ s - G₁ s := funext hh_eq
    rw [heq]
    exact (hF₁_int a b).sub (hG₁_cont.intervalIntegrable a b)
  have hF₀_per : Function.Periodic F₀ P := fun t => by
    dsimp [F₀]
    rw [hPer₀ t]
  have hT₁_per : Function.Periodic T₁ P := by
    intro t
    have h1 := congrFun (ProjectedEvolutionSub.bgPhaseDerivTower_one ν U₀) (t + P)
    have h2 := congrFun (ProjectedEvolutionSub.bgPhaseDerivTower_one ν U₀) t
    change bgPhaseDerivTower ν U₀ 1 (t + P) = bgPhaseDerivTower ν U₀ 1 t
    rw [h1, h2]
    simp [smoothConvectiveLeray, smoothLeraySlice, hPer₀ t]
  have hG₁_per : Function.Periodic G₁ P := fun t => by
    dsimp [G₁]
    rw [hT₁_per t]
  have hFourier : ∀ n : ℤ, ∫ t in (0 : ℝ)..P, fourier n (t : AddCircle P) * h t = 0 := by
    intro n
    have hpair_n := hPair (fun p : ℝ × Space => fourier n (p.1 : AddCircle P) • Ψ p.2)
      (o2IsSolTest P n hΨ)
    unfold pairF phaseInt at hpair_n
    rw [Complex.real_smul] at hpair_n
    have hP_inv_ne : ((P⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero hP.out.ne')
    have hint_Ioc := (mul_eq_zero.mp hpair_n).resolve_left hP_inv_ne
    have hslice_eq : ∀ t : ℝ,
        (∫ y, dotL (fourier n (t : AddCircle P) • Ψ y) (realC (D t y))) =
          fourier n (t : AddCircle P) * h t := by
      intro t
      have heq : (fun y => dotL (fourier n (t : AddCircle P) • Ψ y) (realC (D t y))) =
          fun y => fourier n (t : AddCircle P) * dotL (Ψ y) (realC (D t y)) := by
        funext y
        rw [map_smul, smul_apply, smul_eq_mul]
      rw [heq, integral_const_mul]
    rw [intervalIntegral.integral_of_le hP.out.le]
    simp_rw [← hslice_eq]
    exact hint_Ioc
  let H : ℝ → ℂ := fun t => F₀ t - ∫ s in (0 : ℝ)..t, G₁ s
  have hH_deriv : ∀ t : ℝ, HasDerivAt H (h t) t := by
    intro t
    rw [hh_eq t]
    exact (hF₀_deriv t).sub
      (intervalIntegral.integral_hasDerivAt_right (hG₁_cont.intervalIntegrable 0 t)
        (hG₁_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hG₁_cont.continuousAt)
  have hG₁_period_zero : ∫ s in (0 : ℝ)..P, G₁ s = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hH_deriv t) (hh_int 0 P)
    have h0 := hFourier 0
    simp only [fourier_zero, one_mul] at h0
    have hHP : H P - H 0 = 0 := hftc.symm.trans h0
    have hF0P : F₀ P = F₀ 0 := by simpa using hF₀_per 0
    dsimp [H] at hHP
    rw [intervalIntegral.integral_same, sub_zero, hF0P] at hHP
    linear_combination -hHP
  have hH_per : Function.Periodic H P := by
    intro t
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hG₁_cont.intervalIntegrable (μ := volume) 0 t)
      (hG₁_cont.intervalIntegrable (μ := volume) t (t + P))
    have hper_int : ∫ s in t..(t + P), G₁ s = 0 := by
      rw [hG₁_per.intervalIntegral_add_eq t 0, zero_add, hG₁_period_zero]
    dsimp [H]
    rw [hF₀_per t, ← hadj, hper_int, add_zero]
  exact deriv_eq_zero_of_periodic_of_fourier_deriv_eq_zero hH_per hH_deriv hh_int hFourier τ

end SolTestOrthEqZeroAux

/-- Solenoidal phase-test orthogonality forces `U₁ = bgPhaseDerivTower p.ν (bgField p z) 1`. -/
theorem bgSolTestOrthEqZero_proof : UnforcedLeray.Short.IIb.BgSolTestOrthEqZero := by
  intro hLeray p _ _ z hPer₀ hSol hU₀ _ hTower₁ U₁ hU₁ hDeriv hPair
  apply PointwiseDerivSub.eq_bgPhaseDerivTower_one_of_slice_solenoidal_and_orth p.ν hU₁ hTower₁
  · intro τ
    exact SolTestOrthEqZeroAux.isSolenoidal_sub_bgPhaseDerivTower_one p.ν
      hU₀ hU₁ hDeriv hSol τ
  · intro τ Ψ hΨ
    exact SolTestOrthEqZeroAux.integral_dotL_sub_bgPhaseDerivTower_one_eq_zero p.ν
      hLeray hU₀ hTower₁ hU₁ hDeriv hPer₀ hPair τ Ψ hΨ

end UnforcedLeray.Short.IIb

end
