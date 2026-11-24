import UnforcedLeray.Short.PartI.Sub.T02_1_4_6

/-!
# Part I, task `PartI:T02/1/4/6/1`: the Laplacian of a solenoidal cell test is again one

Source of record: `the November 2 reference manuscript`, lines 261-288.

The target `laplacianTestClosed` proves the leaf `LaplacianTestClosed` of
`Short/PartI/Sub/T02_1_4_6.lean`: a smooth `c`-periodic solenoidal field with `η`-compact
support has a Laplacian `Train.vecLaplacian φ` of the same kind.

Proof outline:
* smoothness, periodicity and `η`-compact support pass through the scalar Laplacian
  `Train.lapS` componentwise (`Cyl.contDiff_partialQ`, `Cyl.IsPeriodic.partialQ`,
  `Cyl.VanishesOutside.partialQ`, and their `η`-analogues);
* mixed partial derivatives of a `C^∞` scalar field commute, from the symmetry of the second
  derivative (`ContDiffAt.isSymmSndFDerivAt`); hence `∂_q` and `∂_η` interchange with `Δ`;
* linearity of the partial derivatives on differentiable fields gives
  `div Δφ = Δ (div φ)`, and `div φ` is identically zero, so `div Δφ = 0`.

The commutation lemmas are copies of those in `Lib/TrainB/InitialDatumDerivativeSolenoidal.lean`,
which is not in the import chain of this file.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### Mixed partials of smooth scalar fields -/

theorem lapTC_partialQ_fderiv {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v z : Plane) :
    Cyl.partialQ (fun x => fderiv ℝ f x v) z = fderiv ℝ (Cyl.partialQ f) z v := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf2.fderiv_right (m := 1) (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable one_ne_zero
  have hscalar : Differentiable ℝ (fun x => fderiv ℝ f x v) := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hdd
  have hq : Cyl.partialQ f = fun x => fderiv ℝ f x (1, 0) := by
    funext x
    exact Cyl.partialQ_eq_fderiv (hf.differentiable (by simp)) x
  rw [Cyl.partialQ_eq_fderiv hscalar z, hq]
  rw [fderiv_clm_apply (hdd z) (differentiableAt_const _),
    fderiv_clm_apply (hdd z) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (1, 0) v

theorem lapTC_comm {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ (Cyl.partialEta f) = Cyl.partialEta (Cyl.partialQ f) := by
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ f) := Cyl.contDiff_partialQ hf
  have hdQ : Differentiable ℝ (Cyl.partialQ f) := hQ.differentiable (by simp)
  have hE : Cyl.partialEta f = fun x => fderiv ℝ f x (0, 1) := by
    funext x
    exact Cyl.partialEta_eq_fderiv (hf.differentiable (by simp)) x
  funext z
  rw [hE, lapTC_partialQ_fderiv hf (0, 1) z, Cyl.partialEta_eq_fderiv hdQ z]

/-! ### Linearity and smoothness of the scalar Laplacian -/

theorem lapTC_partialQ_add {f g : Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Cyl.partialQ (fun z => f z + g z) = fun z => Cyl.partialQ f z + Cyl.partialQ g z := by
  have hfg : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  funext z
  have hsum : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z :=
    fderiv_add (hf z) (hg z)
  show Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z
  rw [Cyl.partialQ_eq_fderiv hfg z, Cyl.partialQ_eq_fderiv hf z,
    Cyl.partialQ_eq_fderiv hg z, hsum]
  rfl

theorem lapTC_partialEta_add {f g : Plane → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Cyl.partialEta (fun z => f z + g z) = fun z => Cyl.partialEta f z + Cyl.partialEta g z := by
  have hfg : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  funext z
  have hsum : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z :=
    fderiv_add (hf z) (hg z)
  show Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z
  rw [Cyl.partialEta_eq_fderiv hfg z, Cyl.partialEta_eq_fderiv hf z,
    Cyl.partialEta_eq_fderiv hg z, hsum]
  rfl

theorem lapTC_contDiff_partialQ {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Cyl.partialQ f) :=
  Cyl.contDiff_partialQ hf

theorem lapTC_contDiff_partialEta {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Cyl.partialEta f) :=
  Cyl.contDiff_partialEta hf

theorem lapTC_contDiff_lapS {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Train.lapS f) := by
  have hQQ : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ f)) :=
    lapTC_contDiff_partialQ (lapTC_contDiff_partialQ hf)
  have hEE : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta f)) :=
    lapTC_contDiff_partialEta (lapTC_contDiff_partialEta hf)
  exact hQQ.add hEE

theorem lapTC_partialQ_lapS {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ (Train.lapS f) = Train.lapS (Cyl.partialQ f) := by
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ f) := lapTC_contDiff_partialQ hf
  have hE : ContDiff ℝ ∞ (Cyl.partialEta f) := lapTC_contDiff_partialEta hf
  have hQQ : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ f)) := lapTC_contDiff_partialQ hQ
  have hEE : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta f)) := lapTC_contDiff_partialEta hE
  have hdQQ : Differentiable ℝ (Cyl.partialQ (Cyl.partialQ f)) := hQQ.differentiable (by simp)
  have hdEE : Differentiable ℝ (Cyl.partialEta (Cyl.partialEta f)) :=
    hEE.differentiable (by simp)
  have key : Cyl.partialQ (Cyl.partialEta (Cyl.partialEta f)) =
      Cyl.partialEta (Cyl.partialEta (Cyl.partialQ f)) := by
    rw [lapTC_comm hE, lapTC_comm hf]
  show Cyl.partialQ (fun z => Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z)
      = fun z => Cyl.partialQ (Cyl.partialQ (Cyl.partialQ f)) z
        + Cyl.partialEta (Cyl.partialEta (Cyl.partialQ f)) z
  rw [lapTC_partialQ_add hdQQ hdEE, key]

theorem lapTC_partialEta_lapS {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialEta (Train.lapS f) = Train.lapS (Cyl.partialEta f) := by
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ f) := lapTC_contDiff_partialQ hf
  have hE : ContDiff ℝ ∞ (Cyl.partialEta f) := lapTC_contDiff_partialEta hf
  have hQQ : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.partialQ f)) := lapTC_contDiff_partialQ hQ
  have hEE : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.partialEta f)) := lapTC_contDiff_partialEta hE
  have hdQQ : Differentiable ℝ (Cyl.partialQ (Cyl.partialQ f)) := hQQ.differentiable (by simp)
  have hdEE : Differentiable ℝ (Cyl.partialEta (Cyl.partialEta f)) :=
    hEE.differentiable (by simp)
  have key : Cyl.partialEta (Cyl.partialQ (Cyl.partialQ f)) =
      Cyl.partialQ (Cyl.partialQ (Cyl.partialEta f)) := by
    rw [← lapTC_comm hQ, lapTC_comm hf]
  show Cyl.partialEta (fun z => Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z)
      = fun z => Cyl.partialQ (Cyl.partialQ (Cyl.partialEta f)) z
        + Cyl.partialEta (Cyl.partialEta (Cyl.partialEta f)) z
  rw [lapTC_partialEta_add hdQQ hdEE, key]

theorem lapTC_lapS_add {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    Train.lapS (fun z => f z + g z) = fun z => Train.lapS f z + Train.lapS g z := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hdQf : Differentiable ℝ (Cyl.partialQ f) :=
    (lapTC_contDiff_partialQ hf).differentiable (by simp)
  have hdQg : Differentiable ℝ (Cyl.partialQ g) :=
    (lapTC_contDiff_partialQ hg).differentiable (by simp)
  have hdEf : Differentiable ℝ (Cyl.partialEta f) :=
    (lapTC_contDiff_partialEta hf).differentiable (by simp)
  have hdEg : Differentiable ℝ (Cyl.partialEta g) :=
    (lapTC_contDiff_partialEta hg).differentiable (by simp)
  funext z
  show Cyl.partialQ (Cyl.partialQ (fun y => f y + g y)) z
      + Cyl.partialEta (Cyl.partialEta (fun y => f y + g y)) z
      = (Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z)
      + (Cyl.partialQ (Cyl.partialQ g) z + Cyl.partialEta (Cyl.partialEta g) z)
  simp only [lapTC_partialQ_add hdf hdg, lapTC_partialEta_add hdf hdg,
    lapTC_partialQ_add hdQf hdQg, lapTC_partialEta_add hdEf hdEg]
  ring

/-! ### Components and the vector Laplacian -/

theorem lapTC_contDiff_comp0 {φ : Plane → Vec} (hsm : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w => φ w 0) :=
  (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hsm

theorem lapTC_contDiff_comp1 {φ : Plane → Vec} (hsm : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w => φ w 1) :=
  (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hsm

theorem lapTC_contDiff_vecLaplacian {φ : Plane → Vec} (hsm : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Train.vecLaplacian φ) := by
  have hL0 : ContDiff ℝ ∞ (Train.lapS (fun w => φ w 0)) :=
    lapTC_contDiff_lapS (lapTC_contDiff_comp0 hsm)
  have hL1 : ContDiff ℝ ∞ (Train.lapS (fun w => φ w 1)) :=
    lapTC_contDiff_lapS (lapTC_contDiff_comp1 hsm)
  have hpair : ContDiff ℝ ∞ (fun z => (Train.lapS (fun w => φ w 0) z,
      Train.lapS (fun w => φ w 1) z)) := hL0.prodMk hL1
  have hT : ContDiff ℝ ∞ (fun z => Train.toVecL (Train.lapS (fun w => φ w 0) z,
      Train.lapS (fun w => φ w 1) z)) := Train.toVecL.contDiff.comp hpair
  exact hT

theorem lapTC_div_vecLaplacian {φ : Plane → Vec} (hsm : ContDiff ℝ ∞ φ)
    (hdiv : ∀ z, Cyl.divergence φ z = 0) (z : Plane) :
    Cyl.divergence (Train.vecLaplacian φ) z = 0 := by
  have hf0 : ContDiff ℝ ∞ (fun w => φ w 0) := lapTC_contDiff_comp0 hsm
  have hf1 : ContDiff ℝ ∞ (fun w => φ w 1) := lapTC_contDiff_comp1 hsm
  have hfun : (fun y => Cyl.partialQ (fun w => φ w 0) y + Cyl.partialEta (fun w => φ w 1) y)
      = fun _ => (0 : ℝ) := funext fun y => hdiv y
  have hA : Cyl.partialQ (Train.lapS (fun w => φ w 0)) z
      = Train.lapS (Cyl.partialQ (fun w => φ w 0)) z :=
    congrFun (lapTC_partialQ_lapS hf0) z
  have hB : Cyl.partialEta (Train.lapS (fun w => φ w 1)) z
      = Train.lapS (Cyl.partialEta (fun w => φ w 1)) z :=
    congrFun (lapTC_partialEta_lapS hf1) z
  have hS : Train.lapS (fun y => Cyl.partialQ (fun w => φ w 0) y
      + Cyl.partialEta (fun w => φ w 1) y) z
      = Train.lapS (Cyl.partialQ (fun w => φ w 0)) z
        + Train.lapS (Cyl.partialEta (fun w => φ w 1)) z :=
    congrFun (lapTC_lapS_add (lapTC_contDiff_partialQ hf0)
      (lapTC_contDiff_partialEta hf1)) z
  show Cyl.partialQ (Train.lapS (fun w => φ w 0)) z
      + Cyl.partialEta (Train.lapS (fun w => φ w 1)) z = 0
  rw [hA, hB, ← hS, hfun]
  simp [Train.lapS, Cyl.partialQ, Cyl.partialEta]

theorem lapTC_periodic_lapS {c : ℝ} {f : Plane → ℝ} (hf : Cyl.IsPeriodic c f) :
    Cyl.IsPeriodic c (Train.lapS f) := by
  intro z
  have h1 : Cyl.partialQ (Cyl.partialQ f) (z.1 + c, z.2) = Cyl.partialQ (Cyl.partialQ f) z :=
    hf.partialQ.partialQ z
  have h2 : Cyl.partialEta (Cyl.partialEta f) (z.1 + c, z.2) =
      Cyl.partialEta (Cyl.partialEta f) z :=
    hf.partialEta.partialEta z
  show Cyl.partialQ (Cyl.partialQ f) (z.1 + c, z.2)
      + Cyl.partialEta (Cyl.partialEta f) (z.1 + c, z.2)
      = Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z
  rw [h1, h2]

theorem lapTC_vanish_lapS {R : ℝ} {f : Plane → ℝ} (hf : Cyl.VanishesOutside R f) :
    Cyl.VanishesOutside R (Train.lapS f) := by
  intro z hz
  have h1 : Cyl.partialQ (Cyl.partialQ f) z = 0 := hf.partialQ.partialQ z hz
  have h2 : Cyl.partialEta (Cyl.partialEta f) z = 0 := hf.partialEta.partialEta z hz
  show Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z = 0
  rw [h1, h2, add_zero]

/-! ### The target -/

theorem laplacianTestClosed : LaplacianTestClosed := by
  unfold LaplacianTestClosed
  intro c _hc φ hφ
  unfold IsSolenoidalCellTest IsCellTest at hφ ⊢
  obtain ⟨⟨hsm, hper, R, hR⟩, hdiv⟩ := hφ
  have hv0 : Cyl.VanishesOutside R (fun w => φ w 0) := fun z hz => by simp [hR z hz]
  have hv1 : Cyl.VanishesOutside R (fun w => φ w 1) := fun z hz => by simp [hR z hz]
  have hPer0 : Cyl.IsPeriodic c (fun w => φ w 0) :=
    fun z => congrArg (fun v : Vec => v 0) (hper z)
  have hPer1 : Cyl.IsPeriodic c (fun w => φ w 1) :=
    fun z => congrArg (fun v : Vec => v 1) (hper z)
  refine ⟨⟨lapTC_contDiff_vecLaplacian hsm, ?_, R, ?_⟩, lapTC_div_vecLaplacian hsm hdiv⟩
  · intro z
    have e0 : Train.lapS (fun w => φ w 0) (z.1 + c, z.2) = Train.lapS (fun w => φ w 0) z :=
      lapTC_periodic_lapS hPer0 z
    have e1 : Train.lapS (fun w => φ w 1) (z.1 + c, z.2) = Train.lapS (fun w => φ w 1) z :=
      lapTC_periodic_lapS hPer1 z
    unfold Train.vecLaplacian
    rw [e0, e1]
  · intro z hz
    have h0 : Train.lapS (fun w => φ w 0) z = 0 := lapTC_vanish_lapS hv0 z hz
    have h1 : Train.lapS (fun w => φ w 1) z = 0 := lapTC_vanish_lapS hv1 z hz
    unfold Train.vecLaplacian
    rw [h0, h1]
    exact map_zero Train.toVecL

end UnforcedLeray.Short.PartI
