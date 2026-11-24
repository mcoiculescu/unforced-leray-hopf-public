import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Units.B0151.DivCurl

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ContDiff
open UnforcedLeray.Cyl (Vec2)

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

theorem partialQ_fderiv_commute {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (v z : Plane) :
    Cyl.partialQ (fun x => fderiv ℝ f x v) z =
      fderiv ℝ (Cyl.partialQ f) z v := by
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

theorem partialEta_fderiv_commute {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (v z : Plane) :
    Cyl.partialEta (fun x => fderiv ℝ f x v) z =
      fderiv ℝ (Cyl.partialEta f) z v := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf2.fderiv_right (m := 1) (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable one_ne_zero
  have hscalar : Differentiable ℝ (fun x => fderiv ℝ f x v) := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hdd
  have hq : Cyl.partialEta f = fun x => fderiv ℝ f x (0, 1) := by
    funext x
    exact Cyl.partialEta_eq_fderiv (hf.differentiable (by simp)) x
  rw [Cyl.partialEta_eq_fderiv hscalar z, hq]
  rw [fderiv_clm_apply (hdd z) (differentiableAt_const _),
    fderiv_clm_apply (hdd z) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (0, 1) v

/-- The cylinder divergence commutes with one smooth constant-direction derivative. -/
theorem divergence_fderiv_commute {u : Plane → Vec2} (hu : ContDiff ℝ ∞ u)
    (v z : Plane) :
    Cyl.divergence (fun x => fderiv ℝ u x v) z =
      fderiv ℝ (Cyl.divergence u) z v := by
  let L₀ : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let L₁ : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 : ContDiff ℝ ∞ (fun x => L₀ (u x)) := L₀.contDiff.comp hu
  have h1 : ContDiff ℝ ∞ (fun x => L₁ (u x)) := L₁.contDiff.comp hu
  have hcomp0 (x : Plane) :
      L₀ (fderiv ℝ u x v) = fderiv ℝ (fun y => L₀ (u y)) x v := by
    have hc := fderiv_comp x L₀.differentiableAt (hu.differentiable (by simp) x)
    rw [L₀.fderiv] at hc
    have hv := congrArg (fun F : Plane →L[ℝ] ℝ => F v) hc
    have hcompose : (L₀ ∘ u) = (fun y => L₀ (u y)) := rfl
    rw [hcompose] at hv
    exact hv.symm
  have hcomp1 (x : Plane) :
      L₁ (fderiv ℝ u x v) = fderiv ℝ (fun y => L₁ (u y)) x v := by
    have hc := fderiv_comp x L₁.differentiableAt (hu.differentiable (by simp) x)
    rw [L₁.fderiv] at hc
    have hv := congrArg (fun F : Plane →L[ℝ] ℝ => F v) hc
    have hcompose : (L₁ ∘ u) = (fun y => L₁ (u y)) := rfl
    rw [hcompose] at hv
    exact hv.symm
  have hq : Cyl.partialQ (fun x => L₀ (u x)) =
      fun x => Cyl.partialQ (fun y => u y 0) x := by
    rfl
  have he : Cyl.partialEta (fun x => L₁ (u x)) =
      fun x => Cyl.partialEta (fun y => u y 1) x := by
    rfl
  have hqcont : ContDiff ℝ ∞ (Cyl.partialQ (fun x => L₀ (u x))) :=
    Cyl.contDiff_partialQ h0
  have hecont : ContDiff ℝ ∞ (Cyl.partialEta (fun x => L₁ (u x))) :=
    Cyl.contDiff_partialEta h1
  calc
    Cyl.divergence (fun x => fderiv ℝ u x v) z =
        Cyl.partialQ (fun x => L₀ (fderiv ℝ u x v)) z +
          Cyl.partialEta (fun x => L₁ (fderiv ℝ u x v)) z := rfl
    _ = fderiv ℝ (Cyl.partialQ (fun x => L₀ (u x))) z v +
          fderiv ℝ (Cyl.partialEta (fun x => L₁ (u x))) z v := by
      rw [show (fun x => L₀ (fderiv ℝ u x v)) =
          (fun x => fderiv ℝ (fun y => L₀ (u y)) x v) from funext hcomp0,
        show (fun x => L₁ (fderiv ℝ u x v)) =
          (fun x => fderiv ℝ (fun y => L₁ (u y)) x v) from funext hcomp1,
        partialQ_fderiv_commute h0 v z, partialEta_fderiv_commute h1 v z]
    _ = fderiv ℝ (Cyl.divergence u) z v := by
      have hdiv : Cyl.divergence u =
          (fun x => Cyl.partialQ (fun y => L₀ (u y)) x +
            Cyl.partialEta (fun y => L₁ (u y)) x) := by
        funext x
        rfl
      rw [hdiv]
      have hadd := fderiv_add (hqcont.differentiable (by simp) z)
        (hecont.differentiable (by simp) z)
      have haddv := congrArg (fun F : Plane →L[ℝ] ℝ => F v) hadd
      exact haddv.symm

/-- Divergence commutes with every ordered smooth directional-derivative word. -/
theorem divergence_iterD_eq_iterD_divergence {u : Plane → Vec2}
    (hu : ContDiff ℝ ∞ u) (vs : List Plane) :
    Cyl.divergence (Sob.iterD vs u) = Sob.iterD vs (Cyl.divergence u) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have htail : ContDiff ℝ ∞ (Sob.iterD vs u) := Sob.contDiff_iterD hu vs
    funext z
    change Cyl.divergence (fun x => fderiv ℝ (Sob.iterD vs u) x v) z =
      fderiv ℝ (Sob.iterD vs (Cyl.divergence u)) z v
    rw [divergence_fderiv_commute htail v z, ih]

/-- Every ordered classical derivative of the actual Train datum remains pointwise
divergence-free. -/
theorem datum_iterD_divergence_zero {c : ℝ} (hc : c ≠ 0) (vs : List Plane) :
    ∀ z, Cyl.divergence (Sob.iterD vs (Train.datum c)) z = 0 := by
  have hiterzero : ∀ ws : List Plane,
      Sob.iterD ws (fun _ : Plane => (0 : ℝ)) = fun _ => 0 := by
    intro ws
    induction ws with
    | nil => rfl
    | cons v ws ih =>
      funext z
      change fderiv ℝ (Sob.iterD ws (fun _ : Plane => (0 : ℝ))) z v = 0
      rw [ih]
      simp
  have hdiv := divergence_iterD_eq_iterD_divergence
    (Train.datum_contDiff hc) vs
  have hzero : Cyl.divergence (Train.datum c) = fun _ => 0 := by
    funext z
    exact Train.datum_div hc z
  rw [hdiv, hzero]
  rw [hiterzero vs]
  intro z
  rfl

#print axioms UnforcedLeray.TrainB.partialQ_fderiv_commute
#print axioms UnforcedLeray.TrainB.partialEta_fderiv_commute
#print axioms UnforcedLeray.TrainB.divergence_fderiv_commute
#print axioms UnforcedLeray.TrainB.divergence_iterD_eq_iterD_divergence
#print axioms UnforcedLeray.TrainB.datum_iterD_divergence_zero

end UnforcedLeray.TrainB
