import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2/viscous`: `ViscousIdentity` (toolkit leaf)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `viscousIdentity` (`Short/PartI/Sub/T05b_2.lean`, the Prop `ViscousIdentity`).

Route. Fix `s ≥ 0`, `R ≥ 1`, `φ = etaCutoff R`, and let `w = v - v'`. For each component
`f = w_i` the cell integration by parts `CellDerivZero` applied to `φ f ∂_q f` (in `q`) and to
`φ f ∂_η f` (in `η`) gives
`∫_cell φ f Δf = -∫_cell φ |∇f|² - ∫_cell φ' f ∂_η f`.
Summing over the two components, and using `ν` as a common factor, gives `cutoffViscous =
viscousRhs`. The integrability of every integrand comes from `CellIntegrableOfSupport`, since each
integrand is continuous and vanishes where `|η| ≥ 2R` (the cutoff `φ` vanishes there, and `φ'`
vanishes there by the derivative bound in `EtaCutoffFacts`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

/-- The `q`-derivative of a `C^∞` function is `C^∞`. -/
theorem vi_partialQ_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialQ g) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  rw [show partialQ g = fun z => fderiv ℝ g z (1, 0) from
    funext fun z => UnforcedLeray.Cyl.partialQ_eq_fderiv hd z]
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- The `η`-derivative of a `C^∞` function is `C^∞`. -/
theorem vi_partialEta_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialEta g) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  rw [show partialEta g = fun z => fderiv ℝ g z (0, 1) from
    funext fun z => UnforcedLeray.Cyl.partialEta_eq_fderiv hd z]
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- Product rule for `∂_q`. -/
theorem vi_partialQ_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    partialQ (fun w => f w * g w) z = f z * partialQ g z + partialQ f z * g z := by
  obtain ⟨x, η⟩ := z
  have hf' : DifferentiableAt ℝ (fun y => f (y, η)) x :=
    (hf (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  have hg' : DifferentiableAt ℝ (fun y => g (y, η)) x :=
    (hg (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  show deriv (fun y => f (y, η) * g (y, η)) x
      = f (x, η) * deriv (fun y => g (y, η)) x + deriv (fun y => f (y, η)) x * g (x, η)
  rw [deriv_fun_mul hf' hg']
  ring

/-- Product rule for `∂_η`. -/
theorem vi_partialEta_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    partialEta (fun w => f w * g w) z = f z * partialEta g z + partialEta f z * g z := by
  obtain ⟨x, η⟩ := z
  have hf' : DifferentiableAt ℝ (fun y => f (x, y)) η :=
    (hf (x, η)).comp η ((differentiableAt_const x).prodMk differentiableAt_id)
  have hg' : DifferentiableAt ℝ (fun y => g (x, y)) η :=
    (hg (x, η)).comp η ((differentiableAt_const x).prodMk differentiableAt_id)
  show deriv (fun y => f (x, y) * g (x, y)) η
      = f (x, η) * deriv (fun y => g (x, y)) η + deriv (fun y => f (x, y)) η * g (x, η)
  rw [deriv_fun_mul hf' hg']
  ring

/-- The transverse cutoff depends only on `η`, so its `q`-derivative vanishes. -/
theorem vi_partialQ_cutoff (R : ℝ) (z : Plane) :
    partialQ (fun w : Plane => etaCutoff R w.2) z = 0 := by
  obtain ⟨x, η⟩ := z
  show deriv (fun _ : ℝ => etaCutoff R η) x = 0
  exact deriv_const x _

/-- The `η`-derivative of `φ_R(η)` as a function on the plane is `φ_R'(η)`. -/
theorem vi_partialEta_cutoff (R : ℝ) (z : Plane) :
    partialEta (fun w : Plane => etaCutoff R w.2) z = deriv (etaCutoff R) z.2 := rfl

/-- A component of a vector field has `∂_η` equal to the `∂_η` of the component. -/
theorem vi_partialEta_comp {g : Plane → Vec} (hg : Differentiable ℝ g) (i : Fin 2) (z : Plane) :
    partialEta g z i = partialEta (fun w => g w i) z := by
  obtain ⟨x, η⟩ := z
  have hd : HasDerivAt (fun η' : ℝ => g (x, η')) (partialEta g (x, η)) η :=
    UnforcedLeray.Cyl.hasDerivAt_sliceEta hg x η
  have hℓ : HasDerivAt (fun η' : ℝ => g (x, η') i) (partialEta g (x, η) i) η :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt η hd
  exact hℓ.deriv.symm

/-! ### The scalar cell integration by parts -/

/-- **Scalar viscous identity.** For a `C^∞` `c`-periodic `f` on the plane and the cutoff
`φ_R(η)`, the four integrands below are integrable on the cell, and
`∫ φ f Δf = -∫ φ |∇f|² - ∫ φ' f ∂_η f`. -/
theorem vi_scalar {c R : ℝ} (hc : 0 < c) (hR0 : 0 < R)
    (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hsm : ContDiff ℝ ∞ (etaCutoff R))
    (hzero : ∀ η : ℝ, 2 * R ≤ |η| → etaCutoff R η = 0)
    (hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0)
    (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (hper : Cyl.IsPeriodic c f) :
    IntegrableOn (fun z : Plane => etaCutoff R z.2 *
        (f z * (partialQ (partialQ f) z + partialEta (partialEta f) z))) (Cyl.cell c) ∧
    IntegrableOn (fun z : Plane => etaCutoff R z.2 *
        (partialQ f z ^ 2 + partialEta f z ^ 2)) (Cyl.cell c) ∧
    IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (f z * partialEta f z))
        (Cyl.cell c) ∧
    ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (f z * (partialQ (partialQ f) z + partialEta (partialEta f) z)) =
      -(∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ f z ^ 2 + partialEta f z ^ 2)) -
        ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (f z * partialEta f z) := by
  -- regularity of the cutoff and of the derivatives of `f`
  have hPsm : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hsm.comp contDiff_snd
  have hPd : Differentiable ℝ (fun z : Plane => etaCutoff R z.2) :=
    (hsm.differentiable (by simp)).comp differentiable_snd
  have hPc : Continuous (fun z : Plane => etaCutoff R z.2) := hPsm.continuous
  have hdPc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hsm.continuous_deriv (by simp)).comp continuous_snd
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hfq : ContDiff ℝ ∞ (partialQ f) := vi_partialQ_contDiff hf
  have hfe : ContDiff ℝ ∞ (partialEta f) := vi_partialEta_contDiff hf
  have hfqq : ContDiff ℝ ∞ (partialQ (partialQ f)) := vi_partialQ_contDiff hfq
  have hfee : ContDiff ℝ ∞ (partialEta (partialEta f)) := vi_partialEta_contDiff hfe
  have hfqd : Differentiable ℝ (partialQ f) := hfq.differentiable (by simp)
  have hfed : Differentiable ℝ (partialEta f) := hfe.differentiable (by simp)
  have hfc : Continuous f := hf.continuous
  have hfqc : Continuous (partialQ f) := hfq.continuous
  have hfec : Continuous (partialEta f) := hfe.continuous
  have hfqqc : Continuous (partialQ (partialQ f)) := hfqq.continuous
  have hfeec : Continuous (partialEta (partialEta f)) := hfee.continuous
  -- integrability of continuous integrands supported in `|η| < 2R`
  have hint : ∀ g : Plane → ℝ, Continuous g → (∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) →
      IntegrableOn g (Cyl.cell c) := fun g hg hgz => hI c R hc hR0 g hg hgz
  have hPint : ∀ g : Plane → ℝ, Continuous g →
      IntegrableOn (fun z : Plane => etaCutoff R z.2 * g z) (Cyl.cell c) := by
    intro g hg
    refine hint _ (hPc.mul hg) (fun z hz => ?_)
    simp only [hzero z.2 hz, zero_mul]
  have hdPint : ∀ g : Plane → ℝ, Continuous g →
      IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * g z) (Cyl.cell c) := by
    intro g hg
    refine hint _ (hdPc.mul hg) (fun z hz => ?_)
    simp only [hdzero z.2 hz, zero_mul]
  -- the `q`-part: `∂_q (φ f ∂_q f)`
  have hq1 : ∀ z : Plane,
      partialQ (fun w : Plane => etaCutoff R w.2 * f w * partialQ f w) z =
        etaCutoff R z.2 * partialQ f z ^ 2 + etaCutoff R z.2 * (f z * partialQ (partialQ f) z) := by
    intro z
    have h1 := vi_partialQ_mul (f := fun w : Plane => etaCutoff R w.2 * f w)
      (g := partialQ f) (hPd.mul hfd) hfqd z
    have h2 := vi_partialQ_mul (f := fun w : Plane => etaCutoff R w.2) (g := f) hPd hfd z
    rw [vi_partialQ_cutoff] at h2
    rw [h1, h2]
    ring
  have hGsm : ContDiff ℝ ∞ (fun w : Plane => etaCutoff R w.2 * f w * partialQ f w) :=
    (hPsm.mul hf).mul hfq
  have hGper : Cyl.IsPeriodic c (fun w : Plane => etaCutoff R w.2 * f w * partialQ f w) := by
    intro z
    simp only [hper z, hper.partialQ z]
  have hGzero : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * f z * partialQ f z = 0 := by
    intro z hz
    simp only [hzero z.2 hz, zero_mul]
  have hZq := (hZ c R hc hR0 (fun w : Plane => etaCutoff R w.2 * f w * partialQ f w)
    (hGsm.of_le (by simp)) hGper hGzero).1
  have hZq' := hZq
  simp only [hq1] at hZq'
  rw [integral_add (hPint (fun z => partialQ f z ^ 2) (by fun_prop))
    (hPint (fun z => f z * partialQ (partialQ f) z) (by fun_prop))] at hZq'
  -- the `η`-part: `∂_η (φ f ∂_η f)`
  have he1 : ∀ z : Plane,
      partialEta (fun w : Plane => etaCutoff R w.2 * f w * partialEta f w) z =
        deriv (etaCutoff R) z.2 * (f z * partialEta f z) + etaCutoff R z.2 * partialEta f z ^ 2 +
          etaCutoff R z.2 * (f z * partialEta (partialEta f) z) := by
    intro z
    have h1 := vi_partialEta_mul (f := fun w : Plane => etaCutoff R w.2 * f w)
      (g := partialEta f) (hPd.mul hfd) hfed z
    have h2 := vi_partialEta_mul (f := fun w : Plane => etaCutoff R w.2) (g := f) hPd hfd z
    rw [vi_partialEta_cutoff] at h2
    rw [h1, h2]
    ring
  have hG2sm : ContDiff ℝ ∞ (fun w : Plane => etaCutoff R w.2 * f w * partialEta f w) :=
    (hPsm.mul hf).mul hfe
  have hG2per : Cyl.IsPeriodic c (fun w : Plane => etaCutoff R w.2 * f w * partialEta f w) := by
    intro z
    simp only [hper z, hper.partialEta z]
  have hG2zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * f z * partialEta f z = 0 := by
    intro z hz
    simp only [hzero z.2 hz, zero_mul]
  have hZe := (hZ c R hc hR0 (fun w : Plane => etaCutoff R w.2 * f w * partialEta f w)
    (hG2sm.of_le (by simp)) hG2per hG2zero).2
  have hZe' := hZe
  simp only [he1] at hZe'
  have iA := hdPint (fun z => f z * partialEta f z) (by fun_prop)
  have iB := hPint (fun z => partialEta f z ^ 2) (by fun_prop)
  have iC := hPint (fun z => f z * partialEta (partialEta f) z) (by fun_prop)
  have iAB : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (f z * partialEta f z) +
      etaCutoff R z.2 * partialEta f z ^ 2) (Cyl.cell c) := iA.add iB
  rw [integral_add iAB iC, integral_add iA iB] at hZe'
  -- splitting of the three integrands of the statement
  have eA : ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (f z * (partialQ (partialQ f) z + partialEta (partialEta f) z)) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * (f z * partialQ (partialQ f) z)) +
        ∫ z in Cyl.cell c, etaCutoff R z.2 * (f z * partialEta (partialEta f) z) := by
    rw [← integral_add (hPint (fun z => f z * partialQ (partialQ f) z) (by fun_prop))
      (hPint (fun z => f z * partialEta (partialEta f) z) (by fun_prop))]
    congr 1
    funext z
    ring
  have eB : ∫ z in Cyl.cell c, etaCutoff R z.2 * (partialQ f z ^ 2 + partialEta f z ^ 2) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * partialQ f z ^ 2) +
        ∫ z in Cyl.cell c, etaCutoff R z.2 * partialEta f z ^ 2 := by
    rw [← integral_add (hPint (fun z => partialQ f z ^ 2) (by fun_prop))
      (hPint (fun z => partialEta f z ^ 2) (by fun_prop))]
    congr 1
    funext z
    ring
  refine ⟨hPint (fun z => f z * (partialQ (partialQ f) z + partialEta (partialEta f) z))
      (by fun_prop),
    hPint (fun z => partialQ f z ^ 2 + partialEta f z ^ 2) (by fun_prop),
    hdPint (fun z => f z * partialEta f z) (by fun_prop), ?_⟩
  rw [eA, eB]
  linarith

/-! ### The viscous identity -/

/-- **Leaf `ViscousIdentity`** (`T_visc = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩`), from the cell integration
by parts of each component of `w = v - v'`. -/
theorem viscousIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hS : TrainSliceSmooth) : ViscousIdentity := by
  intro ν c _hν hc tr tr' R hR s hs
  obtain ⟨_C₀, -, hcut⟩ := hη
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hR0 : 0 < R := by linarith
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h := hder η
    rw [hzero η hη', Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness and periodicity of `w = v - v'` and of its components
  have hsv := hS ν c tr s hs
  have hsv' := hS ν c tr' s hs
  have hw : ContDiff ℝ ∞ (diffV tr tr' s) := hsv.1.sub hsv'.1
  have hwd : Differentiable ℝ (diffV tr tr' s) := hw.differentiable (by simp)
  have hp := tr.isTrain.periodic_v s hs
  have hp' := tr'.isTrain.periodic_v s hs
  have hwp : Cyl.IsPeriodic c (diffV tr tr' s) := fun z => by
    simp only [diffV, hp z, hp' z]
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z : Plane => diffV tr tr' s z i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hw
  have hwpi : ∀ i : Fin 2, Cyl.IsPeriodic c (fun z : Plane => diffV tr tr' s z i) :=
    fun i z => by
      show diffV tr tr' s (z.1 + c, z.2) i = diffV tr tr' s z i
      rw [hwp z]
  -- the scalar identities for the two components
  obtain ⟨hA0, hB0, hC0, hE0⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => diffV tr tr' s z 0) (hcomp 0) (hwpi 0)
  obtain ⟨hA1, hB1, hC1, hE1⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => diffV tr tr' s z 1) (hcomp 1) (hwpi 1)
  -- pointwise expansions of the inner products
  have hinnerL : ∀ z : Plane,
      inner ℝ (diffV tr tr' s z) (Train.vecLaplacian (diffV tr tr' s) z) =
        diffV tr tr' s z 0 * (partialQ (partialQ (fun w : Plane => diffV tr tr' s w 0)) z +
            partialEta (partialEta (fun w : Plane => diffV tr tr' s w 0)) z) +
        diffV tr tr' s z 1 * (partialQ (partialQ (fun w : Plane => diffV tr tr' s w 1)) z +
            partialEta (partialEta (fun w : Plane => diffV tr tr' s w 1)) z) := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      Train.vecLaplacian, Train.lapS, Train.toVec_zero, Train.toVec_one]
    ring
  have hinnerE : ∀ z : Plane,
      inner ℝ (diffV tr tr' s z) (Cyl.partialEta (diffV tr tr' s) z) =
        diffV tr tr' s z 0 * partialEta (fun w : Plane => diffV tr tr' s w 0) z +
        diffV tr tr' s z 1 * partialEta (fun w : Plane => diffV tr tr' s w 1) z := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      vi_partialEta_comp hwd 0 z, vi_partialEta_comp hwd 1 z]
    ring
  have hgradP : ∀ z : Plane,
      etaCutoff R z.2 * gradNormSq (diffV tr tr' s) z =
        etaCutoff R z.2 * (partialQ (fun w : Plane => diffV tr tr' s w 0) z ^ 2 +
            partialEta (fun w : Plane => diffV tr tr' s w 0) z ^ 2) +
        etaCutoff R z.2 * (partialQ (fun w : Plane => diffV tr tr' s w 1) z ^ 2 +
            partialEta (fun w : Plane => diffV tr tr' s w 1) z ^ 2) := by
    intro z
    unfold gradNormSq
    ring
  have hV : ∀ z : Plane,
      etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.vecLaplacian (diffV tr tr' s) z) =
        etaCutoff R z.2 * (diffV tr tr' s z 0 * (partialQ (partialQ
            (fun w : Plane => diffV tr tr' s w 0)) z + partialEta (partialEta
            (fun w : Plane => diffV tr tr' s w 0)) z)) +
        etaCutoff R z.2 * (diffV tr tr' s z 1 * (partialQ (partialQ
            (fun w : Plane => diffV tr tr' s w 1)) z + partialEta (partialEta
            (fun w : Plane => diffV tr tr' s w 1)) z)) := by
    intro z
    rw [hinnerL z]
    ring
  have hJ : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * inner ℝ (diffV tr tr' s z) (Cyl.partialEta (diffV tr tr' s) z) =
        deriv (etaCutoff R) z.2 * (diffV tr tr' s z 0 *
            partialEta (fun w : Plane => diffV tr tr' s w 0) z) +
        deriv (etaCutoff R) z.2 * (diffV tr tr' s z 1 *
            partialEta (fun w : Plane => diffV tr tr' s w 1) z) := by
    intro z
    rw [hinnerE z]
    ring
  -- assemble the two components
  unfold cutoffViscous viscousRhs cutoffDissipation
  simp only [hV, hgradP, hJ]
  rw [integral_add hA0 hA1, integral_add hB0 hB1, integral_add hC0 hC1]
  linear_combination (2 * ν) * hE0 + (2 * ν) * hE1

end UnforcedLeray.Short.PartI
