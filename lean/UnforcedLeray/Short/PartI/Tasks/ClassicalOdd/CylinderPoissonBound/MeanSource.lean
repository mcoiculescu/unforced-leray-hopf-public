import UnforcedLeray.Short.PartI.Sub.T02_3_8
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanMomentumU
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part I, task `PartI:T02/3/8/MeanSource`: the algebraic heart of the mean part

Source of record: `the November 2 reference manuscript`, lines 276-288 and line 447
(`grad p` solves `Δp = -∂_i∂_j(v_i v_j)` when `div v = 0`).

Target: `CylPoisMeanSource` (`Short/PartI/Sub/T02_3_8.lean`).

Proof. Write `a = u_0` (the `q`-component) and `b = u_1` (the `η`-component).

* Pointwise identity (`cpMS_pointwise`).  With `div u = 0`, i.e. `∂_q a = -∂_η b`, and the symmetry
  `∂_q∂_η a = ∂_η∂_q a` of second derivatives of the smooth function `a` (`cpMS_mixed`),
  `poissonSource u = ∂_η²(b²) + 2 ∂_q(b ∂_η a)`.
* Averaging (`cpMS_main`).  The horizontal average of `∂_q(b ∂_η a)` vanishes by periodicity
  (`mm_integral_partialQ_zero`), and the average is additive on continuous integrands.

All auxiliary names start with `cpMS`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane partialQ partialEta)

/-! ### Calculus helpers on `Plane → ℝ` -/

theorem cpMS_partialEta_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialEta g) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have heq : partialEta g = fun z => fderiv ℝ g z (0, 1) :=
    funext fun z => mm_partialEta_eq (hd z)
  rw [heq]
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem cpMS_partialEta_neg (f : Plane → ℝ) (z : Plane) :
    partialEta (fun w => -f w) z = -partialEta f z := by
  obtain ⟨x, η⟩ := z
  show deriv (fun y => -f (x, y)) η = -deriv (fun y => f (x, y)) η
  exact deriv.neg

theorem cpMS_partialEta_add {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    partialEta (fun w => f w + g w) z = partialEta f z + partialEta g z := by
  obtain ⟨x, η⟩ := z
  show deriv (fun y => f (x, y) + g (x, y)) η =
    deriv (fun y => f (x, y)) η + deriv (fun y => g (x, y)) η
  exact deriv_add (mm_diff_snd hf x η) (mm_diff_snd hg x η)

/-- Mixed partial derivatives of a `C^∞` function commute: `∂_q ∂_η a = ∂_η ∂_q a`. -/
theorem cpMS_mixed {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (z : Plane) :
    partialQ (partialEta a) z = partialEta (partialQ a) z := by
  have hd : Differentiable ℝ a := ha.differentiable (by simp)
  have hEa : ContDiff ℝ ∞ (partialEta a) := cpMS_partialEta_contDiff ha
  have hQa : ContDiff ℝ ∞ (partialQ a) := mm_partialQ_contDiff ha
  have h1 : partialQ (partialEta a) z = fderiv ℝ (partialEta a) z (1, 0) :=
    mm_partialQ_eq (hEa.differentiable (by simp) z)
  have h2 : partialEta (partialQ a) z = fderiv ℝ (partialQ a) z (0, 1) :=
    mm_partialEta_eq (hQa.differentiable (by simp) z)
  have hEa_eq : partialEta a = fun w => fderiv ℝ a w (0, 1) :=
    funext fun w => mm_partialEta_eq (hd w)
  have hQa_eq : partialQ a = fun w => fderiv ℝ a w (1, 0) :=
    funext fun w => mm_partialQ_eq (hd w)
  have hF : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hA : DifferentiableAt ℝ (fderiv ℝ a) z := (hF.differentiable (by simp)) z
  have key : ∀ v w : Plane,
      fderiv ℝ (fun y => fderiv ℝ a y v) z w = fderiv ℝ (fderiv ℝ a) z w v := by
    intro v w
    rw [fderiv_clm_apply hA (differentiableAt_const v)]
    simp
  have hC : ContDiffAt ℝ ∞ a z := ha.contDiffAt
  have hsymm : IsSymmSndFDerivAt ℝ a z :=
    hC.isSymmSndFDerivAt (by simp)
  rw [h1, h2, hEa_eq, hQa_eq, key, key]
  exact hsymm (1, 0) (0, 1)

/-! ### The pointwise identity -/

/-- Pointwise: with `∂_q a + ∂_η b = 0`,
`(∂_q a)² + 2 ∂_q b ∂_η a + (∂_η b)² = ∂_η²(b²) + 2 ∂_q(b ∂_η a)`. -/
theorem cpMS_pointwise {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hdiv : ∀ z, partialQ a z + partialEta b z = 0) (z : Plane) :
    partialQ a z ^ 2 + 2 * (partialQ b z * partialEta a z) + partialEta b z ^ 2 =
      partialEta (partialEta (fun w => b w ^ 2)) z +
        2 * partialQ (fun w => b w * partialEta a w) z := by
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hEbd : Differentiable ℝ (partialEta b) :=
    (cpMS_partialEta_contDiff hb).differentiable (by simp)
  have hEad : Differentiable ℝ (partialEta a) :=
    (cpMS_partialEta_contDiff ha).differentiable (by simp)
  have hfun : partialQ a = fun w => -partialEta b w :=
    funext fun w => show partialQ a w = -partialEta b w by linarith [hdiv w]
  have hEQa : partialEta (partialQ a) z = -partialEta (partialEta b) z := by
    rw [hfun]
    exact cpMS_partialEta_neg (partialEta b) z
  have hmix : partialQ (partialEta a) z = partialEta (partialQ a) z := cpMS_mixed ha z
  have hE1 : partialEta (fun w => b w ^ 2) =
      fun w => b w * partialEta b w + partialEta b w * b w := by
    funext w
    have hsq : (fun w => b w ^ 2) = fun w => b w * b w := funext fun w => sq (b w)
    rw [hsq]
    exact mm_partialEta_mul hbd hbd w
  have hD1 : Differentiable ℝ (fun w => b w * partialEta b w) := hbd.mul hEbd
  have hD2 : Differentiable ℝ (fun w => partialEta b w * b w) := hEbd.mul hbd
  rw [hE1, cpMS_partialEta_add hD1 hD2, mm_partialEta_mul hbd hEbd,
    mm_partialEta_mul hEbd hbd, mm_partialQ_mul hbd hEad, hmix, hEQa]
  linear_combination (partialQ a z - partialEta b z) * hdiv z

/-! ### The horizontal average -/

theorem cpMS_main {c : ℝ} (hc : 0 < c) {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hpa : Cyl.IsPeriodic c a) (hpb : Cyl.IsPeriodic c b)
    (hdiv : ∀ z, partialQ a z + partialEta b z = 0) (η : ℝ) :
    hmean c (fun z => partialQ a z ^ 2 + 2 * (partialQ b z * partialEta a z) + partialEta b z ^ 2) η =
      hmean c (partialEta (partialEta (fun w => b w ^ 2))) η := by
  have hEa : ContDiff ℝ ∞ (partialEta a) := cpMS_partialEta_contDiff ha
  have hgC : ContDiff ℝ ∞ (fun w => b w * partialEta a w) := hb.mul hEa
  have hgP : Cyl.IsPeriodic c (fun w => b w * partialEta a w) := by
    intro z
    show b (z.1 + c, z.2) * partialEta a (z.1 + c, z.2) = b z * partialEta a z
    rw [hpb z, hpa.partialEta z]
  have hFc : Continuous (partialEta (partialEta (fun w => b w ^ 2))) :=
    (cpMS_partialEta_contDiff (cpMS_partialEta_contDiff (hb.pow 2))).continuous
  have hGc : Continuous (partialQ (fun w => b w * partialEta a w)) :=
    (mm_partialQ_contDiff hgC).continuous
  have hFi : IntegrableOn (fun q : ℝ => partialEta (partialEta (fun w => b w ^ 2)) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    (hFc.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have hGi : IntegrableOn (fun q : ℝ => 2 * partialQ (fun w => b w * partialEta a w) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    ((hGc.comp (continuous_id.prodMk continuous_const)).const_mul 2).integrableOn_Ioc
  have hint : ∫ q in Ioc (-c / 2) (c / 2),
      (partialQ a (q, η) ^ 2 + 2 * (partialQ b (q, η) * partialEta a (q, η)) +
        partialEta b (q, η) ^ 2) =
      ∫ q in Ioc (-c / 2) (c / 2),
        (partialEta (partialEta (fun w => b w ^ 2)) (q, η) +
          2 * partialQ (fun w => b w * partialEta a w) (q, η)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun q => cpMS_pointwise ha hb hdiv (q, η))
  simp only [hmean]
  rw [hint, integral_add hFi hGi, integral_const_mul,
    mm_integral_partialQ_zero hc hgC hgP η, mul_zero, add_zero]

/-! ### The target -/

/-- **Mean part of the Poisson source** (target `CylPoisMeanSource`): the horizontal average of
`∂_i u_j ∂_j u_i` equals the horizontal average of `∂_η²(u_η²)` for a smooth periodic
divergence-free `u`. -/
theorem cylPoisMeanSource : CylPoisMeanSource := by
  unfold CylPoisMeanSource
  intro c u hc hu hper hdiv η
  have ha : ContDiff ℝ ∞ (fun w => u w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hb : ContDiff ℝ ∞ (fun w => u w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hpa : Cyl.IsPeriodic c (fun w => u w 0) := fun z => by
    show u (z.1 + c, z.2) 0 = u z 0
    rw [hper z]
  have hpb : Cyl.IsPeriodic c (fun w => u w 1) := fun z => by
    show u (z.1 + c, z.2) 1 = u z 1
    rw [hper z]
  exact cpMS_main hc ha hb hpa hpb (fun z => hdiv z) η

end UnforcedLeray.Short.PartI
