import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.KDiv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.Formula

/-!
# `sepWDivFree_all` (PartIII-b:IIIb-D2/3/1/2/2), decomposition

Source of record: `the November 2 reference manuscript` 3600-3621 (`sep:kernel`,
`sep:resolvent`).

Two analytic inputs are isolated as Props and taken as hypotheses:
* `KernelC2`: `K_t` is `C²` for `t > 0` (from `HeatLerayKSmooth`, D2/3/1/1/2, L2);
* `HeatLerayKDivFree`: `∑_i ∂_i K_{ij} = 0` for `t > 0` (3600-3610: `∂_j G_t + ∂_j Δ∫_t^∞ G = 0`,
  using `Δ G_a = ∂_a G_a` and `∫_t^∞ ∂_a G_a = -G_t`).
* `SepWDivDerivFormula`: the shared derivative-under-integral formula (D2/3/1/1/2), with the sum
  over the component index pulled inside the integrals.

From these the pointwise kernel identity (symmetry of second derivatives) and the integral
vanishing are proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `K_t` is `C²` for `t > 0` (hypothesis; proved in D2/3/1/1/2 as `HeatLerayKSmooth`). -/
def KernelC2 : Prop :=
  ∀ t : ℝ, 0 < t → ∀ i j : Fin 3, ContDiff ℝ 2 (fun x => IIIa.heatLerayK t i j x)

/-- Divergence-free heat-Leray kernel in its first index (3600-3610), `t > 0`. -/
def HeatLerayKDivFree : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (j : Fin 3) (x : Space),
    ∑ i : Fin 3, fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector i) = 0

/-- Second derivative of a `C²` scalar function in the direction `u` of a `C²` function's
first derivative: `∂_v (∂_u f) = D²f(v,u)`. -/
theorem fderiv_fderiv_apply_const (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (w v u : Space) :
    fderiv ℝ (fun x => fderiv ℝ f x u) w v = fderiv ℝ (fderiv ℝ f) w v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) w :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) w
  have h := fderiv_clm_apply hd (differentiableAt_const u)
  rw [show (fun x => fderiv ℝ f x u) = fun y => (fderiv ℝ f y) ((fun _ => u) y) from rfl, h]
  simp

/-- Pointwise kernel identity: `∑_i ∂_i∂_k K_{ij} = 0` for `t > 0` (symmetry of second
derivatives plus `∑_i ∂_i K_{ij} = 0`). -/
theorem kernel_div_second (hK : KernelC2) (hdiv : HeatLerayKDivFree) (t : ℝ) (ht : 0 < t)
    (j k : Fin 3) (w : Space) :
    ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x
      (coordinateVector k)) w (coordinateVector i) = 0 := by
  have hsym : ∀ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x
      (coordinateVector k)) w (coordinateVector i) =
      fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x
        (coordinateVector i)) w (coordinateVector k) := by
    intro i
    have hC := hK t ht i j
    rw [fderiv_fderiv_apply_const _ hC w _ _, fderiv_fderiv_apply_const _ hC w _ _]
    have hs : IsSymmSndFDerivAt ℝ (fun x => IIIa.heatLerayK t i j x) w :=
      ContDiffAt.isSymmSndFDerivAt (hC.contDiffAt) (by simp)
    exact hs.eq _ _
  rw [Finset.sum_congr rfl (fun i _ => hsym i)]
  have hdiff : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x
        (coordinateVector i)) w := by
    intro i _
    have hC := hK t ht i j
    have hd : DifferentiableAt ℝ (fderiv ℝ (fun x' => IIIa.heatLerayK t i j x')) w :=
      ((hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) w
    exact hd.clm_apply (differentiableAt_const _)
  have hzero : (∑ i : Fin 3, fun x => fderiv ℝ (fun x' => IIIa.heatLerayK t i j x') x
      (coordinateVector i)) = fun _ => 0 := by
    funext x
    rw [Finset.sum_apply]
    exact hdiv t ht j x
  have hfd := fderiv_sum (𝕜 := ℝ) (u := Finset.univ) (x := w) hdiff
  have h0 : fderiv ℝ (fun _ : Space => (0 : ℝ)) w = 0 := by simp
  rw [hzero, h0] at hfd
  have hL := congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector k)) hfd
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at hL
  exact hL.symm

theorem sepWDivFree_of (hK : KernelC2) (hdiv : HeatLerayKDivFree) (hD : SepWDivDerivFormula) :
    SepWDivFree := by
  intro ν μ rOut P T hν hμ hr hP hS hM τ y hy
  rw [hD ν μ rOut P T hν hμ hr hP hS hM τ y hy]
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space,
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x') x
          (coordinateVector k)) (y - l • z) (coordinateVector i) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) = 0 := by
    intro l hl z
    have ht : 0 < ν * (1 - l ^ 2) := by
      have h1 := hl.1
      have h2 := hl.2
      exact mul_pos hν (by nlinarith)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    have h := kernel_div_second hK hdiv (ν * (1 - l ^ 2)) ht j k (y - l • z)
    rw [h]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ))
    (fun l hl => by simp only [hpt l hl]; simp)]
  simp

/-- `K_t` is `C²` (from `heatLerayKSmooth`, `C³`). -/
theorem kernelC2 : KernelC2 := fun t ht i j => (heatLerayKSmooth t ht i j).of_le (by norm_num)

/-- `∑_i ∂_i K_{ij} = 0` (3600-3610), proved in `L2/KDiv.lean`. -/
theorem heatLerayKDivFree : HeatLerayKDivFree := fun t ht j x => kd_divfree t ht j x

/-- Only the derivative-under-the-integral formula for `sepW` remains. -/
theorem sepWDivFree_of_formula (hD : SepWDivDerivFormula) : SepWDivFree :=
  sepWDivFree_of kernelC2 heatLerayKDivFree hD

/-- **`sepWDivFree_all`** (3600-3621): the separated realization is divergence free off the
source disk, unconditionally. -/
theorem sepWDivFree_all : SepWDivFree := sepWDivFree_of_formula sepWDivDerivFormula

end UnforcedLeray.Short.PartIIIb.Concrete
