import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L2_JointMeas

/-!
# `PartIII-a:T16/1/1/3` : `SepDiffFMeas` (measurability of the derivatives of the integrand)

Source `the November 2 reference manuscript` lines 3604-3617.
For `ν > 0`, `ρ`-a.e. `p = (λ, z)` has `λ ∈ (0,1)`; there `sepDiffF ν μ T τ p` is a finite sum of
the measurable coefficients `a_jk(p) = -2 λ^{2μ+2} T_jk(z, τ + 2 log λ)` times the shifted
directional derivatives `y' ↦ ∂_k K_{ν(1-λ²),ij}(y' - λz)`.  The `n`-th derivative of the latter is
a fixed continuous linear image of `D^{n+1}K_{ν(1-λ²),ij}(y - λz)`, and the joint strong
measurability of these derivatives in `(t, x)` is `heatLerayKJointMeas` (L2).

The argument follows the `PartIII-b` leaf `sepPhiMeasurable_of`, with the restriction `n ≤ 2`
removed (`heatLerayKJointMeas` holds for every order) and the smoothness supplied by
`heatLerayKSmoothAll` (L1).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Linear dependence of `D^n (∂_v f)` on `D^{n+1} f` (a fixed continuous linear map). -/
theorem l3_exists_deriv_clm (n : ℕ) (v : Space) :
    ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Space) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ,
      ∀ (f : Space → ℝ) (x : Space), ContDiff ℝ (n + 1) f →
        iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f y v : ℝ) : ℂ)) x
          = L (iteratedFDeriv ℝ (n + 1) f x) := by
  refine ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℝ ℂ
      Complex.ofRealCLM).comp
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) (Space →L[ℝ] ℝ) ℝ
      (ContinuousLinearMap.apply ℝ ℝ v)).comp
      (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ).toContinuousLinearEquiv.toContinuousLinearMap),
    fun f x hf => ?_⟩
  have h1 : iteratedFDeriv ℝ n (fderiv ℝ f) x
      = (continuousMultilinearCurryRightEquiv' ℝ n Space ℝ) (iteratedFDeriv ℝ (n + 1) f x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x
      = (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fderiv ℝ f) x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left (f := fderiv ℝ f)
      hd.contDiffAt le_rfl
  have h3 : ContDiff ℝ n (fun y => fderiv ℝ f y v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp hd
  have h4 : iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f y v : ℝ) : ℂ)) x
      = Complex.ofRealCLM.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left (f := fun y => fderiv ℝ f y v)
      h3.contDiffAt le_rfl
  rw [h4, h2, h1]
  rfl

/-- **`PartIII-a:T16/1/1/3`**: for `ν > 0` and a separated source, every `y`-derivative of the
`i`-th component of the integrand `sepDiffF` is `ρ`-a.e. strongly measurable in `p`. -/
theorem sepDiffFMeas : UnforcedLeray.Short.IIIa.SepDiffFMeas := by
  intro ν μ P rOut T hν hS τ i n y
  have hJ : HeatLerayKJointMeas := heatLerayKJointMeas
  have hSm : HeatLerayKSmoothAll := heatLerayKSmoothAll
  choose L hL using fun k : Fin 3 => l3_exists_deriv_clm n (coordinateVector k)
  let a : Fin 3 → Fin 3 → ℝ × Space → ℂ := fun j k p =>
    -2 * (p.1 : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)
  have ha : ∀ j k, Measurable (a j k) := by
    intro j k
    have h1 : Measurable fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 j k :=
      (hS.measurable j k).comp
        (((measurable_const.add (measurable_const.mul
          (Real.measurable_log.comp measurable_fst)))).prodMk measurable_snd)
    have h2' : Measurable fun p : ℝ × Space => (p.1 : ℂ) ^ (2 * μ + 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const _
    exact (measurable_const.mul h2').mul (Complex.measurable_ofReal.comp h1)
  let R : ℝ × Space → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ := fun p =>
    ∑ j : Fin 3, ∑ k : Fin 3, a j k p • L k
      (if 0 < ν * (1 - p.1 ^ 2) then
        iteratedFDeriv ℝ (n + 1) (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x)
          (y - p.1 • p.2) else 0)
  have hR : StronglyMeasurable R := by
    simp only [R]
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_
    refine ((ha j k).stronglyMeasurable).smul ?_
    refine (L k).continuous.comp_stronglyMeasurable ?_
    have hm : Measurable fun p : ℝ × Space => (ν * (1 - p.1 ^ 2), y - p.1 • p.2) :=
      (measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2))).prodMk
        (measurable_const.sub (measurable_fst.smul measurable_snd))
    exact (hJ i j (n + 1)).comp_measurable hm
  refine hR.aestronglyMeasurable.congr ?_
  filter_upwards [sepDiffRho_ae_mem] with p hp
  have hp1 : 0 < p.1 := hp.1
  have hp2 : p.1 < 1 := hp.2
  have ht : 0 < ν * (1 - p.1 ^ 2) := mul_pos hν (by nlinarith)
  have hK : ∀ j, ContDiff ℝ (n + 1) (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) :=
    fun j => (hSm _ ht i j).of_le (by exact_mod_cast le_top)
  have hg : ∀ j k, ContDiff ℝ n (fun x : Space =>
      ((fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) := by
    intro j k
    exact Complex.ofRealCLM.contDiff.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp
        ((hK j).fderiv_right (by simp)))
  have hsum : (fun y' => sepDiffF ν μ T τ p y' i) = fun y' => ∑ j : Fin 3, ∑ k : Fin 3,
      a j k p • ((fun x : Space => ((fderiv ℝ
        (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x (coordinateVector k) : ℝ) : ℂ))
        (y' - p.1 • p.2)) := by
    funext y'
    simp only [sepDiffF, a, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have hk : ∀ j k, ContDiff ℝ n (fun y' : Space => a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) :=
    fun j k => ((hg j k).comp (contDiff_id.sub contDiff_const)).const_smul _
  have hj : ∀ j, ContDiffAt ℝ n (fun y' : Space => ∑ k : Fin 3, a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) y :=
    fun j => (ContDiff.sum fun k _ => hk j k).contDiffAt
  symm
  simp only [R, ht, ite_true]
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun k _ => (hk j k).contDiffAt)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ContDiffAt ℝ n (fun y' : Space => ((fderiv ℝ
      (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y' - p.1 • p.2)
      (coordinateVector k) : ℝ) : ℂ)) y :=
    ((hg j k).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc]
  congr 1
  rw [iteratedFDeriv_comp_sub (f := fun x : Space => ((fderiv ℝ
      (fun x => heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x (coordinateVector k) : ℝ) : ℂ)),
    hL k _ _ (hK j)]

end UnforcedLeray.Short.IIIa
