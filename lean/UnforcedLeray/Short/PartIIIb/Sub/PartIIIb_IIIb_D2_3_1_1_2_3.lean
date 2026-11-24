import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# `sepPhiMeasurable`: decomposition (`PartIII-b:IIIb-D2/3/1/1/2/3`)

Source `the November 2 reference manuscript`
3604-3621 (`sep:kernel`, `sep:resolvent`).  The `y`-derivatives of `sepPhi` are, for `l ∈ (0,1)`,
finite sums of measurable scalar coefficients times `(t,x)`-derivatives of `K_t` evaluated at
`(ν(1-l²), y - l z)`; the only analytic input is joint (strong) measurability of the
`x`-derivatives of `K_t` on `t > 0` (`HeatLerayJointMeas`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Joint strong measurability in `(t, x)` of the `x`-derivatives of order `≤ 3` of the
heat-Leray kernel on `t > 0` (extended by `0` for `t ≤ 0`).  True since `(t,x) ↦ K_t(x)` is
`t^{-3/2} K_1(x/√t)` (`heatG`, `heatTail` scale: `∫_t^∞ G_a = t^{-1/2} (∫_1^∞ G_s)(x/√t)`). -/
def HeatLerayJointMeas : Prop :=
  ∀ (i j : Fin 3) (m : ℕ), m ≤ 3 →
    StronglyMeasurable (fun q : ℝ × Space =>
      if 0 < q.1 then iteratedFDeriv ℝ m (fun x => IIIa.heatLerayK q.1 i j x) q.2 else 0)

/-- Parabolic scaling of the heat kernel and of its tail (source 3600-3610, `K_t = δ G_t + D² ∫_t^∞ G_a`):
`G_t(x) = t^{-3/2} G_1(x/√t)` and `∫_t^∞ G_a(x) da = t^{-1/2} (∫_1^∞ G_a)(x/√t)` (substitute
`a = t s` in the tail integral; `heatG` scales by `rpow` and `exp` algebra). -/
def HeatGTailScale : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : Space,
    IIIa.heatG t x = t ^ (-(3 / 2 : ℝ)) * IIIa.heatG 1 ((Real.sqrt t)⁻¹ • x) ∧
    IIIa.heatTail t x = t ^ (-(1 / 2 : ℝ)) * IIIa.heatTail 1 ((Real.sqrt t)⁻¹ • x)

/-- Scaling of the heat-Leray kernel: `K_t(x) = t^{-3/2} K_1(x/√t)` (apply `HeatGTailScale`, and
`fderiv` of `x ↦ f(c • x)` is `c • fderiv f (c • x)`, twice, for the two partials in `part2`). -/
def HeatLerayScale : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (i j : Fin 3) (x : Space),
    IIIa.heatLerayK t i j x
      = t ^ (-(3 / 2 : ℝ)) * IIIa.heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)

/-- Linear dependence of `D^n (∂_v f)` on `D^{n+1} f`. -/
theorem exists_deriv_clm (n : ℕ) (v : Space) :
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

theorem sepPhiMeasurable_of (hJ : HeatLerayJointMeas) (h2 : HeatLerayKSmooth) :
    SepPhiMeasurable := by
  intro ν μ P rOut T hν hS τ i n hn y
  choose L hL using fun k : Fin 3 => exists_deriv_clm n (coordinateVector k)
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
        iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x)
          (y - p.1 • p.2) else 0)
  have hR : StronglyMeasurable R := by
    simp only [R]
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ => Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_
    refine ((ha j k).stronglyMeasurable).smul ?_
    refine (L k).continuous.comp_stronglyMeasurable ?_
    have hm : Measurable fun p : ℝ × Space => (ν * (1 - p.1 ^ 2), y - p.1 • p.2) :=
      (measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2))).prodMk
        (measurable_const.sub (measurable_fst.smul measurable_snd))
    exact (hJ i j (n + 1) (by omega)).comp_measurable hm
  refine hR.aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  have ht : 0 < ν * (1 - p.1 ^ 2) := by
    have := hp.1; have := hp.2; nlinarith [mul_pos hν (sub_pos.2 (show p.1 ^ 2 < 1 by nlinarith))]
  have hK : ∀ j, ContDiff ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) :=
    fun j => ((h2 _ ht i j).of_le (by exact_mod_cast (by omega : n + 1 ≤ 3)))
  have hg : ∀ j k, ContDiff ℝ n (fun x : Space =>
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) := by
    intro j k
    exact Complex.ofRealCLM.contDiff.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp
        ((hK j).fderiv_right (by simp)))
  have hsum : sepPhi ν μ T τ i p = fun y' => ∑ j : Fin 3, ∑ k : Fin 3, a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2)) := by
    funext y'
    simp only [sepPhi, a, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have hk : ∀ j k, ContDiff ℝ n (fun y' : Space => a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) :=
    fun j k => ((hg j k).comp (contDiff_id.sub contDiff_const)).const_smul _
  have hj : ∀ j, ContDiffAt ℝ n (fun y' : Space => ∑ k : Fin 3, a j k p •
      ((fun x : Space => ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x
        (coordinateVector k) : ℝ) : ℂ)) (y' - p.1 • p.2))) y :=
    fun j => (ContDiff.sum fun k _ => hk j k).contDiffAt
  symm
  simp only [R, ht, ite_true]
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun k _ => (hk j k).contDiffAt)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ContDiffAt ℝ n (fun y' : Space => ((fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y' - p.1 • p.2)
      (coordinateVector k) : ℝ) : ℂ)) y :=
    ((hg j k).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc]
  congr 1
  rw [iteratedFDeriv_comp_sub (f := fun x : Space => ((fderiv ℝ
      (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) x (coordinateVector k) : ℝ) : ℂ)),
    hL k _ _ (hK j)]

end UnforcedLeray.Short.PartIIIb.Concrete
