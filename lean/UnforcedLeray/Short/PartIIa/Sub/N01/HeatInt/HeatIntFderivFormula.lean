import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntFderivFormula.Core
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.PlaneHeatFderiv
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds

/-!
# `PartII-a:N01/9/1/2/4/4/4` (heat integral): `HeatIntFderivFormula`

Source `the November 2 reference manuscript`
lines 3379-3383.  Dominated differentiation of the heat integral under the `σ`-integral
(`HIFD.core`, scalar), after passing to the `j`-th component of the vector heat integral
(the slice is bounded and jointly continuous, hence the vector integrands are integrable).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (planeHeat)

theorem hifd_meridC_norm_le (v : MeridC) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]

theorem hifd_planeHeat_proj (θ : ℝ) {u : ℝ × ℝ → MeridC} {B : ℝ} (hc : Continuous u)
    (hB : ∀ y, ‖u y‖ ≤ B) (x : ℝ × ℝ) (j : Fin 2) :
    planeHeat θ u x j = planeHeat θ (fun w => u w j) x := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    let L : MeridC →L[ℝ] ℂ :=
      ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) j).restrictScalars ℝ)
    have hG : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y) :=
      UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
    have hGnn := UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθ
    have hint : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) := by
      refine (hG.mul_const B).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) θ).smul
          (hc.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))).aestronglyMeasurable
      · rw [norm_smul, Real.norm_of_nonneg (hGnn y)]
        exact mul_le_mul_of_nonneg_left (hB _) (hGnn y)
    have h := L.integral_comp_comm hint
    have e : ∀ y : UnforcedLeray.Gaussian.Euc 2,
        L (UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) =
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y) j := by
      intro y
      simp [L]
    simp only [e] at h
    exact h.symm
  · simp only [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

theorem heatIntFderivFormula : UnforcedLeray.Short.PartIIa.N01.HeatIntFderivFormula := by
  intro c ν hc hν μ F hF s hs y j
  obtain ⟨⟨s1, hs1, hvan⟩, hcd, M, hM0, hM1⟩ := heatSliceBounds c hc F hF
  have hco := HIFD.core planeHeatFderiv hν hs μ (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2 j)
    (hcd j) hs1 (fun σ w h => by
      show heatSlice c F σ w j = 0
      rw [hvan σ h w]; rfl)
    (M := M) (fun p => hM0 j p.1 p.2) (fun σ w => hM1 j σ w) y
  refine ⟨hco.1 (UnforcedLeray.B0579.dir j), ?_⟩
  obtain ⟨L, hL, hLv⟩ := hco.2
  -- vector facts
  have hM : 0 ≤ M := (norm_nonneg _).trans (hM0 0 0 (0, 0).2)
  have hVc : Continuous (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2) := by
    have h := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
      (continuous_pi fun i : Fin 2 => (hcd i).continuous)
    exact h
  have hVb : ∀ σ w, ‖heatSlice c F σ w‖ ≤ M + M := fun σ w =>
    (hifd_meridC_norm_le _).trans (add_le_add (hM0 0 σ w) (hM0 1 σ w))
  -- the weight and its bound
  set a : ℝ → ℂ := fun σ => ((σ / s : ℝ) : ℂ) ^ μ with ha
  have haIoi : ContinuousOn a (Ioi 0) := by
    intro σ hσ
    have hpos : 0 < σ / s := div_pos hσ hs
    apply ContinuousAt.continuousWithinAt
    refine ContinuousAt.cpow ?_ continuousAt_const ?_
    · exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.div_const s)
    · exact Complex.ofReal_mem_slitPlane.2 hpos
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (haIoi.mono (fun σ (hσ : σ ∈ Icc s1 s) => lt_of_lt_of_le hs1 hσ.1))
  have hK0' : 0 ≤ max K0 0 := le_max_right _ _
  have haM : AEStronglyMeasurable a (volume.restrict (Ioc 0 s)) :=
    (haIoi.mono (fun σ (hσ : σ ∈ Ioc 0 s) => hσ.1)).aestronglyMeasurable measurableSet_Ioc
  have hPc : ∀ z : ℝ × ℝ, Continuous fun σ : ℝ =>
      planeHeat (ν * (s - σ)) (heatSlice c F σ) z := fun z =>
    HIFD.continuous_planeHeat_param (θ := fun σ => ν * (s - σ))
      (continuous_const.mul (continuous_const.sub continuous_id))
      (u := fun σ w => heatSlice c F σ w) hVc (M := M + M) (fun t w => hVb t w) z
  have hvec : ∀ z : ℝ × ℝ, IntervalIntegrable (fun σ : ℝ => a σ •
      planeHeat (ν * (s - σ)) (heatSlice c F σ) z) volume 0 s := by
    intro z
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    refine Integrable.mono' (g := fun _ => max K0 0 * (M + M)) (integrable_const _)
      (haM.smul (hPc z).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun σ hσ => ?_)
    by_cases h : σ < s1
    · have h0 : heatSlice c F σ = fun _ => 0 := funext fun w => hvan σ h w
      have : planeHeat (ν * (s - σ)) (heatSlice c F σ) z = 0 := by
        rw [h0]; exact congrFun (HIFD.planeHeat_zero_fun _) z
      show ‖a σ • planeHeat (ν * (s - σ)) (heatSlice c F σ) z‖ ≤ _
      rw [this, smul_zero, norm_zero]
      positivity
    · have hσ' : σ ∈ Icc s1 s := ⟨not_lt.1 h, hσ.2⟩
      show ‖a σ • planeHeat (ν * (s - σ)) (heatSlice c F σ) z‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul ((hK0 σ hσ').trans (le_max_left _ _))
        (HIFD.planeHeat_norm_le_all _ (fun w => hVb σ w) z) (norm_nonneg _) hK0'
  -- component of the heat integral
  have hcomp : (fun z : ℝ × ℝ => smoothHeatInt c ν μ F (s, z) j) = fun z : ℝ × ℝ =>
      ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
        planeHeat (ν * (s - σ)) (fun w => heatSlice c F σ w j) z := by
    funext z
    let Lj : MeridC →L[ℝ] ℂ :=
      ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) j).restrictScalars ℝ)
    have h := Lj.intervalIntegral_comp_comm (hvec z)
    have e : ∀ σ : ℝ, Lj (a σ • planeHeat (ν * (s - σ)) (heatSlice c F σ) z) =
        a σ • planeHeat (ν * (s - σ)) (fun w => heatSlice c F σ w j) z := by
      intro σ
      have := hifd_planeHeat_proj (ν * (s - σ)) (u := heatSlice c F σ) (B := M + M)
        (hVc.comp (continuous_const.prodMk continuous_id)) (fun w => hVb σ w) z j
      simp only [Lj]
      show (a σ • planeHeat (ν * (s - σ)) (heatSlice c F σ) z) j = _
      rw [PiLp.smul_apply, this]
    simp only [e] at h
    exact h.symm
  rw [hcomp, hL.fderiv]
  exact hLv _ (by fin_cases j <;> simp [UnforcedLeray.B0579.dir])

end UnforcedLeray.Short.PartIIa.N01
