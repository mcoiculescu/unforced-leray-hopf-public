import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Int
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments

/-!


Step 1: `transp v (u - w) r y = transp v u r y - transp v w r y` (`pd` is linear on `C²` slices).
Step 2: on `[s, σ] ⊆ [s, T]` the Duhamel integrands agree, and `heatSG a (g - h) x =
heatSG a g x - heatSG a h x` pointwise (`integral_sub` against the Gaussian kernel, which is
integrable against bounded continuous functions).
Step 3: `integral_sub` in `r`, with interval integrability from `convTD_Int`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

theorem dphi_pd_sub (j : Fin 2) {f g : Pl → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Pl) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => f y - g y) (fderiv ℝ f x - fderiv ℝ g x) x :=
    (hf x).hasFDerivAt.sub (hg x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem dphi_transp_sub (v : ℝ → Pl → UnforcedLeray.Train.Vec) (u w : ℝ → Pl → ℝ) (r : ℝ)
    (hu : ContDiff ℝ 2 (u r)) (hw : ContDiff ℝ 2 (w r)) (y : Pl) :
    transp v (fun r y => u r y - w r y) r y = transp v u r y - transp v w r y := by
  have hdu : Differentiable ℝ (u r) := hu.differentiable (by norm_num)
  have hdw : Differentiable ℝ (w r) := hw.differentiable (by norm_num)
  unfold transp
  simp only []
  rw [dphi_pd_sub 0 hdu hdw y, dphi_pd_sub 1 hdu hdw y]
  ring

theorem dphi_heatK_cont (a : ℝ) : Continuous (heatK a) := by
  unfold heatK
  fun_prop

/-- Integrability of `y ↦ H_a(x - y) g(y)` for bounded continuous `g`, `a > 0`. -/
theorem dphi_int (a : ℝ) (ha : 0 < a) (B : ℝ) (g : Pl → ℝ) (x : Pl) (hg : Continuous g)
    (hgb : WB B g) : Integrable (fun y : Pl => heatK a (x - y) * g y) := by
  have hK : Integrable (fun z : Pl => heatK a z) := (heatKernelMoments a ha).2.1
  have hKx : Integrable (fun y : Pl => heatK a (x - y)) := hK.comp_sub_left x
  refine Integrable.mono' (hKx.const_mul B)
    (((dphi_heatK_cont a).comp (continuous_const.sub continuous_id)).mul hg).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have hnn : 0 ≤ heatK a (x - y) := ((heatKernelMoments a ha).1 (x - y)).le
  have hb : |g y| ≤ B := (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh y.2)).trans (hgb y)
  rw [norm_mul, Real.norm_of_nonneg hnn, Real.norm_eq_abs]
  calc heatK a (x - y) * |g y| ≤ heatK a (x - y) * B := mul_le_mul_of_nonneg_left hb hnn
    _ = B * heatK a (x - y) := mul_comm _ _

/-- The heat-semigroup integral is linear in the integrand for a bounded continuous pair. -/
theorem dphi_heatSG_sub (a : ℝ) (B1 B2 : ℝ) (g h : Pl → ℝ) (x : Pl) (hg : Continuous g)
    (hh : Continuous h) (hgb : WB B1 g) (hhb : WB B2 h) :
    heatSG a (fun y => g y - h y) x = heatSG a g x - heatSG a h x := by
  unfold heatSG
  by_cases ha : a ≤ 0
  · simp only [if_pos ha]
  · have ha' : 0 < a := lt_of_not_ge ha
    simp only [if_neg ha, mul_sub]
    exact integral_sub (dphi_int a ha' B1 g x hg hgb) (dphi_int a ha' B2 h x hh hhb)

/-- **`PartII-b:T22/1/14/5`**: linearity of `Φ u = duhamelConv ν s (transp v u)` on `[s, T]`. -/
theorem duhamelPhiSub_proof : UnforcedLeray.Short.IIb.CylPDE.DuhamelPhiSub := by
  intro ν s T v hν hsT u w hu hw hFu hFw hBu hBw σ hσ x
  obtain ⟨Bu, hBu⟩ := hBu
  obtain ⟨Bw, hBw⟩ := hBw
  have hsσ : s ≤ σ := hσ.1
  have hσT : σ ≤ T := hσ.2
  have hsub : uIcc s σ ⊆ Icc s T := by
    rw [uIcc_of_le hsσ]
    exact Icc_subset_Icc le_rfl hσT
  have hsubT : uIcc s σ ⊆ uIcc s T := by
    rw [uIcc_of_le hsσ, uIcc_of_le hsT]
    exact Icc_subset_Icc le_rfl hσT
  have hI1 : IntervalIntegrable (fun r => heatSG (ν * (σ - r)) (transp v u r) x)
      MeasureTheory.volume s σ :=
    (convTD_Int ν s T hν hsT Bu (transp v u) hFu hBu σ hσ x).mono_set hsubT
  have hI2 : IntervalIntegrable (fun r => heatSG (ν * (σ - r)) (transp v w r) x)
      MeasureTheory.volume s σ :=
    (convTD_Int ν s T hν hsT Bw (transp v w) hFw hBw σ hσ x).mono_set hsubT
  have hfun : ∀ r ∈ uIcc s σ, transp v (fun r y => u r y - w r y) r =
      fun y => transp v u r y - transp v w r y := by
    intro r hr
    funext y
    exact dphi_transp_sub v u w r (hu r (hsub hr)) (hw r (hsub hr)) y
  unfold duhamelConv
  rw [← intervalIntegral.integral_sub hI1 hI2]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  have hr' := hsub hr
  rw [hfun r hr]
  exact dphi_heatSG_sub (ν * (σ - r)) Bu Bw (transp v u r) (transp v w r) x
    (hFu.c1 r hr').continuous (hFw.c1 r hr').continuous (hBu r hr') (hBw r hr')

end CylPDE

end UnforcedLeray.Short.IIb
