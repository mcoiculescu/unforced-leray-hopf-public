import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.Helpers
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `truncCurlIntertwine`: `curl` intertwines `L₀ + μ` with `wOpT`

Source `the November 2 reference manuscript` lines 1351-1362.
Pointwise calculus on smooth fields: `curl` commutes with `∂_τ` and `Δ` (symmetry of second
derivatives), and `curl (y·∇Ψ) = y·∇ curl Ψ + curl Ψ` (`dy_radialT`). Hence
`curl(L₀Ψ) = L₀(curl Ψ) - ½ curl Ψ` and `wOpT = L₀ + μ - ½`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The `j`-th component map `v ↦ e_j × v`. -/
abbrev crE (j : Fin 3) : CVec3 →L[ℝ] CVec3 := crossCR (EuclideanSpace.single j (1 : ℂ))

theorem curlT_apply (G : ℝ × Space → CVec3) (x : ℝ × Space) :
    curlT G x = ∑ j : Fin 3, crE j (dy j G x) := rfl

theorem fderiv_clm_dir (L : CVec3 →L[ℝ] CVec3) {G : ℝ × Space → CVec3}
    (hG : Differentiable ℝ G) (v p : ℝ × Space) :
    fderiv ℝ (fun q => L (G q)) p v = L (fderiv ℝ G p v) := by
  have h : fderiv ℝ (fun q => L (G q)) p = L.comp (fderiv ℝ G p) :=
    (L.hasFDerivAt.comp p (hG p).hasFDerivAt).fderiv
  rw [h]
  rfl

namespace D2DyL1

theorem dy_clm (L : CVec3 →L[ℝ] CVec3) {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G)
    (j : Fin 3) : dy j (fun q => L (G q)) = fun p => L (dy j G p) := by
  funext p
  exact fderiv_clm_dir L hG _ p

end D2DyL1

theorem dτ_clm (L : CVec3 →L[ℝ] CVec3) {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) :
    dτ (fun q => L (G q)) = fun p => L (dτ G p) := by
  funext p
  exact fderiv_clm_dir L hG _ p

theorem dτ_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ × Space → CVec3}
    (hG : ∀ i ∈ s, Differentiable ℝ (G i)) :
    dτ (∑ i ∈ s, G i) = ∑ i ∈ s, dτ (G i) := by
  funext p
  simp only [dτ, Finset.sum_apply]
  rw [fderiv_sum fun i hi => (hG i hi) p]
  simp

theorem dy_crSum (k : Fin 3) {H : Fin 3 → ℝ × Space → CVec3} (hH : ∀ j, ContDiff ℝ ∞ (H j)) :
    dy k (∑ j : Fin 3, fun x => crE j (H j x)) = ∑ j : Fin 3, fun x => crE j (dy k (H j) x) := by
  rw [dy_sum Finset.univ (G := fun j => fun x => crE j (H j x))
    (fun j _ => ((crE j).contDiff.comp (hH j)).differentiable (by simp)) k]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact D2DyL1.dy_clm (crE j) ((hH j).differentiable (by simp)) k

theorem dτ_crSum {H : Fin 3 → ℝ × Space → CVec3} (hH : ∀ j, ContDiff ℝ ∞ (H j)) :
    dτ (∑ j : Fin 3, fun x => crE j (H j x)) = ∑ j : Fin 3, fun x => crE j (dτ (H j) x) := by
  rw [dτ_sum Finset.univ (G := fun j => fun x => crE j (H j x))
    (fun j _ => ((crE j).contDiff.comp (hH j)).differentiable (by simp))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact dτ_clm (crE j) ((hH j).differentiable (by simp))

theorem curlT_as_sum {Ψ : ℝ × Space → CVec3} :
    curlT Ψ = ∑ j : Fin 3, fun x => crE j (dy j Ψ x) := by
  funext x
  simp [curlT_apply, Finset.sum_apply]

theorem dy_curl_apply {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (k : Fin 3) (x : ℝ × Space) :
    dy k (curlT Ψ) x = ∑ j : Fin 3, crE j (dy k (dy j Ψ) x) := by
  rw [curlT_as_sum, dy_crSum k (H := fun j => dy j Ψ) (fun j => contDiff_dy hΨ j)]
  simp [Finset.sum_apply]

theorem dτ_curl_apply {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) :
    dτ (curlT Ψ) x = ∑ j : Fin 3, crE j (dτ (dy j Ψ) x) := by
  rw [curlT_as_sum, dτ_crSum (H := fun j => dy j Ψ) (fun j => contDiff_dy hΨ j)]
  simp [Finset.sum_apply]

theorem curlT_dτ {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    curlT (dτ Ψ) = dτ (curlT Ψ) := by
  funext x
  rw [dτ_curl_apply hΨ x, curlT_apply]
  simp only [dy_dτ_comm hΨ]

theorem curlT_lapT {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    curlT (lapT Ψ) = lapT (curlT Ψ) := by
  funext x
  have h2 : ∀ k : Fin 3, dy k (dy k (curlT Ψ)) x =
      ∑ j : Fin 3, crE j (dy k (dy k (dy j Ψ)) x) := by
    intro k
    have h1 : dy k (curlT Ψ) = ∑ j : Fin 3, fun x => crE j (dy k (dy j Ψ) x) := by
      funext y
      rw [dy_curl_apply hΨ k y]
      simp [Finset.sum_apply]
    rw [h1, dy_crSum k (H := fun j => dy k (dy j Ψ)) (fun j => contDiff_dy (contDiff_dy hΨ j) k)]
    simp [Finset.sum_apply]
  rw [curlT_apply]
  simp only [dy_lapT hΨ]
  show _ = ∑ k : Fin 3, dy k (dy k (curlT Ψ)) x
  simp only [h2]
  simp only [lapT, Finset.sum_apply, map_sum]
  rw [Finset.sum_comm]

theorem curlT_radialT {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    curlT (radialT Ψ) = radialT (curlT Ψ) + curlT Ψ := by
  funext x
  rw [Pi.add_apply, curlT_apply, curlT_apply]
  have hL : ∀ j : Fin 3, dy j (radialT Ψ) x = radialT (dy j Ψ) x + dy j Ψ x :=
    fun j => congrFun (dy_radialT hΨ j) x
  simp only [hL, map_add]
  have hR : ∀ j : Fin 3, radialT (dy j Ψ) x = ∑ k : Fin 3, (x.2 k) • dy k (dy j Ψ) x :=
    fun j => rfl
  have hRC : radialT (curlT Ψ) x = ∑ k : Fin 3, (x.2 k) • dy k (curlT Ψ) x := rfl
  rw [hRC]
  simp only [dy_curl_apply hΨ, hR, map_sum, map_smul, Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem curlT_add {F G : ℝ × Space → CVec3} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    curlT (fun x => F x + G x) = fun x => curlT F x + curlT G x := by
  funext x
  simp only [curlT_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : dy j (fun x => F x + G x) = fun x => dy j F x + dy j G x :=
    dy_add (hF.differentiable (by simp)) (hG.differentiable (by simp)) j
  rw [h]
  simp only [map_add]

theorem curlT_smul (c : ℝ) {F : ℝ × Space → CVec3} (hF : ContDiff ℝ ∞ F) :
    curlT (fun x => c • F x) = fun x => c • curlT F x := by
  funext x
  simp only [curlT_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : dy j (fun x => c • F x) = fun x => c • dy j F x :=
    dy_smul (hF.differentiable (by simp)) c j
  rw [h]
  simp only [map_smul]

theorem truncCurlIntertwine : TruncCurlIntertwine := by
  intro P ν μ Ψ hΨ
  have hS : ContDiff ℝ ∞ Ψ := hΨ.smooth
  have hexp : (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) =
      fun x => dτ Ψ x + ((-(1 / 2 : ℝ)) • radialT Ψ x + ((-ν) • lapT Ψ x + (μ - 1 / 2 : ℝ) • Ψ x)) := by
    funext x
    simp only [L0, T0, Pi.add_apply, Complex.coe_smul]
    module
  have hR : ContDiff ℝ ∞ (radialT Ψ) := contDiff_radialT hS
  have hLp : ContDiff ℝ ∞ (lapT Ψ) := contDiff_lapT hS
  have hD : ContDiff ℝ ∞ (dτ Ψ) := contDiff_dτ hS
  rw [hexp]
  rw [curlT_add hD ((hR.const_smul _).add ((hLp.const_smul _).add (hS.const_smul _)))]
  rw [curlT_add (hR.const_smul _) ((hLp.const_smul _).add (hS.const_smul _))]
  rw [curlT_add (hLp.const_smul _) (hS.const_smul _)]
  rw [curlT_smul _ hR, curlT_smul _ hLp, curlT_smul _ hS, curlT_dτ hS, curlT_radialT hS,
    curlT_lapT hS]
  funext x
  simp only [wOpT, L0, T0, Pi.add_apply, Pi.smul_apply, Complex.coe_smul]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
