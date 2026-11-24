import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace CurlCommuteAux

/-- `b ↦ e_j × b` as a `ℂ`-linear map. -/
def crossE (j : Fin 3) : CVec3 →L[ℂ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun b => crossC (EuclideanSpace.single j (1 : ℂ)) b
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        fin_cases i <;> fin_cases j <;> simp [crossC] <;> ring
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        fin_cases i <;> fin_cases j <;> simp [crossC] }

/-- The real-linear restriction of `crossE j`. -/
def crossER (j : Fin 3) : CVec3 →L[ℝ] CVec3 := (crossE j).restrictScalars ℝ

theorem crossER_apply (j : Fin 3) (b : CVec3) :
    crossER j b = crossC (EuclideanSpace.single j (1 : ℂ)) b := rfl

theorem diff_of_cd {G : ℝ × Space → CVec3} (h : ContDiff ℝ ∞ G) : Differentiable ℝ G :=
  h.differentiable (by simp)

theorem dir_comp (L : CVec3 →L[ℝ] CVec3) {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G)
    (p v : ℝ × Space) : fderiv ℝ (fun q => L (G q)) p v = L (fderiv ℝ G p v) := by
  have h := L.hasFDerivAt.comp p (hG p).hasFDerivAt
  rw [show (fun q => L (G q)) = L ∘ G from rfl, h.fderiv]
  rfl

theorem dir_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (hF : ∀ i ∈ s, Differentiable ℝ (F i)) (p v : ℝ × Space) :
    fderiv ℝ (fun q => ∑ i ∈ s, F i q) p v = ∑ i ∈ s, fderiv ℝ (F i) p v := by
  rw [fderiv_fun_sum (fun i hi => (hF i hi) p)]
  simp

/-- The directional derivative of `q ↦ ∑ⱼ e_j × H_j q`. -/
theorem dir_cross_sum (v : ℝ × Space) (H : Fin 3 → ℝ × Space → CVec3)
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (q : ℝ × Space) :
    fderiv ℝ (fun p => ∑ j : Fin 3, crossER j (H j p)) q v
      = ∑ j : Fin 3, crossER j (fderiv ℝ (H j) q v) := by
  have hF : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Differentiable ℝ (fun p => crossER j (H j p)) :=
    fun j _ => diff_of_cd ((crossER j).contDiff.comp (hH j))
  rw [dir_sum _ hF q v]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact dir_comp (crossER j) (diff_of_cd (hH j)) q v

/-- `curl` as a sum of the cross products with the `y_j`-derivatives. -/
theorem curlT_fun (G : ℝ × Space → CVec3) :
    curlT G = fun q => ∑ j : Fin 3, crossER j (dy j G q) := rfl

theorem dy_curl_pt {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (k : Fin 3) (q : ℝ × Space) :
    dy k (curlT G) q = ∑ j : Fin 3, crossER j (dy k (dy j G) q) := by
  rw [curlT_fun]
  exact dir_cross_sum (0, coordinateVector k) (fun j => dy j G)
    (fun j => contDiff_dy hG j) q

theorem dy_curl_fun {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (k : Fin 3) :
    dy k (curlT G) = fun q => ∑ j : Fin 3, crossER j (dy k (dy j G) q) :=
  funext fun q => dy_curl_pt hG k q

theorem dτ_curl_pt {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (q : ℝ × Space) :
    dτ (curlT G) q = ∑ j : Fin 3, crossER j (dτ (dy j G) q) := by
  rw [curlT_fun]
  exact dir_cross_sum (1, 0) (fun j => dy j G) (fun j => contDiff_dy hG j) q

/-- `curl` commutes with `∂_τ`. -/
theorem curl_dτ (Θ : ℝ × Space → CVec3) (hΘ : ContDiff ℝ ∞ Θ) :
    curlT (dτ Θ) = dτ (curlT Θ) := by
  funext q
  rw [dτ_curl_pt hΘ q]
  show ∑ j : Fin 3, crossER j (dy j (dτ Θ) q) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_dτ_comm hΘ j]

/-- `curl` commutes with `Δ`. -/
theorem lap_curl (Θ : ℝ × Space → CVec3) (hΘ : ContDiff ℝ ∞ Θ) (q : ℝ × Space) :
    lapT (curlT Θ) q = curlT (lapT Θ) q := by
  have h2 : ∀ j : Fin 3, dy j (lapT Θ) q = ∑ k : Fin 3, dy k (dy k (dy j Θ)) q := fun j => by
    rw [dy_lapT hΘ j]
    rfl
  have h3 : ∀ k : Fin 3, dy k (dy k (curlT Θ)) q
      = ∑ j : Fin 3, crossER j (dy k (dy k (dy j Θ)) q) := by
    intro k
    rw [dy_curl_fun hΘ k]
    exact dir_cross_sum (0, coordinateVector k) (fun j => dy k (dy j Θ))
      (fun j => contDiff_dy (contDiff_dy hΘ j) k) q
  show ∑ k : Fin 3, dy k (dy k (curlT Θ)) q = ∑ j : Fin 3, crossER j (dy j (lapT Θ) q)
  simp only [h3, h2, map_sum]
  exact Finset.sum_comm

/-- The pointwise `curl` of a sum. -/
theorem curl_add {F G : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (q : ℝ × Space) : curlT (F + G) q = curlT F q + curlT G q := by
  simp only [curlT_fun]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_add hF hG j, Pi.add_apply, map_add]

/-- The pointwise `curl` of a real multiple. -/
theorem curl_smulR (c : ℝ) {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (q : ℝ × Space) :
    curlT (c • F) q = c • curlT F q := by
  simp only [curlT_fun]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_smul hF c j, Pi.smul_apply, map_smul]

/-- The derivative of a complex multiple. -/
theorem dy_cmul (c : ℂ) {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (j : Fin 3)
    (q : ℝ × Space) : dy j (c • G) q = c • dy j G q := by
  have h0 := dir_comp ((c • ContinuousLinearMap.id ℂ CVec3).restrictScalars ℝ) hG q
    (0, coordinateVector j)
  have h1 : fderiv ℝ (fun p => c • G p) q (0, coordinateVector j)
      = c • fderiv ℝ G q (0, coordinateVector j) := by
    simpa using h0
  exact h1

/-- The pointwise `curl` of a complex multiple. -/
theorem curl_smulC (c : ℂ) {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (q : ℝ × Space) :
    curlT (c • F) q = c • curlT F q := by
  simp only [curlT_fun]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_cmul c hF j q]
  show crossE j (c • dy j F q) = c • crossE j (dy j F q)
  exact map_smul (crossE j) c _

/-- `curl (y·∇Θ) = y·∇ curl Θ + curl Θ`. -/
theorem curl_radial (Θ : ℝ × Space → CVec3) (hΘ : ContDiff ℝ ∞ Θ) (q : ℝ × Space) :
    curlT (radialT Θ) q = radialT (curlT Θ) q + curlT Θ q := by
  have hL : ∀ j : Fin 3, dy j (radialT Θ) q = radialT (dy j Θ) q + dy j Θ q := fun j => by
    rw [dy_radialT hΘ j]
    rfl
  have hR : ∀ k : Fin 3, dy k (curlT Θ) q = ∑ j : Fin 3, crossER j (dy k (dy j Θ) q) :=
    fun k => dy_curl_pt hΘ k q
  show ∑ j : Fin 3, crossER j (dy j (radialT Θ) q)
    = radialT (curlT Θ) q + ∑ j : Fin 3, crossER j (dy j Θ q)
  simp only [hL, map_add, Finset.sum_add_distrib]
  congr 1
  show ∑ j : Fin 3, crossER j (∑ k : Fin 3, (q.2 k) • dy k (dy j Θ) q)
    = ∑ k : Fin 3, (q.2 k) • dy k (curlT Θ) q
  simp only [map_sum, map_smul, hR, Finset.smul_sum]
  exact Finset.sum_comm

theorem curlCommute_aux_fun (ν μ : ℝ) (Θ : ℝ × Space → CVec3) :
    (fun x => L0 ν Θ x + (μ : ℂ) • Θ x)
      = dτ Θ + (-(1 / 2 : ℝ)) • radialT Θ + (-ν) • lapT Θ + (((μ : ℂ) - 1 / 2) • Θ) := by
  funext x
  simp only [L0, T0, Pi.add_apply, Pi.smul_apply]
  simp only [← Complex.coe_smul]
  push_cast
  module

end CurlCommuteAux

open CurlCommuteAux in
theorem curlCommute : CurlCommute := by
  intro ν μ Θ hΘ
  have d0 : Differentiable ℝ Θ := diff_of_cd hΘ
  have d1 : Differentiable ℝ (dτ Θ) := diff_of_cd (contDiff_dτ hΘ)
  have d2 : Differentiable ℝ (radialT Θ) := diff_of_cd (contDiff_radialT hΘ)
  have d3 : Differentiable ℝ (lapT Θ) := diff_of_cd (contDiff_lapT hΘ)
  have dR : Differentiable ℝ ((-(1 / 2 : ℝ)) • radialT Θ) := d2.const_smul _
  have dL : Differentiable ℝ ((-ν) • lapT Θ) := d3.const_smul _
  have dA : Differentiable ℝ (dτ Θ + (-(1 / 2 : ℝ)) • radialT Θ) := d1.add dR
  have dB : Differentiable ℝ (dτ Θ + (-(1 / 2 : ℝ)) • radialT Θ + (-ν) • lapT Θ) :=
    dA.add dL
  have dC : Differentiable ℝ (((μ : ℂ) - 1 / 2) • Θ) := d0.const_smul _
  funext q
  rw [curlCommute_aux_fun ν μ Θ, curl_add dB dC q, curl_add dA dL q, curl_add d1 dR q,
    curl_smulR _ d2 q, curl_smulR _ d3 q, curl_smulC _ d0 q, curl_dτ Θ hΘ,
    ← lap_curl Θ hΘ q, curl_radial Θ hΘ q]
  simp only [wOpT, L0, T0, Pi.sub_apply, Pi.smul_apply]
  simp only [← Complex.coe_smul]
  push_cast
  module

end UnforcedLeray.Short.PartIIIb.Concrete
