import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatDeriv
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2_2
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/3` (space part): `d/dr' ∫ G_{νr'} g = ν ∫ G ∆g`

Target: `duhEqSpacePart : DuhEqSpacePart`. Source: `the November 2 reference manuscript`,
lines 3427-3440. The heat-age derivative is the Laplacian of the kernel (`∂_θ G = ∆G`), and the
real and imaginary parts of the frozen slice are transferred to the Laplacian by
`TrainB.integral_heatKernel2AgeDerivative_mul_comp_sub`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Fréchet derivative of the slice `y ↦ G (t, y)`. -/
theorem sp_slice_hasFDerivAt {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (y : ℝ × ℝ) :
    HasFDerivAt (fun y' : ℝ × ℝ => G (t, y'))
      ((fderiv ℝ G (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y := by
  have h1 : HasFDerivAt (fun y' : ℝ × ℝ => ((t, y') : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y := hasFDerivAt_prodMk_right t y
  exact ((hG.differentiable (by simp)) (t, y)).hasFDerivAt.comp y h1

theorem sp_slice_fderiv_apply {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (fun y' : ℝ × ℝ => G (t, y')) y v = fderiv ℝ G (t, y) ((0 : ℝ), v) := by
  rw [(sp_slice_hasFDerivAt hG t y).fderiv]
  rfl

theorem sp_slice_fderiv_bound {c : ℝ} {G : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hG : NiceScalar c G) :
    ∃ K : ℝ, ∀ t y, ‖fderiv ℝ (fun y' : ℝ × ℝ => G (t, y')) y‖ ≤ K := by
  obtain ⟨K, hK⟩ := duhSm_bound hc hG 1
  refine ⟨K, fun t y => ?_⟩
  have hF : ‖fderiv ℝ G (t, y)‖ ≤ K := by
    simpa [norm_iteratedFDeriv_one] using hK (t, y)
  rw [(sp_slice_hasFDerivAt hG.1 t y).fderiv]
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_inr]
  calc ‖(fderiv ℝ G (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖fderiv ℝ G (t, y)‖ * ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * 1 := mul_le_mul hF hinr (norm_nonneg _) ((norm_nonneg _).trans hF)
    _ = K := mul_one K

theorem sp_pdC_slice {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    pdC j (fun y' : ℝ × ℝ => G (t, y')) y = duhDir ((0 : ℝ), B0579.dir j) G (t, y) := by
  unfold pdC duhDir
  exact sp_slice_fderiv_apply hG t y _

/-- `∂_q` and `∂_η` of a planar function, in the form used by `Train.lapS`. -/
theorem sp_hasDerivAt_partialQ {G : ℝ × ℝ → ℂ} (hG : Differentiable ℝ G) (z : ℝ × ℝ) :
    HasDerivAt (fun q : ℝ => G (q, z.2)) (pdC 0 G z) z.1 := by
  have h1 : HasDerivAt (fun q : ℝ => ((q, z.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h2 := (hG (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h1
  unfold pdC
  exact h2

theorem sp_hasDerivAt_partialEta {G : ℝ × ℝ → ℂ} (hG : Differentiable ℝ G) (z : ℝ × ℝ) :
    HasDerivAt (fun η : ℝ => G (z.1, η)) (pdC 1 G z) z.2 := by
  have h1 : HasDerivAt (fun η : ℝ => ((z.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have h2 := (hG (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h1
  unfold pdC
  exact h2

theorem sp_partialQ_L (L : ℂ →L[ℝ] ℝ) {G : ℝ × ℝ → ℂ} (hG : Differentiable ℝ G) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun y => L (G y)) z = L (pdC 0 G z) := by
  unfold UnforcedLeray.Cyl.partialQ
  exact ((L.hasFDerivAt).comp_hasDerivAt z.1 (sp_hasDerivAt_partialQ hG z)).deriv

theorem sp_partialEta_L (L : ℂ →L[ℝ] ℝ) {G : ℝ × ℝ → ℂ} (hG : Differentiable ℝ G) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun y => L (G y)) z = L (pdC 1 G z) := by
  unfold UnforcedLeray.Cyl.partialEta
  exact ((L.hasFDerivAt).comp_hasDerivAt z.2 (sp_hasDerivAt_partialEta hG z)).deriv

theorem sp_pdC_differentiable {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    Differentiable ℝ (pdC j G) := by
  have hfd : Differentiable ℝ (fderiv ℝ G) := (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have := hfd.clm_apply (differentiable_const (B0579.dir j))
  unfold pdC
  exact this

/-- The planar Laplacian of a `ℂ`-valued function commutes with a real linear functional. -/
theorem sp_lapS_L (L : ℂ →L[ℝ] ℝ) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (z : ℝ × ℝ) :
    UnforcedLeray.Train.lapS (fun y => L (G y)) z = L (lapC G z) := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  have hd1 : Differentiable ℝ (pdC 0 G) := sp_pdC_differentiable hG 0
  have hd2 : Differentiable ℝ (pdC 1 G) := sp_pdC_differentiable hG 1
  have e1 : UnforcedLeray.Cyl.partialQ (fun y => L (G y)) = fun y => L (pdC 0 G y) :=
    funext (sp_partialQ_L L hd)
  have e2 : UnforcedLeray.Cyl.partialEta (fun y => L (G y)) = fun y => L (pdC 1 G y) :=
    funext (sp_partialEta_L L hd)
  unfold UnforcedLeray.Train.lapS
  rw [e1, e2, sp_partialQ_L L hd1 z, sp_partialEta_L L hd2 z, lapC, map_add]

/-- Splitting a real kernel times a complex function into real and imaginary parts. -/
theorem sp_split_int {K : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (h1 : Integrable (fun w => K w * (φ w).re)) (h2 : Integrable (fun w => K w * (φ w).im)) :
    ∫ w, ((K w : ℝ) : ℂ) * φ w =
      ((∫ w, K w * (φ w).re : ℝ) : ℂ) + Complex.I * ((∫ w, K w * (φ w).im : ℝ) : ℂ) := by
  have e : (fun w => ((K w : ℝ) : ℂ) * φ w) = fun w =>
      ((K w * (φ w).re : ℝ) : ℂ) + Complex.I * ((K w * (φ w).im : ℝ) : ℂ) := by
    funext w
    apply Complex.ext <;> simp
  have i1 : Integrable (fun w => ((K w * (φ w).re : ℝ) : ℂ)) := h1.ofReal
  have i2 : Integrable (fun w => Complex.I * ((K w * (φ w).im : ℝ) : ℂ)) :=
    h2.ofReal.const_mul Complex.I
  rw [e]
  refine (integral_add i1 i2).trans ?_
  rw [integral_const_mul]
  congr 1
  · exact integral_ofReal
  · congr 1
    exact integral_ofReal


/-- The complex slice-integral identity: derivative in the heat age of `∫ G_θ(w) g(x - w)`. -/
theorem sp_theta_complex {g : ℝ × ℝ → ℂ} (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (x : ℝ × ℝ) :
    HasDerivAt (fun θ : ℝ => ∫ w : ℝ × ℝ,
        ((UnforcedLeray.B0284.heatKernel2 θ w : ℝ) : ℂ) * g (x.1 - w.1, x.2 - w.2))
      (∫ w : ℝ × ℝ, ((UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w : ℝ) : ℂ) *
        g (x.1 - w.1, x.2 - w.2)) θ₀ := by
  have hre : Continuous (fun y => (g y).re) := Complex.continuous_re.comp hg
  have him : Continuous (fun y => (g y).im) := Complex.continuous_im.comp hg
  have hbre : ∀ y, ‖(g y).re‖ ≤ M := fun y => (Complex.abs_re_le_norm (g y)).trans (hM y)
  have hbim : ∀ y, ‖(g y).im‖ ≤ M := fun y => (Complex.abs_im_le_norm (g y)).trans (hM y)
  have hR := UnforcedLeray.Short.IIb.deqhd_theta_hasDerivAt hre hbre hθ₀ x
  have hI := UnforcedLeray.Short.IIb.deqhd_theta_hasDerivAt him hbim hθ₀ x
  have hfin := hR.ofReal_comp.add (hI.ofReal_comp.const_mul Complex.I)
  have hint : ∀ {θ : ℝ}, 0 < θ → ∀ φ : ℝ × ℝ → ℝ, Continuous φ → (∀ y, ‖φ y‖ ≤ M) →
      Integrable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w *
        φ (x.1 - w.1, x.2 - w.2)) := by
    intro θ hθ φ hφ hφM
    refine (UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_bdd ?_ (ae_of_all _ fun w => hφM _)
    exact (hφ.comp (by fun_prop)).aestronglyMeasurable
  have hev : ∀ᶠ θ in 𝓝 θ₀,
      (∫ w : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 θ w : ℝ) : ℂ) * g (x.1 - w.1, x.2 - w.2)) =
        ((∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * (fun y => (g y).re) (x.1 - w.1, x.2 - w.2) : ℝ) : ℂ)
          + Complex.I * ((∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * (fun y => (g y).im) (x.1 - w.1, x.2 - w.2) : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    have hθ' : (0 : ℝ) < θ := hθ
    exact sp_split_int (φ := fun w => g (x.1 - w.1, x.2 - w.2))
      (hint hθ' (fun y => (g y).re) hre (fun y => hbre y))
      (hint hθ' (fun y => (g y).im) him (fun y => hbim y))
  have hval : (∫ w : ℝ × ℝ, ((UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w : ℝ) : ℂ) *
        g (x.1 - w.1, x.2 - w.2)) =
      ((∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w *
          (fun y => (g y).re) (x.1 - w.1, x.2 - w.2) : ℝ) : ℂ)
        + Complex.I * ((∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w *
          (fun y => (g y).im) (x.1 - w.1, x.2 - w.2) : ℝ) : ℂ) := by
    refine sp_split_int (φ := fun w => g (x.1 - w.1, x.2 - w.2)) ?_ ?_
    · exact (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀).mul_bdd
        (hre.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun w => hbre _)
    · exact (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀).mul_bdd
        (him.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun w => hbim _)
  have key := hfin.congr_of_eventuallyEq hev
  rw [hval]
  exact key


theorem sp_slice_contDiff {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => G (t, y)) :=
  hG.comp (contDiff_const.prodMk contDiff_id)

theorem sp_re_bound (z : ℂ) {M : ℝ} (hz : ‖z‖ ≤ M) : ‖z.re‖ ≤ M :=
  (Complex.abs_re_le_norm z).trans hz

theorem sp_im_bound (z : ℂ) {M : ℝ} (hz : ‖z‖ ≤ M) : ‖z.im‖ ≤ M :=
  (Complex.abs_im_le_norm z).trans hz

/-- Second slice derivatives of `L ∘ h(t, ·)` are bounded (via the directional derivatives of `h`). -/
theorem sp_second_bound {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hh : NiceScalar c h)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (t : ℝ) (v : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ × ℝ,
      ‖fderiv ℝ (fun y' : ℝ × ℝ => fderiv ℝ (fun y'' : ℝ × ℝ => L (h (t, y''))) y' v) y‖ ≤ M := by
  have hDh := duhDir_nice hh ((0 : ℝ), v)
  obtain ⟨K2, hK2⟩ := sp_slice_fderiv_bound hc hDh
  have hgd : ∀ y : ℝ × ℝ, HasFDerivAt (fun y'' : ℝ × ℝ => h (t, y''))
      (fderiv ℝ (fun y'' : ℝ × ℝ => h (t, y'')) y) y := fun y =>
    ((sp_slice_contDiff hh.1 t).differentiable (by simp) y).hasFDerivAt
  have hd : ∀ y : ℝ × ℝ, HasFDerivAt (fun y'' : ℝ × ℝ => L (h (t, y'')))
      (L.comp (fderiv ℝ (fun y'' : ℝ × ℝ => h (t, y'')) y)) y := fun y =>
    L.hasFDerivAt.comp y (hgd y)
  have hfun : (fun y' : ℝ × ℝ => fderiv ℝ (fun y'' : ℝ × ℝ => L (h (t, y''))) y' v) =
      fun y' => L (duhDir ((0 : ℝ), v) h (t, y')) := by
    funext y'
    rw [(hd y').fderiv, ContinuousLinearMap.comp_apply, sp_slice_fderiv_apply hh.1 t y' v]
    rfl
  rw [hfun]
  refine ⟨K2, (norm_nonneg _).trans (hK2 t (0, 0)), fun y => ?_⟩
  have hDd : HasFDerivAt (fun y'' : ℝ × ℝ => duhDir ((0 : ℝ), v) h (t, y''))
      (fderiv ℝ (fun y'' : ℝ × ℝ => duhDir ((0 : ℝ), v) h (t, y'')) y) y :=
    ((sp_slice_contDiff hDh.1 t).differentiable (by simp) y).hasFDerivAt
  have hd3 : HasFDerivAt (fun y'' : ℝ × ℝ => L (duhDir ((0 : ℝ), v) h (t, y'')))
      (L.comp (fderiv ℝ (fun y'' : ℝ × ℝ => duhDir ((0 : ℝ), v) h (t, y'')) y)) y :=
    L.hasFDerivAt.comp y hDd
  rw [hd3.fderiv]
  calc ‖L.comp (fderiv ℝ (fun y'' : ℝ × ℝ => duhDir ((0 : ℝ), v) h (t, y'')) y)‖
      ≤ ‖L‖ * ‖fderiv ℝ (fun y'' : ℝ × ℝ => duhDir ((0 : ℝ), v) h (t, y'')) y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * K2 := mul_le_mul hL (hK2 t y) (norm_nonneg _) zero_le_one
    _ = K2 := one_mul K2

/-- The planar IBP for the real and imaginary parts of a frozen slice of a nice source. -/
theorem sp_ibp_real (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c)
    (hh : NiceScalar c h) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (t : ℝ) (x : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w *
        L (h (t, (x.1 - w.1, x.2 - w.2))) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ₀ w *
        L (lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)) := by
  have hgC := sp_slice_contDiff hh.1 t
  have hgd : Differentiable ℝ (fun y : ℝ × ℝ => h (t, y)) := hgC.differentiable (by simp)
  obtain ⟨K0, hK0⟩ := duhFd_bdd hc hh
  have hf : ContDiff ℝ ∞ (fun y : ℝ × ℝ => L (h (t, y))) := L.contDiff.comp hgC
  have hfB : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ × ℝ, ‖L (h (t, y))‖ ≤ M := by
    refine ⟨K0, (norm_nonneg _).trans (hK0 (t, (0, 0))), fun y => ?_⟩
    have h1 := L.le_opNorm (h (t, y))
    have h2 : ‖L‖ * ‖h (t, y)‖ ≤ 1 * K0 := mul_le_mul hL (hK0 _) (norm_nonneg _) zero_le_one
    linarith
  have hfD : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ × ℝ, ‖fderiv ℝ (fun y' : ℝ × ℝ => L (h (t, y'))) y‖ ≤ M := by
    obtain ⟨K1, hK1⟩ := sp_slice_fderiv_bound hc hh
    refine ⟨K1, (norm_nonneg _).trans (hK1 t (0, 0)), fun y => ?_⟩
    have hd : HasFDerivAt (fun y' : ℝ × ℝ => L (h (t, y')))
        (L.comp (fderiv ℝ (fun y' : ℝ × ℝ => h (t, y')) y)) y :=
      L.hasFDerivAt.comp y (hgd y).hasFDerivAt
    rw [hd.fderiv]
    calc ‖L.comp (fderiv ℝ (fun y' : ℝ × ℝ => h (t, y')) y)‖
        ≤ ‖L‖ * ‖fderiv ℝ (fun y' : ℝ × ℝ => h (t, y')) y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * K1 := mul_le_mul hL (hK1 t y) (norm_nonneg _) zero_le_one
      _ = K1 := one_mul K1
  have hfQ := sp_second_bound hc hh L hL t ((1 : ℝ), (0 : ℝ))
  have hfE := sp_second_bound hc hh L hL t ((0 : ℝ), (1 : ℝ))
  have key := UnforcedLeray.Short.PartI.IBPLeaf.integral_heatKernel2AgeDerivative_mul_comp_sub
    hθ₀ hf hfB hfD hfQ hfE x
  refine key.trans (integral_congr_ae (Eventually.of_forall fun w => ?_))
  exact congrArg (fun q => UnforcedLeray.B0284.heatKernel2 θ₀ w * q)
    (sp_lapS_L L hgC (x.1 - w.1, x.2 - w.2))

theorem sp_lapC_slice {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hh : NiceScalar c h) (t : ℝ) (y : ℝ × ℝ) :
    lapC (fun y' : ℝ × ℝ => h (t, y')) y =
      duhDir ((0 : ℝ), B0579.dir 0) (duhDir ((0 : ℝ), B0579.dir 0) h) (t, y) +
        duhDir ((0 : ℝ), B0579.dir 1) (duhDir ((0 : ℝ), B0579.dir 1) h) (t, y) := by
  unfold lapC
  have e0 : pdC 0 (fun y' : ℝ × ℝ => h (t, y')) = fun y' => duhDir ((0 : ℝ), B0579.dir 0) h (t, y') :=
    funext fun y' => sp_pdC_slice hh.1 t 0 y'
  have e1 : pdC 1 (fun y' : ℝ × ℝ => h (t, y')) = fun y' => duhDir ((0 : ℝ), B0579.dir 1) h (t, y') :=
    funext fun y' => sp_pdC_slice hh.1 t 1 y'
  rw [e0, e1, sp_pdC_slice (duhDir_nice hh ((0 : ℝ), B0579.dir 0)).1 t 0 y,
    sp_pdC_slice (duhDir_nice hh ((0 : ℝ), B0579.dir 1)).1 t 1 y]

theorem sp_lapC_cont_bdd {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hh : NiceScalar c h) (t : ℝ) :
    Continuous (fun y : ℝ × ℝ => lapC (fun y' : ℝ × ℝ => h (t, y')) y) ∧
      ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖lapC (fun y' : ℝ × ℝ => h (t, y')) y‖ ≤ K := by
  have N0 := duhDir_nice (duhDir_nice hh ((0 : ℝ), B0579.dir 0)) ((0 : ℝ), B0579.dir 0)
  have N1 := duhDir_nice (duhDir_nice hh ((0 : ℝ), B0579.dir 1)) ((0 : ℝ), B0579.dir 1)
  refine ⟨?_, ?_⟩
  · have hfun : (fun y : ℝ × ℝ => lapC (fun y' : ℝ × ℝ => h (t, y')) y) = fun y =>
        duhDir ((0 : ℝ), B0579.dir 0) (duhDir ((0 : ℝ), B0579.dir 0) h) (t, y) +
          duhDir ((0 : ℝ), B0579.dir 1) (duhDir ((0 : ℝ), B0579.dir 1) h) (t, y) :=
      funext (sp_lapC_slice hh t)
    rw [hfun]
    exact ((N0.1.continuous).comp (by fun_prop)).add ((N1.1.continuous).comp (by fun_prop))
  · obtain ⟨K0, hK0⟩ := duhFd_bdd hc N0
    obtain ⟨K1, hK1⟩ := duhFd_bdd hc N1
    refine ⟨K0 + K1, fun y => ?_⟩
    rw [sp_lapC_slice hh t y]
    exact (norm_add_le _ _).trans (add_le_add (hK0 _) (hK1 _))

theorem sp_ibp_complex {c : ℝ} {h : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hh : NiceScalar c h)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (t : ℝ) (x : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, ((UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w : ℝ) : ℂ) *
        h (t, (x.1 - w.1, x.2 - w.2)) =
      ∫ w : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 θ₀ w : ℝ) : ℂ) *
        lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2) := by
  obtain ⟨M, hM⟩ := duhFd_bdd hc hh
  obtain ⟨hLc, Ml, hMl⟩ := sp_lapC_cont_bdd hc hh t
  have hφc : Continuous (fun w : ℝ × ℝ => h (t, (x.1 - w.1, x.2 - w.2))) :=
    hh.1.continuous.comp (by fun_prop)
  have hψc : Continuous (fun w : ℝ × ℝ => lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)) :=
    hLc.comp (by fun_prop)
  have hA_re : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * (h (t, (x.1 - w.1, x.2 - w.2))).re) :=
    duhAI_intR (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀)
      (Complex.continuous_re.comp hφc) (M := M) (fun z => sp_re_bound _ (hM _))
  have hA_im : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w * (h (t, (x.1 - w.1, x.2 - w.2))).im) :=
    duhAI_intR (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ₀)
      (Complex.continuous_im.comp hφc) (M := M) (fun z => sp_im_bound _ (hM _))
  have hG_re : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ₀ w *
        (lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)).re) :=
    duhAI_intR (UnforcedLeray.B0284.integrable_heatKernel2 hθ₀)
      (Complex.continuous_re.comp hψc) (M := Ml) (fun z => sp_re_bound _ (hMl _))
  have hG_im : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ₀ w *
        (lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)).im) :=
    duhAI_intR (UnforcedLeray.B0284.integrable_heatKernel2 hθ₀)
      (Complex.continuous_im.comp hψc) (M := Ml) (fun z => sp_im_bound _ (hMl _))
  have hLreal : ‖Complex.reCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by rw [one_mul, Complex.reCLM_apply]; exact sp_re_bound z le_rfl)
  have hLimag : ‖Complex.imCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by rw [one_mul, Complex.imCLM_apply]; exact sp_im_bound z le_rfl)
  have hR := sp_ibp_real Complex.reCLM hLreal hc hh hθ₀ t x
  have hI := sp_ibp_real Complex.imCLM hLimag hc hh hθ₀ t x
  simp only [Complex.reCLM_apply] at hR
  simp only [Complex.imCLM_apply] at hI
  calc ∫ w : ℝ × ℝ, ((UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w : ℝ) : ℂ) *
        h (t, (x.1 - w.1, x.2 - w.2))
      = ((∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w *
            (h (t, (x.1 - w.1, x.2 - w.2))).re : ℝ) : ℂ) +
          Complex.I * ((∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w *
            (h (t, (x.1 - w.1, x.2 - w.2))).im : ℝ) : ℂ) :=
        sp_split_int (K := fun w => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ₀ w)
          (φ := fun w => h (t, (x.1 - w.1, x.2 - w.2))) hA_re hA_im
    _ = ((∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ₀ w *
            (lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)).re : ℝ) : ℂ) +
          Complex.I * ((∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ₀ w *
            (lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)).im : ℝ) : ℂ) := by
        rw [hR, hI]
    _ = ∫ w : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 θ₀ w : ℝ) : ℂ) *
        lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2) :=
        (sp_split_int (K := fun w => UnforcedLeray.B0284.heatKernel2 θ₀ w)
          (φ := fun w => lapC (fun y : ℝ × ℝ => h (t, y)) (x.1 - w.1, x.2 - w.2)) hG_re hG_im).symm

/-- **Space part** (SP 3427-3440): `d/dr' ∫ G_{νr'}(z) h(s - r, x - z) dz = ν B(r)` at `r' = r > 0`. -/
theorem duhEqSpacePart : UnforcedLeray.Short.IIIa.DuhEqSpacePart := by
  intro c ν h hc hν hn s x r hr
  have hθ : 0 < ν * r := mul_pos hν hr
  obtain ⟨M, hM⟩ := duhFd_bdd hc hn
  have hgc : Continuous (fun y : ℝ × ℝ => h (s - r, y)) := hn.1.continuous.comp (by fun_prop)
  have hthe := sp_theta_complex hgc (fun y => hM _) hθ x
  have hlin : HasDerivAt (fun r' : ℝ => ν * r') ν r := by
    simpa using (hasDerivAt_id r).const_mul ν
  have hcomp := hthe.scomp r hlin
  have hD : (∫ w : ℝ × ℝ, ((UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * r) w : ℝ) : ℂ) *
        h (s - r, (x.1 - w.1, x.2 - w.2))) = duhLap ν h s x r :=
    sp_ibp_complex hc hn hθ (s - r) x
  refine hcomp.congr_deriv ?_
  rw [Complex.real_smul, hD]

end UnforcedLeray.Short.IIIa
