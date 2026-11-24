import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `C¹` slab calculus (helpers for the `C¹` integration-by-parts leaves, source 4268-4270, 5001-5008)

Copies of the `C^∞` lemmas `IIb.srwf_slab_dy` and `IIb.srwf_coord_contDiff`-based pointwise
identities, with the smoothness hypothesis weakened to `C¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.IIb

/-- `∂_{y_i}` of a `C¹` complexified real function, pointwise. -/
theorem c1_id_dy_ofReal {G : ℝ × Space → ℝ} (hG : ContDiff ℝ 1 G) (i : Fin 3) (x : ℝ × Space) :
    dy i (fun w : ℝ × Space => ((G w : ℝ) : ℂ)) x =
      ((fderiv ℝ (fun y => G (x.1, y)) x.2 (coordinateVector i) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ G x := (hG.differentiable (by simp)) x
  have h : HasFDerivAt (fun w : ℝ × Space => ((G w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ G x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
  have hs : fderiv ℝ (fun y => G (x.1, y)) x.2 =
      (fderiv ℝ G x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space hd
  simp only [dy]
  rw [h.fderiv, hs]
  simp [coordinateVector]

/-- **Slab integral of a `y`-derivative, `C¹` version.** For a `C¹` `K` vanishing for `‖y‖ > R`,
the `y_j`-derivative is integrable on `(0,P] × ℝ³` with zero integral. -/
theorem c1_slab_dy {P : ℝ} {K : ℝ × Space → ℂ} (hK : ContDiff ℝ 1 K) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → K (τ, y) = 0) (j : Fin 3) :
    Integrable (fun z => dy j K z) (srwfSlab P) ∧
      ∫ z, dy j K z ∂(srwfSlab P) = 0 := by
  have hcont : Continuous (fun z => dy j K z) := by
    simp only [dy]
    exact (hK.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable (fun z => dy j K z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hcont (srwf_dy_bdd hR j)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show ∫ y, dy j K (t, y) = 0
  have hd : Differentiable ℝ K := hK.differentiable (by simp)
  have hsl : ContDiff ℝ 1 (fun y => K (t, y)) := hK.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y => K (t, y)) :=
    UnforcedLeray.B0005.hasCompactSupport_of_bound (R := R) fun y hy => hR t y hy
  have hpt : ∀ y, dy j K (t, y) = fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) := by
    intro y
    simp only [dy, UnforcedLeray.B0005.fderiv_slice_space (hd (t, y)),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  simp only [hpt]
  have hcd : HasCompactSupport fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    hc.fderiv_apply (𝕜 := ℝ) _
  have hcont' : Continuous fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    (hsl.continuous_fderiv (by simp)).clm_apply continuous_const
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℂ)) (g := fun x => K (t, x)) (v := coordinateVector j)
    (by simp) (by simpa using hcont'.integrable_of_hasCompactSupport hcd)
    (by simpa using hsl.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hsl.differentiable (by simp)) x)
  simpa using this

/-- `∂_τ` of a `C¹` function vanishing for `‖y‖ > R` vanishes there too. -/
theorem c1_dtau_bdd {H : ℝ × Space → ℂ} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → H (τ, y) = 0) :
    ∀ τ y, R < ‖y‖ → dτ H (τ, y) = 0 := by
  intro τ y hy
  have hopen : IsOpen {p : ℝ × Space | R < ‖p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : H =ᶠ[nhds ((τ, y) : ℝ × Space)] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds (show R < ‖((τ, y) : ℝ × Space).2‖ from hy)] with p hp
    exact hR p.1 p.2 hp
  simp [dτ, hev.fderiv_eq]

/-- **Slab integral of a `τ`-derivative, `C¹` version.** For a `C¹`, `P`-periodic `H` vanishing for
`‖y‖ > R`, `∫∫_{(0,P]×ℝ³} ∂_τ H = 0` (`B0005.integral_slab_dτ` for `C¹` functions). -/
theorem c1_slab_dtau {P : ℝ} (hP : 0 < P) {H : ℝ × Space → ℂ} (hH : ContDiff ℝ 1 H)
    (hper : ∀ τ y, H (τ + P, y) = H (τ, y)) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → H (τ, y) = 0) :
    Integrable (fun z => dτ H z) (srwfSlab P) ∧
      ∫ z, dτ H z ∂(srwfSlab P) = 0 := by
  have hcont : Continuous (fun z => dτ H z) := by
    simp only [dτ]
    exact (hH.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable (fun z => dτ H z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hcont (fun t y hy => c1_dtau_bdd hR t y hy)
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  show ∫ x in Ioc (0 : ℝ) P, dτ H (x, y) = 0
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hderiv : ∀ t, HasDerivAt (fun s => H (s, y)) (dτ H (t, y)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (hd (t, y)).hasFDerivAt.comp_hasDerivAt t h1
  rw [← intervalIntegral.integral_of_le hP.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
  have hp := hper 0 y
  simp only [zero_add] at hp
  show H (P, y) - H (0, y) = 0
  rw [hp, sub_self]

end UnforcedLeray.Short.PartIIIb.Concrete
