import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# The Laplacian commutes with convolution in `y`

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  If `Δu = c` in `y` and `Θ` is a phase test, then
`Δ_y (u * Θ) = c * Θ`.  Proof: `u * Θ = Θ_τ * u` (convolution with the smooth compactly
supported `u` on the right), derivatives fall on `u`, and the second-derivative sum is `c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Scalar multiplication `c • v` as a bilinear map `CVec3 × ℝ → CVec3`. -/
def clLsm : CVec3 →L[ℝ] ℝ →L[ℝ] CVec3 :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).flip

/-- The partial derivative `∂_j u` of a scalar function on `ℝ³`. -/
def clPartial (u : Space → ℝ) (j : Fin 3) : Space → ℝ :=
  fun a => fderiv ℝ u a (coordinateVector j)

theorem cl_smooth (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (hκ : KerOK κ)
    (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ) :
    ContDiff ℝ ∞ (convY κ Θ) := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  have hf : LocallyIntegrable κ volume := hκ.1.continuous.locallyIntegrable
  have hgs : ∀ p : ℝ, ∀ x : Space, p ∈ (univ : Set ℝ) → x ∉ Metric.closedBall (0 : Space) R →
      (fun (τ : ℝ) (z : Space) => Θ (τ, z)) p x = 0 := by
    intro p x _ hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hR p x hx
  have hg : ContDiffOn ℝ ∞ (Function.uncurry fun (τ : ℝ) (z : Space) => Θ (τ, z))
      (univ ×ˢ univ) := by
    exact hΘ.smooth.contDiffOn
  have key := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ := volume) (f := κ)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
    (s := univ) (k := Metric.closedBall (0 : Space) R)
    isOpen_univ (isCompact_closedBall _ _) hgs hf hg
  have heq : convY κ Θ = fun q : ℝ × Space =>
      (convolution κ ((fun (τ : ℝ) (z : Space) => Θ (τ, z)) q.1)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume) q.2 := by
    funext x
    simp only [convY, convolution, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]
  rw [heq]
  rw [Set.univ_prod_univ] at key
  exact contDiffOn_univ.mp key

/-- `convY u Θ` on a fixed phase slice is the convolution `Θ_τ ⋆ u`. -/
theorem cl_convY_eq (u : Space → ℝ) (Θ : ℝ × Space → CVec3) (τ : ℝ) :
    (fun y => convY u Θ (τ, y)) = convolution (fun w => Θ (τ, w)) u clLsm volume := by
  funext y
  simp only [convY, convolution_def, clLsm, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Complex.coe_smul]
  have h := integral_sub_left_eq_self (μ := volume)
    (fun t : Space => u (y - t) • Θ (τ, t)) y
  simp only [sub_sub_cancel] at h
  exact h

/-- Derivative of a convolution in its right (compactly supported) argument, in direction `v`. -/
theorem cl_fderiv_conv (f : Space → CVec3) (hf : Continuous f) (g : Space → ℝ)
    (hg : HasCompactSupport g) (hg1 : ContDiff ℝ 1 g) (y v : Space) :
    fderiv ℝ (fun y' => (convolution f g clLsm volume) y') y v =
      (convolution f (fun a => fderiv ℝ g a v) clLsm volume) y := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable
  have hd := hg.hasFDerivAt_convolution_right clLsm hfl hg1 y
  rw [hd.fderiv]
  rw [convolution_precompR_apply clLsm hfl (hg.fderiv (𝕜 := ℝ))
    (hg1.continuous_fderiv one_ne_zero) y v]

/-- Directional partial derivative of a real function of `(τ, y)` that depends on `y` only. -/
theorem cl_dy_eq_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : ℝ × Space → F) (hK : Differentiable ℝ K) (τ : ℝ) (y : Space) (j : Fin 3) :
    dy j K (τ, y) = fderiv ℝ (fun y' => K (τ, y')) y (coordinateVector j) := by
  have h1 : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have h2 := (hK (τ, y)).hasFDerivAt.comp y h1
  have h3 : (fun y' => K (τ, y')) = K ∘ (fun y' => ((τ, y') : ℝ × Space)) := rfl
  rw [h3, h2.fderiv]
  simp [dy]

theorem cl_dy_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : ℝ × Space → F) (hH : ContDiff ℝ ∞ H) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j H) := by
  unfold dy
  exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cl_fderiv_ofReal (g : Space → ℝ) (hg : Differentiable ℝ g) (y v : Space) :
    fderiv ℝ (fun a => ((g a : ℝ) : ℂ)) y v = ((fderiv ℝ g y v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun a => ((g a : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hg y).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- Sum of convolutions is the convolution of the sum. -/
theorem cl_conv_sum (f : Space → CVec3) (hf : Continuous f) (g : Fin 3 → Space → ℝ)
    (hg : ∀ j, HasCompactSupport (g j)) (hgc : ∀ j, Continuous (g j)) (y : Space) :
    ∑ j, (convolution f (g j) clLsm volume) y =
      (convolution f (fun a => ∑ j, g j a) clLsm volume) y := by
  have hint : ∀ j : Fin 3, Integrable (fun t => clLsm (f t) (g j (y - t))) volume := by
    intro j
    exact (hg j).convolutionExists_right clLsm hf.locallyIntegrable (hgc j) y
  simp only [convolution_def]
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  congr 1
  funext t
  simp only [map_sum]

theorem cl_laplace_comm (P : ℝ) (u c : Space → ℝ) (Θ : ℝ × Space → CVec3)
    (hu : KerOK u) (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ)
    (hlap : ∀ x : ℝ × Space, lapT (liftS u) x = ((c x.2 : ℝ) : ℂ)) :
    lapT (convY u Θ) = convY c Θ := by
  have hH : ContDiff ℝ ∞ (convY u Θ) := cl_smooth P u Θ hu hΘ
  have hHd : Differentiable ℝ (convY u Θ) := hH.differentiable (by simp)
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by simp)
  have hcont : ∀ τ : ℝ, Continuous (fun w : Space => Θ (τ, w)) := fun τ =>
    hΘ.smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hPd : ∀ j, ContDiff ℝ ∞ (clPartial u j) := fun j => by
    unfold clPartial
    exact (hu.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hPdc : ∀ j, HasCompactSupport (clPartial u j) := fun j =>
    hu.2.fderiv_apply (𝕜 := ℝ) (coordinateVector j)
  have hPd1 : ∀ j, ContDiff ℝ 1 (clPartial u j) := fun j => (hPd j).of_le (by simp)
  have hPdd : ∀ j, Differentiable ℝ (clPartial u j) := fun j => (hPd j).differentiable (by simp)
  have hdjH : ∀ j, Differentiable ℝ (dy j (convY u Θ)) := fun j =>
    (cl_dy_contDiff _ hH j).differentiable (by simp)
  have key1 : ∀ (τ : ℝ) (y' : Space) (j : Fin 3),
      dy j (convY u Θ) (τ, y') = (convolution (fun w => Θ (τ, w)) (clPartial u j) clLsm volume) y' := by
    intro τ y' j
    rw [cl_dy_eq_slice (convY u Θ) hHd τ y' j, cl_convY_eq u Θ τ]
    exact cl_fderiv_conv _ (hcont τ) u hu.2 hu1 y' (coordinateVector j)
  have key2 : ∀ (τ : ℝ) (y : Space) (j : Fin 3),
      dy j (dy j (convY u Θ)) (τ, y) =
        (convolution (fun w => Θ (τ, w))
          (fun a => fderiv ℝ (clPartial u j) a (coordinateVector j)) clLsm volume) y := by
    intro τ y j
    rw [cl_dy_eq_slice (dy j (convY u Θ)) (hdjH j) τ y j]
    have hfun : (fun y' => dy j (convY u Θ) (τ, y')) =
        convolution (fun w => Θ (τ, w)) (clPartial u j) clLsm volume :=
      funext (fun y' => key1 τ y' j)
    rw [hfun]
    exact cl_fderiv_conv _ (hcont τ) (clPartial u j) (hPdc j) (hPd1 j) y (coordinateVector j)
  have hLS : ContDiff ℝ ∞ (liftS u) :=
    Complex.ofRealCLM.contDiff.comp (hu.1.comp contDiff_snd)
  have hliftd : ∀ (τ : ℝ) (y : Space) (j : Fin 3),
      dy j (liftS u) (τ, y) = ((clPartial u j y : ℝ) : ℂ) := by
    intro τ y j
    rw [cl_dy_eq_slice (liftS u) (hLS.differentiable (by simp)) τ y j]
    have hfun : (fun y' => liftS u (τ, y')) = fun a => ((u a : ℝ) : ℂ) := rfl
    rw [hfun, cl_fderiv_ofReal u (hu1.differentiable (by simp)) y (coordinateVector j)]
    rfl
  have key3a : ∀ (τ : ℝ) (y : Space) (j : Fin 3),
      dy j (dy j (liftS u)) (τ, y) =
        ((fderiv ℝ (clPartial u j) y (coordinateVector j) : ℝ) : ℂ) := by
    intro τ y j
    have hdj : Differentiable ℝ (dy j (liftS u)) :=
      (cl_dy_contDiff _ hLS j).differentiable (by simp)
    rw [cl_dy_eq_slice (dy j (liftS u)) hdj τ y j]
    have hfun : (fun y' => dy j (liftS u) (τ, y')) =
        fun a => ((clPartial u j a : ℝ) : ℂ) :=
      funext (fun y' => hliftd τ y' j)
    rw [hfun, cl_fderiv_ofReal _ (hPdd j) y (coordinateVector j)]
  have key3 : ∀ y : Space, c y = ∑ j, fderiv ℝ (clPartial u j) y (coordinateVector j) := by
    intro y
    have h : ∑ j, dy j (dy j (liftS u)) (0, y) = ((c y : ℝ) : ℂ) := hlap (0, y)
    simp only [key3a] at h
    rw [← Complex.ofReal_sum] at h
    exact (Complex.ofReal_injective h).symm
  have hconv_c : (fun a => ∑ j, fderiv ℝ (clPartial u j) a (coordinateVector j)) = c :=
    funext (fun a => (key3 a).symm)
  have hcpt : ∀ j, HasCompactSupport (fun a => fderiv ℝ (clPartial u j) a (coordinateVector j)) :=
    fun j => (hPdc j).fderiv_apply (𝕜 := ℝ) (coordinateVector j)
  have hcnt : ∀ j, Continuous (fun a => fderiv ℝ (clPartial u j) a (coordinateVector j)) :=
    fun j => ((hPd1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  funext x
  obtain ⟨τ, y⟩ := x
  show ∑ j, dy j (dy j (convY u Θ)) (τ, y) = convY c Θ (τ, y)
  simp only [key2]
  have hfinal : (convolution (fun w => Θ (τ, w)) c clLsm volume) y = convY c Θ (τ, y) :=
    (congrFun (cl_convY_eq c Θ τ) y).symm
  have hcongr : ∀ g : Space → ℝ, g = c →
      (convolution (fun w => Θ (τ, w)) g clLsm volume) y =
        (convolution (fun w => Θ (τ, w)) c clLsm volume) y := fun g hg => by rw [hg]
  exact (cl_conv_sum (fun w => Θ (τ, w)) (hcont τ)
    (fun j a => fderiv ℝ (clPartial u j) a (coordinateVector j)) hcpt hcnt y).trans
    ((hcongr _ hconv_c).trans hfinal)

theorem convLap : UnforcedLeray.Short.PartIIIb.Concrete.ConvLap := by
  intro P u c Θ hu hc hΘ hlap
  exact cl_laplace_comm P u c Θ hu hΘ hlap

end UnforcedLeray.Short.PartIIIb.Concrete
