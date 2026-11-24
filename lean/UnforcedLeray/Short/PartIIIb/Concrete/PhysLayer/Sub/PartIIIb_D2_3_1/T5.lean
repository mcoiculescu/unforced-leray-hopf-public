import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! Helpers for `bracketAxiNoSwirl_of` (source 4171-4174).  The bracket of two axisymmetric
swirl-free `C²` fields is equivariant under the rotations `rotFun θ` about `e₃`, and vanishes in the
`e_y` component on the half plane; equivariance then gives the frame form at every off-axis point. -/

theorem bx_not_axis_of_pos {y : Space} (h : 0 < ϱ y) : y ∉ axis := by
  rintro ⟨h0, h1⟩
  unfold ϱ at h
  rw [h0, h1] at h
  simp at h

theorem bx_not_axis_of_first {y : Space} (h : y 0 ≠ 0) : y ∉ axis := fun ha => h ha.1

theorem bx_ϱ_rot (θ : ℝ) (y : Space) : ϱ (rotFun θ y) = ϱ y := by
  unfold ϱ
  rw [rotFun_apply_zero, rotFun_apply_one]
  congr 1
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.cos_sq_add_sin_sq θ

theorem bx_meridPt_rot (θ : ℝ) (y : Space) : meridPt (rotFun θ y) = meridPt y := by
  simp only [meridPt, bx_ϱ_rot, rotFun_apply_two]

/-- The rotation as a continuous linear map. -/
def bxRot (θ : ℝ) : Space →L[ℝ] Space := LinearMap.toContinuousLinearMap (rotL θ)

theorem bxRot_apply (θ : ℝ) (x : Space) : bxRot θ x = rotFun θ x := rfl

theorem bx_sub_rot (θ : ℝ) (a b : Space) : rotFun θ (a - b) = rotFun θ a - rotFun θ b :=
  (rotL θ).map_sub a b

theorem bx_eR_rot (θ : ℝ) (y : Space) : eR (rotFun θ y) = rotFun θ (eR y) := by
  rw [eR, eR, bx_ϱ_rot]
  ext i
  fin_cases i <;> simp [hor, rotFun] <;> ring

theorem bx_frameL_rot (θ : ℝ) (y : Space) (v : Merid) :
    rotFun θ (frameL y v) = frameL (rotFun θ y) v := by
  rw [frameL_apply, frameL_apply, bx_eR_rot]
  ext i
  fin_cases i <;> simp [rotFun, e3, coordinateVector] <;> ring

theorem bx_frameL2 (y : Space) (a b : ℝ) : frameL y !₂[a, b] = a • eR y + b • e3 := by
  rw [frameL_apply]
  simp

/-- The slice equivariance of an axisymmetric swirl-free field, off the axis. -/
theorem bx_slice_equiv {F : Space → Space}
    (hF : ∀ y, y ∉ axis → F y = frameL y !₂[F (meridPt y) 0, F (meridPt y) 2])
    (θ : ℝ) (y : Space) (hy : y ∉ axis) :
    F (rotFun θ y) = rotFun θ (F y) := by
  have hry : rotFun θ y ∉ axis := bx_not_axis_of_pos (by rw [bx_ϱ_rot]; exact ϱ_pos hy)
  rw [hF (rotFun θ y) hry, hF y hy, bx_meridPt_rot, bx_frameL_rot]

/-- Derivative equivariance: `DF(Ry) (R v) = R (DF(y) v)` when `F` is equivariant near `y`. -/
theorem bx_fderiv_equiv {F : Space → Space} (hF : Differentiable ℝ F) {θ : ℝ} {y : Space}
    (hEq : (fun z => F (rotFun θ z)) =ᶠ[𝓝 y] (fun z => rotFun θ (F z))) (v : Space) :
    fderiv ℝ F (rotFun θ y) (rotFun θ v) = rotFun θ (fderiv ℝ F y v) := by
  have hr : HasFDerivAt (rotFun θ) (bxRot θ) y := by
    have : (rotFun θ) = ⇑(bxRot θ) := funext fun x => (bxRot_apply θ x).symm
    rw [this]
    exact (bxRot θ).hasFDerivAt
  have h1 : HasFDerivAt (fun z => F (rotFun θ z)) ((fderiv ℝ F (rotFun θ y)).comp (bxRot θ)) y :=
    (hF (rotFun θ y)).hasFDerivAt.comp y hr
  have h2 : HasFDerivAt (fun z => rotFun θ (F z)) ((bxRot θ).comp (fderiv ℝ F y)) y := by
    have : (fun z => rotFun θ (F z)) = fun z => (bxRot θ) (F z) :=
      funext fun z => (bxRot_apply θ _).symm
    rw [this]
    exact (bxRot θ).hasFDerivAt.comp y (hF y).hasFDerivAt
  have h3 := h1.congr_of_eventuallyEq hEq.symm
  have huniq := h2.unique h3
  have := congrArg (fun L : Space →L[ℝ] Space => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, bxRot_apply] at this
  exact this.symm

/-- The bracket of two `C²` axisymmetric swirl-free fields is equivariant off the axis. -/
theorem bx_bracket_equiv {U X : Space → Space} (hU : ContDiff ℝ 2 U) (hX : ContDiff ℝ 2 X)
    (hUa : ∀ y, y ∉ axis → U y = frameL y !₂[U (meridPt y) 0, U (meridPt y) 2])
    (hXa : ∀ y, y ∉ axis → X y = frameL y !₂[X (meridPt y) 0, X (meridPt y) 2])
    (θ : ℝ) (y : Space) (hy : y ∉ axis) :
    fderiv ℝ X (rotFun θ y) (U (rotFun θ y)) - fderiv ℝ U (rotFun θ y) (X (rotFun θ y)) =
      rotFun θ (fderiv ℝ X y (U y) - fderiv ℝ U y (X y)) := by
  have hpos : ∀ᶠ z in 𝓝 y, 0 < ϱ z :=
    (isOpen_lt continuous_const continuous_ϱ).mem_nhds (ϱ_pos hy)
  have hXE : (fun z => X (rotFun θ z)) =ᶠ[𝓝 y] (fun z => rotFun θ (X z)) := by
    filter_upwards [hpos] with z hz
    exact bx_slice_equiv hXa θ z (bx_not_axis_of_pos hz)
  have hUE : (fun z => U (rotFun θ z)) =ᶠ[𝓝 y] (fun z => rotFun θ (U z)) := by
    filter_upwards [hpos] with z hz
    exact bx_slice_equiv hUa θ z (bx_not_axis_of_pos hz)
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  rw [bx_slice_equiv hUa θ y hy, bx_slice_equiv hXa θ y hy,
    bx_fderiv_equiv hXd hXE (U y), bx_fderiv_equiv hUd hUE (X y), bx_sub_rot]

/-- A swirl-free field has zero `e_y` component on the half plane. -/
theorem bx_one_comp {F : Space → Space}
    (hF : ∀ y, y ∉ axis → F y = frameL y !₂[F (meridPt y) 0, F (meridPt y) 2])
    {q : Space} (hq : q ∉ axis) (hq1 : q 1 = 0) : F q 1 = 0 := by
  rw [hF q hq]
  simp [frameL_apply, eR, hor, e3, coordinateVector, hq1]

/-- The `e_y` derivative vanishes in directions of the half plane. -/
theorem bx_deriv_one_zero {F : Space → Space} (hFd : Differentiable ℝ F)
    (hF : ∀ y, y ∉ axis → F y = frameL y !₂[F (meridPt y) 0, F (meridPt y) 2])
    {p w : Space} (hp1 : p 1 = 0) (hp0 : 0 < p 0) (hw1 : w 1 = 0) :
    fderiv ℝ F p w 1 = 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
    simpa using h
  have hD : HasDerivAt (fun t : ℝ => F (p + t • w)) (fderiv ℝ F p w) 0 :=
    (hFd p).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hcomp1 : HasDerivAt (fun t : ℝ => F (p + t • w) 1) (fderiv ℝ F p w 1) 0 := by
    have h2 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hD
    convert h2 using 1 <;> first | rfl | simp
  have hev : (fun t : ℝ => F (p + t • w) 1) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => p 0 + t * w 0) := by fun_prop
    have ht : Tendsto (fun t : ℝ => p 0 + t * w 0) (𝓝 0) (𝓝 (p 0 + 0 * w 0)) := hc.tendsto 0
    simp only [zero_mul, add_zero] at ht
    filter_upwards [ht.eventually (lt_mem_nhds hp0)] with t ht0
    have hq0 : (p + t • w) 0 = p 0 + t * w 0 := by simp
    have hq1 : (p + t • w) 1 = 0 := by simp [hp1, hw1]
    apply bx_one_comp hF _ hq1
    apply bx_not_axis_of_first
    rw [hq0]
    exact ht0.ne'
  have hdz : HasDerivAt (fun t : ℝ => F (p + t • w) 1) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  exact hcomp1.unique hdz

/-- The bracket has zero `e_y` component on the half plane. -/
theorem bx_bracket_one_zero {U X : Space → Space} (hUd : Differentiable ℝ U)
    (hXd : Differentiable ℝ X)
    (hUa : ∀ y, y ∉ axis → U y = frameL y !₂[U (meridPt y) 0, U (meridPt y) 2])
    (hXa : ∀ y, y ∉ axis → X y = frameL y !₂[X (meridPt y) 0, X (meridPt y) 2])
    {p : Space} (hp1 : p 1 = 0) (hp0 : 0 < p 0) :
    (fderiv ℝ X p (U p) - fderiv ℝ U p (X p)) 1 = 0 := by
  have hpax : p ∉ axis := bx_not_axis_of_first hp0.ne'
  have hU1 : U p 1 = 0 := bx_one_comp hUa hpax hp1
  have hX1 : X p 1 = 0 := bx_one_comp hXa hpax hp1
  rw [PiLp.sub_apply, bx_deriv_one_zero hXd hXa hp1 hp0 hU1,
    bx_deriv_one_zero hUd hUa hp1 hp0 hX1]
  simp

theorem bx_ϱ_meridPt_eq {p : Space} (hp1 : p 1 = 0) (hp0 : 0 < p 0) : ϱ p = p 0 := by
  unfold ϱ
  rw [hp1, show p 0 ^ 2 + (0 : ℝ) ^ 2 = p 0 ^ 2 by ring]
  exact Real.sqrt_sq hp0.le

theorem bx_eR_rot_p (θ : ℝ) (p : Space) (hp1 : p 1 = 0) (hp0 : 0 < p 0) :
    eR (rotFun θ p) = !₂[Real.cos θ, Real.sin θ, 0] := by
  rw [eR, bx_ϱ_rot, bx_ϱ_meridPt_eq hp1 hp0]
  ext i
  fin_cases i <;> simp [hor, rotFun, hp1, hp0.ne'] <;> field_simp

/-- A vector with zero `e_y` component is the frame lift of its meridional part. -/
theorem bx_frame_vec (b : Space) (θ : ℝ) (p : Space) (hp1 : p 1 = 0) (hp0 : 0 < p 0)
    (hb1 : b 1 = 0) :
    rotFun θ b = frameL (rotFun θ p) !₂[b 0, b 2] := by
  rw [bx_frameL2, bx_eR_rot_p θ p hp1 hp0]
  ext i
  fin_cases i <;> simp [rotFun, e3, coordinateVector, hb1] <;> ring

/-- The frame form of the bracket at `Rθ p` with `p` on the half plane. -/
theorem bx_frame_at {U X : Space → Space} (hU : ContDiff ℝ 2 U) (hX : ContDiff ℝ 2 X)
    (hUa : ∀ y, y ∉ axis → U y = frameL y !₂[U (meridPt y) 0, U (meridPt y) 2])
    (hXa : ∀ y, y ∉ axis → X y = frameL y !₂[X (meridPt y) 0, X (meridPt y) 2])
    (θ : ℝ) {p : Space} (hp1 : p 1 = 0) (hp0 : 0 < p 0) :
    fderiv ℝ X (rotFun θ p) (U (rotFun θ p)) - fderiv ℝ U (rotFun θ p) (X (rotFun θ p)) =
      frameL (rotFun θ p) !₂[(fderiv ℝ X p (U p) - fderiv ℝ U p (X p)) 0,
        (fderiv ℝ X p (U p) - fderiv ℝ U p (X p)) 2] := by
  have hpax : p ∉ axis := bx_not_axis_of_first hp0.ne'
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  rw [bx_bracket_equiv hU hX hUa hXa θ p hpax]
  exact bx_frame_vec _ θ p hp1 hp0 (bx_bracket_one_zero hUd hXd hUa hXa hp1 hp0)

/-- Every off-axis point is a rotation of its meridional point. -/
theorem bx_meridPt_rot_eq (y : Space) :
    rotFun (Complex.arg ⟨y 0, y 1⟩) (meridPt y) = y := by
  have h := rotFun_cylMap (Complex.arg ⟨y 0, y 1⟩) (ϱ y) 0 (y 2)
  have hm : meridPt y = cylMap ((ϱ y, 0), y 2) := by
    ext i
    fin_cases i <;> simp [meridPt, cylMap]
  rw [hm, h, zero_add]
  exact cylMap_polar y

theorem bracketAxiNoSwirl_of : BracketAxiNoSwirl := by
  intro U X hU hX hUA hXA
  have hUs : ∀ τ, ∀ y, y ∉ axis → U τ y = frameL y !₂[U τ (meridPt y) 0, U τ (meridPt y) 2] :=
    fun τ y hy => hUA τ y (mem_univ _) hy
  have hXs : ∀ τ, ∀ y, y ∉ axis → X τ y = frameL y !₂[X τ (meridPt y) 0, X τ (meridPt y) 2] :=
    fun τ y hy => hXA τ y (mem_univ _) hy
  intro τ y _ hy
  dsimp only
  have hp0 : 0 < meridPt y 0 := ϱ_pos hy
  have hp1 : meridPt y 1 = 0 := rfl
  have key := bx_frame_at (hU τ) (hX τ) (hUs τ) (hXs τ) (Complex.arg ⟨y 0, y 1⟩) hp1 hp0
  rw [bx_meridPt_rot_eq y] at key
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
