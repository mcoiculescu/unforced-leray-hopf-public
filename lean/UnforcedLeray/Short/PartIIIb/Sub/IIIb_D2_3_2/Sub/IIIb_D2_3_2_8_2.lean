import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8

/-!
# `IBPBridge`: `L₀ + μ = D_μ` on the complexified real field (source 4140-4141)

For `u = realCf H` with `H` jointly smooth, the three operators of `L₀ = T₀ - νΔ - ½` are
computed pointwise: `∂_τ u = realC(∂_τ H)`, `y·∇u = realC(y·∇H)` and `Δu = realC(physLap H)`,
where `realC` is the ℝ-linear embedding of real vectors into `ℂ³`.  Then
`L₀u + μu = realC(∂_τH - ½ y·∇H - νΔH + (μ-½)H) = realC(physDmu ν μ H)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The ℝ-linear embedding of real vectors into `ℂ³` (as `IIb.absRealCL`). -/
def br_RC : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => B0412.realC x
      map_add' := fun x y => by ext i; simp [B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [B0412.realC_apply, Complex.real_smul] }

theorem br_realCf_eq (H : ℝ → Space → Space) :
    realCf H = fun w => br_RC (H w.1 w.2) := rfl

/-- Chain rule for `realC` (ℝ-linear). -/
theorem br_fderiv_RC (Hf : ℝ × Space → Space) (hHf : Differentiable ℝ Hf) (x v : ℝ × Space) :
    fderiv ℝ (fun w => br_RC (Hf w)) x v = br_RC (fderiv ℝ Hf x v) := by
  have h : HasFDerivAt (fun w => br_RC (Hf w)) (br_RC.comp (fderiv ℝ Hf x)) x :=
    br_RC.hasFDerivAt.comp x (hHf x).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The `y`-expansion `v = ∑ⱼ vⱼ eⱼ`. -/
theorem br_expand (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext i
  simp [coordinateVector, Pi.single_apply]

theorem br_dtau (H : ℝ → Space → Space) (hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2))
    (x : ℝ × Space) :
    dτ (realCf H) x = br_RC (deriv (fun t => H t x.2) x.1) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by simp)
  have hs : fderiv ℝ (fun t => H t x.2) x.1 =
      (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x).comp (ContinuousLinearMap.inl ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_time (hd x)
  have hdev : deriv (fun t => H t x.2) x.1 = fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (1, 0) := by
    rw [← fderiv_apply_one_eq_deriv, hs]
    rfl
  show fderiv ℝ (realCf H) x (1, 0) = _
  rw [br_realCf_eq H, br_fderiv_RC (fun w => H w.1 w.2) hd x (1, 0), hdev]

theorem br_dy (H : ℝ → Space → Space) (hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2))
    (j : Fin 3) (x : ℝ × Space) :
    dy j (realCf H) x = br_RC (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (0, coordinateVector j)) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by simp)
  show fderiv ℝ (realCf H) x (0, coordinateVector j) = _
  rw [br_realCf_eq H, br_fderiv_RC (fun w => H w.1 w.2) hd x (0, coordinateVector j)]

theorem br_radialT (H : ℝ → Space → Space) (hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2))
    (x : ℝ × Space) :
    radialT (realCf H) x = br_RC (fderiv ℝ (H x.1) x.2 x.2) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by simp)
  have hsl : ∀ j : Fin 3, fderiv ℝ (H x.1) x.2 (coordinateVector j) =
      fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x (0, coordinateVector j) := by
    intro j
    have hs : fderiv ℝ (fun y => H x.1 y) x.2 =
        (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
      UnforcedLeray.B0005.fderiv_slice_space (hd x)
    rw [show fderiv ℝ (H x.1) x.2 = fderiv ℝ (fun y => H x.1 y) x.2 from rfl, hs]
    rfl
  have hv : fderiv ℝ (H x.1) x.2 x.2 = ∑ j : Fin 3, x.2 j • fderiv ℝ (H x.1) x.2 (coordinateVector j) := by
    calc fderiv ℝ (H x.1) x.2 x.2
        = fderiv ℝ (H x.1) x.2 (∑ j : Fin 3, x.2 j • coordinateVector j) := by
          rw [← br_expand x.2]
      _ = ∑ j : Fin 3, x.2 j • fderiv ℝ (H x.1) x.2 (coordinateVector j) := by
          rw [map_sum]
          simp [map_smul]
  unfold radialT
  simp only [br_dy H hH, ← hsl]
  rw [hv, map_sum]
  simp only [map_smul]

theorem br_lapT (H : ℝ → Space → Space) (hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2))
    (x : ℝ × Space) :
    lapT (realCf H) x = br_RC (physLap (H x.1) x.2) := by
  have hd : Differentiable ℝ (fun w : ℝ × Space => H w.1 w.2) := hH.differentiable (by simp)
  have hK : ∀ j : Fin 3, ContDiff ℝ ∞ (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) := fun j =>
    (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hKd : ∀ j : Fin 3, Differentiable ℝ (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) := fun j =>
    (hK j).differentiable (by simp)
  have hlap : lapT (realCf H) x = ∑ j : Fin 3, br_RC (fderiv ℝ (fun w : ℝ × Space =>
      fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w (0, coordinateVector j)) x
        (0, coordinateVector j)) := by
    unfold lapT
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : dy j (realCf H) = fun w => br_RC (fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w
        (0, coordinateVector j)) := funext fun w => br_dy H hH j w
    rw [e]
    unfold dy
    rw [br_fderiv_RC _ (hKd j) x (0, coordinateVector j)]
  rw [hlap, ← map_sum]
  congr 1
  unfold physLap physPd2 physPd
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun y' => fderiv ℝ (H x.1) y' (coordinateVector j)) =
      fun y' => fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y') (0, coordinateVector j) := by
    funext y'
    have hs : fderiv ℝ (fun y => H x.1 y) y' =
        (fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y')).comp
          (ContinuousLinearMap.inr ℝ ℝ Space) :=
      UnforcedLeray.B0005.fderiv_slice_space (hd (x.1, y'))
    rw [show fderiv ℝ (H x.1) y' = fderiv ℝ (fun y => H x.1 y) y' from rfl, hs]
    rfl
  rw [e1]
  have hs2 : fderiv ℝ (fun y' => fderiv ℝ (fun w : ℝ × Space => H w.1 w.2) (x.1, y')
      (0, coordinateVector j)) x.2 =
      (fderiv ℝ (fun w : ℝ × Space => fderiv ℝ (fun w' : ℝ × Space => H w'.1 w'.2) w
        (0, coordinateVector j)) x).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    UnforcedLeray.B0005.fderiv_slice_space ((hKd j) x)
  rw [hs2]
  rfl

theorem ibpBridge_proved : IBPBridge := by
  intro ν μ H hH x
  unfold L0 T0
  rw [br_dtau H hH x, br_radialT H hH x, br_lapT H hH x]
  rw [show realCf H x = br_RC (H x.1 x.2) from rfl,
    show realCf (physDmu ν μ H) x = br_RC (physDmu ν μ H x.1 x.2) from rfl]
  unfold physDmu
  rw [Complex.coe_smul]
  simp only [map_sub, map_add, map_smul]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
