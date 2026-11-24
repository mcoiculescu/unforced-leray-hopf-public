import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.FrozenTransportContHelp

open PartIIbF23Sub

theorem frozenOmega_eq (σ : ℝ) (x : B0579.Plane) :
    frozenOmega σ x = ((1 + σ) ^ 2)⁻¹ *
      Real.exp (-(((x.1 / Real.sqrt (1 + σ)) ^ 2 + (x.2 / Real.sqrt (1 + σ)) ^ 2) / 4)) := by
  have h : ‖ofPlane (scalePlane (1 + σ) x)‖ ^ 2 =
      (x.1 / Real.sqrt (1 + σ)) ^ 2 + (x.2 / Real.sqrt (1 + σ)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [ofPlane, scalePlane, sq]
  unfold frozenOmega
  show _ * Real.exp (-(‖ofPlane (scalePlane (1 + σ) x)‖ ^ 2 / 4)) = _
  rw [h]

theorem frozenOmega_congr (σ : ℝ) (hσ : 0 ≤ 1 + σ) (x y : B0579.Plane)
    (h : x.1 ^ 2 + x.2 ^ 2 = y.1 ^ 2 + y.2 ^ 2) : frozenOmega σ x = frozenOmega σ y := by
  rw [frozenOmega_eq, frozenOmega_eq]
  have hs : Real.sqrt (1 + σ) ^ 2 = 1 + σ := Real.sq_sqrt hσ
  have : (x.1 / Real.sqrt (1 + σ)) ^ 2 + (x.2 / Real.sqrt (1 + σ)) ^ 2 =
      (y.1 / Real.sqrt (1 + σ)) ^ 2 + (y.2 / Real.sqrt (1 + σ)) ^ 2 := by
    rw [div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div, h]
  rw [this]

theorem contDiff_frozenOmega (σ : ℝ) : ContDiff ℝ ∞ (frozenOmega σ) := by
  have : frozenOmega σ = fun x : B0579.Plane => ((1 + σ) ^ 2)⁻¹ *
      Real.exp (-(((x.1 / Real.sqrt (1 + σ)) ^ 2 + (x.2 / Real.sqrt (1 + σ)) ^ 2) / 4)) :=
    funext (frozenOmega_eq σ)
  rw [this]
  fun_prop

theorem contDiff_flow (σ τ : ℝ) : ContDiff ℝ ∞ (frozenRadialFlow σ τ) := by
  have h := contDiff_frozenOmega σ
  unfold frozenRadialFlow
  simp only
  fun_prop

theorem flow_sq (σ τ : ℝ) (x : B0579.Plane) :
    (frozenRadialFlow σ τ x).1 ^ 2 + (frozenRadialFlow σ τ x).2 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  unfold frozenRadialFlow
  simp only
  nlinarith [Real.sin_sq_add_cos_sq (-τ * frozenOmega σ x)]

theorem flow_add (σ : ℝ) (hσ : 0 ≤ 1 + σ) (τ τ' : ℝ) (x : B0579.Plane) :
    frozenRadialFlow σ τ (frozenRadialFlow σ τ' x) = frozenRadialFlow σ (τ + τ') x := by
  have hω : frozenOmega σ (frozenRadialFlow σ τ' x) = frozenOmega σ x :=
    frozenOmega_congr σ hσ _ _ (flow_sq σ τ' x)
  unfold frozenRadialFlow at hω ⊢
  simp only at hω ⊢
  rw [hω]
  have e1 : -τ * frozenOmega σ x + -τ' * frozenOmega σ x = -(τ + τ') * frozenOmega σ x := by ring
  have c := Real.cos_add (-τ * frozenOmega σ x) (-τ' * frozenOmega σ x)
  have s := Real.sin_add (-τ * frozenOmega σ x) (-τ' * frozenOmega σ x)
  rw [e1] at c s
  ext
  · simp only; rw [c, s]; ring
  · simp only; rw [c, s]; ring

theorem flow_zero (σ : ℝ) (x : B0579.Plane) : frozenRadialFlow σ 0 x = x := by
  unfold frozenRadialFlow; simp

end UnforcedLeray.Short.IIb.FrozenTransportContHelp
