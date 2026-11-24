import UnforcedLeray.Lib.PhaseSpace.Ops
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_2.RealC

/-!
# Pointwise calculus for the far product rule (helper for `ProdHom`)

Pointwise product, component and real-linear-map rules for `∂_{y_j}` (source 2542-2549, 2563-2569).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

/-- Product rule for a `ℂ`-valued scalar times a `ℂ³`-valued field, at a point. -/
theorem dy_cmul_pt (j : Fin 3) (c : ℝ × UnforcedLeray.Space → ℂ)
    (G : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (x : ℝ × UnforcedLeray.Space)
    (hc : DifferentiableAt ℝ c x) (hG : DifferentiableAt ℝ G x) :
    dy j (fun z => c z • G z) x = c x • dy j G x + dy j c x • G x := by
  simp only [dy]
  rw [fderiv_fun_smul hc hG]
  simp

/-- A continuous real-linear map commutes with `∂_{y_j}` at a point of differentiability. -/
theorem dy_clm_pt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (j : Fin 3) (L : E₁ →L[ℝ] E₂)
    (H : ℝ × UnforcedLeray.Space → E₁) (x : ℝ × UnforcedLeray.Space)
    (hH : DifferentiableAt ℝ H x) :
    dy j (fun z => L (H z)) x = L (dy j H x) := by
  simp only [dy]
  have h := (L.hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  rw [show (fun z => L (H z)) = L ∘ H from rfl, h]
  simp

/-- Coordinate `k` of a `ℂ³`-valued field: `∂_j (G·k) = (∂_j G)·k`. -/
theorem dy_apply_k (j k : Fin 3) (G : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (x : ℝ × UnforcedLeray.Space) (hG : DifferentiableAt ℝ G x) :
    dy j (fun z => G z k) x = dy j G x k := by
  let L : UnforcedLeray.PhaseSpace.CVec3 →L[ℝ] ℂ :=
    (EuclideanSpace.proj k : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).restrictScalars ℝ
  have h := dy_clm_pt j L G x hG
  exact h

/-- Coordinate `k` of a `ℂ³`-valued function is differentiable where the function is. -/
theorem diffAt_apply_k (k : Fin 3) (G : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (x : ℝ × UnforcedLeray.Space) (hG : DifferentiableAt ℝ G x) :
    DifferentiableAt ℝ (fun z => G z k) x := by
  let L : UnforcedLeray.PhaseSpace.CVec3 →L[ℝ] ℂ :=
    (EuclideanSpace.proj k : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).restrictScalars ℝ
  exact L.differentiableAt.comp x hG

/-- `realC` commutes with `∂_{y_j}` at a point of differentiability. -/
theorem dy_realC_pt (j : Fin 3) (H : ℝ × UnforcedLeray.Space → UnforcedLeray.Space)
    (x : ℝ × UnforcedLeray.Space) (hH : DifferentiableAt ℝ H x) :
    dy j (fun z => UnforcedLeray.B0412.realC (H z)) x =
      UnforcedLeray.B0412.realC (dy j H x) := by
  have h := dy_clm_pt j realCLI.toContinuousLinearMap H x hH
  exact h

/-- `realC` is norm preserving. -/
theorem norm_realC_eq (v : UnforcedLeray.Space) :
    ‖UnforcedLeray.B0412.realC v‖ = ‖v‖ := by
  have h := realCLI.norm_map v
  exact h

/-- A coordinate of a `ℂ³` vector is bounded by its norm. -/
theorem norm_apply_k_le (v : UnforcedLeray.PhaseSpace.CVec3) (k : Fin 3) : ‖v k‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v k

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
