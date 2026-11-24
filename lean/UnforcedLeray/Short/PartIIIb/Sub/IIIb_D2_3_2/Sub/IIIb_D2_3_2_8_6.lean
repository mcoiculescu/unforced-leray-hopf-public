import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8

/-!
# `IBPCont` (source 4268-4270): continuity of the derived fields `∇q` and `div(a⊗b + b⊗a)`

Both fields are slices of directional derivatives of jointly smooth maps.  The slice identity
`fderiv (fun y ↦ Ψ (τ, y)) y v = fderiv Ψ (τ, y) (0, v)` (`B0005.fderiv_slice_space`) turns them
into the joint `fderiv` in the directions `(0, e_j)`, which is continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Slice identity for a jointly smooth real function. -/
theorem ibpCont_fderiv_slice {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun y' => Ψ (τ, y')) y v = fderiv ℝ Ψ (τ, y) (0, v) := by
  rw [UnforcedLeray.B0005.fderiv_slice_space (hΨ.differentiable (by simp) (τ, y)),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The directional derivative `∂_{e_j}` of a jointly smooth real function, jointly continuous. -/
theorem ibpCont_dir_continuous {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3) :
    Continuous (fun x : ℝ × Space => fderiv ℝ Ψ x (0, coordinateVector j)) :=
  (hΨ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Coordinates of a jointly smooth vector field are jointly smooth. -/
theorem ibpCont_coord_contDiff {V : ℝ × Space → Space} (hV : ContDiff ℝ ∞ V) (k : Fin 3) :
    ContDiff ℝ ∞ (fun x => V x k) :=
  ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff).comp hV

theorem ibpCont_grad_joint {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ ∞ (fun x : ℝ × Space => q x.1 x.2)) (τ : ℝ) (y : Space) :
    physGrad (q τ) y = WithLp.toLp 2 fun j =>
      fderiv ℝ (fun x : ℝ × Space => q x.1 x.2) (τ, y) (0, coordinateVector j) := by
  unfold physGrad
  congr 1
  funext j
  exact ibpCont_fderiv_slice hq τ y (coordinateVector j)

theorem ibpCont_grad (q : ℝ → Space → ℝ)
    (hq : ContDiff ℝ ∞ (fun x : ℝ × Space => q x.1 x.2)) :
    Continuous (realCf (fun τ y => physGrad (q τ) y)) := by
  have hG : Continuous (fun x : ℝ × Space => physGrad (q x.1) x.2) := by
    have heq : (fun x : ℝ × Space => physGrad (q x.1) x.2) =
        fun x => WithLp.toLp 2 (fun j =>
          fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) x (0, coordinateVector j)) := by
      funext x
      exact ibpCont_grad_joint hq x.1 x.2
    rw [heq]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ibpCont_dir_continuous hq j)
  exact contDiff_realC_8.continuous.comp hG

theorem ibpCont_divPsi_contDiff {U W : ℝ → Space → Space}
    (hU : ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2)) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2 j * W x.1 x.2 i + W x.1 x.2 j * U x.1 x.2 i) :=
  ((ibpCont_coord_contDiff hU j).mul (ibpCont_coord_contDiff hW i)).add
    ((ibpCont_coord_contDiff hW j).mul (ibpCont_coord_contDiff hU i))

theorem ibpCont_div_joint {U W : ℝ → Space → Space}
    (hU : ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2)) (τ : ℝ) (y : Space) :
    physDivSym (U τ) (W τ) y = WithLp.toLp 2 fun i => ∑ j : Fin 3,
      fderiv ℝ (fun x : ℝ × Space => U x.1 x.2 j * W x.1 x.2 i + W x.1 x.2 j * U x.1 x.2 i)
        (τ, y) (0, coordinateVector j) := by
  unfold physDivSym
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ibpCont_fderiv_slice (ibpCont_divPsi_contDiff hU hW i j) τ y (coordinateVector j)

theorem ibpCont_div (U W : ℝ → Space → Space)
    (hU : ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2))
    (hW : ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2)) :
    Continuous (realCf (fun τ y => physDivSym (U τ) (W τ) y)) := by
  have hG : Continuous (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) := by
    have heq : (fun x : ℝ × Space => physDivSym (U x.1) (W x.1) x.2) =
        fun x => WithLp.toLp 2 (fun i => ∑ j : Fin 3,
          fderiv ℝ (fun z : ℝ × Space => U z.1 z.2 j * W z.1 z.2 i + W z.1 z.2 j * U z.1 z.2 i)
            x (0, coordinateVector j)) := by
      funext x
      exact ibpCont_div_joint hU hW x.1 x.2
    rw [heq]
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact continuous_finset_sum _ fun j _ => ibpCont_dir_continuous (ibpCont_divPsi_contDiff hU hW i j) j
  exact contDiff_realC_8.continuous.comp hG

theorem ibpCont_proved : IBPCont :=
  ⟨fun q hq => ibpCont_grad q hq, fun U W hU hW => ibpCont_div U W hU hW⟩

end UnforcedLeray.Short.PartIIIb.Concrete
