import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimY

/-!
# Joint derivative of the scalar kernel and the `h`-direction bound
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem pdLam_hasDerivAt (h : ℝ) : HasDerivAt pdLam (-(pdLam h) / 2) h := by
  have := (((hasDerivAt_id h).div_const 2).neg).exp
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)
  simp [pdLam]; ring

/-- The joint scalar kernel `(h, x) ↦ (xKer ν μ h x M)₂`. -/
def Jt (ν μ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × Space) : ℝ := xKerA ν μ p.1 M p.2

theorem Jt_contDiffOn (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiffOn ℝ 2 (Jt ν μ M) {p : ℝ × Space | 0 < p.1} :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn (xKer_jointC2 ν μ hν M)

theorem Jt_diffAt (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (x : Space) : DifferentiableAt ℝ (Jt ν μ M) (h, x) :=
  ((Jt_contDiffOn ν μ hν M).differentiableOn (by norm_num) (h, x) hh).differentiableAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hh)

theorem Jt_dir (ν μ : ℝ) (hν : 0 < ν) (M : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ} (hh : 0 < h)
    (x v : Space) :
    fderiv ℝ (Jt ν μ M) (h, x) (1, v) = deriv (fun h' => xKerA ν μ h' M x) h +
      fderiv ℝ (fun x' => xKerA ν μ h M x') x v := by
  have hJ := (Jt_diffAt ν μ hν M hh x).hasFDerivAt
  have h1 : HasDerivAt (fun h' => xKerA ν μ h' M x) (fderiv ℝ (Jt ν μ M) (h, x) (1, 0)) h := by
    have := hJ.comp_hasDerivAt h ((hasDerivAt_id h).prodMk (hasDerivAt_const h x))
    simpa [Jt, Function.comp_def] using this
  have h2 : HasFDerivAt (fun x' => xKerA ν μ h M x')
      ((fderiv ℝ (Jt ν μ M) (h, x)).comp (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ Space))) x :=
    hJ.comp x ((hasFDerivAt_const h x).prodMk (hasFDerivAt_id x))
  rw [h1.deriv, h2.fderiv]
  have : ((1 : ℝ), v) = ((1 : ℝ), (0 : Space)) + ((0 : ℝ), v) := by simp
  rw [this, map_add]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
