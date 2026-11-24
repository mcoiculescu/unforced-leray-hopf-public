import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.Imp

/-!
# Helpers for `wardX0YoungL2_proved` (1): sources, derivatives, rotation

Source of record: `the November 2 reference manuscript` (73 pages),
4171-4174, 3611-3621, 4161-4166.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The real-part map `ℂ³ → ℝ³` (local copy). -/
def w10Re : (Fin 3 → ℂ) →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => (v i).re)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp }

theorem w10Re_apply (v : Fin 3 → ℂ) : w10Re v = WithLp.toLp 2 (fun i => (v i).re) := rfl

theorem w10_X0_eq_re (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    sepX0 ν μ T τ y = w10Re (IIIa.sepW ν (μ : ℂ) T y τ - IIIa.sepW ν ((μ : ℂ) + 1) T y τ) := rfl

/-- Order-zero comparison. -/
theorem w10_norm0 (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    ‖sepX0 ν μ T τ y‖ ≤ ‖w10Re‖ * (‖IIIa.sepW ν (μ : ℂ) T y τ‖ +
      ‖IIIa.sepW ν ((μ : ℂ) + 1) T y τ‖) := by
  rw [w10_X0_eq_re]
  refine (w10Re.le_opNorm _).trans ?_
  gcongr
  exact norm_sub_le _ _

/-- Order-one comparison. -/
theorem w10_norm1 (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y)
    (hB : DifferentiableAt ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ) y) :
    ‖fderiv ℝ (sepX0 ν μ T τ) y‖ ≤ ‖w10Re‖ *
      (‖fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y‖ +
        ‖fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ) y‖) := by
  have hd : HasFDerivAt (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ - IIIa.sepW ν ((μ : ℂ) + 1) T y' τ)
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ) y) y :=
    hA.hasFDerivAt.sub hB.hasFDerivAt
  have h := (w10Re.hasFDerivAt.comp y hd).fderiv
  have e : sepX0 ν μ T τ = w10Re ∘ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ -
      IIIa.sepW ν ((μ : ℂ) + 1) T y' τ) := rfl
  rw [e, h]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)

/-- Rotation equivariance of `X₀` off the source disk. -/
theorem w10_equivM {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hMo : M * M.transpose = 1)
    (hTM : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (τ : ℝ) (y : Space)
    (hy : rOut < ϱ y) :
    sepX0 ν μ T τ (actM M y) = actM M (sepX0 ν μ T τ y) := by
  have hI1 := sepIntegrableOfSource_all ν (μ : ℂ) rOut P T hν (by simpa using hμ) hr hP hT hM τ y hy
  have hI2 := sepIntegrableOfSource_all ν ((μ : ℂ) + 1) rOut P T hν (by simp; linarith) hr hP hT
    hM τ y hy
  have h1 := sepWEquivariance M hMo ν (μ : ℂ) T hTM y τ hI1
  have h2 := sepWEquivariance M hMo ν ((μ : ℂ) + 1) T hTM y τ hI2
  unfold sepX0
  ext i
  simp only [h1, h2]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [← Finset.sum_sub_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_sub]

theorem w10_varrho_act {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (y : Space) :
    ϱ (actM (rotM co si) y) = ϱ y := by
  unfold ϱ
  congr 1
  simp only [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  nlinarith [h]

theorem w10_varrho_meridPt (y : Space) : ϱ (meridPt y) = ϱ y := by
  simp only [ϱ, meridPt]
  simp

theorem w10_cos {y : Space} (h : 0 < ϱ y) : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra hh
    have : ϱ y = 0 := by
      unfold ϱ
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
    linarith
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  field_simp
  rw [hρ2]

theorem w10_mer {y : Space} (h : 0 < ϱ y) :
    actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (meridPt y) = y := by
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra hh
    have : ϱ y = 0 := by
      unfold ϱ
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
    linarith
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  ext i
  fin_cases i <;>
    simp [actM, rotM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp

/-- Derivative transformation under an equivariance on an invariant open set (one direction). -/
theorem w10_fderiv_rot {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hMo : M * M.transpose = 1)
    (hUinv : ∀ z ∈ U, actM M z ∈ U)
    (hd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    (he : ∀ z ∈ U, f (actM M z) = actM M (f z)) {z0 : Space} (hz0 : z0 ∈ U) (v : Space) :
    ‖fderiv ℝ f z0 v‖ ≤ ‖fderiv ℝ f (actM M z0)‖ * ‖v‖ := by
  have hL : HasFDerivAt (f ∘ clmOf M) ((fderiv ℝ f (clmOf M z0)).comp (clmOf M)) z0 :=
    (hd _ (hUinv z0 hz0)).hasFDerivAt.comp z0 (clmOf M).hasFDerivAt
  have hR : HasFDerivAt (clmOf M ∘ f) ((clmOf M).comp (fderiv ℝ f z0)) z0 :=
    (clmOf M).hasFDerivAt.comp z0 (hd z0 hz0).hasFDerivAt
  have hev : (f ∘ clmOf M) =ᶠ[nhds z0] (clmOf M ∘ f) := by
    filter_upwards [hU.mem_nhds hz0] with z hz
    simp only [Function.comp, clmOf_apply]
    exact he z hz
  have huniq := (hR.congr_of_eventuallyEq hev).unique hL
  have h3 := congrArg (fun L : Space →L[ℝ] Space => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, clmOf_apply] at h3
  calc ‖fderiv ℝ f z0 v‖ = ‖actM M (fderiv ℝ f z0 v)‖ := (norm_actM hMo _).symm
    _ = ‖fderiv ℝ f (actM M z0) (actM M v)‖ := by rw [h3]
    _ ≤ ‖fderiv ℝ f (actM M z0)‖ * ‖actM M v‖ := (fderiv ℝ f (actM M z0)).le_opNorm _
    _ = ‖fderiv ℝ f (actM M z0)‖ * ‖v‖ := by rw [norm_actM hMo]

end UnforcedLeray.Short.PartIIIb.Concrete
end
