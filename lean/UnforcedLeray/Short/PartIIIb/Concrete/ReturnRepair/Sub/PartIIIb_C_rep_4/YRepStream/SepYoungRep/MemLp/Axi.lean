import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Meas

/-!
# Helper (MemLp folder): axisymmetry and periodicity of the young cut of `sepWre`

For a separated source `T` with `IsAxiSource T`, `sepWre ν μ T` is equivariant under the rotations
about the vertical axis and the reflection `φ ↦ -φ` wherever its `sepW` integrand is integrable.
The young cut `sepYoungCut` (the field of `sepWreYoungL2`) keeps only receivers with
`R√ν ≤ ϱ`, which lie outside the source disk `ϱ ≤ R√(5ν/6)`, so the integrability holds there
(`sepIntegrableOfSource_all`) and the cut is `AxiNoSwirl` at every point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepWre_equivariant (hS : SepWEquivariance) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M * M.transpose = 1) (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (hT : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (y : Space)
    (hI : SepIntegrableAt ν (μ : ℂ) T y τ) :
    sepWre ν μ T τ (actM M y) = actM M (sepWre ν μ T τ y) := by
  have h1 := hS M hM ν (μ : ℂ) T hT y τ hI
  unfold sepWre
  ext i
  simp only [h1]
  simp only [actM, Matrix.mulVec, dotProduct, PiLp.toLp_apply, WithLp.ofLp_toLp]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

/-- Frame form of `sepWre` at an off-axis point, from the integrability at the trace point. -/
theorem sepWre_frame (hS : SepWEquivariance) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IsAxiSource T) (ν μ : ℝ) (τ : ℝ) (y : Space) (hy : y ∉ axis)
    (hI : SepIntegrableAt ν (μ : ℂ) T (meridPt y) τ) :
    sepWre ν μ T τ y = frameL y !₂[sepWre ν μ T τ (meridPt y) 0, sepWre ν μ T τ (meridPt y) 2] := by
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra h
    apply hy
    have h0 : y 0 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h0, pow_eq_zero_iff (two_ne_zero) |>.1 h1⟩
  have hρ : 0 < ϱ y := Real.sqrt_pos.2 hsq
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  have hco : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
    field_simp
    rw [hρ2]
  have hmer : actM (rotM (y 0 / ϱ y) (y 1 / ϱ y)) (meridPt y) = y := by
    ext i
    fin_cases i <;>
      simp [actM, rotM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      field_simp
  have hfix : actM reflM (meridPt y) = meridPt y := by
    ext i
    fin_cases i <;> simp [actM, reflM, meridPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 := sepWre_equivariant hS _ (rotM_orth hco) ν μ T τ
    (fun τ' z => hT.1 _ _ hco τ' z) (meridPt y) hI
  have e2 := sepWre_equivariant hS _ reflM_orth ν μ T τ (fun τ' z => hT.2 τ' z) (meridPt y) hI
  rw [hmer] at e1
  rw [hfix] at e2
  have h1 : sepWre ν μ T τ (meridPt y) 1 = 0 := by
    have := congrArg (fun w : Space => w 1) e2
    simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    linarith
  rw [e1]
  ext i
  fin_cases i <;>
    simp [actM, rotM, frameL_apply, eR, hor, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] <;>
    field_simp

/-- The young cut of `sepWre` (the field of `sepWreYoungL2`): `sepWre` where `R√ν ≤ ϱ`, else `0`. -/
def sepYoungCut (R ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    Space :=
  if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then sepWre ν μ T τ y else 0

theorem sepWre_periodic (ν μ P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hP : ∀ τ z, T (τ + P) z = T τ z) (τ : ℝ) (y : Space) :
    sepWre ν μ T (τ + P) y = sepWre ν μ T τ y := by
  have key : ∀ l : ℝ, ∀ z : Space,
      T (τ + P + 2 * Real.log l) z = T (τ + 2 * Real.log l) z := fun l z => by
    rw [show τ + P + 2 * Real.log l = (τ + 2 * Real.log l) + P by ring]
    exact hP _ _
  unfold sepWre IIIa.sepW
  simp only [key]

theorem sepYoungCut_periodic (R ν μ P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hP : ∀ τ z, T (τ + P) z = T τ z) (τ : ℝ) (y : Space) :
    sepYoungCut R ν μ T (τ + P) y = sepYoungCut R ν μ T τ y := by
  unfold sepYoungCut
  rw [sepWre_periodic ν μ P T hP]

theorem sepYoungCut_measurable (R ν μ : ℝ) (hν : 0 < ν)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) :
    Measurable (fun q : ℝ × Space => sepYoungCut R ν μ T q.1 q.2) := by
  unfold sepYoungCut
  refine Measurable.ite ?_ (sepWre_measurable ν μ hν T hT) measurable_const
  have h0 : Measurable (fun q : ℝ × Space => q.2 0) :=
    (EuclideanSpace.proj (0 : Fin 3)).continuous.measurable.comp measurable_snd
  have h1 : Measurable (fun q : ℝ × Space => q.2 1) :=
    (EuclideanSpace.proj (1 : Fin 3)).continuous.measurable.comp measurable_snd
  exact measurableSet_le measurable_const
    (Real.continuous_sqrt.measurable.comp ((h0.pow_const 2).add (h1.pow_const 2)))

theorem sepYoungCut_axi (R ν μ P : ℝ) (hR : 0 < R) (hν : 0 < ν) (hμ : -(1 / 4) < μ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hP : 0 < P)
    (hS : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hEq : SepWEquivariance) (hAx : IsAxiSource T) :
    AxiNoSwirl (sepYoungCut R ν μ T) := by
  intro τ y _ hy
  have hm0 : ∀ y : Space, meridPt y 0 = ϱ y := fun y => by simp [meridPt]
  have hm1 : ∀ y : Space, meridPt y 1 = 0 := fun y => by simp [meridPt]
  have hϱm : ∀ y : Space, ϱ (meridPt y) = ϱ y := fun y => by
    show Real.sqrt (meridPt y 0 ^ 2 + meridPt y 1 ^ 2) = ϱ y
    rw [hm0, hm1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  have hcond : ∀ y : Space, R * Real.sqrt ν ≤ Real.sqrt (meridPt y 0 ^ 2 + meridPt y 1 ^ 2) ↔
      R * Real.sqrt ν ≤ ϱ y := fun y => by
    rw [show Real.sqrt (meridPt y 0 ^ 2 + meridPt y 1 ^ 2) = ϱ y from hϱm y]
  by_cases hc : R * Real.sqrt ν ≤ ϱ y
  · have hcm : R * Real.sqrt ν ≤ Real.sqrt (meridPt y 0 ^ 2 + meridPt y 1 ^ 2) :=
      (hcond y).2 hc
    have hlt : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
      rw [hϱm y]
      have : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
      nlinarith
    have hI : SepIntegrableAt ν (μ : ℂ) T (meridPt y) τ :=
      sepIntegrableOfSource_all ν (μ : ℂ) (R * Real.sqrt (5 * ν / 6)) P T hν
        (by simpa using hμ) (by positivity) hP hS hM τ (meridPt y) hlt
    unfold sepYoungCut
    rw [if_pos (show R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) from hc)]
    simp only [if_pos hcm]
    exact sepWre_frame hEq T hAx ν μ τ y hy hI
  · have hcm : ¬ R * Real.sqrt ν ≤ Real.sqrt (meridPt y 0 ^ 2 + meridPt y 1 ^ 2) :=
      fun h => hc ((hcond y).1 h)
    have h00 : (!₂[(0 : ℝ), 0] : Merid) = 0 := by
      ext i; fin_cases i <;> rfl
    unfold sepYoungCut
    rw [if_neg (show ¬ R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) from hc)]
    simp only [if_neg hcm, PiLp.zero_apply, h00, map_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
end
