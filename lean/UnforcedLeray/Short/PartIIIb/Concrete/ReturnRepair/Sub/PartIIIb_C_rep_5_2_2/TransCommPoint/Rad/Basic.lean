import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Deriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# Basic facts on `X₀ = sepX0` for the transition-commutator (`TransCommPoint`) leaves

Source `the November 2 reference manuscript` 4171-4214, 3604-3647.
Smoothness off the source disk, uniform derivative bounds `|D^jX₀| ≤ K (ϱ - r_o)^{-5/2-j}`,
rotation equivariance about the vertical axis.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `X₀` is `C²` off the source disk. -/
theorem tcb_smooth {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepX0 ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hW : ∀ m : ℂ, -(1 / 4) < m.re →
      ContDiffOn ℝ 2 (fun y => IIIa.sepW ν m T y τ) {y : Space | rOut < ϱ y} := fun m hm =>
    contDiffOn_pi.2 (fun i =>
      sepWSmoothOn_of IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT hM τ i)
  have h1 := hW (μ : ℂ) (by simpa using hμ)
  have h2 := hW ((μ : ℂ) + 1) (by simp; linarith)
  rw [sepX0_eq_reL]
  exact reL.contDiff.comp_contDiffOn (h1.sub h2)

/-- Uniform derivative bounds for `X₀` (`tcd_wD_bound`, transferred through `reL`). -/
theorem tcb_bound (j : ℕ) (hj : j ≤ 2) {ν μ rOut P : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ ≤ K * (ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j) := by
  obtain ⟨C0, hC0, hb⟩ := tcd_wD_bound j
  have hKc := tcKc_ne_top j
  have hMp := tcMph_ne_top hP hM
  refine ⟨‖reL‖ * (2 * C0) * (tcKc j).toReal * (tcMph P T).toReal, by positivity, ?_⟩
  intro τ y hy
  have hD : 0 < ϱ y - rOut := by linarith
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hW : ∀ m : ℂ, -(1 / 4) < m.re →
      ContDiffOn ℝ 2 (fun y => IIIa.sepW ν m T y τ) {y : Space | rOut < ϱ y} := fun m hm =>
    contDiffOn_pi.2 (fun i =>
      sepWSmoothOn_of IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT hM τ i)
  have h1 := hW (μ : ℂ) (by simpa using hμ)
  have h2 := hW ((μ : ℂ) + 1) (by simp; linarith)
  have hle := iteratedFDeriv_reL_le hU h1 h2 hj (show y ∈ {y : Space | rOut < ϱ y} from hy)
  rw [← sepX0_eq_reL ν μ T τ] at hle
  have b1 := hb ν (μ : ℂ) hν (by simpa using hμ) rOut P T hr hP hT hM τ y hy
  have b2 := hb ν ((μ : ℂ) + 1) hν (by simp; linarith) rOut P T hr hP hT hM τ y hy
  unfold IIIa.wDerivNorm at b1 b2
  have hKe : tcKc j = ENNReal.ofReal (tcKc j).toReal := (ENNReal.ofReal_toReal hKc).symm
  have hMe : tcMph P T = ENNReal.ofReal (tcMph P T).toReal := (ENNReal.ofReal_toReal hMp).symm
  set Dp := (ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j) with hDp
  have hDp0 : 0 ≤ Dp := Real.rpow_nonneg hD.le _
  have hBe : ENNReal.ofReal C0 * (ENNReal.ofReal Dp * tcKc j * tcMph P T) =
      ENNReal.ofReal (C0 * Dp * (tcKc j).toReal * (tcMph P T).toReal) := by
    conv_lhs => rw [hKe, hMe]
    rw [← ENNReal.ofReal_mul hDp0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hC0]
    congr 1
    ring
  rw [hBe] at b1 b2
  have hs : ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ ≤
      ENNReal.ofReal (‖reL‖ * (2 * C0) * (tcKc j).toReal * (tcMph P T).toReal * Dp) := by
    refine hle.trans ?_
    have := mul_le_mul' (le_refl (ENNReal.ofReal ‖reL‖)) (add_le_add b1 b2)
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have := (ofReal_norm (iteratedFDeriv ℝ j (sepX0 ν μ T τ) y)).symm ▸ hs
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this


/-! ### Rotation equivariance -/

theorem tcb_cos {y : Space} (h : 0 < ϱ y) : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra hh
    have : ϱ y = 0 := by
      unfold ϱ
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
    linarith
  have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq.le
  field_simp
  rw [hρ2]

theorem tcb_mer {y : Space} (h : 0 < ϱ y) :
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

theorem tcb_varrho_meridPt (y : Space) : ϱ (meridPt y) = ϱ y := by
  simp only [ϱ, meridPt]
  simp

theorem tcb_varrho_act {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (y : Space) :
    ϱ (actM (rotM co si) y) = ϱ y := by
  unfold ϱ
  congr 1
  simp only [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  nlinarith [h]

theorem tcb_varrho_refl (y : Space) : ϱ (actM reflM y) = ϱ y := by
  unfold ϱ
  congr 1
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem tcb_equivM {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
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


theorem tcb_swirl0 {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hA : IsAxiSource T) (τ : ℝ)
    {q : Space} (hq1 : q 1 = 0) (hq : rOut < ϱ q) : sepX0 ν μ T τ q 1 = 0 := by
  have hfix : actM reflM q = q := by
    ext i
    fin_cases i <;> simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hq1]
  have e2 := tcb_equivM hν hμ hr hP hT hM reflM_orth (fun τ z => hA.2 τ z) τ q hq
  rw [hfix] at e2
  have := congrArg (fun w : Space => w 1) e2
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
  linarith

/-- The meridian representation of `X₀`: the frame lift of its trace on `φ = 0`. -/
theorem tcb_rep {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (hA : IsAxiSource T) (τ : ℝ)
    {y : Space} (hy : rOut < ϱ y) :
    sepX0 ν μ T τ y 0 = (y 0 / ϱ y) * sepX0 ν μ T τ (meridPt y) 0 ∧
    sepX0 ν μ T τ y 1 = (y 1 / ϱ y) * sepX0 ν μ T τ (meridPt y) 0 ∧
    sepX0 ν μ T τ y 2 = sepX0 ν μ T τ (meridPt y) 2 := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  have hco := tcb_cos hρ
  have hp : rOut < ϱ (meridPt y) := by rw [tcb_varrho_meridPt]; exact hy
  have hp1 : (meridPt y) 1 = 0 := by simp [meridPt]
  have h1 := tcb_swirl0 hν hμ hr hP hT hM hA τ hp1 hp
  have e1 := tcb_equivM hν hμ hr hP hT hM (rotM_orth hco) (fun τ z => hA.1 _ _ hco τ z) τ
    (meridPt y) hp
  rw [tcb_mer hρ] at e1
  have c0 := congrArg (fun w : Space => w 0) e1
  have c1 := congrArg (fun w : Space => w 1) e1
  have c2 := congrArg (fun w : Space => w 2) e1
  simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] at c0 c1 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [c0]
  · rw [c1]
  · rw [c2]

theorem tcb_noswirl {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) :
    AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T) := by
  intro τ y hy hax
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  obtain ⟨r0, r1, r2⟩ := tcb_rep hν hμ hr hP hT hM hA τ (show _ < ϱ y from hy)
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  ext i
  fin_cases i
  · simp [frameL_apply, eR, hor, r0]; ring
  · simp [frameL_apply, eR, hor, r1]; ring
  · simp [frameL_apply, eR, hor, r2]


/-! ### Divergence-free -/

theorem tcb_diffAt {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) : DifferentiableAt ℝ (sepX0 ν μ T τ) y := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  exact ((tcb_smooth hν hμ hr hP hT hM τ).contDiffAt (hU.mem_nhds hy)).differentiableAt
    (by norm_num)

theorem tcb_div {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space}
    (hy : rOut < ϱ y) : ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y j = 0 := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWd : ∀ m : ℂ, -(1 / 4) < m.re → ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y' => IIIa.sepW ν m T y' τ j) y := fun m hm j =>
    ((sepWSmoothOn_of IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT hM τ j).contDiffAt
      (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hm1 : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have d1 := sepWDivFree_all ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ y hy
  have d2 := sepWDivFree_all ν ((μ : ℂ) + 1) rOut P T hν hm2 hr hP hT hM τ y hy
  have hX := tcb_diffAt hν hμ hr hP hT hM τ hy
  have key : ∀ j : Fin 3, physPd (sepX0 ν μ T τ) j y j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j) y (coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y (coordinateVector j)).re := by
    intro j
    unfold physPd
    rw [fderiv_apply_coord _ _ _ _ hX]
    have hg : DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) y := (hWd _ hm1 j).sub (hWd _ hm2 j)
    have h := (Complex.reCLM.hasFDerivAt.comp y hg.hasFDerivAt).fderiv
    have e : (fun y' => sepX0 ν μ T τ y' j) = fun y' => Complex.reCLM
        (IIIa.sepW ν (μ : ℂ) T y' τ j - IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) := rfl
    rw [e]
    have e2 : (fun y' => Complex.reCLM (IIIa.sepW ν (μ : ℂ) T y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j)) = Complex.reCLM ∘ (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T y' τ j) := rfl
    rw [e2, h, fderiv_fun_sub (hWd _ hm1 j) (hWd _ hm2 j)]
    simp
  simp only [key]
  rw [← Complex.re_sum ] at *
  rw [Finset.sum_sub_distrib, d1, d2]
  simp


/-! ### Power majorants and the decay clause -/

theorem tcb_maj {a r : ℝ} (ha : 0 ≤ a) (har : a < r) (j : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : ℝ, r ≤ ρ →
      ρ * (ρ - a) ^ (-(5 / 2 : ℝ) - j) ≤ c * ρ ^ (-(3 / 2 : ℝ)) := by
  have hr : 0 < r := lt_of_le_of_lt ha har
  set q : ℝ := (r - a) / r with hq
  have hq0 : 0 < q := div_pos (by linarith) hr
  refine ⟨q ^ (-(5 / 2 + (j : ℝ))) * r ^ (-(j : ℝ)), by positivity, ?_⟩
  intro ρ hρr
  have hρ : 0 < ρ := lt_of_lt_of_le hr hρr
  have h1 : q * ρ ≤ ρ - a := by
    rw [hq, div_mul_eq_mul_div, div_le_iff₀ hr]
    nlinarith
  have h2 : (ρ - a) ^ (-(5 / 2 + (j : ℝ))) ≤ (q * ρ) ^ (-(5 / 2 + (j : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith)
  have e1 : -(5 / 2 : ℝ) - j = -(5 / 2 + (j : ℝ)) := by ring
  rw [e1]
  have e3 : ρ * ρ ^ (-(5 / 2 + (j : ℝ))) = ρ ^ (-(3 / 2 : ℝ)) * ρ ^ (-(j : ℝ)) := by
    have h := Real.rpow_add hρ 1 (-(5 / 2 + (j : ℝ)))
    rw [Real.rpow_one] at h
    rw [← h, ← Real.rpow_add hρ]
    congr 1
    ring
  have e2 : ρ * (q * ρ) ^ (-(5 / 2 + (j : ℝ))) =
      q ^ (-(5 / 2 + (j : ℝ))) * (ρ ^ (-(3 / 2 : ℝ)) * ρ ^ (-(j : ℝ))) := by
    rw [Real.mul_rpow hq0.le hρ.le, ← e3]
    ring
  have h3 : ρ ^ (-(j : ℝ)) ≤ r ^ (-(j : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr hρr (by simp)
  calc ρ * (ρ - a) ^ (-(5 / 2 + (j : ℝ))) ≤ ρ * (q * ρ) ^ (-(5 / 2 + (j : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hρ.le
    _ = q ^ (-(5 / 2 + (j : ℝ))) * (ρ ^ (-(3 / 2 : ℝ)) * ρ ^ (-(j : ℝ))) := e2
    _ ≤ q ^ (-(5 / 2 + (j : ℝ))) * (ρ ^ (-(3 / 2 : ℝ)) * r ^ (-(j : ℝ))) := by
        gcongr
    _ = q ^ (-(5 / 2 + (j : ℝ))) * r ^ (-(j : ℝ)) * ρ ^ (-(3 / 2 : ℝ)) := by ring


theorem tcb_varrho_pt {ρ : ℝ} (h : 0 ≤ ρ) (z : ℝ) : ϱ (!₂[ρ, 0, z] : Space) = ρ := by
  have : ϱ (!₂[ρ, 0, z] : Space) = |ρ| := by simp [ϱ, Real.sqrt_sq_eq_abs]
  rw [this, abs_of_nonneg h]

theorem tcb_norm_e3 : ‖(coordinateVector 2 : Space)‖ = 1 := by
  simp [coordinateVector]

theorem tcb_decay {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ : ℝ) :
    StreamDecay ν R (sepX0 ν μ T) τ := by
  have ha : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  set a := R * Real.sqrt (5 * ν / 6) with hadef
  obtain ⟨K0, hK0, hb0⟩ := tcb_bound 0 (by norm_num) hν hμ ha hP hT hM
  obtain ⟨K1, hK1, hb1⟩ := tcb_bound 1 (by norm_num) hν hμ ha hP hT hM
  intro r z hr
  have hr0 : 0 < r := lt_of_le_of_lt ha hr
  obtain ⟨c0, hc0, hm0⟩ := tcb_maj ha hr 0
  obtain ⟨c1, hc1, hm1⟩ := tcb_maj ha hr 1
  set Cc : ℝ := K0 * c0 + K1 * c1 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hB : IntegrableOn (fun ρ : ℝ => Cc * ρ ^ (-(3 / 2 : ℝ))) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul Cc
  have hpt : ∀ ρ : ℝ, r < ρ → ∀ z' : ℝ,
      ‖ρ * sepX0 ν μ T τ !₂[ρ, 0, z'] 2‖ ≤ Cc * ρ ^ (-(3 / 2 : ℝ)) ∧
      ‖ρ * fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤
        Cc * ρ ^ (-(3 / 2 : ℝ)) ∧
      ‖ρ * sepX0 ν μ T τ !₂[ρ, 0, z'] 0‖ ≤ Cc * ρ ^ (-(3 / 2 : ℝ)) := by
    intro ρ hρ z'
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have hq : ϱ (!₂[ρ, 0, z'] : Space) = ρ := tcb_varrho_pt hρ0.le z'
    have hqa : a < ϱ (!₂[ρ, 0, z'] : Space) := by rw [hq]; exact lt_trans hr hρ
    have b0 := hb0 τ _ hqa
    have b1 := hb1 τ _ hqa
    rw [hq, norm_iteratedFDeriv_zero] at b0
    rw [hq, norm_iteratedFDeriv_one] at b1
    have m0 := hm0 ρ hρ.le
    have m1 := hm1 ρ hρ.le
    simp only [Nat.cast_zero, sub_zero] at b0 m0
    have hg0 : ρ * (K0 * (ρ - a) ^ (-(5 / 2 : ℝ))) ≤ K0 * c0 * ρ ^ (-(3 / 2 : ℝ)) := by
      calc ρ * (K0 * (ρ - a) ^ (-(5 / 2 : ℝ))) = K0 * (ρ * (ρ - a) ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ K0 * (c0 * ρ ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (by simpa using m0) hK0
        _ = _ := by ring
    have hg1 : ρ * (K1 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ))) ≤
        K1 * c1 * ρ ^ (-(3 / 2 : ℝ)) := by
      calc ρ * (K1 * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ))) =
            K1 * (ρ * (ρ - a) ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ))) := by ring
        _ ≤ K1 * (c1 * ρ ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left m1 hK1
        _ = _ := by ring
    have hX0 : ρ * ‖sepX0 ν μ T τ !₂[ρ, 0, z']‖ ≤ K0 * c0 * ρ ^ (-(3 / 2 : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left b0 hρ0.le) hg0
    have hX1 : ρ * ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z']‖ ≤ K1 * c1 * ρ ^ (-(3 / 2 : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left b1 hρ0.le) hg1
    have hp : (0 : ℝ) ≤ ρ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hρ0.le _
    have hC0' : 0 ≤ K0 * c0 * ρ ^ (-(3 / 2 : ℝ)) := by positivity
    have hC1' : 0 ≤ K1 * c1 * ρ ^ (-(3 / 2 : ℝ)) := by positivity
    have hsplit : Cc * ρ ^ (-(3 / 2 : ℝ)) =
        K0 * c0 * ρ ^ (-(3 / 2 : ℝ)) + K1 * c1 * ρ ^ (-(3 / 2 : ℝ)) := by rw [hCc]; ring
    have hcomp : ∀ i : Fin 3, ‖ρ * sepX0 ν μ T τ !₂[ρ, 0, z'] i‖ ≤
        K0 * c0 * ρ ^ (-(3 / 2 : ℝ)) := by
      intro i
      rw [norm_mul, Real.norm_of_nonneg hρ0.le]
      exact le_trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ i) hρ0.le) hX0
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (hcomp 2) (by rw [hsplit]; linarith)
    · rw [norm_mul, Real.norm_of_nonneg hρ0.le]
      have : ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖ ≤
          ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z']‖ := by
        calc _ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2)‖ :=
              PiLp.norm_apply_le _ 2
          _ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z']‖ * ‖(coordinateVector 2 : Space)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = _ := by rw [tcb_norm_e3, mul_one]
      calc ρ * ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z'] (coordinateVector 2) 2‖
          ≤ ρ * ‖fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, z']‖ :=
            mul_le_mul_of_nonneg_left this hρ0.le
        _ ≤ _ := by rw [hsplit]; linarith
    · exact le_trans (hcomp 0) (by rw [hsplit]; linarith)
  refine ⟨⟨fun ρ => Cc * ρ ^ (-(3 / 2 : ℝ)), hB, fun ρ hρ z' _ => ?_⟩, ?_⟩
  · exact ⟨(hpt ρ hρ z').1, (hpt ρ hρ z').2.1⟩
  · have hz : Tendsto (fun ρ : ℝ => Cc * ρ ^ (-(3 / 2 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul Cc
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop r] with ρ hρ
    exact (hpt ρ hρ z).2.2


/-! ### The outward primitive: partial derivatives and the differential of `u` -/

/-- The standing hypotheses on the separated source, unpacked from `TCCtx`. -/
structure TCH (ν R μ P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  hν : 0 < ν
  hR : 0 < R
  hμ : -(1 / 4) < μ
  hP : 0 < P
  hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T
  hM : SepMoment P T
  hA : IsAxiSource T

theorem tcb_of_ctx {σ₁ σ₂ ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {y : Space}
    (h : TCCtx σ₁ σ₂ ν μ R P T y) : TCH ν R μ P T := by
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := h
  exact ⟨hν, by linarith, by linarith [hμ.1], hP, hT, hM, hA⟩

theorem tcb_ann_gt {σ₁ σ₂ ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {y : Space}
    (h : TCCtx σ₁ σ₂ ν μ R P T y) : R * Real.sqrt (5 * ν / 6) < ϱ y := by
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := h
  have hR : 0 < R := by linarith
  have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have := mul_lt_mul_of_pos_left h1 hR
  exact lt_of_lt_of_le this hy.1

theorem TCH.ha {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (H : TCH ν R μ P T) :
    0 ≤ R * Real.sqrt (5 * ν / 6) := by
  have := H.hR; have := H.hν; positivity

theorem tcb_smooth' {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) :=
  tcb_smooth H.hν H.hμ H.ha H.hP H.hT H.hM τ

theorem tcb_partials {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) :
    ∀ r z : ℝ, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim (sepX0 ν μ T) τ r' z)
        (r * sepX0 ν μ T τ !₂[r, 0, z] 2) r ∧
      HasDerivAt (fun z' => outPrim (sepX0 ν μ T) τ r z')
        (-(r * sepX0 ν μ T τ !₂[r, 0, z] 0)) z := by
  intro r z hr
  have hdec := tcb_decay H.hν H.hR H.hμ H.hP H.hT H.hM τ
  refine ⟨outPrimDerivR ν R (sepX0 ν μ T) τ (tcb_smooth' H τ) hdec r z hr,
    outPrimDerivZ ν R (sepX0 ν μ T) τ (tcb_smooth' H τ) ?_ (tcb_noswirl H.hν H.hR H.hμ H.hP H.hT H.hM H.hA) hdec r z hr⟩
  intro y hy
  exact tcb_div H.hν H.hμ H.ha H.hP H.hT H.hM τ hy

theorem tcb_u_c2 {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) :
    ContDiffOn ℝ 2 (fun y : Space => outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)) (youngOpen ν R) :=
  t9_outPrim_c2 H.hν H.hR (tcb_smooth' H τ) (tcb_partials H τ)

theorem tcb_u_diff {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    DifferentiableAt ℝ (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y := by
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  exact ((tcb_u_c2 H τ).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)


theorem tcb_hasDeriv_varrho (y v : Space) (hy : 0 < ϱ y) :
    HasDerivAt (fun s : ℝ => ϱ (y + s • v)) ((y 0 * v 0 + y 1 * v 1) / ϱ y) 0 := by
  have h0 : HasDerivAt (fun s : ℝ => y 0 + s * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (y 0)
  have h1 : HasDerivAt (fun s : ℝ => y 1 + s * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (y 1)
  have hQ := (h0.pow 2).add (h1.pow 2)
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra hh
    have : ϱ y = 0 := by
      unfold ϱ
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
    linarith
  have hne : ((fun s : ℝ => (y 0 + s * v 0) ^ 2 + (y 1 + s * v 1) ^ 2) 0) ≠ 0 := by
    simp only [zero_mul, add_zero]
    exact hsq.ne'
  have hs := hQ.sqrt hne
  have e : (fun s : ℝ => ϱ (y + s • v)) =
      fun s => Real.sqrt ((y 0 + s * v 0) ^ 2 + (y 1 + s * v 1) ^ 2) := by
    funext s
    simp [ϱ]
  rw [e]
  have hq : Real.sqrt ((y 0 + 0 * v 0) ^ 2 + (y 1 + 0 * v 1) ^ 2) = ϱ y := by simp [ϱ]
  simp only [Pi.add_apply, Pi.pow_apply, zero_mul, add_zero] at hs hq
  have hs' : HasDerivAt (fun s : ℝ => Real.sqrt ((y 0 + s * v 0) ^ 2 + (y 1 + s * v 1) ^ 2))
      ((↑2 * y 0 ^ (2 - 1) * v 0 + ↑2 * y 1 ^ (2 - 1) * v 1) /
        (2 * Real.sqrt (y 0 ^ 2 + y 1 ^ 2))) 0 := hs
  convert hs' using 1
  rw [show Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = ϱ y from hq]
  field_simp
  simp
  ring

theorem tcb_line {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y)
    (v : Space) :
    HasDerivAt (fun s : ℝ => outPrim (sepX0 ν μ T) τ (ϱ (y + s • v)) ((y + s • v) 2))
      (fderiv ℝ (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y v) 0 := by
  have hd := tcb_u_diff H τ hy
  have hp : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  exact this

theorem tcb_du_h {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y)
    (v : Space) (hv : v 2 = 0) :
    fderiv ℝ (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y v =
      (y 0 * v 0 + y 1 * v 1) * sepX0 ν μ T τ (meridPt y) 2 := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt H.ha hy
  have h1 := tcb_line H τ hy v
  have hdr := (tcb_partials H τ (ϱ y) (y 2) hy).1
  have h2 := hdr.comp_of_eq (0 : ℝ) (tcb_hasDeriv_varrho y v hρ) (by simp)
  have e : (fun s : ℝ => outPrim (sepX0 ν μ T) τ (ϱ (y + s • v)) ((y + s • v) 2)) =
      (fun r' => outPrim (sepX0 ν μ T) τ r' (y 2)) ∘ (fun s : ℝ => ϱ (y + s • v)) := by
    funext s
    simp [hv]
  rw [e] at h1
  rw [h1.unique h2]
  unfold meridPt
  field_simp

theorem tcb_du_v {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    fderiv ℝ (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y (coordinateVector 2) =
      -(ϱ y * sepX0 ν μ T τ (meridPt y) 0) := by
  have h1 := tcb_line H τ hy (coordinateVector 2)
  have hdz := (tcb_partials H τ (ϱ y) (y 2) hy).2
  have h3 : HasDerivAt (fun s : ℝ => y 2 + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 2)
  have h2 := hdz.comp_of_eq (0 : ℝ) h3 (by simp)
  have e : (fun s : ℝ => outPrim (sepX0 ν μ T) τ (ϱ (y + s • coordinateVector 2))
      ((y + s • coordinateVector 2) 2)) =
      (fun z' => outPrim (sepX0 ν μ T) τ (ϱ y) z') ∘ (fun s : ℝ => y 2 + s) := by
    funext s
    have : ϱ (y + s • coordinateVector 2) = ϱ y := by
      simp [ϱ, coordinateVector]
    show outPrim (sepX0 ν μ T) τ (ϱ (y + s • coordinateVector 2))
      ((y + s • coordinateVector 2) 2) = outPrim (sepX0 ν μ T) τ (ϱ y) (y 2 + s)
    rw [this]
    congr 1
    simp [coordinateVector]
  rw [e] at h1
  rw [h1.unique h2]
  unfold meridPt
  ring

theorem tcb_du {ν R μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (H : TCH ν R μ P T) (τ : ℝ) {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y)
    (v : Space) :
    fderiv ℝ (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y v =
      (y 0 * v 0 + y 1 * v 1) * sepX0 ν μ T τ (meridPt y) 2 -
        ϱ y * v 2 * sepX0 ν μ T τ (meridPt y) 0 := by
  have hdec : v = (v 0) • (coordinateVector 0 : Space) + (v 1) • (coordinateVector 1 : Space) +
      (v 2) • (coordinateVector 2 : Space) := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  have a0 := tcb_du_h H τ hy (coordinateVector 0) (by simp [coordinateVector])
  have a1 := tcb_du_h H τ hy (coordinateVector 1) (by simp [coordinateVector])
  have a2 := tcb_du_v H τ hy
  conv_lhs => rw [hdec]
  rw [map_add, map_add, map_smul, map_smul, map_smul, a0, a1, a2]
  simp [coordinateVector]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
