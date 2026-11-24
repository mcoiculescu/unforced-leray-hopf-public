import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Smooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg

/-!
# `X₀ = sepX0` is `C^∞` off the old disk, and its phase derivative is `C^∞`-built from it
(source 3603-3626, 4171-4201)

Source of record: `the November 2 reference manuscript` (73 pages).

For a separated source `T` with finite `Y₂` moment, `X₀ = W_μ - W_{μ+1}` is `C^∞` in `y` on
`ϱ y > r_o` (`sepW_contDiffOn_top`), and by the free equation `D_{μ+1}X₀ = W_μ`
(`ward:shifted-resolvent`, 4198-4201; `tcd_freeEq`)
`∂_τX₀ = Re W_μ + ½ y·∇X₀ + νΔX₀ - (μ + ½)X₀` is differentiable in `y` there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xd_Wre_top {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepWre ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hWa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (μ : ℂ) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ i)
  have : sepWre ν μ T τ = fun z => reL (IIIa.sepW ν (μ : ℂ) T z τ) := rfl
  rw [this]
  exact reL.contDiff.comp_contDiffOn hWa

theorem xd_X0_top {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepX0 ν μ T τ) {y : Space | rOut < ϱ y} := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hWa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (μ : ℂ) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν (μ : ℂ) rOut P T hν hm1 hr hP hT hM τ i)
  have hWb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν ((μ : ℂ) + 1) rOut P T hν hm2 hr hP hT hM τ i)
  rw [sepX0_eq_reL]
  exact reL.contDiff.comp_contDiffOn (hWa.sub hWb)

theorem xd_physPd_top {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (j : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => physPd f j y) U := by
  unfold physPd
  exact (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem xd_physLap_top {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => physLap f y) U := by
  unfold physLap physPd2
  refine ContDiffOn.sum fun j _ => ?_
  exact xd_physPd_top hU (xd_physPd_top hU hf _) j

/-- The phase derivative of `X₀` is differentiable in `y` off the old disk (the free equation
`D_{μ+1}X₀ = W_μ` expresses it through `y`-derivatives of `X₀` of order `≤ 2` and `W_μ`). -/
theorem xd_Zd_diffOn {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) :
    DifferentiableOn ℝ (fun y => deriv (fun t => sepX0 ν μ T t y) τ) {y : Space | rOut < ϱ y} := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hZ := xd_X0_top hν hμ hr hP hT hM τ
  have hW := xd_Wre_top hν hμ hr hP hT hM τ
  have hB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ (sepX0 ν μ T τ) y y)
      {y : Space | rOut < ϱ y} :=
    (hZ.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_id
  have hC := xd_physLap_top hU hZ
  have hall : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => sepWre ν μ T τ y + (1 / 2 : ℝ) • fderiv ℝ (sepX0 ν μ T τ) y y +
        ν • physLap (sepX0 ν μ T τ) y - ((μ + 1) - 1 / 2) • sepX0 ν μ T τ y)
      {y : Space | rOut < ϱ y} :=
    (((hW.add (hB.const_smul _)).add (hC.const_smul _)).sub (hZ.const_smul _))
  refine (hall.differentiableOn (by simp)).congr fun y hy => ?_
  exact tcd_freeEq hν hμ hr hP hT hM τ hy

end UnforcedLeray.Short.PartIIIb.Concrete
