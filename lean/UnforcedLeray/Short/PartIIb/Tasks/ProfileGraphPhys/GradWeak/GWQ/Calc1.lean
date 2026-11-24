import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTDeriv.Deriv
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: the radial test fields `(y_j/ϱ) Ψ e_i`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- Real vectors of `ℝ³` seen in `ℂ³`, as a real-linear map. -/
def realCL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

theorem realCL_apply (x : Space) : realCL x = UnforcedLeray.B0412.realC x := rfl

/-- The real frame vector `e_i(y)`. -/
def Evec (i : Fin 2) (y : Space) : Space := Axi.frameL y (EuclideanSpace.single i 1)

theorem frameC_eq (i : Fin 2) (y : Space) : frameC i y = realCL (Evec i y) := rfl

theorem Evec_zero : Evec 0 = Axi.eR := by
  funext y; simp [Evec, Axi.frameL_apply]

theorem Evec_one : Evec 1 = fun _ => Axi.e3 := by
  funext y; simp [Evec, Axi.frameL_apply]

/-- The `j`-th radial test `(y_j/ϱ) Ψ e_i` (real scalar coefficient). -/
def tst (c ε a : ℝ) (φ : Coord → ℝ) (i : Fin 2) (j : Fin 3) : ℝ × Space → CVec3 :=
  fun x => (Axi.eR x.2 j * ctLift c ε a φ x) • realCL (Evec i x.2)

theorem ctLift_vanish {c ε a : ℝ} (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ y, Axi.ϱ y < δ → ctLift c ε a φ (τ, y) = 0 := by
  obtain ⟨a0, Q, ha0, hQ, hsupp⟩ := coord_support_bounds hφ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  refine ⟨ε⁻¹ / (Q + 1), by positivity, fun τ y hy => ?_⟩
  have h := age_out hR ha0 hQ hy
  have hterm : ∀ n : ℤ, termR c ε⁻¹ a φ n (τ, y) = 0 := by
    intro n
    unfold termR
    rw [phi_eq_zero_of_out hsupp h, mul_zero]
  rw [ctLift_eq_tsum]
  simp only [hterm, tsum_zero]

theorem contDiffAt_Evec (i : Fin 2) {y : Space} (hy : y ∉ Axi.axis) :
    ContDiffAt ℝ ∞ (Evec i) y := by
  fin_cases i
  · show ContDiffAt ℝ ∞ (Evec 0) y
    rw [Evec_zero]
    exact Axi.contDiffOn_eR.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)
  · show ContDiffAt ℝ ∞ (Evec 1) y
    rw [Evec_one]
    exact contDiffAt_const

theorem tst_contDiff {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) (j : Fin 3) : ContDiff ℝ ∞ (tst c ε a φ i j) := by
  obtain ⟨δ, hδ, hvan⟩ := ctLift_vanish (c := c) (a := a) hε hφ
  rw [contDiff_iff_contDiffAt]
  rintro ⟨τ, y⟩
  by_cases hy : Axi.ϱ y < δ
  · have hopen : IsOpen {x : ℝ × Space | Axi.ϱ x.2 < δ} :=
      isOpen_lt (Axi.continuous_ϱ.comp continuous_snd) continuous_const
    have hz : tst c ε a φ i j =ᶠ[𝓝 (τ, y)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hy] with x hx
      simp [tst, hvan x.1 x.2 hx]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · have hax : y ∉ Axi.axis := fun h => hy (by rw [(Axi.mem_axis_iff y).1 h]; exact hδ)
    have hΨ : ContDiffAt ℝ ∞ (ctLift c ε a φ) (τ, y) :=
      (ctLift_contDiff hc hε hφ).contDiffAt
    have hA : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.eR x.2 j) (τ, y) :=
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt).comp (τ, y)
        ((Axi.contDiffOn_eR.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hax)).comp (τ, y)
          contDiffAt_snd)
    have hEv : ContDiffAt ℝ ∞ (Evec i) ((τ, y).2) := contDiffAt_Evec i hax
    have hE : ContDiffAt ℝ ∞ (fun x : ℝ × Space => realCL (Evec i x.2)) (τ, y) :=
      (realCL.contDiff.contDiffAt).comp (τ, y) (hEv.comp (τ, y) contDiffAt_snd)
    exact (hA.mul hΨ).smul hE

theorem tst_isPhaseTest {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) (i : Fin 2) (j : Fin 3) :
    IsPhaseTest (2 * ε * c) (tst c ε a φ i j) := by
  refine ⟨tst_contDiff hc hε hφ i j, fun τ y => ?_, ?_⟩
  · have h := ctLift_periodic c ε a hε φ (τ, y)
    simp only [tst]
    rw [h]
  · obtain ⟨Rb, hRb⟩ := ctLift_bounded (c := c) (a := a) hε hφ
    exact ⟨Rb, fun τ y hy => by simp [tst, hRb τ y hy]⟩

end UnforcedLeray.Short.IIb.GWQ
