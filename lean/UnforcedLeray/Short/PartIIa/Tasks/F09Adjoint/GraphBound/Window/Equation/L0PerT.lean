import UnforcedLeray.Lib.PhaseTrace
import UnforcedLeray.Units.B0005.Bridge.Weak
import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.TimeSuppL0

/-!


Analogue of `Units/B0424/Calc.lean` `L0T_perT`, with `T₀ = ∂_τ - ½ y·∇` in place of the
transpose drift `driftT`. The periodization commutation for `∂_τ` and `y·∇` is proved here
in the same way as `driftT_perT` (`Lib/PhaseTrace/Periodize.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseTrace UnforcedLeray.PhaseSpace

theorem l0p_dτ_congr {Φ Ψ : ℝ × Space → CVec3} {p : ℝ × Space} (h : Φ =ᶠ[𝓝 p] Ψ) :
    dτ Φ p = dτ Ψ p := by
  simp only [dτ, h.fderiv_eq]

theorem l0p_radialT_congr {Φ Ψ : ℝ × Space → CVec3} {p : ℝ × Space} (h : Φ =ᶠ[𝓝 p] Ψ) :
    radialT Φ p = radialT Ψ p := by
  simp only [radialT, dy, h.fderiv_eq]

theorem l0p_dτ_sum_shift {G : ℝ × Space → CVec3} (hGs : ContDiff ℝ ∞ G) (s : Finset ℤ) (P : ℝ) :
    dτ (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) =
      fun p => ∑ k ∈ s, dτ G (p.1 + k * P, p.2) := by
  funext p
  have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun p : ℝ × Space => G (p.1 + k * P, p.2)) p :=
    fun k _ => ((contDiff_shift hGs _).differentiable (by simp)).differentiableAt
  simp only [dτ]
  rw [fderiv_fun_sum hdiff, sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [fderiv_shift]

theorem l0p_radialT_sum_shift {G : ℝ × Space → CVec3} (hGs : ContDiff ℝ ∞ G) (s : Finset ℤ)
    (P : ℝ) :
    radialT (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) =
      fun p => ∑ k ∈ s, radialT G (p.1 + k * P, p.2) := by
  funext p
  have h2 : ∀ j : Fin 3, dy j (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) p =
      ∑ k ∈ s, dy j G (p.1 + k * P, p.2) := fun j =>
    congrFun (UnforcedLeray.B0005.dy_sum_shift hGs s P j) p
  simp only [radialT, h2, Finset.smul_sum]
  exact Finset.sum_comm

theorem l0p_timeSupp_dτ {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G) :
    TimeSupp A B (dτ G) :=
  UnforcedLeray.B0005.timeSupp_fderiv_apply hG (1, 0)

theorem l0p_timeSupp_radialT {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G) :
    TimeSupp A B (radialT G) := by
  intro τ y hτ
  simp only [radialT]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [UnforcedLeray.B0005.timeSupp_dy hG j τ y hτ, smul_zero]

/-- `∂_τ` commutes with periodization. -/
theorem l0p_dτ_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → CVec3} {A B : ℝ}
    (hG : TimeSupp A B G) (hGs : ContDiff ℝ ∞ G) : dτ (perT P G) = perT P (dτ G) := by
  funext p₀
  rw [l0p_dτ_congr (perT_eventuallyEq hP hG p₀), l0p_dτ_sum_shift hGs,
    perT_eq_sum (l0p_timeSupp_dτ hG) _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)]

/-- `y·∇` commutes with periodization. -/
theorem l0p_radialT_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → CVec3} {A B : ℝ}
    (hG : TimeSupp A B G) (hGs : ContDiff ℝ ∞ G) :
    radialT (perT P G) = perT P (radialT G) := by
  funext p₀
  rw [l0p_radialT_congr (perT_eventuallyEq hP hG p₀), l0p_radialT_sum_shift hGs,
    perT_eq_sum (l0p_timeSupp_radialT hG) _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)]

/-- **`L₀` commutes with periodization** (`PartII-a:F09/3/1/1/2`). -/
theorem L0_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) (ν : ℝ) :
    UnforcedLeray.B0411.L0 ν (perT P G) = perT P (UnforcedLeray.B0411.L0 ν G) := by
  have hdτ := l0p_dτ_perT hP hG hGs
  have hrad := l0p_radialT_perT hP hG hGs
  have hla := UnforcedLeray.B0005.lapT_perT hP hG hGs
  funext p₀
  have hidx : ∀ {H : ℝ × Space → CVec3}, TimeSupp A B H → perT P H p₀ =
      ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), H (p₀.1 + k * P, p₀.2) := fun hH =>
    perT_eq_sum hH _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)
  have e1 : UnforcedLeray.B0411.L0 ν (perT P G) p₀ =
      dτ (perT P G) p₀ - (1 / 2 : ℝ) • radialT (perT P G) p₀ - ν • lapT (perT P G) p₀
        - (1 / 2 : ℝ) • perT P G p₀ := rfl
  rw [e1, hdτ, hrad, hla, hidx (l0p_timeSupp_dτ hG), hidx (l0p_timeSupp_radialT hG),
    hidx (UnforcedLeray.B0005.timeSupp_lapT hG), hidx hG,
    hidx (timeSupp_L0 hG ν)]
  simp only [UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0, Finset.sum_sub_distrib,
    Finset.smul_sum]

end UnforcedLeray.Short.PartIIa
