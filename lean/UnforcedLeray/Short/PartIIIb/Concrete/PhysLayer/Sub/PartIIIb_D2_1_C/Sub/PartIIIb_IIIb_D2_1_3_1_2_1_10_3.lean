import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# `weakCurlDeriv`: the weak curl commutes with the weak `y`-derivative

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
For a phase test `Θ`: `curl(∂ⱼ Θ) = ∂ⱼ(curl Θ)` (symmetry of second derivatives), and the weak
relations `∇ψ`, `∂ⱼΦ`, `curl ψ = Φ` transfer across the commutation. No integrability is needed,
only `HasPtwOp` equalities.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wcdLin (a : CVec3) : CVec3 →ₗ[ℝ] CVec3 where
  toFun := crossC a
  map_add' b c := by
    ext i
    fin_cases i <;> simp [crossC] <;> ring
  map_smul' r b := by
    ext i
    fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

/-- The continuous `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wcdL (a : CVec3) : CVec3 →L[ℝ] CVec3 :=
  { toLinearMap := wcdLin a
    cont := by
      show Continuous (crossC a)
      unfold crossC
      fun_prop }

theorem wcdL_apply (a b : CVec3) : wcdL a b = crossC a b := rfl

/-- Derivative of a composite with a continuous linear map. -/
theorem wcd_dy_clm {L : CVec3 →L[ℝ] CVec3} {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F)
    (j : Fin 3) : dy j (fun p => L (F p)) = fun p => L (dy j F p) := by
  funext p
  have h := ((L.hasFDerivAt).comp p (hF p).hasFDerivAt).fderiv
  simp only [dy]
  rw [show (fun q => L (F q)) = L ∘ F from rfl, h]
  rfl

/-- The curl of a phase test is a phase test. -/
theorem wcd_isPhaseTest_curlT {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (curlT Θ) := by
  have h : curlT Θ = ∑ k : Fin 3, (fun x => wcdL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) := by
    funext x
    simp [curlT, Finset.sum_apply, wcdL_apply]
  rw [h]
  exact IsPhaseTest.sum Finset.univ fun k _ => (hΘ.dy k).clm_comp _

/-- `curl(∂ⱼΘ) = -∂ⱼ(curl Θ)` pointwise on phase tests, i.e. `curl (-∂ⱼΘ) = -∂ⱼ curl Θ`. -/
theorem wcd_curlT_neg_dy {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (j : Fin 3) :
    curlT (-(dy j Θ)) = -(dy j (curlT Θ)) := by
  have hs : ContDiff ℝ ∞ Θ := hΘ.smooth
  have hd : ∀ k : Fin 3, Differentiable ℝ (dy k Θ) := fun k =>
    (hΘ.dy k).smooth.differentiable (by simp)
  have hcurl : curlT Θ = ∑ k : Fin 3, (fun x => wcdL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) := by
    funext x
    simp [curlT, Finset.sum_apply, wcdL_apply]
  have hdy : dy j (curlT Θ) =
      ∑ k : Fin 3, (fun x => wcdL (EuclideanSpace.single k (1 : ℂ)) (dy j (dy k Θ) x)) := by
    rw [hcurl, dy_sum (G := fun k x => wcdL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x))
      Finset.univ (fun k _ => (wcdL _).differentiable.comp (hd k)) j]
    exact Finset.sum_congr rfl fun k _ => wcd_dy_clm (hd k) j
  have hcomm : ∀ k : Fin 3, dy k (dy j Θ) = dy j (dy k Θ) := fun k => dy_dy_comm hs k j
  have hneg' : ∀ k : Fin 3, dy k (-(dy j Θ)) = -(dy j (dy k Θ)) := fun k => by
    rw [dy_neg, hcomm k]
  have hneg : curlT (-(dy j Θ)) =
      ∑ k : Fin 3, (fun x => wcdL (EuclideanSpace.single k (1 : ℂ)) (dy k (-(dy j Θ)) x)) := by
    funext x
    simp [curlT, Finset.sum_apply, wcdL_apply]
  rw [hdy, hneg]
  funext x
  simp [hneg', Finset.sum_apply, map_neg, Finset.sum_neg_distrib]

/-- **WeakCurlDeriv** (source 1334-1337, 1351-1362, 1470-1480): the weak curl commutes with the
weak `y`-derivative. -/
theorem weakCurlDeriv : WeakCurlDeriv := by
  intro P ν μ D hD j Θ hΘ
  have g1 : pairF P (-(dy j (curlT Θ))) D.ψ = pairF P (curlT Θ) (D.Dψ j) :=
    (hD.spΦ.grad j).2 (curlT Θ) (wcd_isPhaseTest_curlT hΘ)
  have g2 : pairF P (curlT (-(dy j Θ))) D.ψ = pairF P (-(dy j Θ)) D.Φ :=
    hD.spΦ.curl (-(dy j Θ)) (hΘ.dy j).neg
  have g3 : pairF P (-(dy j Θ)) D.Φ = pairF P Θ (D.DΦ j) := (hD.dΦ j).2 Θ hΘ
  rw [← g1, ← wcd_curlT_neg_dy hΘ j, g2, g3]

end UnforcedLeray.Short.PartIIIb.Concrete
