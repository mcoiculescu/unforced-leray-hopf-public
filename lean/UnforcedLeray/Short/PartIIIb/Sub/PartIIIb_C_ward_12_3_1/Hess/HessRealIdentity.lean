import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.HessTransfer
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation

/-!
# Real-test identity for the window Hessian (source 1426-1436)

Task `PartIII-b:C/ward/12/3/1/2/2/3`.  Hessian analogue of `UnforcedLeray.Short.PartIIa.WinBack.real_identity`
for a single weak second derivative `D2 c j k` (no sum over the diagonal).  The left transfer is
`integral_windowField_sD2_t` (`HessTransfer`), the right transfer is `WinBack.integral_D_lapTest_t`,
and the pointwise identity is `WinBack.windowLap_shift_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

/-- Integrability of the transported side for a real test (one component `D c`). -/
theorem hsRI_integrable {r : ℝ≥0∞} [Fact (1 ≤ r)] (τ₀ ν : ℝ) (c : Fin 3)
    (D : Fin 3 → PS 3 → ℂ) (hmem : MemLp (D c) r volume)
    {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p : ℝ × Space => windowLap ν τ₀ D p c * ((a p : ℝ) : ℂ)) := by
  have hφ : IsSTTest (UnforcedLeray.B0424.lapTest τ₀ a : PS 3 → ℝ) :=
    UnforcedLeray.B0424.isSTTest_lapTest ha hsup
  have hf : Integrable (fun X => D c X * ((UnforcedLeray.B0424.lapTest τ₀ a X : ℝ) : ℂ)) :=
    UnforcedLeray.Short.PartIIa.WinBack.integrable_of_memLp_mul hmem
      (Complex.continuous_ofReal.comp hφ.continuous) (hφ.2.comp_left Complex.ofReal_zero)
  have hk2 := (UnforcedLeray.B0424.integrable_expChart_iff _).1 hf.integrableOn
  have hk2' : Integrable (fun p : ℝ × Space => D c (Real.exp p.1, p.2) *
      ((a (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ)) := by
    refine hk2.congr (Filter.Eventually.of_forall fun p => ?_)
    have he : ((Real.exp p.1 : ℝ) : ℂ) * ((Real.exp (-p.1) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    simp only [UnforcedLeray.B0424.expChart,
      UnforcedLeray.Short.PartIIa.WinBack.lapTest_expChart, Complex.real_smul,
      Complex.ofReal_mul]
    linear_combination (D c (Real.exp p.1, p.2) *
      ((a (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ)) * he
  have hk3 := (UnforcedLeray.B0424.integrable_dilChart_iff _).1 hk2'
  have hk4 : Integrable (fun p : ℝ × Space => Real.exp (3 * p.1 / 2) •
      (D c (Real.exp p.1, Real.exp (p.1 / 2) • p.2) * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ))) := by
    refine hk3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [UnforcedLeray.B0424.dilChart,
      UnforcedLeray.Short.PartIIa.WinBack.expNeg_smul_expPos]
  have hk5 := (hk4.const_mul (ν : ℂ)).congr
    (Filter.Eventually.of_forall fun p =>
      (UnforcedLeray.Short.PartIIa.WinBack.windowLap_shift_eq (D := D) hsup c p).symm)
  exact (UnforcedLeray.B0424.integrable_shift_iff τ₀
    (fun p : ℝ × Space => windowLap ν τ₀ D p c * ((a p : ℝ) : ℂ))).1 hk5

/-- **Real-test identity for the window Hessian** (source 1426-1436): for a real smooth
compactly supported test `a` in the window, the component `c` of the cutoff pull-back `W` pairs
with `ν sD2 j k a` exactly as the transported field `windowLap` of `D2 c j k` pairs with `a`,
and the transported side is integrable. -/
theorem hess_real_identity {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {P : ℝ} [Fact (0 < P)] {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ ν : ℝ)
    (c j k : Fin 3) (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ)
    (hD2 : MemLp (D2 c j k) r volume ∧ UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3)
      (windowField χ τ₀ W c) j k (D2 c j k))
    {a : PS 3 → ℝ} (ha : IsSTTest a)
    (hsup : tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p : ℝ × Space => windowLap ν τ₀ (fun c X => D2 c j k X) p c *
      ((a p : ℝ) : ℂ)) ∧
    ∫ p : ℝ × Space, W p c * ((ν * sD2 j k a p : ℝ) : ℂ) =
      ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => D2 c j k X) p c * ((a p : ℝ) : ℂ) := by
  have hφ : IsSTTest (UnforcedLeray.B0424.lapTest τ₀ a : PS 3 → ℝ) :=
    UnforcedLeray.B0424.isSTTest_lapTest ha hsup
  have hsum : ∫ X, windowField χ τ₀ W c X *
      ((sD2 j k (UnforcedLeray.B0424.lapTest τ₀ a) X : ℝ) : ℂ) =
      ∫ X, D2 c j k X * ((UnforcedLeray.B0424.lapTest τ₀ a X : ℝ) : ℂ) :=
    hD2.2 _ hφ
  have hL := integral_windowField_sD2_t χ hχ τ₀ W c ha hsup j k
  have hR := UnforcedLeray.Short.PartIIa.WinBack.integral_D_lapTest_t τ₀ (D2 c j k) ha hsup
  have hkey : ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sD2 j k a (τ₀ + p.1, p.2) : ℝ) : ℂ) =
      ∫ p : ℝ × Space, Real.exp (3 * p.1 / 2) •
        (D2 c j k (Real.exp p.1, Real.exp (p.1 / 2) • p.2) * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ)) :=
    hL.symm.trans (hsum.trans hR)
  have hshift1 : ∫ p : ℝ × Space, W p c * ((ν * sD2 j k a p : ℝ) : ℂ) =
      (ν : ℂ) * ∫ p : ℝ × Space, W p c * ((sD2 j k a p : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hshift2 : ∫ p : ℝ × Space, W p c * ((sD2 j k a p : ℝ) : ℂ) =
      ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sD2 j k a (τ₀ + p.1, p.2) : ℝ) : ℂ) :=
    (UnforcedLeray.B0424.integral_shift τ₀ (fun p => W p c * ((sD2 j k a p : ℝ) : ℂ))).symm
  have hshift3 : ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => D2 c j k X) p c *
      ((a p : ℝ) : ℂ) = ∫ p : ℝ × Space, windowLap ν τ₀ (fun c X => D2 c j k X)
        (τ₀ + p.1, p.2) c * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ) :=
    (UnforcedLeray.B0424.integral_shift τ₀ (fun p => windowLap ν τ₀
      (fun c X => D2 c j k X) p c * ((a p : ℝ) : ℂ))).symm
  have hpt : ∀ p : ℝ × Space, windowLap ν τ₀ (fun c X => D2 c j k X) (τ₀ + p.1, p.2) c *
      ((a (τ₀ + p.1, p.2) : ℝ) : ℂ) = (ν : ℂ) * (Real.exp (3 * p.1 / 2) •
        (D2 c j k (Real.exp p.1, Real.exp (p.1 / 2) • p.2) * ((a (τ₀ + p.1, p.2) : ℝ) : ℂ))) :=
    fun p => UnforcedLeray.Short.PartIIa.WinBack.windowLap_shift_eq hsup c p
  refine ⟨hsRI_integrable τ₀ ν c (fun c X => D2 c j k X) hD2.1 ha hsup, ?_⟩
  rw [hshift1, hshift2, hkey, hshift3, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_const_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
