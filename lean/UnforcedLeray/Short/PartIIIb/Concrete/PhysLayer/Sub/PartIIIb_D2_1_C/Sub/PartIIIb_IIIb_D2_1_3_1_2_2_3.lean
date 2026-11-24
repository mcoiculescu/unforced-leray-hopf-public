import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2

/-!
# `MollApproxIdentity`: decomposition

Source `the November 2 reference manuscript` lines 1556-1583 (mollified differences
converge strongly in `Y_2`).  `ρ ⋆ g - g = ∫ ρ(z)(g(· - z) - g) dz`; Minkowski's integral inequality
in the cell `L²` and continuity of translation in `L²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Measurability of `ρ ⋆ g` and Minkowski's integral inequality for the `Y_2` norm
(source 1556-1583): `‖ρ ⋆ g - g‖ ≤ ∫ ρ_norm(z) ‖g(· - z) - g‖ dz`. Proof sketch: `ρ ⋆ g - g(x) =
∫ ρ_norm(z)(g(x-z) - g(x)) dz`; `phaseLpNorm_eq` turns the norm into an `L²(muP P)` lintegral;
apply `MeasureTheory.lintegral_Lp_mul_le`-type / `ENNReal` Minkowski for integrals (or Hölder
against `ρ_norm`), measurability through `StronglyMeasurable.integral_prod_right`. -/
def MollMinkowski : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (g : ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsInYr P 2 g →
      AEStronglyMeasurable (mollP ρ g) volume ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => mollP ρ g x - g x) ≤
        ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x)

/-- Continuity of translation in the cell `L²` norm for `g ∈ Y_2` (source 1556-1583): `P`-periodic
`g` in `L²((0,P] × ℝ³)`; translation by `|z| ≤ 1` is controlled on a slightly larger cell
(density of `C_c` functions in `L²`, `Lp` translation continuity). -/
def PhaseTranslateContinuous : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ × Space, ‖z‖ < δ →
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x) < ENNReal.ofReal ε

theorem mollApproxIdentity_of (h1 : MollMinkowski) (h2 : PhaseTranslateContinuous) :
    MollApproxIdentity := by
  intro P hP g hg ε hε
  have he : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨δ, hδ, hT⟩ := h2 P hP g hg _ he
  refine ⟨δ, hδ, fun ρ hρ => ?_⟩
  obtain ⟨hm, hM⟩ := h1 P hP ρ g hg
  refine ⟨hm, lt_of_le_of_lt hM ?_⟩
  have hnn : ∀ z, 0 ≤ ρ.normed volume z := fun z => ρ.nonneg_normed z
  have h1' : ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - g x) ≤
      ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ENNReal.ofReal (ε / 2) := by
    refine lintegral_mono fun z => ?_
    by_cases hz : ρ.normed volume z = 0
    · simp [hz]
    · have hzs : z ∈ Function.support (ρ.normed volume) := hz
      rw [ρ.support_normed_eq] at hzs
      have : ‖z‖ < δ := by
        have := mem_ball_zero_iff.mp hzs
        linarith
      exact mul_le_mul_right (hT z this).le _
  have h2' : ∫⁻ z, ENNReal.ofReal (ρ.normed volume z) * ENNReal.ofReal (ε / 2) =
      ENNReal.ofReal (ε / 2) := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (ρ.integrable_normed) (Eventually.of_forall hnn),
      ρ.integral_normed]
    simp
  calc _ ≤ _ := h1'
    _ = ENNReal.ofReal (ε / 2) := h2'
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
