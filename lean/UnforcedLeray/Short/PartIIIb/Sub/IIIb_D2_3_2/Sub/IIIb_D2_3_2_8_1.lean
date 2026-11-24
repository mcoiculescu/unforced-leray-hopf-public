import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `IBPAdjoint`: `L₀ᵗ` is the transpose of `L₀` against a phase test (source 4268)

For a smooth `P`-periodic `u` and a phase test `Φ`, the Lagrange identity `lagrange_L0` gives
`L₀ᵗΦ·u - Φ·L₀u = srwf_lagRHS`, whose slab integral vanishes: the `τ`-derivative by
`B0005.integral_slab_dτ` and the `y`-derivatives by `srwf_slab_dy` (compact `y`-support).
The `μ`-terms are bilinear and cancel pointwise in the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.IIb

theorem ibpAdjoint_proved : IBPAdjoint := by
  intro P ν μ hP u hu hper Φ hΦ
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by simp)
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  -- the pairing `Φ·u` and its `τ`-derivative
  have hD : ContDiff ℝ ∞ (dotFn Φ u) := srwf_dotFn_contDiff hΦc hu
  have hH : IsPhaseTest P (dotFn Φ u) := srwf_dotFn_isPhaseTest hΦ hu hper
  obtain ⟨R₂, hR₂⟩ := hH.dτ.bounded_support
  have hτint : Integrable (fun z => dτ (dotFn Φ u) z) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hH.dτ.continuous (R := R₂) hR₂
  have hτzero : ∫ z, dτ (dotFn Φ u) z ∂(srwfSlab P) = 0 :=
    UnforcedLeray.B0005.integral_slab_dτ hH
  -- the `y`-derivative terms of `lagrange_L0`
  have hY : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z) (srwfSlab P) ∧
        ∫ z, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) :=
      (Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd)).mul hD
    exact srwf_slab_dy (R := R) hK (fun τ y hy => by simp [dotFn, hR τ y hy]) j
  have hN : ∀ j : Fin 3,
      Integrable (fun z => dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) z)
        (srwfSlab P) ∧
        ∫ z, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) z ∂(srwfSlab P) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) :=
      (srwf_dotFn_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hΦc j) hu).sub
        (srwf_dotFn_contDiff hΦc (UnforcedLeray.PhaseSpace.contDiff_dy hu j))
    exact srwf_slab_dy (R := R) hK
      (fun τ y hy => by simp [dotFn, hR τ y hy, srwf_dy_bdd hR j τ y hy]) j
  have hlag : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z) (u z) - dotL (Φ z) (L0 ν u z) = srwf_lagRHS ν Φ u z :=
    fun z => lagrange_L0 ν hΦc hu z
  have hRHSint : Integrable (srwf_lagRHS ν Φ u) (srwfSlab P) := by
    have i1 : Integrable (fun z => -dτ (dotFn Φ u) z) (srwfSlab P) := hτint.neg
    have i2 : Integrable (fun z => (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z) (srwfSlab P) :=
      (integrable_finsetSum _ fun j _ => (hY j).1).const_mul _
    have i3 : Integrable (fun z => (ν : ℂ) *
        ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) z)
        (srwfSlab P) :=
      (integrable_finsetSum _ fun j _ => (hN j).1).const_mul _
    exact (i1.add i2).sub i3
  have hRHSzero : ∫ z, srwf_lagRHS ν Φ u z ∂(srwfSlab P) = 0 := by
    have i1 : Integrable (fun z => -dτ (dotFn Φ u) z) (srwfSlab P) := hτint.neg
    have i2 : Integrable (fun z => (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z) (srwfSlab P) :=
      (integrable_finsetSum _ fun j _ => (hY j).1).const_mul _
    have i3 : Integrable (fun z => (ν : ℂ) *
        ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) z)
        (srwfSlab P) :=
      (integrable_finsetSum _ fun j _ => (hN j).1).const_mul _
    have i12 : Integrable (fun z => -dτ (dotFn Φ u) z + (1 / 2 : ℂ) *
        ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z) (srwfSlab P) :=
      i1.add i2
    have e : (fun z => srwf_lagRHS ν Φ u z) = fun z =>
        (-dτ (dotFn Φ u) z + (1 / 2 : ℂ) *
          ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) z) -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) z :=
      rfl
    rw [e, integral_sub i12 i3, integral_add i1 i2, integral_neg,
      integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun j _ => (hY j).1,
      integral_finsetSum _ fun j _ => (hN j).1,
      Finset.sum_eq_zero fun j _ => (hY j).2, Finset.sum_eq_zero fun j _ => (hN j).2, hτzero]
    simp
  -- continuity and integrability of `Φ·(L₀u + μu)`
  have hL0c : Continuous (L0 ν u) := by
    have h := (((contDiff_dτ hu).sub ((contDiff_radialT hu).const_smul (1 / 2 : ℝ))).sub
      ((contDiff_lapT hu).const_smul ν)).sub (hu.const_smul (1 / 2 : ℝ))
    exact h.continuous
  have hgc : Continuous (fun z => dotL (Φ z) (L0 ν u z + (μ : ℂ) • u z)) :=
    (dotL.continuous.comp hΦc.continuous).clm_apply
      (hL0c.add (hu.continuous.const_smul (μ : ℂ)))
  have hgint : Integrable (fun z => dotL (Φ z) (L0 ν u z + (μ : ℂ) • u z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P) hgc (R := R)
      (fun t y hy => by simp [hR t y hy])
  -- pointwise: the `μ`-terms cancel and the Lagrange remainder is left over
  have hdiff : ∀ z : ℝ × Space,
      dotL (L0T ν Φ z + (μ : ℂ) • Φ z) (u z) =
        dotL (Φ z) (L0 ν u z + (μ : ℂ) • u z) + srwf_lagRHS ν Φ u z := by
    intro z
    have h := hlag z
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination h
  have hsum : Integrable (fun z => dotL (Φ z) (L0 ν u z + (μ : ℂ) • u z) +
      srwf_lagRHS ν Φ u z) (srwfSlab P) := hgint.add hRHSint
  show phaseInt P (fun x => dotL (L0T ν Φ x + (μ : ℂ) • Φ x) (u x)) =
    phaseInt P (fun x => dotL (Φ x) (L0 ν u x + (μ : ℂ) • u x))
  rw [show (fun x => dotL (L0T ν Φ x + (μ : ℂ) • Φ x) (u x)) =
      fun x => dotL (Φ x) (L0 ν u x + (μ : ℂ) • u x) + srwf_lagRHS ν Φ u x from funext hdiff]
  rw [srwf_phaseInt_eq hsum, srwf_phaseInt_eq hgint, integral_add hgint hRHSint, hRHSzero,
    add_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
