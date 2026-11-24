import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3

/-!
# `KcGradWeak` (leaf B of `PartIII-b:C/flatset/col/4/3`)

Source of record `the November 2 reference manuscript` 3236-3240, 3426-3430.
The weak cell derivatives of `K_c ξ = kcLp ξ` are the real-part fields `kcGQ ξ` (direction `q`,
index `0`) and `kcGE ξ` (direction `η`, index `1`), by `realBiotSavart_hasWeakDerivs`.  Passing from
the `L²` identity to pointwise representatives uses `kcMer_ae`; the complex identity follows from
the real one by `integral_ofReal`, and integrability from `B0583.integrable_testLp_mul` (real part).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (HasWeakCellDerivC)
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
  (realPartVelocityLp realPartVelocityCLM realPartVelocityCLM_apply coeFn_realPartVelocityLp
    realBiotSavart_hasWeakDerivs HasWeakRealVelDeriv)

/-- Integrability of a test function against the real part of a complex `L²(cell)` velocity. -/
theorem integrable_realPart_mul {c : ℝ} (w : Lp UnforcedLeray.B0581.Vel 2 (B0581.cellVol c))
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (i : Fin 2) :
    Integrable (fun x => φ x * ((realPartVelocityLp w x : UnforcedLeray.Train.Vec)) i)
      (B0581.cellVol c) := by
  refine ((UnforcedLeray.B0583.integrable_testLp_mul c hφ i w).re).congr ?_
  filter_upwards [coeFn_realPartVelocityLp w] with x hx
  rw [hx, realPartVelocityCLM_apply, RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- Complex identity from the real one (`integral_ofReal`). -/
theorem complex_identity_of_real {c : ℝ} (j : Fin 2) (u g φ : B0579.Plane → ℝ)
    (hreal : ∫ x in B0579.cell c, B0579.pd j φ x * u x = -∫ x in B0579.cell c, φ x * g x) :
    ∫ x in B0579.cell c, ((u x : ℝ) : ℂ) * ((B0579.pd j φ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, ((g x : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) := by
  have h1 : ∀ x, ((u x : ℝ) : ℂ) * ((B0579.pd j φ x : ℝ) : ℂ) =
      ((B0579.pd j φ x * u x : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have h2 : ∀ x, ((g x : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) = ((φ x * g x : ℝ) : ℂ) := by
    intro x; push_cast; ring
  simp only [h1, h2, integral_complex_ofReal, hreal, Complex.ofReal_neg]

/-- A weak derivative criterion for real functions, transported to complex pointwise values. -/
theorem hasWeakCellDerivC_of_real {c : ℝ} (j : Fin 2) (u g : B0579.Plane → ℝ)
    (hint : ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
      Integrable (fun x => B0579.pd j ψ x * u x) (volume.restrict (B0579.cell c)) ∧
        Integrable (fun x => ψ x * g x) (volume.restrict (B0579.cell c)))
    (hid : ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, B0579.pd j ψ x * u x = -∫ x in B0579.cell c, ψ x * g x) :
    HasWeakCellDerivC c j (fun x => ((u x : ℝ) : ℂ)) (fun x => ((g x : ℝ) : ℂ)) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => complex_identity_of_real j u g ψ (hid ψ hψ)⟩
  · refine ((hint ψ hψ).1.ofReal).congr (Eventually.of_forall fun x => ?_)
    exact (Complex.ofReal_mul _ _).trans (mul_comm _ _)
  · refine ((hint ψ hψ).2.ofReal).congr (Eventually.of_forall fun x => ?_)
    exact (Complex.ofReal_mul _ _).trans (mul_comm _ _)

/-- Weak derivative in the `q` direction (index `0`). -/
theorem kcGradWeak_dir0 {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m)
    (G1 : ℝ × ℝ → Merid) (hG1 : G1 =ᵐ[volume.restrict (B0579.cell c)] (kcGQ ξ : ℝ × ℝ → Merid))
    (i : Fin 2) :
    HasWeakCellDerivC c 0 (fun x => ((kcMer ξ x i : ℝ) : ℂ)) (fun x => ((G1 x i : ℝ) : ℂ)) := by
  apply hasWeakCellDerivC_of_real 0 (fun x => kcMer ξ x i) (fun x => G1 x i)
  · intro ψ hψ
    constructor
    · have hI := integrable_realPart_mul
        (UnforcedLeray.B0583.velocity c one_le_of_fact (reX ξ.1) (reX_circ ξ)) (hψ.pd 0) i
      refine hI.congr ?_
      filter_upwards [kcMer_ae ξ] with x hx
      exact congrArg (fun t : ℝ => B0579.pd 0 ψ x * t) (congrArg (fun v : Merid => v i) hx).symm
    · have hI := integrable_realPart_mul
        (UnforcedLeray.B0583.velGradQ c one_le_of_fact (reX ξ.1)) hψ i
      refine hI.congr ?_
      filter_upwards [hG1] with x hx
      exact congrArg (fun t : ℝ => ψ x * t) (congrArg (fun v : Merid => v i) hx).symm
  · intro ψ hψ
    show ∫ x in B0579.cell c, B0579.pd 0 ψ x * kcMer ξ x i =
      -∫ x in B0579.cell c, ψ x * G1 x i
    have e1 : (fun x => B0579.pd 0 ψ x * kcMer ξ x i) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => B0579.pd 0 ψ x * (kcLp ξ : ℝ × ℝ → Merid) x i) := by
      filter_upwards [kcMer_ae ξ] with x hx
      exact congrArg (fun v : Merid => B0579.pd 0 ψ x * v i) hx
    have e2 : (fun x => ψ x * G1 x i) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => ψ x * (kcGQ ξ : ℝ × ℝ → Merid) x i) := by
      filter_upwards [hG1] with x hx
      exact congrArg (fun v : Merid => ψ x * v i) hx
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact (realBiotSavart_hasWeakDerivs one_le_of_fact (reX ξ.1) (reX_circ ξ)).1 ψ hψ i

/-- Weak derivative in the `η` direction (index `1`). -/
theorem kcGradWeak_dir1 {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m)
    (G2 : ℝ × ℝ → Merid) (hG2 : G2 =ᵐ[volume.restrict (B0579.cell c)] (kcGE ξ : ℝ × ℝ → Merid))
    (i : Fin 2) :
    HasWeakCellDerivC c 1 (fun x => ((kcMer ξ x i : ℝ) : ℂ)) (fun x => ((G2 x i : ℝ) : ℂ)) := by
  apply hasWeakCellDerivC_of_real 1 (fun x => kcMer ξ x i) (fun x => G2 x i)
  · intro ψ hψ
    constructor
    · have hI := integrable_realPart_mul
        (UnforcedLeray.B0583.velocity c one_le_of_fact (reX ξ.1) (reX_circ ξ)) (hψ.pd 1) i
      refine hI.congr ?_
      filter_upwards [kcMer_ae ξ] with x hx
      exact congrArg (fun t : ℝ => B0579.pd 1 ψ x * t) (congrArg (fun v : Merid => v i) hx).symm
    · have hI := integrable_realPart_mul
        (UnforcedLeray.B0583.velGradEta c one_le_of_fact (reX ξ.1) (reX_circ ξ)) hψ i
      refine hI.congr ?_
      filter_upwards [hG2] with x hx
      exact congrArg (fun t : ℝ => ψ x * t) (congrArg (fun v : Merid => v i) hx).symm
  · intro ψ hψ
    show ∫ x in B0579.cell c, B0579.pd 1 ψ x * kcMer ξ x i =
      -∫ x in B0579.cell c, ψ x * G2 x i
    have e1 : (fun x => B0579.pd 1 ψ x * kcMer ξ x i) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => B0579.pd 1 ψ x * (kcLp ξ : ℝ × ℝ → Merid) x i) := by
      filter_upwards [kcMer_ae ξ] with x hx
      exact congrArg (fun v : Merid => B0579.pd 1 ψ x * v i) hx
    have e2 : (fun x => ψ x * G2 x i) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => ψ x * (kcGE ξ : ℝ × ℝ → Merid) x i) := by
      filter_upwards [hG2] with x hx
      exact congrArg (fun v : Merid => ψ x * v i) hx
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact (realBiotSavart_hasWeakDerivs one_le_of_fact (reX ξ.1) (reX_circ ξ)).2 ψ hψ i

/-- **Leaf B** (source 3236-3240, 3426-3430): the weak cell derivative of `K_cξ` is the pair of
gradient fields, for any pointwise representatives. -/
theorem kcGradWeak : KcGradWeak := by
  intro c m _ _ ξ G1 G2 hG1 hG2 i j
  fin_cases j
  · exact kcGradWeak_dir0 ξ G1 hG1 i
  · exact kcGradWeak_dir1 ξ G2 hG2 i

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
