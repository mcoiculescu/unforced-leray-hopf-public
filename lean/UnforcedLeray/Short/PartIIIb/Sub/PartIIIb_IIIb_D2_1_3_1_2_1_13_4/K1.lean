import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13_4

/-!
# `curlMulGen`: weak curl move for a general smooth compactly supported multiplier

Source `the November 2 reference manuscript`
lines 1351-1362 (generalisation of `truncCurlMove` from `χₙ` to any `f`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem curlT_mul_product {P : ℝ} {f : Space → ℝ} (hf : SmF f) {Θ : ℝ × Space → CVec3}
    (hΘ : IsPhaseTest P Θ) :
    curlT (fun x => f x.2 • Θ x) =
      fun x => f x.2 • curlT Θ x + crossC (gradC f x.2) (Θ x) := by
  have ha : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hd : ∀ j : Fin 3, ∀ x : ℝ × Space,
      dy j (fun x => f x.2 • Θ x) x = f x.2 • dy j Θ x + sd j f x.2 • Θ x := by
    intro j x
    have h := dy_mulT ha (hΘ.smooth.differentiable (by simp)) j
    exact congrFun h x
  funext x
  rw [curlT_apply' ((fun x => f x.2 • Θ x)), crossC_gradC_sum', curlT_apply' Θ,
    Finset.smul_sum]
  simp only [hd, map_add, map_smul, Finset.sum_add_distrib]
  rfl

theorem curlMulGen : CurlMulGen := by
  intro P hP ψ' Φ' hcurl hψL hΦL f hf Ψ hΨ
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨hfc, R, hR⟩ := hf
  have hΨc : IsPhaseTest P (fun x => f x.2 • Ψ x) := isPhaseTest_smulF ⟨hfc, R, hR⟩ hΨ
  have hc := hcurl _ hΨc
  have hcurlΨ : IsPhaseTest P (curlT Ψ) := isPhaseTest_curlT hΨ
  have hA : IsPhaseTest P (fun x => f x.2 • curlT Ψ x) := isPhaseTest_smulF ⟨hfc, R, hR⟩ hcurlΨ
  have hB : IsPhaseTest P (fun x => crossC (gradC f x.2) (Ψ x)) :=
    isPhaseTest_crossGrad ⟨hfc, R, hR⟩ hΨ
  have iA := intPT hP hA hψL
  have iB := intPT hP hB hψL
  have iCΦ : Integrable (fun x : ℝ × Space => dotL (Ψ x) (f x.2 • Φ' x))
      (volume.restrict (phaseCell P)) := by
    refine Integrable.congr (intPT hP hΨc hΦL) (ae_of_all _ fun x => ?_)
    exact dotL_real_smul' _ _ _
  have iXΘ : Integrable (fun x : ℝ × Space => dotL (Ψ x) (crossC (gradC f x.2) (ψ' x)))
      (volume.restrict (phaseCell P)) := by
    refine Integrable.congr iB.neg (ae_of_all _ fun x => ?_)
    exact (triple_dotL' _ _ _).symm
  have iSum : Integrable (fun x : ℝ × Space => dotL (Ψ x)
      (f x.2 • Φ' x + crossC (gradC f x.2) (ψ' x))) (volume.restrict (phaseCell P)) := by
    refine Integrable.congr (iCΦ.add iXΘ) (ae_of_all _ fun x => ?_)
    simp [map_add]
  have iAB : Integrable (fun x : ℝ × Space => dotL (f x.2 • curlT Ψ x +
      crossC (gradC f x.2) (Ψ x)) (ψ' x)) (volume.restrict (phaseCell P)) := by
    refine Integrable.congr (iA.add iB) (ae_of_all _ fun x => ?_)
    simp [dotL_apply]
  have e1 : pairF P Ψ (Vf f ψ' Φ') = pairF P Ψ (fun x => f x.2 • Φ' x) +
      pairF P Ψ (fun x => crossC (gradC f x.2) (ψ' x)) :=
    UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable iCΦ iXΘ iSum
  have e2 : pairF P Ψ (fun x => f x.2 • Φ' x) = pairF P (fun x => f x.2 • Ψ x) Φ' := by
    simp only [pairF]
    congr 1
    funext x
    exact (dotL_real_smul' _ _ _).symm
  have e3 : pairF P Ψ (fun x => crossC (gradC f x.2) (ψ' x)) =
      -pairF P (fun x => crossC (gradC f x.2) (Ψ x)) ψ' := by
    simp only [pairF]
    rw [← phaseInt_neg']
    congr 1
    funext x
    exact triple_dotL' _ _ _
  have e5 : pairF P (curlT (fun x => f x.2 • Ψ x)) ψ' =
      pairF P (fun x => f x.2 • curlT Ψ x) ψ' +
        pairF P (fun x => crossC (gradC f x.2) (Ψ x)) ψ' := by
    rw [curlT_mul_product ⟨hfc, R, hR⟩ hΨ]
    exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable iA iB iAB
  rw [e1, e2, e3, ← hc, e5]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
