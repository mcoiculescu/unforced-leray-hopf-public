import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

namespace AdjRemFormAux

theorem pairF_csmul_right (P : ℝ) (X u : ℝ × Space → CVec3) (c : ℂ) :
    pairF P X (fun x => c • u x) = c * pairF P X u := by
  unfold pairF phaseInt
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem pair_sub_right {P : ℝ} (X Y Z : ℝ × Space → CVec3)
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x - Z x) = pairF P X Y - pairF P X Z := by
  have hYZ : Integrable (fun z => dotL (X z) (Y z - Z z)) (muP P) :=
    (hY.sub hZ).congr (ae_of_all _ fun z => by simp [map_sub])
  rw [pair_eq_integral P X _ hYZ, pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [integral_sub hY hZ, smul_sub]

theorem int_sub_aux {P : ℝ} {Θ Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (Θ z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (Θ z) (Z z)) (muP P)) :
    Integrable (fun z => dotL (Θ z) ((fun x => Y x - Z x) z)) (muP P) :=
  (hY.sub hZ).congr (ae_of_all _ fun z => by simp [map_sub])

end AdjRemFormAux

open AdjRemFormAux in
/-- The adjoint remainder formula, with the membership `a, b ∈ Y_2` supplied (the
hypotheses that the second-slot pairing split needs). -/
theorem adjRemainderFormula_of_mem (P ν μ : ℝ) (hP : 0 < P)
    (Φ g a b : ℝ × Space → CVec3) (hdom : FWUAdjDom P ν μ Φ g)
    (ha_mem : UnforcedLeray.Short.IIb.IsInYr P 2 a) (hb_mem : UnforcedLeray.Short.IIb.IsInYr P 2 b)
    (ha : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a)
    (hb : UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b)
    (Θ : ℝ × Space → CVec3) (hΘ : IsPhaseTest P Θ) :
    pairF P (fun x => L0 ν Θ x + (μ : ℂ) • Θ x) Φ - pairF P Θ g
      = pairF P Θ (remH μ Φ g a b) := by
  have hΦ : LocL2 P Φ := Or.inl hdom.mem
  have hg : LocL2 P g := Or.inl hdom.mem_g
  have hfun : (fun x => L0 ν Θ x + (μ : ℂ) • Θ x)
      = (-(driftT Θ) + -(nuLapT ν Θ)) + ((1 + μ : ℝ) • Θ) := by
    funext x
    simp only [L0, T0, driftT, nuLapT, Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
    simp only [← Complex.coe_smul]
    push_cast
    module
  have hL : IsPhaseTest P (nuLapT ν Θ) := hΘ.lapT.const_smul ν
  have hX1 : IsPhaseTest P (-(driftT Θ)) := hΘ.driftT.neg
  have hX2 : IsPhaseTest P (-(nuLapT ν Θ)) := hL.neg
  have hX : IsPhaseTest P (-(driftT Θ) + -(nuLapT ν Θ)) := hX1.add hX2
  have hY : IsPhaseTest P ((1 + μ : ℝ) • Θ) := hΘ.const_smul _
  have hc : pairF P ((1 + μ : ℝ) • Θ) Φ = ((1 + μ : ℝ) : ℂ) * pairF P Θ Φ :=
    wlm_pairF_const_smul P (1 + μ) Θ Φ
  have iPhi : Integrable (fun z => dotL (Θ z) (Φ z)) (muP P) :=
    wlm_integrable hP hΘ hΦ
  have iA : Integrable (fun z => dotL (Θ z) (a z)) (muP P) :=
    wlm_integrable hP hΘ (Or.inl ha_mem)
  have iB : Integrable (fun z => dotL (Θ z) (b z)) (muP P) :=
    wlm_integrable hP hΘ (Or.inl hb_mem)
  have iG : Integrable (fun z => dotL (Θ z) (g z)) (muP P) :=
    wlm_integrable hP hΘ hg
  have iC : Integrable (fun z => dotL (Θ z) (((1 + μ : ℝ) : ℂ) • Φ z)) (muP P) := by
    have h := iPhi.const_mul ((1 + μ : ℝ) : ℂ)
    refine h.congr (ae_of_all _ fun z => ?_)
    simp [map_smul, smul_eq_mul]
  have iW1 : Integrable (fun z => dotL (Θ z) ((fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) z))
      (muP P) := int_sub_aux iC iA
  have iW : Integrable (fun z => dotL (Θ z)
      ((fun x => (fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) x - b x) z)) (muP P) :=
    int_sub_aux iW1 iB
  have hR : remH μ Φ g a b
      = fun x => (fun x => (fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) x - b x) x - g x := rfl
  have e1 : pairF P ((-(driftT Θ) + -(nuLapT ν Θ)) + ((1 + μ : ℝ) • Θ)) Φ
      = pairF P (-(driftT Θ) + -(nuLapT ν Θ)) Φ + pairF P ((1 + μ : ℝ) • Θ) Φ :=
    wlm_pairF_add hP hX hY hΦ
  have e2 : pairF P (-(driftT Θ) + -(nuLapT ν Θ)) Φ
      = pairF P (-(driftT Θ)) Φ + pairF P (-(nuLapT ν Θ)) Φ :=
    wlm_pairF_add hP hX1 hX2 hΦ
  have e3 : pairF P (-(driftT Θ)) Φ = -pairF P (driftT Θ) Φ := wlm_pairF_neg P _ _
  have e4 : pairF P (-(nuLapT ν Θ)) Φ = -pairF P (nuLapT ν Θ) Φ := wlm_pairF_neg P _ _
  rw [hfun, e1, e2, e3, e4, hb Θ hΘ, ha Θ hΘ, hc, hR,
    pair_sub_right Θ _ g iW iG, pair_sub_right Θ _ b iW1 iB,
    pair_sub_right Θ _ a iC iA, pairF_csmul_right]
  ring

theorem adjRemainderFormula : AdjRemainderFormula := by
  intro P ν μ hP _ hν hμ Φ g a b hdom ha_mem hb_mem ha hb Θ hΘ
  exact adjRemainderFormula_of_mem P ν μ hP Φ g a b hdom ha_mem hb_mem ha hb Θ hΘ

end UnforcedLeray.Short.PartIIIb.Concrete
