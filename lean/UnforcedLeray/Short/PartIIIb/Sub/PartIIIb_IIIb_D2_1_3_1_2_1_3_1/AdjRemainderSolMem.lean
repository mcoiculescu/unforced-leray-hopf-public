import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1.AdjRemainderFormula
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3.Grad

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

namespace AdjRemSolAux

theorem driftT_gradT {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) :
    driftT (gradT φ) = gradT (fun q => (-1 : ℝ) • dτ φ q + (1 / 2 : ℝ) • radialT φ q + (1 : ℝ) • φ q) := by
  have hA : ContDiff ℝ ∞ (fun q => (-1 : ℝ) • dτ φ q + (1 / 2 : ℝ) • radialT φ q) :=
    ((GradAux.cdDτ h).const_smul _).add ((GradAux.cdRadial h).const_smul _)
  rw [GradAux.gradT_add_fun hA (h.const_smul _),
    GradAux.gradT_add_fun ((GradAux.cdDτ h).const_smul _) ((GradAux.cdRadial h).const_smul _),
    GradAux.gradT_smul_fun (GradAux.cdDτ h), GradAux.gradT_smul_fun (GradAux.cdRadial h),
    GradAux.gradT_smul_fun h]
  funext p
  have e1 : dτ (gradT φ) p = gradT (dτ φ) p := congrFun (GradAux.gr_dτ h) p
  have e2 : radialT (gradT φ) p = gradT (radialT φ) p - gradT φ p := by
    have := congrFun (GradAux.gr_radial h) p
    rw [this]
    abel
  simp only [driftT, e1, e2, Complex.coe_smul]
  module

theorem nuLapT_gradT {φ : ℝ × Space → ℂ} (h : ContDiff ℝ ∞ φ) (ν : ℝ) :
    nuLapT ν (gradT φ) = gradT (fun q => ν • lapT φ q) := by
  rw [GradAux.gradT_smul_fun (GradAux.cdLap h)]
  funext p
  have e3 : lapT (gradT φ) p = gradT (lapT φ) p := congrFun (GradAux.gr_lap h) p
  simp only [nuLapT, Pi.smul_apply, e3]

end AdjRemSolAux

open AdjRemFormAux AdjRemSolAux in
/-- The remainder field is weakly solenoidal, with `a, b ∈ Y_2` supplied. -/
theorem adjRemainderSol_of_mem (P ν μ : ℝ) (hP : 0 < P)
    (Φ g a b : ℝ × Space → CVec3) (hdom : FWUAdjDom P ν μ Φ g)
    (ha_mem : UnforcedLeray.Short.IIb.IsInYr P 2 a) (hb_mem : UnforcedLeray.Short.IIb.IsInYr P 2 b)
    (ha : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a)
    (hb : UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b) :
    IsWeakSolenoidal P (remH μ Φ g a b) := by
  intro φ hφ
  have hX : IsPhaseTest P (gradT φ) := hφ.gradT
  have hΦ : LocL2 P Φ := Or.inl hdom.mem
  have iPhi : Integrable (fun z => dotL (gradT φ z) (Φ z)) (muP P) := wlm_integrable hP hX hΦ
  have iA : Integrable (fun z => dotL (gradT φ z) (a z)) (muP P) :=
    wlm_integrable hP hX (Or.inl ha_mem)
  have iB : Integrable (fun z => dotL (gradT φ z) (b z)) (muP P) :=
    wlm_integrable hP hX (Or.inl hb_mem)
  have iG : Integrable (fun z => dotL (gradT φ z) (g z)) (muP P) :=
    wlm_integrable hP hX (Or.inl hdom.mem_g)
  have iC : Integrable (fun z => dotL (gradT φ z) (((1 + μ : ℝ) : ℂ) • Φ z)) (muP P) := by
    have h := iPhi.const_mul ((1 + μ : ℝ) : ℂ)
    refine h.congr (ae_of_all _ fun z => ?_)
    simp [map_smul, smul_eq_mul]
  have iW1 : Integrable (fun z => dotL (gradT φ z)
      ((fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) z)) (muP P) := int_sub_aux iC iA
  have iW : Integrable (fun z => dotL (gradT φ z)
      ((fun x => (fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) x - b x) z)) (muP P) :=
    int_sub_aux iW1 iB
  have hR : remH μ Φ g a b
      = fun x => (fun x => (fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x) x - b x) x - g x := rfl
  have hpa : pairF P (gradT φ) a = 0 := by
    rw [← ha _ hX, nuLapT_gradT hφ.smooth]
    exact hdom.sol _ (hφ.lapT.const_smul ν)
  have hpb : pairF P (gradT φ) b = 0 := by
    rw [← hb _ hX, driftT_gradT hφ.smooth]
    exact hdom.sol _ ((((hφ.dτ.const_smul (-1 : ℝ)).add (hφ.radialT.const_smul (1 / 2 : ℝ))).add
      (hφ.const_smul (1 : ℝ))))
  rw [hR, pair_sub_right _ _ g iW iG, pair_sub_right _ _ b iW1 iB,
    pair_sub_right _ _ a iC iA, pairF_csmul_right, hpa, hpb, hdom.sol φ hφ, hdom.sol_g φ hφ]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
