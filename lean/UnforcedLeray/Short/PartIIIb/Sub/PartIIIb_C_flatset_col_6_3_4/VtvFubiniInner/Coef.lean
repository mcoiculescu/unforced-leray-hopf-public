import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvRLinAE

/-!
# Coefficient form of `R(r,·)` (source 4610)

For a fixed age `r`, `R(r,φ) = r^μ ∫_cell [a₀ φ + a₁ ∂_qφ + a₂ ∂_ηφ + a₃ ∂_q²φ + a₄ ∂_η²φ]`
with coefficients built from `f(r,·)`, `ω(r)`, `b(r,·)`, the train `v`, and `E = curl v`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (flowIntegrand lapP)

section Coef

variable {ν c : ℝ}

def cA0 (tr : UnforcedLeray.B0140.TrainSol ν c) (u : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  -(u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
    u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ))

def cA1 (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ) (F : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ)
    (x : ℝ × ℝ) : ℂ := -(F x 1) + om x * (tr.v r x 0 : ℂ)

def cA2 (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ) (F : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ)
    (x : ℝ × ℝ) : ℂ := F x 0 + om x * (tr.v r x 1 : ℂ)

def cA3 (ν : ℝ) (om : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := om x * (ν : ℂ)

theorem int_a0 (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    {u : ℝ × ℝ → Fin 2 → ℂ} (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => cA0 tr u r x * (ψ x : ℂ)) (B0579.cell c) := by
  have h0 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hu 0) (theta_test tr hr 0 hψ)
  have h1 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hu 1) (theta_test tr hr 1 hψ)
  refine (h0.add h1).neg.congr (Eventually.of_forall fun x => ?_)
  simp only [cA0, Pi.neg_apply, Pi.add_apply]
  push_cast
  ring

theorem int_a1 (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    {om : ℝ × ℝ → ℂ} {F : ℝ × ℝ → Fin 2 → ℂ}
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => om x * (ψ x : ℂ)) (B0579.cell c))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (B0579.cell c)))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => cA1 tr om F r x * (ψ x : ℂ)) (B0579.cell c) := by
  have h0 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 1) hψ
  have h1 := hom _ (cyl_mul_sp (v_comp_smooth tr hr 0) (v_comp_periodic tr hr 0) hψ)
  refine (h0.neg.add h1).congr (Eventually.of_forall fun x => ?_)
  simp only [cA1, Pi.neg_apply, Pi.add_apply]
  push_cast
  ring

theorem int_a2 (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    {om : ℝ × ℝ → ℂ} {F : ℝ × ℝ → Fin 2 → ℂ}
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => om x * (ψ x : ℂ)) (B0579.cell c))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (B0579.cell c)))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => cA2 tr om F r x * (ψ x : ℂ)) (B0579.cell c) := by
  have h0 := UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 0) hψ
  have h1 := hom _ (cyl_mul_sp (v_comp_smooth tr hr 1) (v_comp_periodic tr hr 1) hψ)
  refine (h0.add h1).congr (Eventually.of_forall fun x => ?_)
  simp only [cA2, Pi.add_apply]
  push_cast
  ring

theorem int_a3 (ν : ℝ) {om : ℝ × ℝ → ℂ}
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => om x * (ψ x : ℂ)) (B0579.cell c))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => cA3 ν om x * (ψ x : ℂ)) (B0579.cell c) := by
  refine ((hom _ hψ).const_mul (ν : ℂ)).congr (Eventually.of_forall fun x => ?_)
  simp only [cA3]
  ring

theorem Qid (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ) (u F : ℝ × ℝ → Fin 2 → ℂ)
    (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    (F x 0 * (B0579.pd 1 φ x : ℂ) - F x 1 * (B0579.pd 0 φ x : ℂ)) +
        flowIntegrand tr om u r φ x =
      cA0 tr u r x * (φ x : ℂ) + cA1 tr om F r x * (B0579.pd 0 φ x : ℂ) +
        cA2 tr om F r x * (B0579.pd 1 φ x : ℂ) + cA3 ν om x * (B0579.pd 0 (B0579.pd 0 φ) x : ℂ) +
        cA3 ν om x * (B0579.pd 1 (B0579.pd 1 φ) x : ℂ) := by
  rw [flow_eq]
  simp only [cA0, cA1, cA2, cA3, lapP]
  push_cast
  ring

theorem Rform {μ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om g : ℝ → ℝ × ℝ → ℂ) (b : Chart → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, MemLp (fun x => f (r, x) i) 2 (volume.restrict (B0579.cell c)))
    (hu : ∀ j, MemLp (fun x => b (r, x) j) 2 (volume.restrict (B0579.cell c)))
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => om r x * (ψ x : ℂ)) (B0579.cell c))
    (hcurl : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, g r x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, (f (r, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          f (r, x) 1 * (B0579.pd 0 ψ x : ℂ)))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    vtvR μ tr om g b r φ = ((r : ℂ) ^ (μ : ℂ)) *
      (((((∫ x in B0579.cell c, cA0 tr (fun x => b (r, x)) r x * (φ x : ℂ)) +
        ∫ x in B0579.cell c, cA1 tr (om r) (fun x => f (r, x)) r x * (B0579.pd 0 φ x : ℂ)) +
        ∫ x in B0579.cell c, cA2 tr (om r) (fun x => f (r, x)) r x * (B0579.pd 1 φ x : ℂ)) +
        ∫ x in B0579.cell c, cA3 ν (om r) x * (B0579.pd 0 (B0579.pd 0 φ) x : ℂ)) +
        ∫ x in B0579.cell c, cA3 ν (om r) x * (B0579.pd 1 (B0579.pd 1 φ) x : ℂ)) := by
  unfold vtvR
  rw [hcurl φ hφ]
  have e1 : IntegrableOn (fun x => f (r, x) 0 * (B0579.pd 1 φ x : ℂ) -
      f (r, x) 1 * (B0579.pd 0 φ x : ℂ)) (B0579.cell c) :=
    (UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 0) (hφ.pd 1)).sub
      (UnforcedLeray.Short.IIIa.Exist.lfc_integrableOn_vol_test (hF 1) (hφ.pd 0))
  have e2 := flow_int tr hr.le (om r) (fun x => b (r, x)) hom hu hφ
  rw [← integral_add e1 e2]
  have i0 := int_a0 tr hr.le hu hφ
  have i1 := int_a1 tr hr.le hom hF (hφ.pd 0)
  have i2 := int_a2 tr hr.le hom hF (hφ.pd 1)
  have i3 := int_a3 ν hom ((hφ.pd 0).pd 0)
  have i4 := int_a3 ν hom ((hφ.pd 1).pd 1)
  have e : ∀ x, (f (r, x) 0 * (B0579.pd 1 φ x : ℂ) - f (r, x) 1 * (B0579.pd 0 φ x : ℂ)) +
      flowIntegrand tr (om r) (fun x => b (r, x)) r φ x =
      cA0 tr (fun x => b (r, x)) r x * (φ x : ℂ) +
        cA1 tr (om r) (fun x => f (r, x)) r x * (B0579.pd 0 φ x : ℂ) +
        cA2 tr (om r) (fun x => f (r, x)) r x * (B0579.pd 1 φ x : ℂ) +
        cA3 ν (om r) x * (B0579.pd 0 (B0579.pd 0 φ) x : ℂ) +
        cA3 ν (om r) x * (B0579.pd 1 (B0579.pd 1 φ) x : ℂ) :=
    fun x => Qid tr (om r) (fun x => b (r, x)) (fun x => f (r, x)) r φ x
  simp_rw [e]
  rw [integral_add, integral_add, integral_add, integral_add]
  all_goals first
    | exact i0 | exact i1 | exact i2 | exact i3 | exact i4
    | exact i0.add i1 | exact (i0.add i1).add i2 | exact ((i0.add i1).add i2).add i3

end Coef

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
