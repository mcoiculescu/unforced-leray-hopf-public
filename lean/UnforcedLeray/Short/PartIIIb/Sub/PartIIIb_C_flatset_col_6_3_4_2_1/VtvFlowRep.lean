import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/1/1` (`vtvFlowRep`): the flow representation

Source of record: `the November 2 reference manuscript` (line 4610).
For `r > 0` and a cylinder test `φ`, the test `ψ = νΔφ + v·∇φ` is a cylinder test, so the third
clause of `IsBiotSavart` gives `⟨om(r),ψ⟩ = ∫ b·∇^⊥ψ`; the two cell integrals `om ψ` and `(b·∇E)φ`
are integrable, hence `∫ flowIntegrand = ∫ vtvFlowRHS`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (flowIntegrand lapP IsBiotSavart)

theorem vtvFR_add {c : ℝ} {φ χ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (hχ : B0579.IsCylTest c χ) : B0579.IsCylTest c (fun x => φ x + χ x) := by
  obtain ⟨R1, h1⟩ := hφ.band
  obtain ⟨R2, h2⟩ := hχ.band
  refine ⟨hφ.smooth.add hχ.smooth, fun x => ?_, ⟨max R1 R2, fun x hx => ?_⟩⟩
  · simp only [hφ.periodic x, hχ.periodic x]
  · have hx1 : R1 < |x.2| := lt_of_le_of_lt (le_max_left _ _) hx
    have hx2 : R2 < |x.2| := lt_of_le_of_lt (le_max_right _ _) hx
    simp only [h1 x hx1, h2 x hx2, add_zero]

theorem vtvFR_mul {c : ℝ} {a φ : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hap : ∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x) (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => a x * φ x) := by
  obtain ⟨R, hR⟩ := hφ.band
  refine ⟨ha.mul hφ.smooth, fun x => ?_, ⟨R, fun x hx => ?_⟩⟩
  · simp only [hap x, hφ.periodic x]
  · simp only [hR x hx, mul_zero]

theorem vtvFR_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => ((f x : ℝ) : ℂ)) 2 μ :=
  hf.ofReal

theorem vtvFR_memLp {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    MemLp φ 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.vanish
  exact B0579.memLp_cell_of_continuous hφ.continuous (B0579.isCompact_box c R)
    (fun x hx hxK => hR x hx hxK)

theorem vtvFR_vel_contDiff {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ}
    (hr : 0 ≤ r) (i : Fin 2) : ContDiff ℝ ∞ (fun y : ℝ × ℝ => tr.v r y i) :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
    (UnforcedLeray.Short.IIIa.slice_contDiff (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      tr.isTrain.smooth_v hr)

theorem vtvFR_vel_per {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ}
    (hr : 0 ≤ r) (i : Fin 2) (x : ℝ × ℝ) : tr.v r (x.1 + c, x.2) i = tr.v r x i :=
  congrArg (fun u => u i) (tr.isTrain.periodic_v r hr x)

theorem vtvFR_psi_cyl {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun y => ν * lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y)) := by
  have hL : B0579.IsCylTest c (fun y => lapP φ y) :=
    vtvFR_add ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)
  have hN : B0579.IsCylTest c (fun y => ν * lapP φ y) :=
    vtvFR_mul (a := fun _ => ν) contDiff_const (fun _ => rfl) hL
  have h0 : B0579.IsCylTest c (fun y => tr.v r y 0 * B0579.pd 0 φ y) :=
    vtvFR_mul (vtvFR_vel_contDiff tr hr 0) (fun x => vtvFR_vel_per tr hr 0 x) (hφ.pd 0)
  have h1 : B0579.IsCylTest c (fun y => tr.v r y 1 * B0579.pd 1 φ y) :=
    vtvFR_mul (vtvFR_vel_contDiff tr hr 1) (fun x => vtvFR_vel_per tr hr 1 x) (hφ.pd 1)
  exact vtvFR_add hN (vtvFR_add h0 h1)

/-- The Ec-term `(b·∇E) φ` of the flow integrand, written as in `flowIntegrand`. -/
def vtvFR_B {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (b : Chart → Fin 2 → ℂ) (r : ℝ)
    (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  (b (r, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℂ) +
    b (r, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℂ)) * (φ x : ℂ)

/-- **Flow representation** (source 4610). -/
theorem vtvFlowRep : VtvFlowRep := by
  intro ν c μ tr om g b G f H r hr φ hφ
  have hBS := H.2.2.2.2.1
  have hOmInt := H.2.2.2.2.2.2.2.2
  have hBSr : IsBiotSavart c (om r) (fun x => b (r, x)) := hBS r hr
  set ψ : ℝ × ℝ → ℝ := fun y => ν * lapP φ y +
      (tr.v r y 0 * B0579.pd 0 φ y + tr.v r y 1 * B0579.pd 1 φ y) with hψdef
  have hψc : B0579.IsCylTest c ψ := vtvFR_psi_cyl tr hr.le hφ
  have hOm : IntegrableOn (fun x => om r x * (ψ x : ℂ)) (B0579.cell c) := hOmInt r hr ψ hψc
  have hBid : ∫ x in B0579.cell c, om r x * (ψ x : ℂ) =
      ∫ x in B0579.cell c, (b (r, x) 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        b (r, x) 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) :=
    hBSr.2.2 ψ hψc
  have hEc : ContDiff ℝ ∞ (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr r y) :=
    UnforcedLeray.Short.IIIa.slice_contDiff
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (UnforcedLeray.Short.IIIa.Ec_contDiffOn tr) hr.le
  have hdiff : ∀ j : Fin 2, ContDiff ℝ ∞ (B0579.pd j (UnforcedLeray.B0238.Ec tr r)) :=
    fun j => (contDiff_infty_iff_fderiv.1 hEc).2.clm_apply contDiff_const
  have hEmem : ∀ j : Fin 2, MemLp (fun x => B0579.pd j (UnforcedLeray.B0238.Ec tr r) x * φ x) 2
      (volume.restrict (B0579.cell c)) := by
    intro j
    obtain ⟨R, hR⟩ := hφ.vanish
    exact B0579.memLp_cell_of_continuous ((hdiff j).continuous.mul hφ.continuous)
      (B0579.isCompact_box c R) (fun x hx hxK => by simp [hR x hx hxK])
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hBj : ∀ j : Fin 2, MemLp (fun x => b (r, x) j) 2 (volume.restrict (B0579.cell c)) :=
    fun j => (hBSr.1 j)
  have hB : IntegrableOn (vtvFR_B tr b r φ) (B0579.cell c) := by
    have h0 : Integrable (fun x => b (r, x) 0 *
        ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      MemLp.integrable_mul (hBj 0) (vtvFR_ofReal (hEmem 0))
    have h1 : Integrable (fun x => b (r, x) 1 *
        ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x * φ x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      MemLp.integrable_mul (hBj 1) (vtvFR_ofReal (hEmem 1))
    refine (h0.add h1).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, vtvFR_B]
    push_cast
    ring
  have hA : IntegrableOn (fun x => b (r, x) 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
      b (r, x) 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) (B0579.cell c) := by
    have h0 : Integrable (fun x => b (r, x) 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      MemLp.integrable_mul (hBj 0) (vtvFR_ofReal (vtvFR_memLp (hψc.pd 1)))
    have h1 : Integrable (fun x => b (r, x) 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      MemLp.integrable_mul (hBj 1) (vtvFR_ofReal (vtvFR_memLp (hψc.pd 0)))
    exact h0.sub h1
  calc ∫ x in B0579.cell c, flowIntegrand tr (om r) (fun x => b (r, x)) r φ x
      = ∫ x in B0579.cell c, (om r x * (ψ x : ℂ) - vtvFR_B tr b r φ x) := rfl
    _ = (∫ x in B0579.cell c, om r x * (ψ x : ℂ)) - ∫ x in B0579.cell c, vtvFR_B tr b r φ x :=
        integral_sub hOm hB
    _ = (∫ x in B0579.cell c, (b (r, x) 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
          b (r, x) 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ))) - ∫ x in B0579.cell c, vtvFR_B tr b r φ x := by
        rw [hBid]
    _ = ∫ x in B0579.cell c, ((b (r, x) 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
          b (r, x) 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) - vtvFR_B tr b r φ x) :=
        (integral_sub hA hB).symm
    _ = ∫ x in B0579.cell c, vtvFlowRHS tr b r φ x := rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
