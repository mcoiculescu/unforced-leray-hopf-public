import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.Congr
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_3.Neg

/-!
# Part II-b, task `PartII-b:P1/1/3`: additivity and real homogeneity of the ring lift `NvC`

Target `blNvLin_proof : BLNvLin` (SP 1902-1906). Proved here:

* `blNvLin_proof` uses the congruence for `R > 0` (`blrCongr_proof`) and `R < 0` (`Linear_3/Neg`).
  The case `R > 0` is `blrCongr_proof` (`Linear_1/Congr.lean`), and the case `R = 0` is
  trivial because `age 0 y = 0`, so every lift vanishes.

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Every `H_p` class has a measurable representative. -/
theorem linear3_exists_meas_rep {c : ℝ} (g : HpR c) :
    ∃ B : ℝ × (ℝ × ℝ) → Axi.Merid, Measurable B ∧
      (g : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] B :=
  ⟨(Lp.aestronglyMeasurable g).mk _,
    (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable,
    (Lp.aestronglyMeasurable g).ae_eq_mk⟩

theorem linear3_realC_zero : UnforcedLeray.B0412.realC (0 : Space) = 0 := by
  simp [UnforcedLeray.B0412.realC]

theorem linear3_realC_add (u v : Space) :
    UnforcedLeray.B0412.realC (u + v) = UnforcedLeray.B0412.realC u + UnforcedLeray.B0412.realC v := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

theorem linear3_realC_smul (a : ℝ) (v : Space) :
    UnforcedLeray.B0412.realC (a • v) = a • UnforcedLeray.B0412.realC v := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]

/-- The lift congruence for every sign of `R` (the `R = 0` case is trivial). -/
theorem linear3_nvc_congr (R c : ℝ) (hc : 0 < c) (g : HpR c)
    (B : ℝ × (ℝ × ℝ) → Axi.Merid) (hB : Measurable B)
    (hae : (g : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] B) :
    ∀ᵐ x : ℝ × Space, NvC R (toProf c g) x =
      UnforcedLeray.B0412.realC (Axi.Nv R (Axi.perExt c B) x.1 x.2) := by
  rcases lt_trichotomy R 0 with h | h | h
  · exact blrCongrNeg_core R c h hc g B hB hae
  · subst h
    refine Filter.Eventually.of_forall fun x => ?_
    simp [NvC, Axi.Nv, Axi.age, linear3_realC_zero]
  · exact blrCongr_proof R c h hc g B hB hae

/-- **`PartII-b:P1/1/3`** `BLNvLin`. -/
theorem blNvLin_proof : BLNvLin := by
  intro R c hc g₁ g₂
  refine ⟨?_, ?_⟩
  · obtain ⟨B₁, hB₁m, hB₁⟩ := linear3_exists_meas_rep g₁
    obtain ⟨B₂, hB₂m, hB₂⟩ := linear3_exists_meas_rep g₂
    have hsum : ((g₁ + g₂ : HpR c) : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] B₁ + B₂ := by
      filter_upwards [Lp.coeFn_add g₁ g₂, hB₁, hB₂] with z h1 h2 h3
      simp only [Pi.add_apply] at h1 ⊢
      rw [h1, h2, h3]
    have h12 := linear3_nvc_congr R c hc (g₁ + g₂) (B₁ + B₂) (hB₁m.add hB₂m) hsum
    have h1 := linear3_nvc_congr R c hc g₁ B₁ hB₁m hB₁
    have h2 := linear3_nvc_congr R c hc g₂ B₂ hB₂m hB₂
    filter_upwards [h12, h1, h2] with x e12 e1 e2
    have hpe : Axi.perExt c (B₁ + B₂) = Axi.perExt c B₁ + Axi.perExt c B₂ := rfl
    rw [e12, e1, e2, hpe, Axi.Nv_add, linear3_realC_add]
  · intro a
    obtain ⟨B₁, hB₁m, hB₁⟩ := linear3_exists_meas_rep g₁
    have hsm : ((a • g₁ : HpR c) : ℝ × (ℝ × ℝ) → Axi.Merid) =ᵐ[hMeas c bgp] a • B₁ := by
      filter_upwards [Lp.coeFn_smul a g₁, hB₁] with z h1 h2
      simp only [Pi.smul_apply] at h1 ⊢
      rw [h1, h2]
    have he := linear3_nvc_congr R c hc (a • g₁) (a • B₁) (hB₁m.const_smul a) hsm
    have h1 := linear3_nvc_congr R c hc g₁ B₁ hB₁m hB₁
    filter_upwards [he, h1] with x e e1
    have hpe : Axi.perExt c (a • B₁) = a • Axi.perExt c B₁ := rfl
    rw [e, e1, hpe, Axi.Nv_smul, linear3_realC_smul]

end UnforcedLeray.Short.IIb
