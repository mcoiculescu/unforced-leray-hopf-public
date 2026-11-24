import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1

/-!
# Part I, task `PartI:T08/4/1/1/1/1` (`VcJetLocalL2`): time-local `L²` bound for `V_c`

Source: `the November 2 reference manuscript` line 294 (`V_c^p`) and lines 326-329
(the bounds for `V_c`, `Q_c`).

What is proved here (no sorry, no axiom):

* `vcJetLocal_window`: for an age `s > 0` with `width ν s < c²`, the target conclusion holds for
  `r` in a window around `s`. The window is chosen so that `width ν r ≤ c²` there, and
  `Train.Vc_bounds` (with `m = 1`) plus `1 ≤ width ν r ≤ c²` give a dominating function
  `C (1 + η²/c²)⁻¹` that is `L²` on the cell. The constant `K` is its square integral.
* `vcJetLocalL2_of_late`: the target `VcJetLocalL2` follows from the window lemma and the leaf
  `VcJetLocalLate`, which covers the ages with `c² ≤ width ν s`.

Not proved: `VcJetLocalLate`. `Train.Vc_bounds` is stated only for `width ν s ≤ c²`, and the
periodized velocity `Vc = periodize c (isoV ν s)` has no bound at late ages in the library.
So the target `vcJetLocalL2_proof : VcJetLocalL2` is not proved in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- Integrability of the square of the transverse weight `(1 + η²/a)⁻¹` on the real line
(copy of the private lemma in `ErrJetL2/VcWordL2.lean`). -/
private theorem vcJL_weight_sq_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun η : ℝ => ((1 + η ^ 2 / a)⁻¹) ^ 2) := by
  have hφ : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) := by
    refine (integrable_inv_one_add_sq).mono' ?_ ?_
    · have hc : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
        Continuous.inv₀ (by fun_prop) (fun x => by positivity)
      exact (hc.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h0 : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
      have h1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h := hφ.comp_div hsq
  have e : (fun η : ℝ => ((1 + (η / Real.sqrt a) ^ 2)⁻¹) ^ 2) =
      fun η : ℝ => ((1 + η ^ 2 / a)⁻¹) ^ 2 := by
    funext η
    rw [div_pow, Real.sq_sqrt ha.le]
  simpa only [e] using h

/-- The `L²` membership of the transverse weight `(1 + η²/a)⁻¹` on the centred cell
(copy of the private lemma in `ErrJetL2/VcWordL2.lean`). -/
private theorem vcJL_weight_memLp_cell {a c : ℝ} (ha : 0 < a) :
    MemLp (fun z : Plane => (1 + z.2 ^ 2 / a)⁻¹) 2 (Cyl.cellμ c) := by
  have hcont : Continuous (fun z : Plane => (1 + z.2 ^ 2 / a)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) (fun z => ?_)
    have h : 0 < 1 + z.2 ^ 2 / a := by
      have := div_nonneg (sq_nonneg z.2) ha.le
      linarith
    exact h.ne'
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  rw [Cyl.cellμ_eq_prod]
  have : IsFiniteMeasure (volume.restrict (Set.Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  exact (vcJL_weight_sq_integrable ha).comp_snd _

/-- Leaf: time-local `L²(cell)` bound on word derivatives of `V_c` at the late ages
`c² ≤ width ν s`. Not available in the library: `Train.Vc_bounds` needs `width ν s ≤ c²`. -/
def VcJetLocalLate : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ s : ℝ, 0 < s → c ^ 2 ≤ width ν s →
    ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (wordComp w (Vc ν c r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (Vc ν c r) k z) ^ 2 ≤ K

/-- Window lemma: the target conclusion at an age `s` with `width ν s < c²`. The window is
`|r - s| < (c² - width ν s)/ν`, on which `1 ≤ width ν r ≤ c²`. -/
theorem vcJetLocal_window (ν c s : ℝ) (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 < s)
    (hlt : width ν s < c ^ 2) (w : List Bool) (k : Fin 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (wordComp w (Vc ν c r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (Vc ν c r) k z) ^ 2 ≤ K := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hν0 : ν ≠ 0 := hν.ne'
  have hwdef : ∀ x : ℝ, width ν x = 1 + ν * x := fun x => rfl
  obtain ⟨C, b, hC, hb, h⟩ := UnforcedLeray.Train.Vc_bounds w.length 1
  have hε : ν * ((c ^ 2 - width ν s) / ν) = c ^ 2 - width ν s := by
    field_simp
  have hεpos : 0 < (c ^ 2 - width ν s) / ν := div_pos (by linarith) hν
  have hG : MemLp (fun z : Plane => C * (1 + z.2 ^ 2 / c ^ 2)⁻¹) 2 (Cyl.cellμ c) :=
    (vcJL_weight_memLp_cell (a := c ^ 2) (c := c) hc2).const_mul C
  refine ⟨(c ^ 2 - width ν s) / ν, hεpos,
    ∫ z in Cyl.cell c, (C * (1 + z.2 ^ 2 / c ^ 2)⁻¹) ^ 2, ?_⟩
  intro r hr hrs
  -- the window keeps the width below c²
  have hlt' : r - s < (c ^ 2 - width ν s) / ν := lt_of_le_of_lt (le_abs_self _) hrs
  have hmul : ν * (r - s) < ν * ((c ^ 2 - width ν s) / ν) := mul_lt_mul_of_pos_left hlt' hν
  have hsub : ν * (r - s) = ν * r - ν * s := by ring
  have hw1 : 1 ≤ width ν r := by
    rw [hwdef]; nlinarith [mul_nonneg hν.le hr.le]
  have hw2 : width ν r ≤ c ^ 2 := by
    have hs' := hwdef s
    rw [hwdef]; linarith
  have hwpos : 0 < width ν r := by linarith
  have hVc : ContDiff ℝ ∞ (Vc ν c r) := UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 hwpos
  have hVk : ContDiff ℝ ∞ (fun x => Vc ν c r x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hVc
  have hmeas : AEStronglyMeasurable (wordComp w (Vc ν c r) k) (Cyl.cellμ c) :=
    (B0151.contDiff_derivWord hVk w).continuous.aestronglyMeasurable
  have hpow : width ν r ^ (-(3 + (w.length : ℝ)) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw1 (by
      have : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
      linarith)
  have hz := fun z : Plane => (h ν c r hc0 hw1 hw2).1 w rfl k z
  have key : ∀ z : Plane,
      |wordComp w (Vc ν c r) k z| ≤ C * (1 + z.2 ^ 2 / c ^ 2)⁻¹ := by
    intro z
    have hpa : 0 < 1 + z.2 ^ 2 / width ν r := by
      have := div_nonneg (sq_nonneg z.2) hwpos.le
      linarith
    have hpc : 0 < 1 + z.2 ^ 2 / c ^ 2 := by
      have := div_nonneg (sq_nonneg z.2) hc2.le
      linarith
    have hle : 1 + z.2 ^ 2 / c ^ 2 ≤ 1 + z.2 ^ 2 / width ν r := by
      have := div_le_div_of_nonneg_left (sq_nonneg z.2) hwpos hw2
      linarith
    have hzz := hz z
    rw [pow_one] at hzz
    have hf : |wordComp w (Vc ν c r) k z| * (1 + z.2 ^ 2 / width ν r) ≤ C := by
      have h1 : |wordComp w (Vc ν c r) k z| * (1 + z.2 ^ 2 / width ν r) =
          (1 + z.2 ^ 2 / width ν r) * |wordComp w (Vc ν c r) k z| := mul_comm _ _
      rw [h1]
      calc (1 + z.2 ^ 2 / width ν r) * |wordComp w (Vc ν c r) k z|
          ≤ C * width ν r ^ (-(3 + (w.length : ℝ)) / 2) := hzz
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
        _ = C := mul_one C
    have hfa : |wordComp w (Vc ν c r) k z| ≤ C / (1 + z.2 ^ 2 / width ν r) :=
      (le_div_iff₀ hpa).2 hf
    have hfc : C / (1 + z.2 ^ 2 / width ν r) ≤ C / (1 + z.2 ^ 2 / c ^ 2) :=
      div_le_div_of_nonneg_left hC hpc hle
    have e1 : C / (1 + z.2 ^ 2 / c ^ 2) = C * (1 + z.2 ^ 2 / c ^ 2)⁻¹ := div_eq_mul_inv _ _
    linarith
  have hb' : MemLp (wordComp w (Vc ν c r) k) 2 (Cyl.cellμ c) := by
    refine MemLp.of_le hG hmeas (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hC (inv_nonneg.2
      (by have := div_nonneg (sq_nonneg z.2) hc2.le; linarith)))]
    exact key z
  refine ⟨hb', ?_⟩
  refine integral_mono hb'.integrable_sq hG.integrable_sq (fun z => ?_)
  have hk := key z
  have hab := abs_nonneg (wordComp w (Vc ν c r) k z)
  nlinarith [sq_abs (wordComp w (Vc ν c r) k z), mul_le_mul hk hk hab (le_trans hab hk)]

/-- Conditional form of the target: `VcJetLocalL2` follows from the late-age leaf
`VcJetLocalLate`. The unconditional target `vcJetLocalL2_proof` is blocked on that leaf. -/
theorem vcJetLocalL2_of_late (hL : VcJetLocalLate) : VcJetLocalL2 := by
  intro ν c hν hc s hs w k
  by_cases hlt : width ν s < c ^ 2
  · exact vcJetLocal_window ν c s hν hc hs hlt w k
  · exact hL ν c hν hc s hs (not_lt.mp hlt) w k

end UnforcedLeray.Short.PartI
