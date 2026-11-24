import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_1
import UnforcedLeray.Units.B0242

/-!
# Part I, task `PartI:T08/4/1/1/1/1/1` (`VcJetLocalLate`): time-local `L²` bound for `V_c` at late ages

Source: `the November 2 reference manuscript` line 294 (`V_c^p`, a Gaussian
periodization with `ψ^p = -(2/a) e^{-|x|²/(4a)}`) and lines 326-329 (`‖D^jV_c‖_∞ ≤ C a^{-(3+j)/2}`).

Statement: `VcJetLocalLate` (Sub/PartI_T08_4_1_1_1_1.lean). The statement is true: `isoV` is
Gaussian-decaying in `η`, so `V_c = periodize c (isoV ν r)` is `L²` on the cell.

Route (no sorry, no axiom, no new hypotheses):

* `late_Vc_split`: the `c`-periodization is the sum of `m` translates of the `(m c)`-periodization
  (same computation as `UnforcedLeray.Short.IIb.Vc_split`, DriftC2/VcBound.lean).
* With `m` chosen so that `width ν r ≤ (m c)²` on the window `0 < r < 2 s`, `Train.Vc_bounds` applies
  to each translate. Its weight `(1 + η²/a)` is unchanged by the `q`-translation, so the
  `(mc)`-period bound is inherited with the constant `m C` and the weight `(1 + η²/(mc)²)⁻¹`.
* The `q`-translation is commuted with the word derivative (`late_derivWord_shift`) and the finite
  sum with it (`late_derivWord_sum`).
* The dominating weight `(1 + η²/(mc)²)⁻¹` is `L²` on the cell, as in the window lemma.

The window is `|r - s| < s`, so the proof does not use the hypothesis `c² ≤ width ν s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- Integrability of the square of `(1 + η²/a)⁻¹` on the real line. -/
private theorem late_weight_sq_integrable {a : ℝ} (ha : 0 < a) :
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

/-- `(1 + η²/a)⁻¹` is `L²` on the cell `Cyl.cellμ c`. -/
private theorem late_weight_memLp_cell {a c : ℝ} (ha : 0 < a) :
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
  exact (late_weight_sq_integrable ha).comp_snd _

/-- The `c`-periodization splits into `m` translates of the `m c`-periodization. -/
theorem late_Vc_split (ν c s : ℝ) (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (m : ℕ) [NeZero m]
    (z : ℝ × ℝ) :
    UnforcedLeray.Train.Vc ν c s z =
      ∑ j : Fin m, UnforcedLeray.Train.Vc ν ((m : ℝ) * c) s (z.1 - (j : ℕ) * c, z.2) := by
  simp only [UnforcedLeray.Train.Vc, UnforcedLeray.Gaussian.periodize]
  have hsum := UnforcedLeray.Train.summable_isoV hν hc.ne' hs z
  let E : Fin m × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv m).symm
  have hE : ∀ p : Fin m × ℤ, E p = p.2 * m + ((p.1 : ℕ) : ℤ) := fun p => by
    simp [E, Int.divModEquiv]
  have hs' : Summable (fun p : Fin m × ℤ =>
      UnforcedLeray.Train.isoV ν s (z.1 - (E p : ℝ) * c, z.2)) := (E.summable_iff (f := fun n : ℤ =>
        UnforcedLeray.Train.isoV ν s (z.1 - (n : ℝ) * c, z.2))).2 hsum
  have h1 := (E.tsum_eq (fun n : ℤ => UnforcedLeray.Train.isoV ν s (z.1 - (n : ℝ) * c, z.2))).symm
  have h2 := hs'.tsum_prod' (fun j => hs'.prod_factor j)
  rw [h1, h2, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine tsum_congr fun k => ?_
  congr 2
  rw [hE]
  push_cast
  ring

/-- Word derivatives commute with a horizontal shift `z ↦ (z.1 - a, z.2)`. -/
theorem late_partialX_shift (a : ℝ) (g : Plane → ℝ) :
    UnforcedLeray.GaussianVortex.partialX (fun z => g (z.1 - a, z.2)) =
      fun z => UnforcedLeray.GaussianVortex.partialX g (z.1 - a, z.2) := by
  funext z
  show deriv (fun x : ℝ => g (x - a, z.2)) z.1 = deriv (fun x : ℝ => g (x, z.2)) (z.1 - a)
  exact deriv_comp_sub_const (f := fun x : ℝ => g (x, z.2)) a z.1

theorem late_derivWord_shift (a : ℝ) (w : List Bool) (g : Plane → ℝ) :
    UnforcedLeray.B0151.derivWord w (fun z => g (z.1 - a, z.2)) =
      fun z => UnforcedLeray.B0151.derivWord w g (z.1 - a, z.2) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      rfl
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      exact late_partialX_shift a _

theorem late_derivWord_zero (w : List Bool) :
    UnforcedLeray.B0151.derivWord w (fun _ : Plane => (0 : ℝ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      funext z
      simp [UnforcedLeray.GaussianVortex.partialY]
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      funext z
      simp [UnforcedLeray.GaussianVortex.partialX]

/-- Word derivatives of a sum of two smooth functions. -/
theorem late_derivWord_add (w : List Bool) {A B : Plane → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) :
    UnforcedLeray.B0151.derivWord w (fun z => A z + B z) =
      fun z => UnforcedLeray.B0151.derivWord w A z + UnforcedLeray.B0151.derivWord w B z := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have dA := (UnforcedLeray.B0151.contDiff_derivWord hA w).differentiable (by simp)
    have dB := (UnforcedLeray.B0151.contDiff_derivWord hB w).differentiable (by simp)
    cases b
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      funext z
      exact UnforcedLeray.B0242.partialY_add dA dB z
    · simp only [UnforcedLeray.B0151.derivWord]
      rw [ih]
      funext z
      exact UnforcedLeray.B0242.partialX_add dA dB z

/-- Word derivatives of a finite sum of smooth functions. -/
theorem late_derivWord_sum {ι : Type*} (S : Finset ι) (w : List Bool) (A : ι → Plane → ℝ)
    (hA : ∀ i, ContDiff ℝ ∞ (A i)) :
    UnforcedLeray.B0151.derivWord w (fun z => ∑ i ∈ S, A i z) =
      fun z => ∑ i ∈ S, UnforcedLeray.B0151.derivWord w (A i) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact late_derivWord_zero w
  | insert a S ha ih =>
    have hS : ContDiff ℝ ∞ (fun z => ∑ i ∈ S, A i z) :=
      ContDiff.sum (fun i _ => hA i)
    simp only [Finset.sum_insert ha]
    rw [late_derivWord_add w (hA a) hS, ih]

/-- Uniform single-translate bound: `|∂_w V_c(z)| ≤ C (1 + η²/c'²)⁻¹` whenever
`1 ≤ width ν r ≤ c'²`, with `C` depending on `w` only. -/
theorem late_single_bound (w : List Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c' r : ℝ), 0 < c' → 1 ≤ width ν r → width ν r ≤ c' ^ 2 →
      ∀ (k : Fin 2) (z : Plane),
        |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| ≤
          C * (1 + z.2 ^ 2 / c' ^ 2)⁻¹ := by
  obtain ⟨C, b, hC, hb, h⟩ := UnforcedLeray.Train.Vc_bounds w.length 1
  refine ⟨C, hC, fun ν c' r hc' hw1 hw2 k z => ?_⟩
  have hz := (h ν c' r hc' hw1 hw2).1 w rfl k z
  rw [pow_one] at hz
  have hpos : 0 < width ν r := by linarith
  have hpow : width ν r ^ (-(3 + ((w.length : ℕ) : ℝ)) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw1 (by
      have : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
      linarith)
  have hQ : 0 < 1 + z.2 ^ 2 / c' ^ 2 := by
    have := div_nonneg (sq_nonneg z.2) (sq_nonneg c')
    linarith
  have hQP : 1 + z.2 ^ 2 / c' ^ 2 ≤ 1 + z.2 ^ 2 / width ν r := by
    have := div_le_div_of_nonneg_left (sq_nonneg z.2) hpos hw2
    linarith
  have h1 : |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| *
      (1 + z.2 ^ 2 / width ν r) ≤ C := by
    calc |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| *
          (1 + z.2 ^ 2 / width ν r)
        = (1 + z.2 ^ 2 / width ν r) *
            |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| := mul_comm _ _
      _ ≤ C * width ν r ^ (-(3 + ((w.length : ℕ) : ℝ)) / 2) := hz
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
      _ = C := mul_one C
  have h2 : |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| ≤
      C / (1 + z.2 ^ 2 / c' ^ 2) := by
    rw [le_div_iff₀ hQ]
    calc |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| *
          (1 + z.2 ^ 2 / c' ^ 2)
        ≤ |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c' r x k) z| *
            (1 + z.2 ^ 2 / width ν r) :=
          mul_le_mul_of_nonneg_left hQP (abs_nonneg _)
      _ ≤ C := h1
  rw [div_eq_mul_inv] at h2
  exact h2

/-- **Leaf `VcJetLocalLate`**: time-local `L²(cell)` bound on word derivatives of `V_c`. -/
theorem vcJetLocalLate_proof : UnforcedLeray.Short.PartI.VcJetLocalLate := by
  intro ν c hν hc s hs _hcs w k
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC, hbd⟩ := late_single_bound w
  have hwdef : ∀ x : ℝ, width ν x = 1 + ν * x := fun x => rfl
  -- the period multiplier `m`: `(m c)² ≥ 1 + 2 ν s` (the window is `0 < r < 2 s`)
  set m : ℕ := ⌈Real.sqrt (1 + 2 * ν * s) / c⌉₊ + 1 with hm
  have : NeZero m := ⟨by omega⟩
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [hm]; positivity
  have hmc : Real.sqrt (1 + 2 * ν * s) ≤ (m : ℝ) * c := by
    have h1 : Real.sqrt (1 + 2 * ν * s) / c ≤
        (⌈Real.sqrt (1 + 2 * ν * s) / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = (⌈Real.sqrt (1 + 2 * ν * s) / c⌉₊ : ℝ) + 1 := by
      rw [hm]; push_cast; ring
    rw [div_le_iff₀ hc0] at h1
    nlinarith
  have hsq : 1 + 2 * ν * s ≤ ((m : ℝ) * c) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt (1 + 2 * ν * s) := Real.sqrt_nonneg _
    have hnn : 0 ≤ 1 + 2 * ν * s := by
      have := mul_pos hν hs
      linarith
    have := pow_le_pow_left₀ h0 hmc 2
    rwa [Real.sq_sqrt hnn] at this
  have hmc0 : 0 < (m : ℝ) * c := mul_pos hm0 hc0
  -- the dominating weight, `L²` on the cell
  have hG : MemLp (fun z : Plane => ((m : ℝ) * C) * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹) 2
      (Cyl.cellμ c) :=
    (late_weight_memLp_cell (a := ((m : ℝ) * c) ^ 2) (c := c) (pow_pos hmc0 2)).const_mul
      ((m : ℝ) * C)
  have hGnn : ∀ z : Plane, 0 ≤ (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹ := fun z => by positivity
  have hmC : 0 ≤ (m : ℝ) * C := mul_nonneg hm0.le hC
  refine ⟨s, hs, ∫ z in Cyl.cell c,
    (((m : ℝ) * C) * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹) ^ 2, ?_⟩
  intro r hr hrs
  obtain ⟨hrl, hru⟩ := abs_lt.1 hrs
  have hr0 : 0 < r := by linarith
  have hr2 : r < 2 * s := by linarith
  have hνr : ν * r ≤ 2 * ν * s := by
    have := mul_lt_mul_of_pos_left hr2 hν
    nlinarith
  have hw1 : 1 ≤ width ν r := by
    rw [hwdef]
    nlinarith [mul_nonneg hν.le hr0.le]
  have hw2 : width ν r ≤ ((m : ℝ) * c) ^ 2 := by
    rw [hwdef]
    linarith
  have hwpos : 0 < width ν r := by linarith
  -- the periodic split and the derivative of the components
  have hVc := UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 hwpos
  have hVk : ContDiff ℝ ∞ (fun x => Vc ν c r x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hVc
  have hmeas : AEStronglyMeasurable (wordComp w (Vc ν c r) k) (Cyl.cellμ c) :=
    (UnforcedLeray.B0151.contDiff_derivWord hVk w).continuous.aestronglyMeasurable
  have hVm := UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hmc0 hwpos
  set G : Plane → ℝ := fun y => Vc ν ((m : ℝ) * c) r y k with hGdef
  have hGk : ContDiff ℝ ∞ G :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hVm
  have hShift : ∀ a : ℝ, ContDiff ℝ ∞ (fun z : Plane => G (z.1 - a, z.2)) := fun a =>
    hGk.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  have hfun : (fun z : Plane => Vc ν c r z k) =
      fun z => ∑ j : Fin m, G (z.1 - (j : ℕ) * c, z.2) := by
    funext z
    rw [late_Vc_split ν c r hν hc0 hr0.le m z]
    exact map_sum (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) _ _
  have hdec : wordComp w (Vc ν c r) k =
      fun z => ∑ j : Fin m, UnforcedLeray.B0151.derivWord w G (z.1 - (j : ℕ) * c, z.2) := by
    have e1 : wordComp w (Vc ν c r) k =
        UnforcedLeray.B0151.derivWord w (fun z => ∑ j : Fin m, G (z.1 - (j : ℕ) * c, z.2)) := by
      unfold wordComp
      rw [hfun]
    rw [e1, late_derivWord_sum Finset.univ w (fun j : Fin m => fun z => G (z.1 - (j : ℕ) * c, z.2))
      (fun j => hShift _)]
    funext z
    apply Finset.sum_congr rfl
    intro j _
    rw [late_derivWord_shift]
  -- the pointwise bound with the `m`-fold constant
  have hbound : ∀ z : Plane,
      |wordComp w (Vc ν c r) k z| ≤ ((m : ℝ) * C) * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹ := by
    intro z
    rw [hdec]
    show |∑ j : Fin m, UnforcedLeray.B0151.derivWord w G (z.1 - (j : ℕ) * c, z.2)| ≤ _
    calc |∑ j : Fin m, UnforcedLeray.B0151.derivWord w G (z.1 - (j : ℕ) * c, z.2)|
        ≤ ∑ j : Fin m, |UnforcedLeray.B0151.derivWord w G (z.1 - (j : ℕ) * c, z.2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin m, C * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹ :=
          Finset.sum_le_sum (fun j _ => hbd ν ((m : ℝ) * c) r hmc0 hw1 hw2 k (z.1 - (j : ℕ) * c, z.2))
      _ = ((m : ℝ) * C) * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hMemLp : MemLp (wordComp w (Vc ν c r) k) 2 (Cyl.cellμ c) := by
    refine MemLp.of_le hG hmeas (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmC (hGnn z))]
    exact hbound z
  refine ⟨hMemLp, ?_⟩
  refine integral_mono hMemLp.integrable_sq hG.integrable_sq (fun z => ?_)
  have hk := hbound z
  have hab := abs_nonneg (wordComp w (Vc ν c r) k z)
  calc (wordComp w (Vc ν c r) k z) ^ 2 = |wordComp w (Vc ν c r) k z| ^ 2 := (sq_abs _).symm
    _ ≤ (((m : ℝ) * C) * (1 + z.2 ^ 2 / ((m : ℝ) * c) ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ hab hk 2

end UnforcedLeray.Short.PartI
