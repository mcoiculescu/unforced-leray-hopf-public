import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6

/-!
# `sepWHRep`: the h-representation of the separated response (`PartIII-b:C/rep/2/6/1`)

Source of record: `the November 2 reference manuscript`, lines 3611-3626
(`sep:resolvent`) and 3603-3610 (`sep:kernel`). With `l = exp(-h/2)` (so `dl = -(l/2) dh`,
`l² = e^{-h}`, `2 log l = -h`) the response `sepW` becomes the kernel integral `kerInt`
with the kernel `Gker ν m`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Change of variables `l = exp(-h/2)` from `Ioi 0` onto `Ioo 0 1`. -/
theorem integral_Ioo_eq_exp_h (g : ℝ → ℂ) :
    ∫ l in Ioo (0 : ℝ) 1, g l =
      ∫ h in Ioi (0 : ℝ), (Real.exp (-h / 2) * (1 / 2) : ℝ) • g (Real.exp (-h / 2)) := by
  have himg : (fun h : ℝ => Real.exp (-h / 2)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext l
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.exp_lt_one_iff]
      have : (0 : ℝ) < h := hh
      linarith
    · rintro ⟨hl0, hl1⟩
      refine ⟨-2 * Real.log l, ?_, ?_⟩
      · have : Real.log l < 0 := Real.log_neg hl0 hl1
        show (0 : ℝ) < -2 * Real.log l
        linarith
      · show Real.exp (-(-2 * Real.log l) / 2) = l
        rw [show -(-2 * Real.log l) / 2 = Real.log l by ring, Real.exp_log hl0]
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun h : ℝ => Real.exp (-h / 2)) (Real.exp (-x / 2) * (-1 / 2)) (Ioi 0) x := by
    intro x _
    have h1 : HasDerivAt (fun h : ℝ => -h / 2) (-1 / 2) x := by
      simpa using ((hasDerivAt_id x).neg).div_const 2
    exact (h1.exp).hasDerivWithinAt
  have hinj : InjOn (fun h : ℝ => Real.exp (-h / 2)) (Ioi 0) := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  norm_num

/-- `(e^t)^w = exp(w t)` for the complex power of a positive real. -/
theorem cpow_exp_real_h (w : ℂ) (t : ℝ) :
    ((Real.exp t : ℝ) : ℂ) ^ w = Complex.exp (w * (t : ℂ)) := by
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.ofReal_exp,
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]

/-- The algebraic identity behind the change of variables. -/
theorem alg_aux_h (E P C J : ℂ) (h : E * P = C) : -2 * (E * (1 / 2) * (P * J)) = -(C * J) := by
  rw [← h]
  ring

/-- **`sepWHRep`** (`PartIII-b:C/rep/2/6/1`, source 3611-3621): the separated response equals the
h-kernel integral `kerInt T (Gker ν m)`. -/
theorem sepWHRep : SepWHRep := by
  intro ν m rOut P hν hm hr hP T hT hM τ y i
  have hsq : ∀ h : ℝ, Real.exp (-h / 2) ^ 2 = Real.exp (-h) := by
    intro h
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hτ : ∀ h : ℝ, τ + 2 * (-h / 2) = τ - h := fun h => by ring
  have hEP : ∀ h : ℝ, ((Real.exp (-h / 2) : ℝ) : ℂ) *
      Complex.exp ((2 * m + 2) * ((-h / 2 : ℝ) : ℂ)) = Complex.exp (-(m + 3 / 2) * (h : ℂ)) := by
    intro h
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hR : ∀ (h : ℝ) (z : Space), ∑ j : Fin 3, ∑ k : Fin 3,
      Gker ν m h y z i j k * ((T (τ - h) z j k : ℝ) : ℂ) =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
          (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
          ((T (τ - h) z j k : ℝ) : ℂ) := by
    intro h z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Gker]
    ring
  unfold IIIa.sepW kerInt
  rw [integral_Ioo_eq_exp_h, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  simp only [hsq h, Real.log_exp, hτ h, Complex.real_smul, cpow_exp_real_h]
  simp only [hR h]
  rw [integral_const_mul, ← hEP h]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
