import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1_3

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Exponent bookkeeping: `1/p + 1/q = 1/2` gives `((ofReal p)⁻¹ + (ofReal q)⁻¹)⁻¹ = 2`. -/
lemma holder3_triple {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (h : 1 / p + 1 / q = 1 / 2) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 2 := by
  refine ⟨?_⟩
  have key : p⁻¹ + q⁻¹ = (2:ℝ)⁻¹ := by
    simp only [inv_eq_one_div]
    linarith
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_add (inv_nonneg.2 hp.le) (inv_nonneg.2 hq.le), key,
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Powers: `|f|^2 ∈ L^{p/2}` when `f ∈ L^p`. -/
lemma holder3_mem_pow_two {μ : Measure Plane} {f : Plane → ℝ} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun z => |f z| ^ (2:ℝ)) (ENNReal.ofReal (p / 2)) μ := by
  have hdiv : ENNReal.ofReal (p / 2) = ENNReal.ofReal p / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp
  have h := hf.norm_rpow_div (2 : ENNReal)
  rw [← hdiv] at h
  simpa [Real.norm_eq_abs] using h

/-- Three-factor Hölder on a general measure, in the real-exponent form. -/
theorem holder3_core {μ : Measure Plane} (a b d : Plane → ℝ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (h : 1 / p + 1 / q + 1 / 2 = 1)
    (ha : MemLp a 2 μ) (hb : MemLp b (ENNReal.ofReal p) μ) (hd : MemLp d (ENNReal.ofReal q) μ) :
    |∫ z, a z * (b z * d z) ∂μ| ≤
      (∫ z, a z * a z ∂μ) ^ (1 / 2 : ℝ) * (∫ z, |b z| ^ p ∂μ) ^ (1 / p) *
        (∫ z, |d z| ^ q ∂μ) ^ (1 / q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hpi : 0 < 1 / p := by positivity
  have hqi : 0 < 1 / q := by positivity
  have h2p : 2 < p := by
    by_contra hc
    push_neg at hc
    have : 1 / 2 ≤ 1 / p := one_div_le_one_div_of_le hp0 hc
    linarith
  have h2q : 2 < q := by
    by_contra hc
    push_neg at hc
    have : 1 / 2 ≤ 1 / q := one_div_le_one_div_of_le hq0 hc
    linarith
  have hsum : (p / 2)⁻¹ + (q / 2)⁻¹ = 1 := by
    rw [inv_div, inv_div]
    have e1 : (2:ℝ) / p = 2 * (1 / p) := by ring
    have e2 : (2:ℝ) / q = 2 * (1 / q) := by ring
    rw [e1, e2]
    linarith
  have hPQ : (p / 2).HolderConjugate (q / 2) :=
    Real.holderConjugate_iff.mpr ⟨by linarith, hsum⟩
  -- Step 1: absolute value of the integral.
  have hstep1 : |∫ z, a z * (b z * d z) ∂μ| ≤ ∫ z, |a z| * |b z * d z| ∂μ :=
    abs_integral_le_integral_abs.trans
      (le_of_eq (integral_congr_ae (ae_of_all _ fun z => by simp [abs_mul])))
  -- Integrability of the factors.
  have ha2 : MemLp (fun z => |a z|) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    simpa [Real.norm_eq_abs] using ha.norm
  have hbd : MemLp (b * d) (2 : ENNReal) μ := by
    haveI := holder3_triple hp0 hq0 (by linarith)
    exact MemLp.mul hd hb
  have hbd2 : MemLp (fun z => |b z * d z|) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    simpa [Real.norm_eq_abs] using hbd.norm
  -- Step 2: Hölder with exponents 2, 2.
  have key1 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun z => |a z|) (g := fun z => |b z * d z|)
    (ae_of_all _ fun z => abs_nonneg _) (ae_of_all _ fun z => abs_nonneg _) ha2 hbd2
  -- Step 3: Hölder with exponents p/2, q/2 on the squared factors.
  have hf2 := holder3_mem_pow_two (μ := μ) hb
  have hd2 := holder3_mem_pow_two (μ := μ) hd
  have key2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hPQ
    (ae_of_all _ fun z => Real.rpow_nonneg (abs_nonneg _) _)
    (ae_of_all _ fun z => Real.rpow_nonneg (abs_nonneg _) _) hf2 hd2
  have hmul : ∀ x y : ℝ, |x * y| ^ (2:ℝ) = |x| ^ (2:ℝ) * |y| ^ (2:ℝ) := fun x y => by
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hpow : ∀ x r : ℝ, (|x| ^ (2:ℝ)) ^ (r / 2) = |x| ^ r := fun x r => by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1 <;> ring
  have hpt : ∀ x : ℝ, |x| ^ (2:ℝ) = x * x := fun x => by
    rw [Real.rpow_two, sq_abs, sq]
  have hI2 : ∫ z, |b z * d z| ^ (2:ℝ) ∂μ = ∫ z, |b z| ^ (2:ℝ) * |d z| ^ (2:ℝ) ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => hmul (b z) (d z))
  have he1 : ∫ z, (|b z| ^ (2:ℝ)) ^ (p / 2) ∂μ = ∫ z, |b z| ^ p ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => hpow (b z) p)
  have he2 : ∫ z, (|d z| ^ (2:ℝ)) ^ (q / 2) ∂μ = ∫ z, |d z| ^ q ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => hpow (d z) q)
  rw [he1, he2] at key2
  have hS : ∫ z, |b z * d z| ^ (2:ℝ) ∂μ ≤
      (∫ z, |b z| ^ p ∂μ) ^ (1 / (p / 2)) * (∫ z, |d z| ^ q ∂μ) ^ (1 / (q / 2)) := by
    rw [hI2]
    exact key2
  have hA : ∫ z, |a z| ^ (2:ℝ) ∂μ = ∫ z, a z * a z ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => hpt (a z))
  have hB0 : 0 ≤ ∫ z, |b z| ^ p ∂μ := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hD0 : 0 ≤ ∫ z, |d z| ^ q ∂μ := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hA0 : 0 ≤ ∫ z, |a z| ^ (2:ℝ) ∂μ := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hS0 : 0 ≤ ∫ z, |b z * d z| ^ (2:ℝ) ∂μ :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have eB : ((∫ z, |b z| ^ p ∂μ) ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) = (∫ z, |b z| ^ p ∂μ) ^ (1 / p) := by
    rw [← Real.rpow_mul hB0]
    congr 1
    ring
  have eD : ((∫ z, |d z| ^ q ∂μ) ^ (1 / (q / 2))) ^ (1 / 2 : ℝ) = (∫ z, |d z| ^ q ∂μ) ^ (1 / q) := by
    rw [← Real.rpow_mul hD0]
    congr 1
    ring
  have hS12 : (∫ z, |b z * d z| ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
      (∫ z, |b z| ^ p ∂μ) ^ (1 / p) * (∫ z, |d z| ^ q ∂μ) ^ (1 / q) := by
    calc (∫ z, |b z * d z| ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ)
        ≤ ((∫ z, |b z| ^ p ∂μ) ^ (1 / (p / 2)) * (∫ z, |d z| ^ q ∂μ) ^ (1 / (q / 2))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hS0 hS (by norm_num)
      _ = ((∫ z, |b z| ^ p ∂μ) ^ (1 / (p / 2))) ^ (1 / 2 : ℝ) *
            ((∫ z, |d z| ^ q ∂μ) ^ (1 / (q / 2))) ^ (1 / 2 : ℝ) :=
          Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hD0 _)
      _ = (∫ z, |b z| ^ p ∂μ) ^ (1 / p) * (∫ z, |d z| ^ q ∂μ) ^ (1 / q) := by rw [eB, eD]
  calc |∫ z, a z * (b z * d z) ∂μ|
      ≤ ∫ z, |a z| * |b z * d z| ∂μ := hstep1
    _ ≤ (∫ z, |a z| ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫ z, |b z * d z| ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ) := key1
    _ ≤ (∫ z, |a z| ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          ((∫ z, |b z| ^ p ∂μ) ^ (1 / p) * (∫ z, |d z| ^ q ∂μ) ^ (1 / q)) :=
          mul_le_mul_of_nonneg_left hS12 (Real.rpow_nonneg hA0 _)
    _ = (∫ z, a z * a z ∂μ) ^ (1 / 2 : ℝ) * (∫ z, |b z| ^ p ∂μ) ^ (1 / p) *
          (∫ z, |d z| ^ q ∂μ) ^ (1 / q) := by
          rw [hA]
          ring

theorem midHolder3_proof : UnforcedLeray.Short.PartI.MidHolder3 := by
  intro c a b d p q hp hq h ha hb hd
  exact holder3_core a b d p q hp hq h ha hb hd

end UnforcedLeray.Short.PartI
