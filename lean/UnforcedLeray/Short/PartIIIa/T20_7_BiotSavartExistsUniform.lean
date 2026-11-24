import UnforcedLeray.Short.PartIIIa.T20_6_RealBiotSavartUniform
import UnforcedLeray.Short.PartIIIa.Sub.T20

/-!
# Part III-a, task `PartIII-a:T20/7`: the complex Biot-Savart existence bound

Source of record: `the November 2 reference manuscript`, lines 3236-3240.
Target: `CTE.BiotSavartExistsUniform` (`Sub/T20.lean`, unchanged).

Proof. Take `C0` from `realBiotSavartUniform` (`m > 2`) and set `C := 2 * C0`. For a complex
`f` in `L²(cellMeasure d m)` with zero circulation, let `ω₁ = Re f` and `ω₂ = Im f` as elements
of `X_{d,m}` (real `L²`), each with zero circulation. The real case gives velocities `u₁`, `u₂`
and the complex velocity is `u = u₁ + i u₂`. Then:
* `IsBiotSavart`: the three clauses are linear in `(f, u)` with real test functions, and the
  integrals split since every integrand is integrable (`L²` times `L²` on the cell, and
  `Re f ψ`, `Im f ψ` via `integrableOn_mul_neg`).
* Norm: `velNorm` satisfies Minkowski's inequality, and `‖ω_i‖ ≤ ‖f‖_{X_{d,m}}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.CTE

namespace T20_7

/-- Minkowski inequality for the `ℓ²`-sum of `L²` norms (`ENNReal.Lp_add_le` with `p = 2`). -/
lemma sum_sq_rpow_le {ι : Type*} (s : Finset ι) (A B C : ι → ℝ≥0∞)
    (h : ∀ i, C i ≤ A i + B i) :
    (∑ i ∈ s, C i ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∑ i ∈ s, A i ^ 2) ^ (1 / 2 : ℝ) + (∑ i ∈ s, B i ^ 2) ^ (1 / 2 : ℝ) := by
  have hC : ∑ i ∈ s, C i ^ 2 ≤ ∑ i ∈ s, (A i + B i) ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity) (h i) 2
  have hM := ENNReal.Lp_add_le s A B (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at hM
  exact (ENNReal.rpow_le_rpow hC (by norm_num)).trans hM

/-- The velocity `u₁ + i u₂` has `velNorm` at most the sum of the two `velNorm`s. -/
lemma velNorm_add_I_le (d : ℝ) (u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ)
    (h₁ : ∀ j, MemLp (fun x => u₁ x j) 2 (volume.restrict (B0579.cell d)))
    (h₂ : ∀ j, MemLp (fun x => u₂ x j) 2 (volume.restrict (B0579.cell d))) :
    velNorm d (fun x j => u₁ x j + Complex.I * u₂ x j) ≤ velNorm d u₁ + velNorm d u₂ := by
  unfold velNorm
  refine sum_sq_rpow_le Finset.univ
    (fun j => eLpNorm (fun x => u₁ x j) 2 (volume.restrict (B0579.cell d)))
    (fun j => eLpNorm (fun x => u₂ x j) 2 (volume.restrict (B0579.cell d)))
    (fun j => eLpNorm (fun x => u₁ x j + Complex.I * u₂ x j) 2 (volume.restrict (B0579.cell d)))
    (fun j => ?_)
  have hI : eLpNorm (fun x => Complex.I * u₂ x j) 2 (volume.restrict (B0579.cell d))
      = eLpNorm (fun x => u₂ x j) 2 (volume.restrict (B0579.cell d)) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_I, one_mul])
  refine (eLpNorm_add_le (h₁ j).aestronglyMeasurable
    ((h₂ j).aestronglyMeasurable.const_mul Complex.I) (by norm_num)).trans ?_
  rw [hI]

/-- `L²(cell)` membership of a cylinder test function. -/
lemma memLp_cell_test {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    MemLp φ 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.vanish
  exact B0579.memLp_cell_of_continuous hφ.continuous (B0579.isCompact_box c R) hR

/-- Products of an `L²(cell)` complex component with a test function are integrable. -/
lemma integrableOn_comp_test {c : ℝ} (v : ℝ × ℝ → Fin 2 → ℂ)
    (hv : ∀ j, MemLp (fun x => v x j) 2 (volume.restrict (B0579.cell c))) (j : Fin 2)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => v x j * (φ x : ℂ)) (B0579.cell c) := by
  have hL : MemLp (fun x => (φ x : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    (memLp_cell_test hφ).ofReal
  exact (hv j).integrable_mul hL

/-- A real `X_{d,m}` element times a test function, viewed as complex, is integrable. -/
lemma integrableOn_X_test_complex {d m : ℝ} (ω : B0579.X d m) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) :
    IntegrableOn (fun x => ((ω x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell d) := by
  have h1 : IntegrableOn (fun x => ω x * ψ x) (B0579.cell d) := by
    refine (B0579.integrableOn_mul_neg d m ω (B0579.testLp d (-m) hψ)).congr_fun_ae ?_
    filter_upwards [B0579.coeFn_testLp d (-m) hψ] with x hx
    simp only [hx]
  refine (Integrable.ofReal h1).congr (Eventually.of_forall fun x => ?_)
  simp

/-- The `X_{d,m}` norm of a real function dominated pointwise by `‖f‖` is at most `‖f‖_{X}`. -/
lemma norm_le_xNorm {d m : ℝ} {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure d m))
    {φ : ℝ × ℝ → ℝ} (hφ : ∀ x, ‖φ x‖ ≤ ‖f x‖) (g : B0579.X d m)
    (hg : (g : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure d m] φ) :
    ‖g‖ ≤ (xNorm d m f).toReal := by
  rw [Lp.norm_def]
  apply ENNReal.toReal_mono hf.2.ne
  calc eLpNorm (g : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure d m)
      = eLpNorm φ 2 (B0579.cellMeasure d m) := eLpNorm_congr_ae hg
    _ ≤ eLpNorm f 2 (B0579.cellMeasure d m) := eLpNorm_mono hφ

end T20_7

open T20_7

/-- **`PartIII-a:T20/7`: the complex case of `BiotSavartExistsUniform`.** -/
theorem biotSavart_exists_uniform : UnforcedLeray.Short.IIIa.CTE.BiotSavartExistsUniform := by
  intro m hm
  obtain ⟨C0, hC0nn, hC0⟩ := realBiotSavartUniform m (by linarith)
  refine ⟨2 * C0, fun d hd f hf hz _hev => ?_⟩
  have hF : Fact (0 < d) := ⟨by linarith⟩
  unfold HasZeroCirculation at hz
  obtain ⟨hint, hzero⟩ := hz
  have hre : MemLp (fun x => (f x).re) 2 (B0579.cellMeasure d m) := hf.re
  have him : MemLp (fun x => (f x).im) 2 (B0579.cellMeasure d m) := hf.im
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁ : B0579.X d m,
      (ω₁ : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure d m] (fun x => (f x).re) :=
    ⟨hre.toLp _, MemLp.coeFn_toLp hre⟩
  obtain ⟨ω₂, hω₂⟩ : ∃ ω₂ : B0579.X d m,
      (ω₂ : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure d m] (fun x => (f x).im) :=
    ⟨him.toLp _, MemLp.coeFn_toLp him⟩
  have ae₁ : (ω₁ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] (fun x => (f x).re) :=
    (B0579.ac_cellMeasure d m).ae_le hω₁
  have ae₂ : (ω₂ : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell d)] (fun x => (f x).im) :=
    (B0579.ac_cellMeasure d m).ae_le hω₂
  have hcirc₁ : ∫ x in B0579.cell d, ω₁ x = 0 := by
    rw [integral_congr_ae ae₁]
    have h := integral_re hint
    rw [hzero] at h
    simpa using h
  have hcirc₂ : ∫ x in B0579.cell d, ω₂ x = 0 := by
    rw [integral_congr_ae ae₂]
    have h := integral_im hint
    rw [hzero] at h
    simpa using h
  obtain ⟨u₁, hu₁, hv₁⟩ := hC0 d hd ω₁ hcirc₁
  obtain ⟨u₂, hu₂, hv₂⟩ := hC0 d hd ω₂ hcirc₂
  unfold IsBiotSavart at hu₁ hu₂
  obtain ⟨hm₁, hdiv₁, hcurl₁⟩ := hu₁
  obtain ⟨hm₂, hdiv₂, hcurl₂⟩ := hu₂
  refine ⟨fun x j => u₁ x j + Complex.I * u₂ x j, ?_, ?_⟩
  · unfold IsBiotSavart
    refine ⟨fun j => (hm₁ j).add ((hm₂ j).const_mul Complex.I), ?_, ?_⟩
    · intro ψ hψ
      have hA : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ)
          + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell d) :=
        (integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 0)).add
          (integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 1))
      have hB : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ)
          + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell d) :=
        (integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 0)).add
          (integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 1))
      have hsplit : ∀ x, (u₁ x 0 + Complex.I * u₂ x 0) * (B0579.pd 0 ψ x : ℂ)
          + (u₁ x 1 + Complex.I * u₂ x 1) * (B0579.pd 1 ψ x : ℂ)
          = (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ))
            + Complex.I * (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) :=
        fun x => by ring
      show ∫ x in B0579.cell d, ((u₁ x 0 + Complex.I * u₂ x 0) * (B0579.pd 0 ψ x : ℂ)
          + (u₁ x 1 + Complex.I * u₂ x 1) * (B0579.pd 1 ψ x : ℂ)) = 0
      rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA (hB.const_mul _),
        integral_const_mul, hdiv₁ ψ hψ, hdiv₂ ψ hψ]
      ring
    · intro ψ hψ
      have hI1 : IntegrableOn (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ)
          - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell d) :=
        (integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 1)).sub
          (integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 0))
      have hI2 : IntegrableOn (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ)
          - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell d) :=
        (integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 1)).sub
          (integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 0))
      have c1 : ∫ x in B0579.cell d, ((ω₁ x : ℝ) : ℂ) * (ψ x : ℂ)
          = ∫ x in B0579.cell d, (u₁ x 0 * (B0579.pd 1 ψ x : ℂ)
            - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) := hcurl₁ ψ hψ
      have c2 : ∫ x in B0579.cell d, ((ω₂ x : ℝ) : ℂ) * (ψ x : ℂ)
          = ∫ x in B0579.cell d, (u₂ x 0 * (B0579.pd 1 ψ x : ℂ)
            - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := hcurl₂ ψ hψ
      have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell d)),
          f x * (ψ x : ℂ) = ((ω₁ x : ℝ) : ℂ) * (ψ x : ℂ)
            + Complex.I * (((ω₂ x : ℝ) : ℂ) * (ψ x : ℂ)) := by
        filter_upwards [ae₁, ae₂] with x h₁ h₂
        simp only [h₁, h₂]
        conv_lhs => rw [← Complex.re_add_im (f x)]
        ring
      have hsplit : ∀ x, (u₁ x 0 + Complex.I * u₂ x 0) * (B0579.pd 1 ψ x : ℂ)
          - (u₁ x 1 + Complex.I * u₂ x 1) * (B0579.pd 0 ψ x : ℂ)
          = (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ))
            + Complex.I * (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        fun x => by ring
      show ∫ x in B0579.cell d, f x * (ψ x : ℂ) = ∫ x in B0579.cell d,
          ((u₁ x 0 + Complex.I * u₂ x 0) * (B0579.pd 1 ψ x : ℂ)
            - (u₁ x 1 + Complex.I * u₂ x 1) * (B0579.pd 0 ψ x : ℂ))
      rw [integral_congr_ae hpt, integral_add (integrableOn_X_test_complex ω₁ hψ)
        ((integrableOn_X_test_complex ω₂ hψ).const_mul _), integral_const_mul, c1, c2,
        integral_congr_ae (Eventually.of_forall hsplit), integral_add hI1 (hI2.const_mul _),
        integral_const_mul]
  · have hn₁ := norm_le_xNorm hf (φ := fun x => (f x).re)
      (fun x => by
        show ‖(f x).re‖ ≤ ‖f x‖
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm (f x)) ω₁ hω₁
    have hn₂ := norm_le_xNorm hf (φ := fun x => (f x).im)
      (fun x => by
        show ‖(f x).im‖ ≤ ‖f x‖
        rw [Real.norm_eq_abs]
        exact Complex.abs_im_le_norm (f x)) ω₂ hω₂
    have hfin : xNorm d m f ≠ ⊤ := hf.2.ne
    have hX : ENNReal.ofReal (C0 * (xNorm d m f).toReal)
        = ENNReal.ofReal C0 * xNorm d m f := by
      rw [ENNReal.ofReal_mul hC0nn, ENNReal.ofReal_toReal hfin]
    calc velNorm d (fun x j => u₁ x j + Complex.I * u₂ x j)
        ≤ velNorm d u₁ + velNorm d u₂ := velNorm_add_I_le d u₁ u₂ hm₁ hm₂
      _ ≤ ENNReal.ofReal (C0 * (xNorm d m f).toReal)
          + ENNReal.ofReal (C0 * (xNorm d m f).toReal) :=
          add_le_add
            (hv₁.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn₁ hC0nn)))
            (hv₂.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn₂ hC0nn)))
      _ = ENNReal.ofReal (2 * C0) * xNorm d m f := by
          rw [hX, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring
