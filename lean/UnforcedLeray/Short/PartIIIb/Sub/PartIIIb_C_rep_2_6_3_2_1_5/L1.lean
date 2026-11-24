import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4

/-!
# `SepGapPointwiseUnif` (`PartIII-b:C/rep/2/6/3/2/1/5/1`)

Source `the November 2 reference manuscript`
3603-3626, 3800-3807, 4171-4200.

The proof of `sepGapPointwise` (`Sub/IIIb-D2_3_1_1_2/L4.lean`) with the observation point
`y = y₀` fixed: the constant `18 Cn c^{-6}` depends only on the kernel constant `Cn` and on `y₀`,
not on `τ`, `i`, `l`, `z`, `n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepGapPointwiseUnif : SepGapPointwiseUnif := by
  intro ν μ rOut P T hν hμ hr hP hS y0 hy0
  obtain ⟨Cn, hCn0, hCn⟩ := L4_kern IIIa.sepKernelBounds
  have h2 := heatLerayKSmooth
  set d : ℝ := (ϱ y0 - rOut) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set c : ℝ := d / (1 + (‖y0‖ + 1) + d) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; linarith [norm_nonneg y0]
  refine ⟨18 * Cn * c ^ (-6 : ℝ), by positivity, ?_⟩
  intro τ i l hl z n hn
  have hl0 : 0 < l := hl.1
  by_cases hz : rOut < ϱ z
  · have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz
    refine (L4_phi ν μ T τ i l z hl hν h2 n hn y0).trans ?_
    have : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ = 0 := by
      intro j k; simp [hT]
    simp only [this, zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (L4_majorant_nonneg μ T τ n l z hl0)
  · push Not at hz
    have hyb : ‖y0 - y0‖ < min d 1 := by
      rw [sub_self, norm_zero]; exact lt_min hd0 one_pos
    have hgeom := L4_geom rOut d (min d 1) y0 y0 z l hl hz hyb (min_le_left _ _) (min_le_right _ _)
      hd0 (by rw [hd]; linarith)
    have hx0 : 0 < ‖y0 - l • z‖ := lt_of_lt_of_le (by positivity) hgeom |>.trans_le' le_rfl
    have hx : y0 - l • z ≠ 0 := norm_pos_iff.1 hx0
    refine (L4_phi ν μ T τ i l z hl hν h2 n hn y0).trans ?_
    have hpow : ‖y0 - l • z‖ ^ (-4 - (n : ℝ)) ≤ c ^ (-6 : ℝ) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
      have h1 : ‖y0 - l • z‖ ^ (-4 - (n : ℝ)) ≤ (c * (1 + l * ‖z‖)) ^ (-4 - (n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hgeom (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      rw [Real.mul_rpow hc0.le (by positivity)] at h1
      have h3 : c ^ (-4 - (n : ℝ)) ≤ c ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by
          have : (n : ℝ) ≤ 2 := by exact_mod_cast hn
          linarith)
      have h4 : (1 + l * ‖z‖) ^ (-4 - (n : ℝ)) = (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
        congr 1; ring
      rw [h4] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
    have hterm : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y0 - l • z)‖ ≤ 2 * Cn * c ^ (-6 : ℝ) * sepMajorant μ T τ n (l, z) := by
      intro j k
      have ht : 0 < ν * (1 - l ^ 2) := by
        have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
      have hk := hCn n hn _ hx i j _ ht
      have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
      have hn1 : ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ ≤
          2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Complex.norm_cpow_eq_rpow_re_of_pos hl0]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          zero_mul, sub_zero, Real.norm_eq_abs]
        have := L4_entry (T (τ + 2 * Real.log l) z) j k
        have hp : 0 ≤ l ^ (2 * μ.re + 2) := by positivity
        have h2' : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2']
        nlinarith
      rw [he, mul_one]
      have hA : 0 ≤ ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ :=
        norm_nonneg _
      calc _ ≤ (2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
            (Cn * (c ^ (-6 : ℝ) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))))) := by
            refine mul_le_mul hn1 (hk.trans (mul_le_mul_of_nonneg_left hpow hCn0)) (norm_nonneg _)
              (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        _ = 2 * Cn * c ^ (-6 : ℝ) * sepMajorant μ T τ n (l, z) := by
            unfold sepMajorant; simp only; ring
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm := L4_majorant_nonneg μ T τ n l z hl0
    push_cast
    nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
