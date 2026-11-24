import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# The pointwise majorant of the far part (source 3996-4014, 3611-3621, 3604-3610)

Proves `farPointwiseMajorant_of (hK : SepKernelBounds) : FarPointwiseMajorant`
(defined in `Sub/PositiveKernel.lean`).

Route: the `j = 0` bound of `SepKernelBounds` gives `|∇K_t(w)| ≤ C₀ |w|^{-4}` for `w ≠ 0`,
`t > 0`. The output `farOut` is `s^{-1/2}` times the merid part of the negative response
`-sepWfar`, which is bounded entrywise by `2 · 9 · |C₀|` times the positive majorant `farMajE`
(the `z`-integral is taken off the null set `z = l⁻¹ y` where `y - l z = 0`). The merid part has two
components, so the constant is `36 |C₀|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The `j = 0` derivative bound along a coordinate direction. -/
private lemma fpm_coord_bound (C0 t : ℝ) (x : UnforcedLeray.Space) (i j k : Fin 3)
    (h : ‖iteratedFDeriv ℝ (0 + 1) (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖
      ≤ C0 * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ))) :
    ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x
        (UnforcedLeray.coordinateVector k)‖ ≤ C0 * ‖x‖ ^ (-4 : ℝ) := by
  have hn : (-4 : ℝ) - ((0 : ℕ) : ℝ) = -4 := by norm_num
  rw [hn, zero_add, norm_iteratedFDeriv_one] at h
  have hc : ‖UnforcedLeray.coordinateVector k‖ = 1 := by
    simp [UnforcedLeray.coordinateVector]
  calc _ ≤ ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖
        * ‖UnforcedLeray.coordinateVector k‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖ := by
        rw [hc, mul_one]
    _ ≤ C0 * ‖x‖ ^ (-4 : ℝ) := h

/-- Entrywise bound by the Frobenius norm. -/
private lemma fpm_entry (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    ‖M j k‖ ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  rw [Real.norm_eq_abs]
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  apply Real.abs_le_sqrt
  calc M j k ^ 2 ≤ ∑ i', M j i' ^ 2 :=
        Finset.single_le_sum (f := fun i' => M j i' ^ 2) (fun i' _ => sq_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ i, ∑ i', M i i' ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ i', M i i' ^ 2)
          (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- Sum of nine terms. -/
private lemma fpm_sum9 (f : Fin 3 → Fin 3 → ℂ) (B : ℝ) (h : ∀ j k, ‖f j k‖ ≤ B) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, f j k‖ ≤ 9 * B := by
  have h2 : ∑ j : Fin 3, ∑ k : Fin 3, ‖f j k‖ ≤ ∑ j : Fin 3, ∑ k : Fin 3, B :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h j k
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, f j k‖ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖f j k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, B := h2
    _ = 9 * B := by simp only [Fin.sum_univ_three]; ring

/-- The `enorm` as an `ofReal` of the norm. -/
private lemma fpm_enorm_eq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ :=
  (ofReal_norm x).symm

/-- The `enorm` of a negation. -/
private lemma fpm_enorm_neg (w : ℂ) : ‖-w‖ₑ = ‖w‖ₑ := by
  simp

/-- The `enorm` of the merid part of a complex `3`-vector is bounded by the two components. -/
private lemma fpm_merRe_enorm_le (v : Fin 3 → ℂ) :
    ‖UnforcedLeray.Short.PartIIIb.NearInst.merRe v‖ₑ ≤ ‖v 0‖ₑ + ‖v 2‖ₑ := by
  have e0 : (UnforcedLeray.Short.PartIIIb.NearInst.merRe v) 0 = (v 0).re := by
    simp [UnforcedLeray.Short.PartIIIb.NearInst.merRe]
  have e1 : (UnforcedLeray.Short.PartIIIb.NearInst.merRe v) 1 = (v 2).re := by
    simp [UnforcedLeray.Short.PartIIIb.NearInst.merRe]
  have a0 : ‖(v 0).re‖ ≤ ‖v 0‖ := by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have a1 : ‖(v 2).re‖ ≤ ‖v 2‖ := by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hsq : ‖UnforcedLeray.Short.PartIIIb.NearInst.merRe v‖ ≤ ‖v 0‖ + ‖v 2‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [e0, e1]
    nlinarith [mul_le_mul a0 a0 (norm_nonneg _) (norm_nonneg _),
      mul_le_mul a1 a1 (norm_nonneg _) (norm_nonneg _),
      mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 2))]
  calc ‖UnforcedLeray.Short.PartIIIb.NearInst.merRe v‖ₑ
      = ENNReal.ofReal ‖UnforcedLeray.Short.PartIIIb.NearInst.merRe v‖ := fpm_enorm_eq _
    _ ≤ ENNReal.ofReal (‖v 0‖ + ‖v 2‖) := ENNReal.ofReal_le_ofReal hsq
    _ = ‖v 0‖ₑ + ‖v 2‖ₑ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), fpm_enorm_eq (v 0),
          fpm_enorm_eq (v 2)]

/-- Integration in `z` off a null set, with a pointwise bound. -/
private lemma fpm_zbound (K : ℝ≥0∞) (hK : K ≠ ⊤) (g : UnforcedLeray.Space → ℂ)
    (m : UnforcedLeray.Space → ℝ≥0∞) (w : UnforcedLeray.Space)
    (h : ∀ z : UnforcedLeray.Space, z ≠ w → ‖g z‖ₑ ≤ K * m z) :
    ‖∫ z : UnforcedLeray.Space, g z‖ₑ ≤ K * ∫⁻ z : UnforcedLeray.Space, m z := by
  refine (enorm_integral_le_lintegral_enorm g).trans ?_
  rw [← lintegral_const_mul' K _ hK]
  apply lintegral_mono_ae
  filter_upwards [MeasureTheory.Measure.ae_ne (volume : Measure UnforcedLeray.Space) w] with z hz
  exact h z hz

/-- Integration in `l ∈ (0,1)` with a pointwise bound. -/
private lemma fpm_lbound (K : ℝ≥0∞) (hK : K ≠ ⊤) (G : ℝ → ℂ) (p m : ℝ → ℝ≥0∞)
    (h : ∀ l ∈ Ioo (0 : ℝ) 1, ‖G l‖ₑ ≤ p l * (K * m l)) :
    ‖∫ l in Ioo (0 : ℝ) 1, G l‖ₑ ≤ K * ∫⁻ l in Ioo (0 : ℝ) 1, p l * m l := by
  refine (enorm_integral_le_lintegral_enorm G).trans ?_
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ‖G l‖ₑ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, p l * (K * m l) :=
        setLIntegral_mono' measurableSet_Ioo h
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, K * (p l * m l) := lintegral_congr fun l => by ring
    _ = K * ∫⁻ l in Ioo (0 : ℝ) 1, p l * m l := lintegral_const_mul' K _ hK

/-- The masked negative response is bounded by the positive majorant (one component). -/
private lemma fpm_sepW_enorm_le {C0 : ℝ}
    (hC : ∀ (t : ℝ), 0 < t → ∀ (x : UnforcedLeray.Space), x ≠ 0 → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x
        (UnforcedLeray.coordinateVector k)‖ ≤ |C0| * ‖x‖ ^ (-4 : ℝ))
    (ν μ R δ s : ℝ) (hν : 0 < ν)
    (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : UnforcedLeray.Space) (τ : ℝ) (i : Fin 3) :
    ‖UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ)
        (fun τ' (z : UnforcedLeray.Space) =>
          if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then T τ' z else 0) y τ i‖ₑ
      ≤ ENNReal.ofReal (18 * |C0|) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : UnforcedLeray.Space,
            (if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
              ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ)) *
                UnforcedLeray.Short.IIIa.srcNorm T (τ + 2 * Real.log l) z
            else 0) := by
  unfold UnforcedLeray.Short.IIIa.sepW
  dsimp only
  have h2 : ‖(-2 : ℂ)‖ₑ = 2 := by
    rw [fpm_enorm_eq]
    norm_num
  have h18 : ENNReal.ofReal (18 * |C0|) = 2 * ENNReal.ofReal (9 * |C0|) := by
    rw [show (18 : ℝ) * |C0| = 2 * (9 * |C0|) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [enorm_mul, h2, h18, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine fpm_lbound _ ENNReal.ofReal_ne_top _ (fun l => ENNReal.ofReal (l ^ (2 * μ + 2))) _ ?_
  intro l hl
  have hpow : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ₑ = ENNReal.ofReal (l ^ (2 * μ + 2)) := by
    have hre : (2 * (μ : ℂ) + 2).re = 2 * μ + 2 := by simp
    rw [fpm_enorm_eq, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, hre]
  rw [enorm_mul, hpow]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine fpm_zbound _ ENNReal.ofReal_ne_top _ _ (l⁻¹ • y) ?_
  intro z hz
  have hw : y - l • z ≠ 0 := by
    intro h0
    apply hz
    have h1 : l • z = y := (sub_eq_zero.mp h0).symm
    rw [← h1, smul_smul, inv_mul_cancel₀ hl.1.ne', one_smul]
  by_cases hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · simp only [if_pos hm]
    have hterm : ∀ j k : Fin 3,
        ‖((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
            (y - l • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖
          ≤ |C0| * ‖y - l • z‖ ^ (-4 : ℝ) * UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
      intro j k
      rw [norm_mul, Complex.norm_real, Complex.norm_real]
      exact mul_le_mul
        (hC (ν * (1 - l ^ 2)) (mul_pos hν (by nlinarith [hl.1, hl.2])) (y - l • z) hw i j k)
        (fpm_entry _ j k) (norm_nonneg _) (by positivity)
    have hsum := fpm_sum9 _ _ hterm
    have key : ENNReal.ofReal (9 * (|C0| * ‖y - l • z‖ ^ (-4 : ℝ) *
        UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) =
        ENNReal.ofReal (9 * |C0|) * (ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ)) *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖y - l • z‖ ^ (-4 : ℝ)),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 * |C0|)]
      congr 1
      ring
    rw [fpm_enorm_eq]
    unfold UnforcedLeray.Short.IIIa.srcNorm
    refine le_of_le_of_eq (ENNReal.ofReal_le_ofReal hsum) ?_
    exact key
  · simp only [if_neg hm]
    simp

/-- **The pointwise majorant of the far part.** -/
theorem farPointwiseMajorant_of (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) :
    FarPointwiseMajorant := by
  obtain ⟨C0, hC0⟩ := hK 0
  have hC : ∀ (t : ℝ), 0 < t → ∀ (x : UnforcedLeray.Space), x ≠ 0 → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x
        (UnforcedLeray.coordinateVector k)‖ ≤ |C0| * ‖x‖ ^ (-4 : ℝ) := by
    intro t ht x hx i j k
    exact (fpm_coord_bound C0 t x i j k ((hC0 x hx i j).1 t ht)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity))
  unfold FarPointwiseMajorant
  refine ⟨36 * |C0|, by positivity, ?_⟩
  intro R c ν δ S μ hν f x
  by_cases hxS : x.1 < S
  · have hW : ∀ i : Fin 3,
        ‖(-sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x)) i‖ₑ
          ≤ ENNReal.ofReal (18 * |C0|) * farMajE R c δ μ f x := by
      intro i
      rw [Pi.neg_apply, fpm_enorm_neg]
      exact fpm_sepW_enorm_le hC ν μ R δ x.1 hν (cartLift R c f) (chartY R x) (chartTau R x) i
    have hmerRe : ‖merRe (-sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x)
        (chartTau R x))‖ₑ ≤ ENNReal.ofReal (36 * |C0|) * farMajE R c δ μ f x := by
      refine (fpm_merRe_enorm_le _).trans ?_
      refine (add_le_add (hW 0) (hW 2)).trans (le_of_eq ?_)
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 18 * |C0|)
        (by positivity : (0 : ℝ) ≤ 18 * |C0|),
        show 18 * |C0| + 18 * |C0| = 36 * |C0| by ring]
    rw [farOut, if_pos hxS, enorm_smul,
      Real.enorm_eq_ofReal (by positivity : (0 : ℝ) ≤ (Real.sqrt x.1)⁻¹)]
    refine (mul_le_mul_of_nonneg_left hmerRe zero_le).trans (le_of_eq ?_)
    ring
  · rw [farOut, if_neg hxS]
    simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
