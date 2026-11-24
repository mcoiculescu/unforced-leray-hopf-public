import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14

/-!
# `farOutMajorant` (source 3604-3610, 3611-3621, 3996-4011)

Pointwise positive majorant of the far kernel output.  The kernel bound `sep:kernel` (`j = 0`)
gives `|∂_k K_{ij}(x)| ≤ C |x|^{-4}` for `x ≠ 0`, uniformly in `t > 0`; the Bochner integrals of
`sepW` are dominated by their absolute integrals (`enorm_integral_le_lintegral_enorm`), and the
masked integrand is the indicator of `farMaj`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

lemma farMaj_entry_le (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  apply Real.abs_le_sqrt
  calc M j k ^ 2 ≤ ∑ l : Fin 3, M j l ^ 2 :=
        Finset.single_le_sum (f := fun l => M j l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, M i l ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ l : Fin 3, M i l ^ 2)
          (fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ j)

lemma farMaj_tensorNorm_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  exact Real.sqrt_nonneg _

lemma farMaj_tensorNorm_zero :
    UnforcedLeray.Short.IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  simp

lemma farMaj_sum_bound (A B : ℝ) (a b : Fin 3 → Fin 3 → ℝ)
    (ha : ∀ j k, |a j k| ≤ A) (hb : ∀ j k, |b j k| ≤ B) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((b j k : ℝ) : ℂ)‖ ≤ 9 * (A * B) := by
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((b j k : ℝ) : ℂ)‖
      ≤ ∑ j : Fin 3, ‖∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((b j k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖((a j k : ℝ) : ℂ) * ((b j k : ℝ) : ℂ)‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, A * B :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (ha j k) (hb j k) (abs_nonneg _) (le_trans (abs_nonneg _) (ha j k))
    _ = 9 * (A * B) := by simp; ring

lemma farMaj_kernel_bound (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, x ≠ 0 → ∀ t : ℝ, 0 < t → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)‖
        ≤ C * ‖x‖ ^ (-4 : ℝ) := by
  obtain ⟨C, hC⟩ := hK 0
  refine ⟨|C|, abs_nonneg _, fun x hx t ht i j k => ?_⟩
  have h1 : ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x‖
      ≤ C * ‖x‖ ^ (-4 : ℝ) := by
    simpa using (hC x hx i j).1 t ht
  have h2 := (fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x).le_opNorm
    (coordinateVector k)
  have hk1 : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
  rw [hk1, mul_one] at h2
  refine h2.trans (h1.trans ?_)
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

lemma farMaj_merRe_norm_le (w : Fin 3 → ℂ) :
    ‖merRe w‖ ≤ ‖w 0‖ + ‖w 2‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [merRe, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Real.norm_eq_abs, sq_abs]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h0 : (w 0).re ^ 2 ≤ ‖w 0‖ ^ 2 := by
    have := Complex.abs_re_le_norm (w 0)
    nlinarith [abs_nonneg (w 0).re, sq_abs (w 0).re, norm_nonneg (w 0)]
  have h2 : (w 2).re ^ 2 ≤ ‖w 2‖ ^ 2 := by
    have := Complex.abs_re_le_norm (w 2)
    nlinarith [abs_nonneg (w 2).re, sq_abs (w 2).re, norm_nonneg (w 2)]
  nlinarith [mul_nonneg (norm_nonneg (w 0)) (norm_nonneg (w 2))]

/-- The `z`-integral of one `sepW` integrand (the `l`-slice). -/
def farMajWz (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ)
    (i : Fin 3) (l : ℝ) : ℂ :=
  ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
      (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)

/-- The `z`-slice bound. -/
lemma farMaj_Wz_bound (C0 ν : ℝ) (hC0 : 0 ≤ C0) (hν : 0 < ν)
    (hk : ∀ x : Space, x ≠ 0 → ∀ t : ℝ, 0 < t → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)‖
        ≤ C0 * ‖x‖ ^ (-4 : ℝ))
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ) (i : Fin 3) (l : ℝ)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal ‖farMajWz ν T y τ i l‖ ≤
      ENNReal.ofReal (9 * C0) * ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
        UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
  obtain ⟨hl0, hl1⟩ := hl
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith)
  have hae : ∀ᵐ z ∂(volume : Measure Space), y - l • z ≠ 0 := by
    filter_upwards [(Set.countable_singleton (l⁻¹ • y)).ae_notMem (volume : Measure Space)]
      with z hz h
    apply hz
    have h' : y = l • z := sub_eq_zero.mp h
    rw [Set.mem_singleton_iff, h', smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
  have hpt : ∀ z : Space, y - l • z ≠ 0 →
      ‖∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z) (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖
        ≤ 9 * (C0 * ‖y - l • z‖ ^ (-4 : ℝ) *
          UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
    intro z hz
    refine farMaj_sum_bound (C0 * ‖y - l • z‖ ^ (-4 : ℝ))
      (UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))
      (fun j k => fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
        (y - l • z) (coordinateVector k))
      (fun j k => T (τ + 2 * Real.log l) z j k) ?_ ?_
    · intro j k
      have := hk (y - l • z) hz (ν * (1 - l ^ 2)) ht i j k
      rwa [Real.norm_eq_abs] at this
    · intro j k
      exact farMaj_entry_le _ j k
  have hnorm : ENNReal.ofReal ‖farMajWz ν T y τ i l‖ ≤
      ∫⁻ z : Space, ENNReal.ofReal (9 * C0) * ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
        UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
    rw [ofReal_norm]
    unfold farMajWz
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with z hz
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 9 * C0 by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 ≤ ‖y - l • z‖ ^ (-4 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hp := hpt z hz
    calc _ ≤ _ := hp
      _ = 9 * C0 * (‖y - l • z‖ ^ (-4 : ℝ) *
          UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by ring
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hnorm
  exact hnorm

lemma farMaj_sepW_bound (C0 ν : ℝ) (hC0 : 0 ≤ C0) (hν : 0 < ν)
    (hk : ∀ x : Space, x ≠ 0 → ∀ t : ℝ, 0 < t → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)‖
        ≤ C0 * ‖x‖ ^ (-4 : ℝ))
    (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ) (i : Fin 3) :
    ENNReal.ofReal ‖UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T y τ i‖ ≤
      ENNReal.ofReal (2 * (9 * C0)) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
            UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
  have hsep : UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T y τ i =
      -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * farMajWz ν T y τ i l := rfl
  rw [hsep]
  have hI : ENNReal.ofReal ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
      farMajWz ν T y τ i l‖ ≤
      ENNReal.ofReal (9 * C0) * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
        ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
          UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) := by
    rw [ofReal_norm]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
    have hp : (2 * (μ : ℂ) + 2).re = 2 * μ + 2 := by simp
    rw [← ofReal_norm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, hp,
      ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
    have hz := farMaj_Wz_bound C0 ν hC0 hν hk T y τ i l hl
    calc ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal ‖farMajWz ν T y τ i l‖
        ≤ ENNReal.ofReal (l ^ (2 * μ + 2)) * (ENNReal.ofReal (9 * C0) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
            UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) := by
          gcongr
      _ = _ := by ring
  have h2 : ‖(-2 : ℂ) * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
      farMajWz ν T y τ i l‖ = 2 * ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
        farMajWz ν T y τ i l‖ := by
    rw [norm_mul]; norm_num
  rw [h2, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  calc ENNReal.ofReal 2 * ENNReal.ofReal ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
        farMajWz ν T y τ i l‖
      ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (9 * C0) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
            UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- The masked integrand of `farMaj` is the `sepW` integrand of the indicator-masked tensor. -/
lemma farMaj_eq_masked (R c μ δ : ℝ) (f : Chart → Ten3) (x : Chart) :
    farMaj R c μ δ f x = ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
      ∫⁻ z : Space, ENNReal.ofReal (‖chartY R x - l • z‖ ^ (-4 : ℝ) *
        UnforcedLeray.Short.IIIa.tensorNorm
          ((fun τ' z' => if Real.exp δ * x.1 < R ^ 2 / (z' 0 ^ 2 + z' 1 ^ 2)
            then cartLift R c f τ' z' else 0) (chartTau R x + 2 * Real.log l) z)) := by
  unfold farMaj
  refine lintegral_congr fun l => ?_
  congr 1
  refine lintegral_congr fun z => ?_
  by_cases hc : Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · simp [hc]
  · simp [hc, UnforcedLeray.Short.IIIa.tensorNorm]

/-- **Pointwise positive majorant** (source 3604-3610, 3996-4011). -/
theorem farOutMajorant : FarOutMajorant := by
  intro hK R c ν δ S μ hR hc hν hδ hS hμ
  obtain ⟨C0, hC0, hk⟩ := farMaj_kernel_bound hK
  refine ⟨36 * C0, by positivity, fun f _hf x => ?_⟩
  have hW : ∀ i : Fin 3, ENNReal.ofReal ‖sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f)
      (chartY R x) (chartTau R x) i‖ ≤ ENNReal.ofReal (2 * (9 * C0)) * farMaj R c μ δ f x := by
    intro i
    rw [farMaj_eq_masked R c μ δ f x]
    exact farMaj_sepW_bound C0 ν hC0 hν hk μ
      (fun τ' z => if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then cartLift R c f τ' z else 0)
      (chartY R x) (chartTau R x) i
  unfold farOut farMajOut
  by_cases hx : x.1 < S
  · rw [if_pos hx, if_pos hx]
    set W := sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x) with hWdef
    have hsqrt : 0 ≤ (Real.sqrt x.1)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [norm_smul, Real.norm_of_nonneg hsqrt, ENNReal.ofReal_mul hsqrt]
    have hm : ENNReal.ofReal ‖merRe (-W)‖ ≤
        2 * (ENNReal.ofReal (2 * (9 * C0)) * farMaj R c μ δ f x) := by
      calc ENNReal.ofReal ‖merRe (-W)‖
          ≤ ENNReal.ofReal (‖(-W) 0‖ + ‖(-W) 2‖) :=
            ENNReal.ofReal_le_ofReal (farMaj_merRe_norm_le _)
        _ ≤ ENNReal.ofReal ‖(-W) 0‖ + ENNReal.ofReal ‖(-W) 2‖ := ENNReal.ofReal_add_le
        _ ≤ _ := by
          rw [Pi.neg_apply, Pi.neg_apply, norm_neg, norm_neg, two_mul]
          exact add_le_add (hW 0) (hW 2)
    calc ENNReal.ofReal (Real.sqrt x.1)⁻¹ * ENNReal.ofReal ‖merRe (-W)‖
        ≤ ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          (2 * (ENNReal.ofReal (2 * (9 * C0)) * farMaj R c μ δ f x)) := by gcongr
      _ = ENNReal.ofReal (36 * C0) * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMaj R c μ δ f x) := by
        have e : ENNReal.ofReal (36 * C0) = 2 * ENNReal.ofReal (2 * (9 * C0)) := by
          rw [show (36 * C0) = 2 * (2 * (9 * C0)) by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        rw [e]
        ring
  · rw [if_neg hx, if_neg hx, norm_zero, ENNReal.ofReal_zero]
    exact zero_le

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
