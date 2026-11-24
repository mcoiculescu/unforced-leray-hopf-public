import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.SigmaToLambda
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# `PDX0RepIntegrable` (`PartIII-b:C/rep/5/1/2/4/1/2/7/1`)

Source `the November 2 reference manuscript` 3604-3617, 3708, 4171.
Kernel bound `IIIa.sepKernelBounds` (`j = 0`) and the jointly measurable derivative `T8_1.Gm`
give the pointwise majorants of `sepPhi` and of `xKer`; `pdSigmaToLambda` turns the finite
`σ`-form moment into the finite `l`-form majorant on `sepRho`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Elementary bounds -/

lemma abs_entry_le_tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm
  apply Real.abs_le_sqrt
  have h1 : M j k ^ 2 ≤ ∑ j', M j j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M j j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : ∑ j', M j j' ^ 2 ≤ ∑ i, ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j', M i j' ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  linarith

lemma tensorNorm_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ IIIa.tensorNorm M :=
  Real.sqrt_nonneg _

lemma sum_entry_bound_complex (a : Fin 3 → Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (A : ℝ)
    (hA : 0 ≤ A) (ha : ∀ j k, |a j k| ≤ A) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖
      ≤ 9 * A * IIIa.tensorNorm M := by
  have hterm : ∀ j k, ‖((a j k : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖ ≤ A * IIIa.tensorNorm M := fun j k => by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ha j k) (abs_entry_le_tensorNorm M j k) (abs_nonneg _) hA
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖
      ≤ ∑ j : Fin 3, ‖∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖((a j k : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, A * IIIa.tensorNorm M :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = 9 * A * IIIa.tensorNorm M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

lemma sum_entry_bound_real (a : Fin 3 → Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (A : ℝ)
    (hA : 0 ≤ A) (ha : ∀ j k, |a j k| ≤ A) :
    |∑ j : Fin 3, ∑ k : Fin 3, a j k * M j k| ≤ 9 * A * IIIa.tensorNorm M := by
  have hterm : ∀ j k, |a j k * M j k| ≤ A * IIIa.tensorNorm M := fun j k => by
    rw [abs_mul]
    exact mul_le_mul (ha j k) (abs_entry_le_tensorNorm M j k) (abs_nonneg _) hA
  calc |∑ j : Fin 3, ∑ k : Fin 3, a j k * M j k|
      ≤ ∑ j : Fin 3, |∑ k : Fin 3, a j k * M j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |a j k * M j k| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, A * IIIa.tensorNorm M :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = 9 * A * IIIa.tensorNorm M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

lemma norm_space_le (v : Space) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i : Fin 3, |v i| ≤ B) :
    ‖v‖ ≤ 3 * B := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have q0 : v 0 ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg (v 0), sq_abs (v 0)]
  have q1 : v 1 ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg (v 1), sq_abs (v 1)]
  have q2 : v 2 ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg (v 2), sq_abs (v 2)]
  nlinarith

lemma varrho_smul_pos (l : ℝ) (hl0 : 0 < l) (z : Space) : ϱ (l • z) = l * ϱ z := by
  rw [ϱ_smul, abs_of_pos hl0]

lemma pdLam_pos (h : ℝ) : 0 < pdLam h := Real.exp_pos _

lemma pdLam_lt_one (h : ℝ) (hh : 0 < h) : pdLam h < 1 := by
  unfold pdLam
  rw [Real.exp_lt_one_iff]
  linarith

lemma pdLam_log (τ l : ℝ) (hl : 0 < l) : pdLam (τ - (τ + 2 * Real.log l)) = l := by
  unfold pdLam
  rw [show -((τ - (τ + 2 * Real.log l)) / 2) = Real.log l by ring]
  exact Real.exp_log hl

/-- The kernel bound at `j = 0`: `|Gm| ≤ C |w|^{-4}` off the origin, uniformly in `t > 0`. -/
lemma gm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t → ∀ (w : Space), w ≠ 0 →
    ∀ (i j k : Fin 3), |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹ := by
  obtain ⟨C, hC⟩ := IIIa.sepKernelBounds 0
  refine ⟨|C|, abs_nonneg _, fun t ht w hw i j k => ?_⟩
  rw [T8_1.Gm_eq k i j t hw]
  have hk := (hC w hw i j).1 t ht
  simp only [Nat.cast_zero, sub_zero] at hk
  have hpow : ‖w‖ ^ (-4 : ℝ) = (‖w‖ ^ 4)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _)]
    congr 1
    exact_mod_cast Real.rpow_natCast ‖w‖ 4
  rw [hpow] at hk
  have hop := ContinuousLinearMap.le_opNorm
    (fderiv ℝ (fun y => IIIa.heatLerayK t i j y) w) (coordinateVector k)
  have hcv : ‖coordinateVector k‖ = 1 := by
    simp [coordinateVector, PiLp.norm_single]
  rw [norm_iteratedFDeriv_one] at hk
  have hC' : C ≤ |C| := le_abs_self C
  have hinv : 0 ≤ (‖w‖ ^ 4)⁻¹ := by positivity
  calc |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) w (coordinateVector k)|
      = ‖fderiv ℝ (fun y => IIIa.heatLerayK t i j y) w (coordinateVector k)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fun y => IIIa.heatLerayK t i j y) w‖ * ‖coordinateVector k‖ := hop
    _ = ‖fderiv ℝ (fun y => IIIa.heatLerayK t i j y) w‖ := by rw [hcv, mul_one]
    _ ≤ C * (‖w‖ ^ 4)⁻¹ := hk
    _ ≤ |C| * (‖w‖ ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hC' hinv

/-- On the support, a receiver on the ray `x = l • z` (`0 < l < 1`) forces the tensor to vanish. -/
lemma zero_of_eq {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {x z : Space} {l : ℝ}
    (hsupp : ∀ σ z', T σ z' ≠ 0 → ϱ z' < ϱ x) (hl0 : 0 < l) (hl1 : l < 1) (hx : x = l • z)
    (σ : ℝ) : T σ z = 0 := by
  by_contra hne
  have h1 := hsupp σ z hne
  rw [hx, varrho_smul_pos l hl0] at h1
  have h2 : 0 ≤ ϱ z := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.2 hl1.le) h2]

lemma sepPhi_eq_gm {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (ν : ℝ) (μ' : ℂ) (τ : ℝ)
    (i : Fin 3) {x z : Space} {l : ℝ}
    (hsupp : ∀ σ z', T σ z' ≠ 0 → ϱ z' < ϱ x) (hl0 : 0 < l) (hl1 : l < 1) :
    sepPhi ν μ' T τ i (l, z) x =
      -2 * (l : ℂ) ^ (2 * μ' + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
  unfold sepPhi
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hw : x - l • z = 0
  · have hx : x = l • z := sub_eq_zero.mp hw
    rw [zero_of_eq hsupp hl0 hl1 hx (τ + 2 * Real.log l)]
    simp
  · rw [T8_1.Gm_eq k i j (ν * (1 - l ^ 2)) hw]

lemma xKer_apply (ν μ h : ℝ) (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    xKer ν μ h x M i = -(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5)) *
      ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - pdLam h ^ 2)) i j x') x
          (coordinateVector k) * M j k := by
  simp only [xKer, gradKCon, PiLp.smul_apply, smul_eq_mul]

/-! ## 2. The integrands as jointly measurable functions -/

lemma measurable_tensorNorm_comp {α : Type*} [MeasurableSpace α] (F : α → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun a => F a i j) : Measurable fun a => IIIa.tensorNorm (F a) := by
  unfold IIIa.tensorNorm
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hF i j).pow_const 2)

/-- The majorant `E_{e0}(e) = ofReal(λ^{e0} |x - λ z|^{-4}) · |T(e)|`, `λ = pdLam(τ - e.1)`. -/
def phiE (e0 : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (x : Space)
    (e : ℝ × Space) : ℝ≥0∞ :=
  ENNReal.ofReal (pdLam (τ - e.1) ^ e0 * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) *
    IIIa.srcNorm T e.1 e.2

lemma phiE_measurable (e0 : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space) :
    Measurable (phiE e0 T τ x) := by
  have hlam : Measurable fun e : ℝ × Space => pdLam (τ - e.1) := by
    unfold pdLam; fun_prop
  have h1 : Measurable fun e : ℝ × Space =>
      ENNReal.ofReal (pdLam (τ - e.1) ^ e0 * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) :=
    Measurable.ennreal_ofReal ((hlam.pow_const e0).mul
      ((((measurable_const.sub (hlam.smul measurable_snd)).norm).pow_const 4).inv))
  have h2 : Measurable fun e : ℝ × Space => IIIa.srcNorm T e.1 e.2 :=
    Measurable.ennreal_ofReal (measurable_tensorNorm_comp (fun e : ℝ × Space => T e.1 e.2) hTm)
  exact h1.mul h2

/-- `phiE` at the `l`-coordinates `e = (τ + 2 log l, z)`. -/
lemma phiE_log (e0 : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (x z : Space)
    (l : ℝ) (hl : 0 < l) :
    phiE e0 T τ x (τ + 2 * Real.log l, z) =
      ENNReal.ofReal (l ^ e0 * (‖x - l • z‖ ^ 4)⁻¹) * IIIa.srcNorm T (τ + 2 * Real.log l) z := by
  unfold phiE
  simp only [pdLam_log τ l hl]

/-- The `σ`-form hypothesis integrand equals the `sepRho`-transferred `phiE` integrand. -/
lemma sigma_hyp_eq (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (x : Space) :
    ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) *
        phiE (2 * μ + 2) T τ x e =
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) * IIIa.srcNorm T e.1 e.2 := by
  refine lintegral_congr fun e => ?_
  by_cases h : e.1 < τ
  · have hl0 := pdLam_pos (τ - e.1)
    simp only [h, ↓reduceIte, phiE]
    rw [show 2 * μ + 3 = (2 * μ + 2) + 1 by ring, Real.rpow_add_one hl0.ne']
    have hk : ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 2) * pdLam (τ - e.1) *
        (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) =
        ENNReal.ofReal (pdLam (τ - e.1)) *
          ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 2) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) := by
      rw [← ENNReal.ofReal_mul hl0.le]
      congr 1
      ring
    rw [hk, mul_assoc]
  · simp [h]

/-- The `σ`-form moment gives the finiteness of the `l`-form majorant. -/
lemma phiE_lintegral_finite (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) * IIIa.srcNorm T e.1 e.2 < ⊤) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, phiE (2 * μ + 2) T τ x (τ + 2 * Real.log l, z) < ⊤ := by
  have hP := pdSigmaToLambda τ (phiE (2 * μ + 2) T τ x) (phiE_measurable _ T hTm τ x)
  rw [sigma_hyp_eq μ T τ x] at hP
  have h2I : 2 * ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, phiE (2 * μ + 2) T τ x (τ + 2 * Real.log l, z)
      < ⊤ := by
    rw [← hP]; exact hfin
  refine lt_top_iff_ne_top.2 fun h => ?_
  rw [h, ENNReal.mul_top (by norm_num)] at h2I
  exact lt_irrefl _ h2I

/-! ## 3. Pointwise bounds -/

/-- The `sepPhi` pointwise bound on the `l`-slice `0 < l < 1`. -/
lemma norm_sepPhi_le {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (ν : ℝ) (hν : 0 < ν) (m : ℂ)
    (τ : ℝ) (i : Fin 3) (x z : Space) (l : ℝ)
    (hsupp : ∀ σ z', T σ z' ≠ 0 → ϱ z' < ϱ x) (hl0 : 0 < l) (hl1 : l < 1)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, 0 < t → ∀ w, w ≠ 0 → ∀ i j k, |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹) :
    ‖sepPhi ν m T τ i (l, z) x‖ ≤
      2 * (9 * C * (‖x - l • z‖ ^ 4)⁻¹ * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
        l ^ (2 * m + 2).re := by
  rw [sepPhi_eq_gm ν m τ i hsupp hl0 hl1]
  by_cases hw : x - l • z = 0
  · have hT := zero_of_eq hsupp hl0 hl1 (sub_eq_zero.mp hw) (τ + 2 * Real.log l)
    rw [hT]
    simp [hw]
  · have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith)
    have hA := sum_entry_bound_complex
      (fun j k => T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z)) (T (τ + 2 * Real.log l) z)
      (C * (‖x - l • z‖ ^ 4)⁻¹) (mul_nonneg hC0 (inv_nonneg.2 (pow_nonneg (norm_nonneg _) 4)))
      (fun j k => hC _ ht (x - l • z) hw i j k)
    have hl := Complex.norm_cpow_eq_rpow_re_of_pos hl0 (2 * m + 2)
    have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, h2, hl]
    have hnn : 0 ≤ l ^ (2 * m + 2).re := Real.rpow_nonneg hl0.le _
    calc 2 * l ^ (2 * m + 2).re *
          ‖∑ j : Fin 3, ∑ k : Fin 3, ((T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) : ℝ) : ℂ) *
            ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)‖
        ≤ 2 * l ^ (2 * m + 2).re * (9 * (C * (‖x - l • z‖ ^ 4)⁻¹) *
            IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 2 * (9 * C * (‖x - l • z‖ ^ 4)⁻¹ * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
            l ^ (2 * m + 2).re := by ring


/-! ## 4. The `xKer` integrand -/

/-- The `i`-th component of the `xKer` integrand, with `Gm` in place of `fderiv`. -/
def xKerGm (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (x : Space) (i : Fin 3)
    (e : ℝ × Space) : ℝ :=
  if e.1 < τ then -(pdLam (τ - e.1) ^ (2 * μ + 3) - pdLam (τ - e.1) ^ (2 * μ + 5)) *
    ∑ j : Fin 3, ∑ k : Fin 3,
      T8_1.Gm k i j (ν * (1 - pdLam (τ - e.1) ^ 2), x - pdLam (τ - e.1) • e.2) * T e.1 e.2 j k
  else 0

lemma xKerGm_eq (ν μ τ : ℝ) (x : Space) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ x) (e : ℝ × Space) :
    (if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0) =
      WithLp.toLp 2 (fun i => xKerGm ν μ T τ x i e) := by
  by_cases h : e.1 < τ
  · have hl0 := pdLam_pos (τ - e.1)
    have hl1 := pdLam_lt_one (τ - e.1) (by linarith)
    rw [if_pos h]
    ext i
    rw [xKer_apply]
    simp only [xKerGm, if_pos h, PiLp.toLp_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hw : x - pdLam (τ - e.1) • e.2 = 0
    · have hM := zero_of_eq hsupp hl0 hl1 (sub_eq_zero.mp hw) e.1
      rw [hM]
      simp
    · rw [T8_1.Gm_eq k i j _ hw]
  · rw [if_neg h]
    ext i
    simp [xKerGm, h]

lemma xKerGm_measurable (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space) (i : Fin 3) :
    Measurable (fun e => xKerGm ν μ T τ x i e) := by
  have hlam : Measurable fun e : ℝ × Space => pdLam (τ - e.1) := by
    unfold pdLam; fun_prop
  have hτ1 : Measurable fun e : ℝ × Space => ν * (1 - pdLam (τ - e.1) ^ 2) :=
    measurable_const.mul (measurable_const.sub (hlam.pow_const 2))
  have hx1 : Measurable fun e : ℝ × Space => x - pdLam (τ - e.1) • e.2 :=
    measurable_const.sub (hlam.smul measurable_snd)
  unfold xKerGm
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
  refine Measurable.mul (Measurable.neg ((hlam.pow_const _).sub (hlam.pow_const _))) ?_
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  exact ((T8_1.measurable_Gm k i j).comp (hτ1.prodMk hx1)).mul (hTm j k)

/-- The `Space`-valued `xKer` integrand, as a named function (its `i`-th component is `xKerGm`). -/
def xKerVec (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (x : Space)
    (e : ℝ × Space) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 => xKerGm ν μ T τ x i e)

lemma xKerVec_eq (ν μ τ : ℝ) (x : Space) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ x) (e : ℝ × Space) :
    (if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0) =
      xKerVec ν μ T τ x e :=
  xKerGm_eq ν μ τ x T hsupp e

lemma measurable_xKerVec (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space) :
    Measurable (fun e : ℝ × Space => xKerVec ν μ T τ x e) := by
  unfold xKerVec
  exact (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    (measurable_pi_lambda (fun e : ℝ × Space => fun i : Fin 3 => xKerGm ν μ T τ x i e)
      (fun i => xKerGm_measurable ν μ T hTm τ x i))

lemma norm_xKer_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, 0 < t → ∀ w, w ≠ 0 → ∀ i j k, |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹)
    (ν μ h : ℝ) (hν : 0 < ν) (hl0 : 0 < pdLam h) (hl1 : pdLam h < 1) (w : Space) (hw : w ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖xKer ν μ h w M‖ ≤ 27 * C * pdLam h ^ (2 * μ + 3) * (‖w‖ ^ 4)⁻¹ * IIIa.tensorNorm M := by
  have ht : 0 < ν * (1 - pdLam h ^ 2) := mul_pos hν (by nlinarith)
  have hX : 0 ≤ (‖w‖ ^ 4)⁻¹ := inv_nonneg.2 (pow_nonneg (norm_nonneg _) 4)
  have hlamA : 0 ≤ pdLam h ^ (2 * μ + 3) := Real.rpow_nonneg hl0.le _
  have hc : |-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))| ≤ pdLam h ^ (2 * μ + 3) := by
    have h1 : pdLam h ^ (2 * μ + 5) ≤ pdLam h ^ (2 * μ + 3) :=
      Real.rpow_le_rpow_of_exponent_ge hl0 hl1.le (by linarith)
    have h2 : 0 ≤ pdLam h ^ (2 * μ + 5) := Real.rpow_nonneg hl0.le _
    rw [abs_neg, abs_of_nonneg (by linarith)]
    linarith
  have hS : ∀ i : Fin 3, |∑ j : Fin 3, ∑ k : Fin 3,
      fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - pdLam h ^ 2)) i j x') w
        (coordinateVector k) * M j k| ≤ 9 * (C * (‖w‖ ^ 4)⁻¹) * IIIa.tensorNorm M := by
    intro i
    have e2 : ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun x' => IIIa.heatLerayK (ν * (1 - pdLam h ^ 2)) i j x') w
          (coordinateVector k) * M j k =
        ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - pdLam h ^ 2), w) * M j k :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
        rw [T8_1.Gm_eq k i j _ hw]
    rw [e2]
    exact sum_entry_bound_real (fun j k => T8_1.Gm k i j (ν * (1 - pdLam h ^ 2), w)) M
      (C * (‖w‖ ^ 4)⁻¹) (mul_nonneg hC0 hX) (fun j k => hC _ ht w hw i j k)
  have hv : ‖xKer ν μ h w M‖ ≤
      3 * (pdLam h ^ (2 * μ + 3) * (9 * (C * (‖w‖ ^ 4)⁻¹) * IIIa.tensorNorm M)) := by
    apply norm_space_le _ _
      (mul_nonneg hlamA (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC0 hX))
        (tensorNorm_nonneg M)))
    intro i
    rw [xKer_apply, abs_mul]
    exact mul_le_mul hc (hS i) (abs_nonneg _) hlamA
  calc ‖xKer ν μ h w M‖
      ≤ 3 * (pdLam h ^ (2 * μ + 3) * (9 * (C * (‖w‖ ^ 4)⁻¹) * IIIa.tensorNorm M)) := hv
    _ = 27 * C * pdLam h ^ (2 * μ + 3) * (‖w‖ ^ 4)⁻¹ * IIIa.tensorNorm M := by ring

/-- Pointwise `ℓ`-majorant of the `xKer` integrand (the `ofReal` form used for finiteness). -/
lemma xKer_ite_enorm_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, 0 < t → ∀ w, w ≠ 0 → ∀ i j k, |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹)
    (ν μ τ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (x : Space) (hν : 0 < ν)
    (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ x) (e : ℝ × Space) :
    ‖(if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0)‖ₑ ≤
      ENNReal.ofReal (27 * C) * ((if e.1 < τ then ENNReal.ofReal
        (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm T e.1 e.2) := by
  by_cases h : e.1 < τ
  · rw [if_pos h, if_pos h]
    by_cases hw : x - pdLam (τ - e.1) • e.2 = 0
    · have hM := zero_of_eq hsupp (pdLam_pos (τ - e.1)) (pdLam_lt_one (τ - e.1) (by linarith))
        (sub_eq_zero.mp hw) e.1
      have h0 : xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) = 0 := by
        rw [hM]
        ext i
        simp [xKer_apply]
      rw [h0, enorm_zero]
      exact zero_le
    · have hb := norm_xKer_le hC0 hC ν μ (τ - e.1) hν (pdLam_pos (τ - e.1))
        (pdLam_lt_one (τ - e.1) (by linarith)) _ hw (T e.1 e.2)
      have hlamA : 0 ≤ pdLam (τ - e.1) ^ (2 * μ + 3) := Real.rpow_nonneg (pdLam_pos _).le _
      have hX : 0 ≤ (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ :=
        inv_nonneg.2 (pow_nonneg (norm_nonneg _) 4)
      rw [← ofReal_norm]
      have h27 : (0 : ℝ) ≤ 27 * C := by linarith
      have hpos : 0 ≤ pdLam (τ - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ :=
        mul_nonneg hlamA hX
      have hfac : 27 * C * pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ * IIIa.tensorNorm (T e.1 e.2) =
          (27 * C) * ((pdLam (τ - e.1) ^ (2 * μ + 3) *
            (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) * IIIa.tensorNorm (T e.1 e.2)) := by ring
      calc ENNReal.ofReal ‖xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2)‖
          ≤ ENNReal.ofReal (27 * C * pdLam (τ - e.1) ^ (2 * μ + 3) *
              (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹ * IIIa.tensorNorm (T e.1 e.2)) :=
            ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal (27 * C) * (ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
              (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) * ENNReal.ofReal (IIIa.tensorNorm (T e.1 e.2))) := by
            rw [hfac, ENNReal.ofReal_mul h27, ENNReal.ofReal_mul hpos]
        _ = ENNReal.ofReal (27 * C) * (ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
              (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) * IIIa.srcNorm T e.1 e.2) := rfl
  · rw [if_neg h, if_neg h]
    simp

set_option maxHeartbeats 4000000 in
/-- **The `xKer` integrand is volume-integrable** (the second conjunct of `PDX0RepIntegrable`). -/
lemma integrable_xKer (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space)
    (hν : 0 < ν) (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ x)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) * IIIa.srcNorm T e.1 e.2 < ⊤) :
    Integrable (fun e : ℝ × Space =>
      if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0) volume := by
  obtain ⟨C, hC0, hC⟩ := gm_bound
  have hfun : (fun e : ℝ × Space =>
      if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0) =
      fun e : ℝ × Space => xKerVec ν μ T τ x e := by
    funext e
    by_cases h : e.1 < τ
    · have hl0 := pdLam_pos (τ - e.1)
      have hl1 := pdLam_lt_one (τ - e.1) (by linarith)
      rw [if_pos h]
      unfold xKerVec
      ext i
      rw [xKer_apply]
      simp only [xKerGm, if_pos h, PiLp.toLp_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases hw : x - pdLam (τ - e.1) • e.2 = 0
      · have hM := zero_of_eq hsupp hl0 hl1 (sub_eq_zero.mp hw) e.1
        rw [hM]
        simp
      · rw [T8_1.Gm_eq k i j _ hw]
    · rw [if_neg h]
      unfold xKerVec
      ext i
      simp [xKerGm, h]
  have hmeas : Measurable (fun e : ℝ × Space =>
      if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0) := by
    rw [hfun]
    exact measurable_xKerVec ν μ T hTm τ x
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hstep1 : ∫⁻ e : ℝ × Space, ‖(if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (T e.1 e.2)
          else 0)‖ₑ ∂volume ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal (27 * C) * ((if e.1 < τ then ENNReal.ofReal
          (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
          IIIa.srcNorm T e.1 e.2) ∂volume := by
    apply lintegral_mono
    intro e
    exact xKer_ite_enorm_le hC0 hC ν μ τ T x hν hsupp e
  have hstep2 : ∫⁻ e : ℝ × Space, ENNReal.ofReal (27 * C) * ((if e.1 < τ then ENNReal.ofReal
          (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
          IIIa.srcNorm T e.1 e.2) ∂volume = ENNReal.ofReal (27 * C) * ∫⁻ e : ℝ × Space, (if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
          else 0) * IIIa.srcNorm T e.1 e.2 ∂volume := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hstep2] at hstep1
  exact lt_of_le_of_lt hstep1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-! ## 5. The `sepPhi` integrands and the target -/

set_option maxHeartbeats 4000000 in
lemma integrable_sepPhi (ν μ : ℝ) (m : ℂ) (hm : 2 * μ + 2 ≤ (2 * m + 2).re)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (τ : ℝ) (x : Space)
    (hν : 0 < ν) (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ x)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) * IIIa.srcNorm T e.1 e.2 < ⊤)
    (i : Fin 3) :
    Integrable (fun p => sepPhi ν m T τ i p x) sepRho := by
  obtain ⟨C, hC0, hC⟩ := gm_bound
  have hlogm : Measurable fun p : ℝ × Space => (τ + 2 * Real.log p.1, p.2) := by
    fun_prop
  let G : ℝ × Space → ℂ := fun p => -2 * (p.1 : ℂ) ^ (2 * m + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((T8_1.Gm k i j (ν * (1 - p.1 ^ 2), x - p.1 • p.2) : ℝ) : ℂ) *
          ((T (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)
  have hGm : Measurable G := by
    have h1 : Measurable fun p : ℝ × Space => (p.1 : ℂ) ^ (2 * m + 2) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const _
    refine measurable_const.mul h1 |>.mul ?_
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    have hA : Measurable fun p : ℝ × Space => T8_1.Gm k i j (ν * (1 - p.1 ^ 2), x - p.1 • p.2) :=
      (T8_1.measurable_Gm k i j).comp
        ((measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2))).prodMk
          (measurable_const.sub (measurable_fst.smul measurable_snd)))
    have hB : Measurable fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 j k :=
      (hTm j k).comp hlogm
    exact (Complex.measurable_ofReal.comp hA).mul (Complex.measurable_ofReal.comp hB)
  have hae : (fun p => sepPhi ν m T τ i p x) =ᵐ[sepRho] G := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp
    exact sepPhi_eq_gm ν m τ i hsupp hp.1 hp.2
  have hfinE := phiE_lintegral_finite μ T hTm τ x hfin
  have hphim : Measurable fun p : ℝ × Space => phiE (2 * μ + 2) T τ x (τ + 2 * Real.log p.1, p.2) :=
    (phiE_measurable _ T hTm τ x).comp hlogm
  refine ⟨(hGm.aestronglyMeasurable.congr hae.symm), ?_⟩
  unfold HasFiniteIntegral
  have hb : ∀ᵐ p ∂sepRho, ‖sepPhi ν m T τ i p x‖ₑ ≤
      ENNReal.ofReal (18 * C) * phiE (2 * μ + 2) T τ x (τ + 2 * Real.log p.1, p.2) := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp
    obtain ⟨hl0, hl1⟩ := hp
    have hn := norm_sepPhi_le ν hν m τ i x p.2 p.1 hsupp hl0 hl1 C hC0 hC
    rw [← ofReal_norm]
    have hpow : p.1 ^ (2 * m + 2).re ≤ p.1 ^ (2 * μ + 2) :=
      Real.rpow_le_rpow_of_exponent_ge hl0 hl1.le hm
    have hnn : 0 ≤ (‖x - p.1 • p.2‖ ^ 4)⁻¹ := inv_nonneg.2 (pow_nonneg (norm_nonneg _) 4)
    have htn := tensorNorm_nonneg (T (τ + 2 * Real.log p.1) p.2)
    have hpos : 0 ≤ p.1 ^ (2 * μ + 2) * (‖x - p.1 • p.2‖ ^ 4)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hl0.le _) hnn
    have hle : ‖sepPhi ν m T τ i p x‖ ≤
        18 * C * (p.1 ^ (2 * μ + 2) * (‖x - p.1 • p.2‖ ^ 4)⁻¹) *
          IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := by
      refine hn.trans ?_
      have hA : 0 ≤ 2 * (9 * C * (‖x - p.1 • p.2‖ ^ 4)⁻¹ *
          IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by positivity
      calc _ ≤ 2 * (9 * C * (‖x - p.1 • p.2‖ ^ 4)⁻¹ *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) * p.1 ^ (2 * μ + 2) :=
            mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by ring
    have h18 : (0 : ℝ) ≤ 18 * C := by linarith
    calc ENNReal.ofReal ‖sepPhi ν m T τ i p x‖
        ≤ ENNReal.ofReal (18 * C * (p.1 ^ (2 * μ + 2) * (‖x - p.1 • p.2‖ ^ 4)⁻¹) *
            IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (18 * C) * phiE (2 * μ + 2) T τ x (τ + 2 * Real.log p.1, p.2) := by
          rw [phiE_log _ T τ x p.2 p.1 hl0, mul_assoc, ENNReal.ofReal_mul h18,
            ENNReal.ofReal_mul hpos]
          rfl
  calc ∫⁻ p, ‖sepPhi ν m T τ i p x‖ₑ ∂sepRho
      ≤ ∫⁻ p, ENNReal.ofReal (18 * C) *
          phiE (2 * μ + 2) T τ x (τ + 2 * Real.log p.1, p.2) ∂sepRho := lintegral_mono_ae hb
    _ = ENNReal.ofReal (18 * C) * ∫⁻ p,
          phiE (2 * μ + 2) T τ x (τ + 2 * Real.log p.1, p.2) ∂sepRho :=
        lintegral_const_mul _ hphim
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        unfold sepRho
        rw [lintegral_prod _ hphim.aemeasurable]
        exact hfinE

theorem pdX0RepIntegrable : PDX0RepIntegrable := by
  intro ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin
  have hTm : ∀ i j, Measurable fun s : ℝ × Space => oldPhys R c g s.1 s.2 i j :=
    fun i j => T8_1.measurable_oldPhys_entry R c g hg i j
  refine ⟨fun i => ⟨?_, ?_⟩, integrable_xKer ν μ _ hTm τ x hν hsupp hfin⟩
  · exact integrable_sepPhi ν μ (μ : ℂ) (by simp) _ hTm τ x hν hsupp hfin i
  · refine integrable_sepPhi ν μ ((μ : ℂ) + 1) ?_ _ hTm τ x hν hsupp hfin i
    simp

end UnforcedLeray.Short.PartIIIb.Concrete

end
