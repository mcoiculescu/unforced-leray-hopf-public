import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.SepDomFacts
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L5_FDerivBound

/-!
# Dominated convergence for the far truncations (organizer `ORG:C-review/far-bridge/1`)

Proves `FarOutTruncTendsto` (FarBridge.lean) from the separated kernel bounds.  Source of record
`the November 2 reference manuscript` 3604-3621 (`sep:kernel`, `sep:resolvent`) and
3905-3912 (the mask `t > e^δ s`, i.e. `|z'| < e^{-δ/2} R/√s`).

Structure:
1. mask geometry: under the mask, `|y - λz| ≥ D = (1-e^{-δ/2})R/√s` (`ft_mask_gap`);
2. kernel and algebra bound: `|∂K_t| ≤ C|x|^{-4}`, `ft_sum_norm_le`; the majorant `ft_sepMaj`
   is the order-zero gap majorant of `IIIa.sepDom`;
3. inner dominated convergence in `z` (`ft_sepZInt_tendsto`), pointwise by eventual equality of
   the truncated masked sources (`ft_mskT_eventually`);
4. outer dominated convergence in `λ` (`ft_sepW_tendsto`), with `IIIa.sepDom < ⊤` as the
   integrable bound;
5. assembly through `merRe` (`farOutTruncTendsto`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarBridge

/-! ## 1. Mask geometry -/

theorem ft_mask_pos {R δ s : ℝ} (hs : 0 < s) {z : UnforcedLeray.Space}
    (hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) : 0 < z 0 ^ 2 + z 1 ^ 2 := by
  by_contra h
  push_neg at h
  have hz : z 0 ^ 2 + z 1 ^ 2 = 0 := le_antisymm h (by positivity)
  rw [hz, div_zero] at hm
  linarith [mul_pos (Real.exp_pos δ) hs]

/-- The mask forces `|z'| ≤ e^{-δ/2} R/√s`. -/
theorem ft_mask_radius_le {R δ s : ℝ} (hR : 0 < R) (hs : 0 < s) {z : UnforcedLeray.Space}
    (hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) :
    Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp (-(δ / 2)) * R / Real.sqrt s := by
  have hq := ft_mask_pos hs hm
  have hm' : Real.exp δ * s * (z 0 ^ 2 + z 1 ^ 2) < R ^ 2 := (lt_div_iff₀ hq).1 hm
  have hm'' : Real.exp δ * ((z 0 ^ 2 + z 1 ^ 2) * s) < R ^ 2 := by nlinarith [hm']
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have he : Real.exp (-(δ / 2)) ^ 2 = (Real.exp δ)⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hB : 0 ≤ Real.exp (-(δ / 2)) * R / Real.sqrt s := by
    have := Real.exp_pos (-(δ / 2))
    exact div_nonneg (mul_nonneg this.le hR.le) (Real.sqrt_nonneg _)
  have hle : z 0 ^ 2 + z 1 ^ 2 ≤ (Real.exp (-(δ / 2)) * R / Real.sqrt s) ^ 2 := by
    rw [div_pow, mul_pow, he, hsq, le_div_iff₀ hs]
    have hinv := mul_le_mul_of_nonneg_left hm''.le (inv_nonneg.2 (Real.exp_pos δ).le)
    rw [inv_mul_cancel_left₀ (Real.exp_pos δ).ne'] at hinv
    linarith [hinv]
  calc Real.sqrt (z 0 ^ 2 + z 1 ^ 2)
      ≤ Real.sqrt ((Real.exp (-(δ / 2)) * R / Real.sqrt s) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.exp (-(δ / 2)) * R / Real.sqrt s := Real.sqrt_sq hB

/-- The radial gap `|y - λz| ≥ (1 - e^{-δ/2})R/√s` under the mask (`radial_gap`). -/
theorem ft_mask_gap {R δ s : ℝ} (hR : 0 < R) (hs : 0 < s) {y z : UnforcedLeray.Space}
    (hy : R / Real.sqrt s ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    (1 - Real.exp (-(δ / 2))) * R / Real.sqrt s ≤ ‖y - l • z‖ := by
  have h := IIIa.radial_gap y z l (Real.exp (-(δ / 2)) * R / Real.sqrt s) (R / Real.sqrt s) hl
    (ft_mask_radius_le hR hs hm) hy
  have e : (1 - Real.exp (-(δ / 2))) * R / Real.sqrt s =
      R / Real.sqrt s - Real.exp (-(δ / 2)) * R / Real.sqrt s := by ring
  rw [e]
  exact h

theorem ft_chartY_radius {R : ℝ} (hR : 0 < R) (p : Chart) :
    R / Real.sqrt p.1 ≤ Real.sqrt (NearInst.chartY R p 0 ^ 2 + NearInst.chartY R p 1 ^ 2) := by
  have h : NearInst.chartY R p 0 ^ 2 + NearInst.chartY R p 1 ^ 2 = (R / Real.sqrt p.1) ^ 2 := by
    simp [NearInst.chartY]
  exact le_of_eq (by rw [h, Real.sqrt_sq (div_nonneg hR.le (Real.sqrt_nonneg _))])

theorem ft_chartOf_fst (R c : ℝ) (z : UnforcedLeray.Space) (τ : ℝ) :
    (NearInst.chartOf R c z τ).1 = R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) := by
  simp only [NearInst.chartOf, NearInst.hRad]
  rw [Real.sq_sqrt (by positivity)]

/-! ## 2. Kernel and algebra bounds -/

/-- `|∂_{e_k} K_t(x)| ≤ C|x|^{-4}` for `t > 0`, `x ≠ 0` (`sep:kernel`, `j = 0`). -/
theorem ft_kernel_bound (hK : IIIa.SepKernelBounds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x : UnforcedLeray.Space, x ≠ 0 → ∀ i j k : Fin 3,
      |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
        C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) := by
  obtain ⟨C, hC⟩ := hK 0
  refine ⟨|C|, abs_nonneg _, fun t ht x hx i j k => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 1 (fun y => IIIa.heatLerayK t i j y) x‖ ≤
      C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) := (hC x hx i j).1 t ht
  have hv : ‖(coordinateVector k : UnforcedLeray.Space)‖ = 1 := by simp [coordinateVector]
  have hA := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 1 (fun y => IIIa.heatLerayK t i j y) x)
    (fun _ : Fin 1 => (coordinateVector k : UnforcedLeray.Space))
  rw [iteratedFDeriv_one_apply] at hA
  simp only [hv, Finset.prod_const_one, mul_one] at hA
  have h2 : |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
      ‖iteratedFDeriv ℝ 1 (fun y => IIIa.heatLerayK t i j y) x‖ := by
    rw [← Real.norm_eq_abs]
    exact hA
  exact h2.trans (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (Real.rpow_nonneg (norm_nonneg _) _)))

/-- The `9`-term algebra bound for the kernel-times-tensor sum. -/
theorem ft_sum_norm_le (a m : Fin 3 → Fin 3 → ℝ) {A N : ℝ} (ha : ∀ j k, |a j k| ≤ A)
    (hm : ∀ j k, |m j k| ≤ N) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((m j k : ℝ) : ℂ)‖ ≤ 9 * (A * N) := by
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((m j k : ℝ) : ℂ)‖
      ≤ ∑ j : Fin 3, ‖∑ k : Fin 3, ((a j k : ℝ) : ℂ) * ((m j k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖((a j k : ℝ) : ℂ) * ((m j k : ℝ) : ℂ)‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, A * N := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (ha j k) (hm j k) (abs_nonneg _) hA
    _ = 9 * (A * N) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## 3. The masked source and the integrand -/

/-- The source masked to the far region `e^δ s < R²/|z'|²` (source 3905-3912). -/
def ft_mskT (R δ s : ℝ) (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun τ z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then T τ z else 0

theorem ft_sepWfar_eq (ν : ℝ) (μ : ℂ) (R δ s : ℝ)
    (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ) (y : UnforcedLeray.Space) (τ : ℝ) :
    NearInst.sepWfar ν μ R δ s T y τ = IIIa.sepW ν μ (ft_mskT R δ s T) y τ := rfl

theorem ft_mskT_measurable {R δ s : ℝ} {T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ i j, Measurable fun p : ℝ × UnforcedLeray.Space => T p.1 p.2 i j) (i j : Fin 3) :
    Measurable fun p : ℝ × UnforcedLeray.Space => ft_mskT R δ s T p.1 p.2 i j := by
  have hset : MeasurableSet {p : ℝ × UnforcedLeray.Space |
      Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2)} :=
    measurableSet_lt measurable_const (by fun_prop)
  have e : (fun p : ℝ × UnforcedLeray.Space => ft_mskT R δ s T p.1 p.2 i j) =
      fun p => if Real.exp δ * s < R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2) then T p.1 p.2 i j else 0 := by
    funext p
    simp only [ft_mskT]
    split_ifs <;> simp
  rw [e]
  exact Measurable.ite hset (hT i j) measurable_const

/-- The truncated cartLift has entries bounded by the untruncated one. -/
theorem ft_tensorNorm_indicator_le (R c : ℝ) (W : Set Chart) (f : Chart → Ten3)
    (τ : ℝ) (z : UnforcedLeray.Space) :
    IIIa.tensorNorm (NearInst.cartLift R c (W.indicator f) τ z) ≤
      IIIa.tensorNorm (NearInst.cartLift R c f τ z) := by
  rw [cartLift_indicator]
  split_ifs
  · exact le_rfl
  · have h0 : IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      simp [IIIa.tensorNorm]
    rw [h0]
    exact Real.sqrt_nonneg _

/-- Eventually in the truncation index, the masked truncated source equals the masked source. -/
theorem ft_mskT_eventually {R c δ s : ℝ} (hR : 0 < R) (hs : 0 < s) {f : Chart → Ten3}
    {W : ℕ → Set Chart} (hmono : Monotone W) (hcov : ∀ p : Chart, 0 < p.1 → ∃ k, p ∈ W k)
    (τ : ℝ) (z : UnforcedLeray.Space) :
    ∀ᶠ k in atTop, ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f)) τ z =
      ft_mskT R δ s (NearInst.cartLift R c f) τ z := by
  by_cases hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · have hq := ft_mask_pos hs hm
    obtain ⟨k0, hk0⟩ := hcov (NearInst.chartOf R c z τ) (by
      rw [ft_chartOf_fst]
      exact div_pos (pow_pos hR 2) hq)
    refine Filter.eventually_atTop.2 ⟨k0, fun k hk => ?_⟩
    have hmem : NearInst.chartOf R c z τ ∈ W k := hmono hk hk0
    simp only [ft_mskT, if_pos hm, cartLift_indicator, if_pos hmem]
  · exact Filter.Eventually.of_forall fun k => by simp only [ft_mskT, if_neg hm]

/-- The `z`-integrand of `IIIa.sepW` at fixed `(τ, y, λ)`. -/
def ft_sepIntg (ν : ℝ) (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (τ : ℝ) (y : UnforcedLeray.Space) (l : ℝ) (z : UnforcedLeray.Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    ((if 0 < ν * (1 - l ^ 2) then
        fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
          (coordinateVector k) else 0 : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)

theorem ft_sepZInt_eq (ν : ℝ) (T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) (l : ℝ) :
    sepZInt ν T i τ y l = ∫ z, ft_sepIntg ν T i τ y l z := rfl

theorem ft_sepIntg_measurable (ν : ℝ)
    {T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ i j, Measurable fun p : ℝ × UnforcedLeray.Space => T p.1 p.2 i j) (i : Fin 3)
    (τ : ℝ) (y : UnforcedLeray.Space) (l : ℝ) :
    Measurable (fun z => ft_sepIntg ν T i τ y l z) := by
  have hc : Measurable (fun z : UnforcedLeray.Space =>
      ((((τ, y) : ℝ × UnforcedLeray.Space), l), z)) :=
    measurable_const.prodMk measurable_id
  have hsum := (sepSummand_measurable ν T hT i).comp hc
  unfold ft_sepIntg
  exact hsum

/-! ## 4. The majorant -/

/-- The order-zero gap majorant with the constant `9C` of the kernel bound. -/
def ft_sepMaj (C D : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (τ l : ℝ)
    (y z : UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal (9 * C) * (IIIa.sepKd 0 D (y - l • z) * g (τ + 2 * Real.log l) z)

theorem ft_sepMaj_lt_top (C D : ℝ) {g : ℝ → UnforcedLeray.Space → ℝ≥0∞}
    (hgfin : ∀ τ' z, g τ' z < ⊤) (τ l : ℝ) (y z : UnforcedLeray.Space) :
    ft_sepMaj C D g τ l y z < ⊤ := by
  unfold ft_sepMaj
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ (hgfin _ _))
  unfold IIIa.sepKd
  split_ifs <;> simp

theorem ft_sepMaj_joint (C D : ℝ) {g : ℝ → UnforcedLeray.Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ : ℝ) (y : UnforcedLeray.Space) :
    Measurable (fun p : ℝ × UnforcedLeray.Space => ft_sepMaj C D g τ p.1 y p.2) := by
  unfold ft_sepMaj
  refine measurable_const.mul ((((sd_measurable_sepKd 0 D).comp
    (measurable_const.sub (measurable_fst.smul measurable_snd)))).mul ?_)
  exact hg.comp ((measurable_const.add (measurable_const.mul
    (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd)

theorem ft_sepMaj_z (C D : ℝ) {g : ℝ → UnforcedLeray.Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ l : ℝ) (y : UnforcedLeray.Space) :
    Measurable (fun z => ft_sepMaj C D g τ l y z) := by
  unfold ft_sepMaj
  have hsm : Measurable (fun z : UnforcedLeray.Space => y - l • z) :=
    measurable_const.sub (measurable_id.const_smul l)
  have hpr : Measurable (fun z : UnforcedLeray.Space => ((τ + 2 * Real.log l, z) :
      ℝ × UnforcedLeray.Space)) :=
    measurable_const.prodMk measurable_id
  have hgz : Measurable (fun z : UnforcedLeray.Space => g (τ + 2 * Real.log l) z) :=
    hg.comp hpr
  have hK : Measurable (fun z : UnforcedLeray.Space => IIIa.sepKd 0 D (y - l • z)) :=
    (sd_measurable_sepKd 0 D).comp hsm
  exact measurable_const.mul (hK.mul hgz)

/-! ## 5. Domination of the masked integrand -/

/-- Pointwise domination of the masked `z`-integrand by the real majorant of `ft_sepMaj`. -/
theorem ft_sepIntg_norm_le {ν : ℝ} (hν : 0 < ν) {C : ℝ} (hC : 0 ≤ C)
    (hKC : ∀ t : ℝ, 0 < t → ∀ x : UnforcedLeray.Space, x ≠ 0 → ∀ i j k : Fin 3,
      |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
        C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    {R c δ s : ℝ} (hR : 0 < R) (hs : 0 < s) (hδ : 0 < δ) {f : Chart → Ten3}
    {T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hTb : ∀ τ' z, IIIa.tensorNorm (T τ' z) ≤ IIIa.tensorNorm (NearInst.cartLift R c f τ' z))
    {y : UnforcedLeray.Space} (hy : R / Real.sqrt s ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (τ : ℝ) (i : Fin 3) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (z : UnforcedLeray.Space) :
    ‖ft_sepIntg ν (ft_mskT R δ s T) i τ y l z‖ ≤
      (ft_sepMaj C ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s)
        (IIIa.srcNorm (NearInst.cartLift R c f)) τ l y z).toReal := by
  have hexp : Real.exp (-(δ / 2)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hDpos : 0 < (1 - Real.exp (-(δ / 2))) * R / Real.sqrt s :=
    div_pos (mul_pos (by linarith) hR) (Real.sqrt_pos.2 hs)
  have hpos : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  by_cases hm : Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
  · have hgap := ft_mask_gap hR hs hy hm hl
    have hx0 : y - l • z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hgap
      linarith
    have hsk : IIIa.sepKd 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s) (y - l • z) =
        ENNReal.ofReal (‖y - l • z‖ ^ (-4 - ((0 : ℕ) : ℝ))) := by
      unfold IIIa.sepKd
      rw [if_pos hgap]
    have htr : (ft_sepMaj C ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s)
        (IIIa.srcNorm (NearInst.cartLift R c f)) τ l y z).toReal =
        9 * C * (‖y - l • z‖ ^ (-4 - ((0 : ℕ) : ℝ)) *
          IIIa.tensorNorm (NearInst.cartLift R c f (τ + 2 * Real.log l) z)) := by
      have h9 : (0 : ℝ) ≤ 9 * C := by linarith
      have hpw : (0 : ℝ) ≤ ‖y - l • z‖ ^ (-4 - ((0 : ℕ) : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have hTN : (0 : ℝ) ≤ IIIa.tensorNorm (NearInst.cartLift R c f (τ + 2 * Real.log l) z) := by
        unfold IIIa.tensorNorm
        exact Real.sqrt_nonneg _
      unfold ft_sepMaj
      rw [hsk]
      unfold IIIa.srcNorm
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h9,
        ENNReal.toReal_ofReal hpw, ENNReal.toReal_ofReal hTN]
    have hunf : ft_sepIntg ν (ft_mskT R δ s T) i τ y l z =
        ∑ j : Fin 3, ∑ k : Fin 3,
          ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
            (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
      unfold ft_sepIntg
      simp only [if_pos hpos, ft_mskT, if_pos hm]
    rw [hunf, htr]
    have hk : ∀ j k : Fin 3, |fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
        (y - l • z) (coordinateVector k)| ≤ C * ‖y - l • z‖ ^ (-4 - ((0 : ℕ) : ℝ)) :=
      fun j k => hKC _ hpos _ hx0 i j k
    have hm' : ∀ j k : Fin 3, |T (τ + 2 * Real.log l) z j k| ≤
        IIIa.tensorNorm (NearInst.cartLift R c f (τ + 2 * Real.log l) z) :=
      fun j k => le_trans (IIIa.l5_abs_le_tensorNorm _ j k) (hTb _ _)
    have hA : 0 ≤ C * ‖y - l • z‖ ^ (-4 - ((0 : ℕ) : ℝ)) :=
      mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
    have hN : 0 ≤ IIIa.tensorNorm (NearInst.cartLift R c f (τ + 2 * Real.log l) z) := by
      unfold IIIa.tensorNorm
      exact Real.sqrt_nonneg _
    have hsum := ft_sum_norm_le
      (fun j k => fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
        (coordinateVector k))
      (fun j k => T (τ + 2 * Real.log l) z j k) hk hm' hA hN
    exact hsum.trans (le_of_eq (by ring))
  · have hz0 : ∀ j k : Fin 3, ft_mskT R δ s T (τ + 2 * Real.log l) z j k = 0 := by
      intro j k
      simp only [ft_mskT, if_neg hm, Matrix.zero_apply]
    have h0 : ft_sepIntg ν (ft_mskT R δ s T) i τ y l z = 0 := by
      unfold ft_sepIntg
      simp only [hz0, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero]
    rw [h0, norm_zero]
    exact ENNReal.toReal_nonneg

/-! ## 6. Inner dominated convergence in `z` -/

theorem ft_sepZInt_tendsto {ν : ℝ} (hν : 0 < ν) {C : ℝ} (hC : 0 ≤ C)
    (hKC : ∀ t : ℝ, 0 < t → ∀ x : UnforcedLeray.Space, x ≠ 0 → ∀ i j k : Fin 3,
      |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
        C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    {R c δ s : ℝ} (hR : 0 < R) (hs : 0 < s) (hδ : 0 < δ) {f : Chart → Ten3}
    (hf : Measurable f) {W : ℕ → Set Chart} (hW : ∀ k, MeasurableSet (W k))
    (hmono : Monotone W) (hcov : ∀ p : Chart, 0 < p.1 → ∃ k, p ∈ W k)
    {y : UnforcedLeray.Space} (hy : R / Real.sqrt s ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (τ : ℝ) (i : Fin 3) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1)
    (hfin : ∫⁻ z, ft_sepMaj C ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s)
      (IIIa.srcNorm (NearInst.cartLift R c f)) τ l y z ≠ ⊤) :
    Tendsto (fun k => sepZInt ν (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f))) i τ y l)
      atTop (𝓝 (sepZInt ν (ft_mskT R δ s (NearInst.cartLift R c f)) i τ y l)) := by
  have hTk : ∀ k, ∀ i j : Fin 3, Measurable fun p : ℝ × UnforcedLeray.Space =>
      NearInst.cartLift R c ((W k).indicator f) p.1 p.2 i j := fun k i j =>
    T8_1.measurable_cartLift_entry R c _ (hf.indicator (hW k)) i j
  have hgfin : ∀ τ' z, IIIa.srcNorm (NearInst.cartLift R c f) τ' z < ⊤ := by
    intro τ' z
    unfold IIIa.srcNorm
    exact ENNReal.ofReal_lt_top
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm (NearInst.cartLift R c f))) :=
    sd_measurable_srcNorm R c f hf
  simp only [ft_sepZInt_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun z => (ft_sepMaj C ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s)
      (IIIa.srcNorm (NearInst.cartLift R c f)) τ l y z).toReal)
    (fun k => (ft_sepIntg_measurable ν (fun i' j' => ft_mskT_measurable (hTk k) i' j')
      i τ y l).aestronglyMeasurable) ?_
    (fun k => Filter.Eventually.of_forall fun z =>
      ft_sepIntg_norm_le hν hC hKC hR hs hδ (fun τ' z' => ft_tensorNorm_indicator_le R c (W k) f τ' z')
        hy τ i hl z) ?_
  · exact integrable_toReal_of_lintegral_ne_top
      (ft_sepMaj_z C _ hgm τ l y).aemeasurable hfin
  · refine Filter.Eventually.of_forall fun z => ?_
    have hev : ∀ᶠ k in atTop, ft_sepIntg ν (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f)))
        i τ y l z = ft_sepIntg ν (ft_mskT R δ s (NearInst.cartLift R c f)) i τ y l z := by
      filter_upwards [ft_mskT_eventually (c := c) (δ := δ) (f := f) hR hs hmono hcov
        (τ + 2 * Real.log l) z] with k hk
      unfold ft_sepIntg
      rw [hk]
    exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)

/-! ## 7. Outer dominated convergence in `λ` and the `sepW` limit -/

theorem ft_sepW_tendsto {ν : ℝ} (hν : 0 < ν) {C : ℝ} (hC : 0 ≤ C)
    (hKC : ∀ t : ℝ, 0 < t → ∀ x : UnforcedLeray.Space, x ≠ 0 → ∀ i j k : Fin 3,
      |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
        C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    {R c δ s : ℝ} (hR : 0 < R) (hs : 0 < s) (hδ : 0 < δ) {μ : ℝ} {f : Chart → Ten3}
    (hf : Measurable f) {W : ℕ → Set Chart} (hW : ∀ k, MeasurableSet (W k))
    (hmono : Monotone W) (hcov : ∀ p : Chart, 0 < p.1 → ∃ k, p ∈ W k)
    {y : UnforcedLeray.Space} (hy : R / Real.sqrt s ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (τ : ℝ) (i : Fin 3)
    (hfin : IIIa.sepDom (2 * μ + 2) 0 ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt s)
      (IIIa.srcNorm (NearInst.cartLift R c f)) τ y < ⊤) :
    Tendsto (fun k => IIIa.sepW ν (μ : ℂ) (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f)))
        y τ i) atTop
      (𝓝 (IIIa.sepW ν (μ : ℂ) (ft_mskT R δ s (NearInst.cartLift R c f)) y τ i)) := by
  have key : ∀ T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.sepW ν (μ : ℂ) T y τ i =
        -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i τ y l :=
    fun T => sepW_eq_sepZInt ν hν μ T i (τ, y)
  simp only [key]
  refine Tendsto.const_mul (-2) ?_
  set D := (1 - Real.exp (-(δ / 2))) * R / Real.sqrt s with hD
  set g := IIIa.srcNorm (NearInst.cartLift R c f) with hg
  have hgm : Measurable (Function.uncurry g) := sd_measurable_srcNorm R c f hf
  have hgfin : ∀ τ' z, g τ' z < ⊤ := by
    intro τ' z
    rw [hg]
    unfold IIIa.srcNorm
    exact ENNReal.ofReal_lt_top
  -- the outer lintegral is finite
  have hfun : (fun l : ℝ => ENNReal.ofReal (l ^ (2 * μ + 2)) *
      ∫⁻ z, ft_sepMaj C D g τ l y z) =
      fun l => ENNReal.ofReal (9 * C) * (ENNReal.ofReal (l ^ (2 * μ + 2)) *
        ∫⁻ z, IIIa.sepKd 0 D (y - l • z) * g (τ + 2 * Real.log l) z) := by
    funext l
    unfold ft_sepMaj
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  have hOut : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
      ∫⁻ z, ft_sepMaj C D g τ l y z ≠ ⊤ := by
    have hfin' : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
        ∫⁻ z, IIIa.sepKd 0 D (y - l • z) * g (τ + 2 * Real.log l) z ≠ ⊤ := hfin.ne
    rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin'
  have hImeas : Measurable (fun l : ℝ => ∫⁻ z, ft_sepMaj C D g τ l y z) :=
    (ft_sepMaj_joint C D hgm τ y).lintegral_prod_right'
  have hae : ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z, ft_sepMaj C D g τ l y z < ⊤ := by
    refine ae_lt_top ?_ hOut
    exact (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul hImeas
  have hmain : ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      l ∈ Ioo (0 : ℝ) 1 ∧ ∫⁻ z, ft_sepMaj C D g τ l y z ≠ ⊤ := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with l hl hmem
    refine ⟨hmem, fun htop => ?_⟩
    have hne : ENNReal.ofReal (l ^ (2 * μ + 2)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hmem.1 _)).ne'
    have h2 := hl
    rw [htop, ENNReal.mul_top hne] at h2
    exact lt_irrefl _ h2
  -- the outer dominated convergence
  have hsz : ∀ T : ℝ → UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, Measurable fun p : ℝ × UnforcedLeray.Space => T p.1 p.2 i j) →
      Measurable (fun l : ℝ => sepZInt ν T i τ y l) := by
    intro T hT
    have hl' : Measurable (fun l : ℝ => (((τ, y) : ℝ × UnforcedLeray.Space), l)) :=
      measurable_const.prodMk measurable_id
    exact ((sepZInt_measurable ν T hT i).comp_measurable hl').measurable
  refine tendsto_integral_of_dominated_convergence
    (fun l => (ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z, ft_sepMaj C D g τ l y z).toReal)
    (fun k => ?_) ?_ ?_ ?_
  · have hTcart : ∀ i j : Fin 3, Measurable fun p : ℝ × UnforcedLeray.Space =>
        NearInst.cartLift R c ((W k).indicator f) p.1 p.2 i j := fun i j =>
      T8_1.measurable_cartLift_entry R c _ (hf.indicator (hW k)) i j
    have hsk := hsz (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f)))
      (fun i j => ft_mskT_measurable hTcart i j)
    exact ((Complex.measurable_ofReal.pow_const _).aestronglyMeasurable).mul
      hsk.aestronglyMeasurable
  · exact integrable_toReal_of_lintegral_ne_top
      (((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul hImeas).aemeasurable) hOut
  · intro k
    filter_upwards [hmain] with l hl
    obtain ⟨hlI, hI⟩ := hl
    have hre : (2 * (μ : ℂ) + 2).re = 2 * μ + 2 := by simp
    have hint : Integrable (fun z => (ft_sepMaj C D g τ l y z).toReal) :=
      integrable_toReal_of_lintegral_ne_top (ft_sepMaj_z C D hgm τ l y).aemeasurable hI
    have hbd : ‖sepZInt ν (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f))) i τ y l‖ ≤
        (∫⁻ z, ft_sepMaj C D g τ l y z).toReal := by
      rw [ft_sepZInt_eq, ← integral_toReal (ft_sepMaj_z C D hgm τ l y).aemeasurable
        (Filter.Eventually.of_forall fun z => ft_sepMaj_lt_top C D hgfin τ l y z)]
      exact norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun z =>
        ft_sepIntg_norm_le hν hC hKC hR hs hδ
          (fun τ' z' => ft_tensorNorm_indicator_le R c (W k) f τ' z') hy τ i hlI z)
    have hnorm : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ = l ^ (2 * μ + 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hlI.1, hre]
    calc ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2) *
          sepZInt ν (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f))) i τ y l‖
        = l ^ (2 * μ + 2) *
          ‖sepZInt ν (ft_mskT R δ s (NearInst.cartLift R c ((W k).indicator f))) i τ y l‖ := by
          rw [norm_mul, hnorm]
      _ ≤ l ^ (2 * μ + 2) * (∫⁻ z, ft_sepMaj C D g τ l y z).toReal :=
          mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hlI.1.le _)
      _ = (ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z, ft_sepMaj C D g τ l y z).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hlI.1.le _)]
  · filter_upwards [hmain] with l hl
    obtain ⟨hlI, hI⟩ := hl
    exact Tendsto.const_mul _ (ft_sepZInt_tendsto hν hC hKC hR hs hδ hf hW hmono hcov hy τ i hlI hI)

/-! ## 8. The far truncation tends to the far output -/

theorem ft_continuous_merRe : Continuous NearInst.merRe := by
  unfold NearInst.merRe
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact Complex.continuous_re.comp (continuous_apply 0)
  · exact Complex.continuous_re.comp (continuous_apply 2)

theorem farOutTruncTendsto : FarOutTruncTendsto := by
  intro R c ν μ δ S hR hc hν hμ hδ f hf W hW hmono hcov x hx hfin
  obtain ⟨C, hC, hKC⟩ := ft_kernel_bound IIIa.sepKernelBounds
  unfold NearInst.Masked.farOut
  split_ifs with hS
  · have hvec : Tendsto (fun k => NearInst.sepWfar ν (μ : ℂ) R δ x.1
        (NearInst.cartLift R c ((W k).indicator f)) (NearInst.chartY R x) (NearInst.chartTau R x))
        atTop (𝓝 (NearInst.sepWfar ν (μ : ℂ) R δ x.1 (NearInst.cartLift R c f)
          (NearInst.chartY R x) (NearInst.chartTau R x))) := by
      refine tendsto_pi_nhds.2 fun i => ?_
      simp only [ft_sepWfar_eq]
      exact ft_sepW_tendsto hν hC hKC hR hx hδ hf hW hmono hcov (ft_chartY_radius hR x)
        (NearInst.chartTau R x) i hfin
    exact ((ft_continuous_merRe.tendsto _).comp hvec.neg).const_smul _
  · exact tendsto_const_nhds

end UnforcedLeray.Short.PartIIIb.Concrete.FarBridge
