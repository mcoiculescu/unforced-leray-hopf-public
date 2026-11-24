import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_1_org
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D

/-!
# `PartIII-a:T21/c3/2/1/2/2/1/2`: leaf `RelB1c`

Source of record: `the November 2 reference manuscript` (SP) 2941-2946, 2962-2970.

Route.  Fix the block data; the constant `M` is built from the block only: the clock normaliser
`N(s,t)⁻¹ ≤ e^{|Re λ| B} e^{|Re κ| B / b}` (`clockN_inv_bounds`, SP 2998-2999), the free cylinder
energy `‖S(t,s) f‖_{X_{m,c}} ≤ e^{K t₂} ‖f‖_{X_{m,c}}` for the BUC train (`weak_energy`, SP
2092-2118), and the dilation norms on `L²_m` (`‖J_{a⁻¹}‖ ≤ a^{3/2}`, `‖J_a‖ ≤ a^{(m-3)/2}` for
`a ≥ 1`), with `1 ≤ a(s) ≤ a(t) ≤ a(t₂)`.

For `W` in the class at `σ`, `W = W₁ + i E₂` with `E₂ = I_s J_{a(s)}⁻¹ f₂` (the cell part of the
second test) and `W₁ = W - i E₂`, which agrees on the cell with `J_{a(s)}⁻¹ f₁`.  For each piece the
pin gives (SP 2941-2943)
`F_rel(τ,σ) X = N⁻¹ (J_{a(t)⁻¹} ⟦ω(t)⟧ + J_{(d_t/d_s)²} (X - I_s J_{a(s)}⁻¹ f))`,
whose norm is bounded by the three facts above; the cell data `‖f_i‖_{X_{m,c}}` are bounded by
`a(t₂)^{(m-3)/2} ‖W‖` because `|f_i| ≤ |f₁ + i f₂|` pointwise.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub RelRegularityOrg
namespace RelRegularityOrg2

namespace RelB1cAux

/-- The cell part `I_d J_a⁻¹ f` (`d = c/√a`) of a real cell field `f` on `B0579.cell c`, as an
element of `L²_m`. -/
def b1cCellPart {m : ℝ} (hm1 : 1 < m) (c a : ℝ) (f : ℝ × ℝ → ℝ) : Planar.L2w m :=
  RelB4locAux.dilW' hm1 a⁻¹ (RelB4locAux.liftC c m f)

theorem b1c_norm_liftC_eq {c m : ℝ} {g : ℝ × ℝ → ℝ} (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    ‖RelB4locAux.liftC c m g‖ = (eLpNorm g 2 (B0579.cellMeasure c m)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (RelB4locAux.coeFn_liftC hg),
    RelB4locAux.eLpNorm_liftFun hg.1]

theorem b1c_coeFn_cellPart {m c a : ℝ} (hm1 : 1 < m) (hc : 0 < c) (ha : 0 < a)
    {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    ⇑(b1cCellPart hm1 c a f) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (cellLen c a) (JscaleInv a (fun x => ((f x : ℝ) : ℂ))) (cToPlane z) := by
  have hα : 0 < a⁻¹ := inv_pos.2 ha
  unfold b1cCellPart
  rw [RelB4locAux.dilW'_of_pos hm1 hα]
  filter_upwards [Planar.coeFn_dilW hm1 hα (RelB4locAux.liftC c m f),
    Planar.dilWFun_congr hα (RelB4locAux.coeFn_liftC hf)] with z h1 h2
  rw [RelB4locAux.cellZeroExt_JscaleInv_eq hc ha f z]
  exact h1.trans h2

theorem b1c_norm_cellPart_le_liftC {m c a : ℝ} (hm1 : 1 < m) (ha : 1 ≤ a) (f : ℝ × ℝ → ℝ) :
    ‖b1cCellPart hm1 c a f‖ ≤ a ^ ((3 : ℝ) / 2) * ‖RelB4locAux.liftC c m f‖ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  unfold b1cCellPart
  rw [RelB4locAux.dilW'_of_pos hm1 (inv_pos.2 ha0)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (Planar.norm_dilW_inv_le_of_one_le hm1 ha) (norm_nonneg _))

theorem b1c_norm_liftC_le_cellPart {m c a : ℝ} (hm1 : 1 < m) (ha : 1 ≤ a) (f : ℝ × ℝ → ℝ) :
    ‖RelB4locAux.liftC c m f‖ ≤ a ^ ((m - 3) / 2) * ‖b1cCellPart hm1 c a f‖ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hinv : Planar.dilW hm1 ha0 (b1cCellPart hm1 c a f) = RelB4locAux.liftC c m f := by
    unfold b1cCellPart
    rw [RelB4locAux.dilW'_of_pos hm1 (inv_pos.2 ha0)]
    have h := congrArg (fun T : Planar.L2w m →L[ℂ] Planar.L2w m => T (RelB4locAux.liftC c m f))
      (Planar.dilW_comp_inv hm1 ha0)
    simpa using h
  calc ‖RelB4locAux.liftC c m f‖ = ‖Planar.dilW hm1 ha0 (b1cCellPart hm1 c a f)‖ := by rw [hinv]
    _ ≤ ‖Planar.dilW hm1 ha0‖ * ‖b1cCellPart hm1 c a f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ a ^ ((m - 3) / 2) * ‖b1cCellPart hm1 c a f‖ :=
        mul_le_mul_of_nonneg_right (Planar.norm_dilW_le_of_one_le hm1 ha) (norm_nonneg _)

/-- A real cell field dominated by `|f₁ + i f₂|` has cell part of norm at most `‖W‖` when `W`
agrees on the cell with `J_a⁻¹ (f₁ + i f₂)`. -/
theorem b1c_norm_cellPart_le_of_dom {m c a : ℝ} (hm1 : 1 < m) (hc : 0 < c) (ha : 0 < a)
    {g f₁ f₂ : ℝ × ℝ → ℝ} (hg : MemLp g 2 (B0579.cellMeasure c m))
    (hdom : ∀ y, |g y| ≤ ‖((f₁ y : ℝ) : ℂ) + Complex.I * ((f₂ y : ℝ) : ℂ)‖)
    (W : Planar.L2w m)
    (hW : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (cellLen c a) →
      (W : ℂ → ℂ) z = JscaleInv a
        (fun x => ((f₁ x : ℝ) : ℂ) + Complex.I * ((f₂ x : ℝ) : ℂ)) (cToPlane z)) :
    ‖b1cCellPart hm1 c a g‖ ≤ ‖W‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [b1c_coeFn_cellPart hm1 hc ha hg, (Planar.wMeasure_ac m).ae_le hW] with z h1 h2
  rw [h1]
  simp only [cellZeroExt]
  by_cases hin : cToPlane z ∈ B0579.cell (cellLen c a)
  · rw [indicator_of_mem hin, h2 hin]
    simp only [JscaleInv, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hdom _
  · rw [indicator_of_notMem hin, norm_zero]
    exact norm_nonneg _

/-- Identification of a pinned value of `F_rel` with planar dilations (SP 2941-2943). -/
theorem b1c_pin_eq {m c : ℝ} (hm1 : 1 < m) (hc : 0 < c) {a_s a_t N : ℝ} (has : 0 < a_s)
    (hat : 0 < a_t) (X : Planar.L2w m) (f : ℝ × ℝ → ℝ) (hf : MemLp f 2 (B0579.cellMeasure c m))
    (hX : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (cellLen c a_s) →
      (X : ℂ → ℂ) z = JscaleInv a_s (fun x => ((f x : ℝ) : ℂ)) (cToPlane z))
    (wf : ℝ × ℝ → ℝ) (hwf : MemLp wf 2 (B0579.cellMeasure c m)) (V : Planar.L2w m)
    (hV : ⇑V =ᵐ[volume] fun z => ((N : ℂ)⁻¹) * periodizedExt (cellLen c a_s) (cellLen c a_t)
      (JscaleInv a_t (fun x => ((wf x : ℝ) : ℂ))) (fun y => (X : ℂ → ℂ) (planeToC y))
      (cToPlane z)) :
    V = ((N : ℂ)⁻¹) • (RelB4locAux.dilW' hm1 a_t⁻¹ (RelB4locAux.liftC c m wf) +
      RelB4locAux.dilW' hm1 ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹
        (X - b1cCellPart hm1 c a_s f)) := by
  have hds : 0 < cellLen c a_s := div_pos hc (Real.sqrt_pos.2 has)
  have hdt : 0 < cellLen c a_t := div_pos hc (Real.sqrt_pos.2 hat)
  have hα : 0 < a_t⁻¹ := inv_pos.2 hat
  have hβ : 0 < ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹ := by positivity
  have heS : (fun w => (X : ℂ → ℂ) w -
      cellZeroExt (cellLen c a_s) (fun y => (X : ℂ → ℂ) (planeToC y)) (cToPlane w))
        =ᵐ[Planar.wMeasure m] ⇑(X - b1cCellPart hm1 c a_s f) := by
    filter_upwards [Lp.coeFn_sub X (b1cCellPart hm1 c a_s f), b1c_coeFn_cellPart hm1 hc has hf,
      (Planar.wMeasure_ac m).ae_le hX] with w h1 h2 h3
    rw [h1, Pi.sub_apply, h2]
    congr 1
    simp only [cellZeroExt]
    by_cases hin : cToPlane w ∈ B0579.cell (cellLen c a_s)
    · simp only [indicator_of_mem hin, planeToC_cToPlane]
      exact h3 hin
    · simp only [indicator_of_notMem hin]
  rw [RelB4locAux.dilW'_of_pos hm1 hα, RelB4locAux.dilW'_of_pos hm1 hβ]
  apply Lp.ext
  filter_upwards [(Planar.wMeasure_ac m).ae_le hV,
    Lp.coeFn_smul ((N : ℂ)⁻¹) (Planar.dilW hm1 hα (RelB4locAux.liftC c m wf) +
      Planar.dilW hm1 hβ (X - b1cCellPart hm1 c a_s f)),
    Lp.coeFn_add (Planar.dilW hm1 hα (RelB4locAux.liftC c m wf))
      (Planar.dilW hm1 hβ (X - b1cCellPart hm1 c a_s f)),
    Planar.coeFn_dilW hm1 hα (RelB4locAux.liftC c m wf),
    Planar.coeFn_dilW hm1 hβ (X - b1cCellPart hm1 c a_s f),
    Planar.dilWFun_congr hα (RelB4locAux.coeFn_liftC hwf),
    Planar.dilWFun_congr hβ heS] with z h1 h2 h3 h4 h5 h6 h7
  have h4' : (Planar.dilW hm1 hα (RelB4locAux.liftC c m wf) : ℂ → ℂ) z =
      Planar.dilWFun a_t⁻¹ (RelB4locAux.liftFun c wf) z := h4.trans h6
  have h5' : (Planar.dilW hm1 hβ (X - b1cCellPart hm1 c a_s f) : ℂ → ℂ) z =
      Planar.dilWFun ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹ (fun w => (X : ℂ → ℂ) w -
        cellZeroExt (cellLen c a_s) (fun y => (X : ℂ → ℂ) (planeToC y)) (cToPlane w)) z :=
    h5.trans h7.symm
  rw [h1, h2, Pi.smul_apply, h3, Pi.add_apply, h4', h5', smul_eq_mul]
  congr 1
  simp only [periodizedExt]
  rw [RelB4locAux.cellZeroExt_JscaleInv_eq hc hat wf z,
    RelB4locAux.extDil_eq_dilWFun hds hdt (X : ℂ → ℂ) z]

theorem b1c_cellLen_ratio_sq {c a_s a_t : ℝ} (hc : 0 < c) (has : 0 < a_s) (hat : 0 < a_t) :
    (cellLen c a_s / cellLen c a_t) ^ 2 = a_t / a_s := by
  unfold cellLen
  have h1 : Real.sqrt a_s ^ 2 = a_s := Real.sq_sqrt has.le
  have h2 : Real.sqrt a_t ^ 2 = a_t := Real.sq_sqrt hat.le
  have hs0 : Real.sqrt a_s ≠ 0 := (Real.sqrt_pos.2 has).ne'
  have ht0 : Real.sqrt a_t ≠ 0 := (Real.sqrt_pos.2 hat).ne'
  have e : c / Real.sqrt a_s / (c / Real.sqrt a_t) = Real.sqrt a_t / Real.sqrt a_s := by
    field_simp
  rw [e, div_pow, h1, h2]

/-- The norm of `N⁻¹ (T₁ L + T₂ (X - E))` for bounded `T₁, T₂`. -/
theorem b1c_abstract_norm_le {m N p : ℝ} (hN : 0 < N) (hp : 0 ≤ p)
    (T₁ T₂ : Planar.L2w m →L[ℂ] Planar.L2w m) (L X E Lf : Planar.L2w m)
    (hT₁ : ‖T₁‖ ≤ p) (hT₂ : ‖T₂‖ ≤ p) (hE : ‖E‖ ≤ p * ‖Lf‖) :
    ‖((N : ℂ)⁻¹) • (T₁ L + T₂ (X - E))‖ ≤ N⁻¹ * (p * ‖L‖ + p * (‖X‖ + p * ‖Lf‖)) := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hN.le)
  calc ‖T₁ L + T₂ (X - E)‖ ≤ ‖T₁ L‖ + ‖T₂ (X - E)‖ := norm_add_le _ _
    _ ≤ ‖T₁‖ * ‖L‖ + ‖T₂‖ * ‖X - E‖ := add_le_add (T₁.le_opNorm _) (T₂.le_opNorm _)
    _ ≤ p * ‖L‖ + p * (‖X‖ + p * ‖Lf‖) :=
        add_le_add (mul_le_mul_of_nonneg_right hT₁ (norm_nonneg _))
          (mul_le_mul hT₂ ((norm_sub_le _ _).trans (add_le_add le_rfl hE)) (norm_nonneg _) hp)

/-- Norm bound of a pinned value of `F_rel` on a block with `1 ≤ a_s ≤ a_t ≤ A`. -/
theorem b1c_pinned_norm_le {m c : ℝ} (hm1 : 1 < m) (hc : 0 < c) {a_s a_t A N : ℝ}
    (has : 1 ≤ a_s) (hst : a_s ≤ a_t) (htA : a_t ≤ A) (hN : 0 < N)
    (X : Planar.L2w m) (f : ℝ × ℝ → ℝ) (hf : MemLp f 2 (B0579.cellMeasure c m))
    (hX : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (cellLen c a_s) →
      (X : ℂ → ℂ) z = JscaleInv a_s (fun x => ((f x : ℝ) : ℂ)) (cToPlane z))
    (wf : ℝ × ℝ → ℝ) (hwf : MemLp wf 2 (B0579.cellMeasure c m)) (V : Planar.L2w m)
    (hV : ⇑V =ᵐ[volume] fun z => ((N : ℂ)⁻¹) * periodizedExt (cellLen c a_s) (cellLen c a_t)
      (JscaleInv a_t (fun x => ((wf x : ℝ) : ℂ))) (fun y => (X : ℂ → ℂ) (planeToC y))
      (cToPlane z)) :
    ‖V‖ ≤ N⁻¹ * (A ^ ((3 : ℝ) / 2) * ‖RelB4locAux.liftC c m wf‖ +
      A ^ ((3 : ℝ) / 2) * (‖X‖ + A ^ ((3 : ℝ) / 2) * ‖RelB4locAux.liftC c m f‖)) := by
  have has0 : 0 < a_s := lt_of_lt_of_le zero_lt_one has
  have hat1 : 1 ≤ a_t := has.trans hst
  have hat0 : 0 < a_t := lt_of_lt_of_le zero_lt_one hat1
  have hA0 : 0 ≤ A := hat0.le.trans htA
  have hp : ∀ x : ℝ, 0 ≤ x → x ≤ A → x ^ ((3 : ℝ) / 2) ≤ A ^ ((3 : ℝ) / 2) := fun x hx hxA =>
    Real.rpow_le_rpow hx hxA (by norm_num)
  have hpA : 0 ≤ A ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hA0 _
  have hT₁ : ‖RelB4locAux.dilW' hm1 a_t⁻¹‖ ≤ A ^ ((3 : ℝ) / 2) := by
    rw [RelB4locAux.dilW'_of_pos hm1 (inv_pos.2 hat0)]
    exact (Planar.norm_dilW_inv_le_of_one_le hm1 hat1).trans (hp a_t hat0.le htA)
  have hratio := b1c_cellLen_ratio_sq hc has0 hat0
  have hr1 : 1 ≤ a_t / a_s := (one_le_div has0).2 hst
  have hrA : a_t / a_s ≤ A := (div_le_self hat0.le has).trans htA
  have hT₂ : ‖RelB4locAux.dilW' hm1 ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹‖ ≤
      A ^ ((3 : ℝ) / 2) := by
    rw [hratio, RelB4locAux.dilW'_of_pos hm1 (inv_pos.2 (lt_of_lt_of_le zero_lt_one hr1))]
    exact (Planar.norm_dilW_inv_le_of_one_le hm1 hr1).trans
      (hp _ (div_nonneg hat0.le has0.le) hrA)
  have hE : ‖b1cCellPart hm1 c a_s f‖ ≤ A ^ ((3 : ℝ) / 2) * ‖RelB4locAux.liftC c m f‖ :=
    (b1c_norm_cellPart_le_liftC hm1 has f).trans
      (mul_le_mul_of_nonneg_right (hp a_s has0.le (hst.trans htA)) (norm_nonneg _))
  rw [b1c_pin_eq hm1 hc has0 hat0 X f hf hX wf hwf V hV]
  exact b1c_abstract_norm_le hN hpA _ _ _ _ _ _ hT₁ hT₂ hE

/-- The free cylinder energy bound in the `liftC` norm. -/
theorem b1c_liftC_flow_le {m ν c T K : ℝ} {tr : B0140.TrainSol ν c} (hK : 0 < K)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {g : B0579.Plane → ℝ}
    (hg : B0579.IsCylTest c g) {w : ℝ → B0579.Plane → ℝ}
    (hw : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s g w)
    (hE : UnforcedLeray.Short.IIb.cylEnergy c m (w t) ≤
      Real.exp (2 * K * (t - s)) * UnforcedLeray.Short.IIb.cylEnergy c m g) :
    ‖RelB4locAux.liftC c m (w t)‖ ≤ Real.exp (K * T) * ‖RelB4locAux.liftC c m g‖ := by
  have hwt : MemLp (w t) 2 (B0579.cellMeasure c m) := hw.memX t hst
  have hg2 : MemLp g 2 (B0579.cellMeasure c m) := hg.memLp m
  rw [b1c_norm_liftC_eq hwt, b1c_norm_liftC_eq hg2, RelB4locAux.eLpNorm_eq_sqrt_energy hwt,
    RelB4locAux.eLpNorm_eq_sqrt_energy hg2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have h2 := Real.sqrt_le_sqrt hE
  have h3 : Real.sqrt (Real.exp (2 * K * (t - s)) * UnforcedLeray.Short.IIb.cylEnergy c m g) =
      Real.exp (K * (t - s)) * Real.sqrt (UnforcedLeray.Short.IIb.cylEnergy c m g) := by
    rw [Real.sqrt_mul (Real.exp_pos _).le,
      show 2 * K * (t - s) = K * (t - s) + K * (t - s) by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have h4 : Real.exp (K * (t - s)) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hK.le)
  calc Real.sqrt (UnforcedLeray.Short.IIb.cylEnergy c m (w t))
      ≤ Real.sqrt (Real.exp (2 * K * (t - s)) * UnforcedLeray.Short.IIb.cylEnergy c m g) := h2
    _ = Real.exp (K * (t - s)) * Real.sqrt (UnforcedLeray.Short.IIb.cylEnergy c m g) := h3
    _ ≤ Real.exp (K * T) * Real.sqrt (UnforcedLeray.Short.IIb.cylEnergy c m g) :=
        mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)

/-- Upper bound of the inverse clock normaliser on a block (SP 2998-2999). -/
theorem b1c_clockN_inv_le (P : PlanarData) {ν t₁ t₂ B b σ τ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (ht₁₂ : t₁ ≤ t₂) (hb : 0 < b) (hbt : b ≤ clockTheta ν t₂)
    (hBz : movingZ ν t₂ - movingZ ν t₁ = B) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B) :
    (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ ≤
      Real.exp (|P.eigenvalue.re| * B) * Real.exp (|P.kappa.re| / b * B) := by
  obtain ⟨hs1, hst, ht2⟩ := RelB4locAux.ageAt_props hν ht₁ ht₁₂ hBz hσ hστ hτB
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs1
  have ht0 : 0 ≤ ageAt ν t₁ τ := hs0.trans hst
  have hθ : clockTheta ν t₂ ≤ clockTheta ν (ageAt ν t₁ τ) := by
    unfold clockTheta clockA
    apply inv_anti₀ (by positivity)
    have := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hν.le hν.le)
    nlinarith
  have hbr : b ≤ clockTheta ν (ageAt ν t₁ τ) := hbt.trans hθ
  have hb' := (RelFreeTestSub.clockN_inv_bounds P hν hs0 hst hb hbr).1
  have hzτ := VariationOfConstantsSub.movingZ_ageAt_sub hν ht₂ hBz hτB
  have hzσ := VariationOfConstantsSub.movingZ_ageAt_sub hν ht₂ hBz (hστ.trans hτB)
  have hΔ : movingZ ν (ageAt ν t₁ τ) - movingZ ν (ageAt ν t₁ σ) = τ - σ := by linarith
  rw [hΔ] at hb'
  refine hb'.trans (mul_le_mul (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_)
    (Real.exp_pos _).le (Real.exp_pos _).le)
  · have h1 : -P.eigenvalue.re * (τ - σ) ≤ |P.eigenvalue.re| * (τ - σ) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    have h2 : |P.eigenvalue.re| * (τ - σ) ≤ |P.eigenvalue.re| * B :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  · exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (abs_nonneg _) hb.le)

/-- The final arithmetic. -/
theorem b1c_arith {V Ninv CN p eK D w X Lω Lf : ℝ} (hNinv0 : 0 ≤ Ninv) (hNinv : Ninv ≤ CN)
    (hp : 0 ≤ p) (heK : 0 ≤ eK) (hD : 0 ≤ D) (hw : 0 ≤ w)
    (hV : V ≤ Ninv * (p * Lω + p * (X + p * Lf)))
    (hLω : Lω ≤ eK * Lf) (hLf : Lf ≤ D * w) (hX : X ≤ 2 * w) :
    V ≤ CN * (p * (eK * D) + p * (2 + p * D)) * w := by
  have h0 : Lω ≤ eK * (D * w) := hLω.trans (mul_le_mul_of_nonneg_left hLf heK)
  have h2 : p * Lω ≤ p * (eK * (D * w)) := mul_le_mul_of_nonneg_left h0 hp
  have h3 : p * Lf ≤ p * (D * w) := mul_le_mul_of_nonneg_left hLf hp
  have h4 : p * (X + p * Lf) ≤ p * (2 * w + p * (D * w)) :=
    mul_le_mul_of_nonneg_left (add_le_add hX h3) hp
  have h5 : p * Lω + p * (X + p * Lf) ≤ (p * (eK * D) + p * (2 + p * D)) * w := by
    calc p * Lω + p * (X + p * Lf) ≤ p * (eK * (D * w)) + p * (2 * w + p * (D * w)) :=
          add_le_add h2 h4
      _ = (p * (eK * D) + p * (2 + p * D)) * w := by ring
  have h6 : 0 ≤ (p * (eK * D) + p * (2 + p * D)) * w := by positivity
  calc V ≤ Ninv * (p * Lω + p * (X + p * Lf)) := hV
    _ ≤ Ninv * ((p * (eK * D) + p * (2 + p * D)) * w) := mul_le_mul_of_nonneg_left h5 hNinv0
    _ ≤ CN * ((p * (eK * D) + p * (2 + p * D)) * w) := mul_le_mul_of_nonneg_right hNinv h6
    _ = CN * (p * (eK * D) + p * (2 + p * D)) * w := by ring

end RelB1cAux

open RelB1cAux

/-- **Leaf `RelB1c`** (SP 2941-2946, 2962-2970): the pinned relative free evolution is uniformly
bounded on the per-`σ` class, with a constant depending only on the block. -/
theorem relB1c_leaf (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.RelRegularityOrg2.RelB1c κ := by
  intro P m K B b ν tr t₁ t₂ ctx
  obtain ⟨_hκ, _hP, hm, _hB, hb, hν, _hF, htr, ht₁, ht₁₂, hbt, hBz⟩ := ctx
  have hm1 : 1 < m := by linarith
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨Ke, hKe, hEn⟩ := RelB4locAux.weak_energy (m := m) (T := t₂) hm hν hc htr ht₂
  have hA1 : 1 ≤ clockA ν t₂ := by
    unfold clockA
    have := mul_nonneg hν.le ht₂
    linarith
  have hp0 : 0 ≤ clockA ν t₂ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hD0 : 0 ≤ clockA ν t₂ ^ ((m - 3) / 2) := Real.rpow_nonneg (by linarith) _
  have heK0 : 0 ≤ Real.exp (Ke * t₂) := (Real.exp_pos _).le
  refine ⟨2 * (Real.exp (|P.eigenvalue.re| * B) * Real.exp (|P.kappa.re| / b * B) *
    (clockA ν t₂ ^ ((3 : ℝ) / 2) * (Real.exp (Ke * t₂) * clockA ν t₂ ^ ((m - 3) / 2)) +
      clockA ν t₂ ^ ((3 : ℝ) / 2) * (2 + clockA ν t₂ ^ ((3 : ℝ) / 2) *
        clockA ν t₂ ^ ((m - 3) / 2)))), ?_⟩
  intro F_rel hFp σ τ hσ hστ hτB W hW
  obtain ⟨hs1, hst, ht2⟩ := RelB4locAux.ageAt_props hν ht₁ ht₁₂ hBz hσ hστ hτB
  obtain ⟨f₁, f₂, hf₁, hf₂, ⟨ω₁, hω₁⟩, ⟨ω₂, hω₂⟩, hWc⟩ := hW
  have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs1
  have ht0 : 0 ≤ ageAt ν t₁ τ := hs0.trans hst
  -- clocks
  have has1 : 1 ≤ clockA ν (ageAt ν t₁ σ) := by
    unfold clockA
    have := mul_nonneg hν.le hs0
    linarith
  have has0 : 0 < clockA ν (ageAt ν t₁ σ) := lt_of_lt_of_le zero_lt_one has1
  have hast : clockA ν (ageAt ν t₁ σ) ≤ clockA ν (ageAt ν t₁ τ) := by
    unfold clockA
    have := mul_le_mul_of_nonneg_left hst hν.le
    linarith
  have hatA : clockA ν (ageAt ν t₁ τ) ≤ clockA ν t₂ := by
    unfold clockA
    have := mul_le_mul_of_nonneg_left ht2 hν.le
    linarith
  have hasA : clockA ν (ageAt ν t₁ σ) ≤ clockA ν t₂ := hast.trans hatA
  have hN : 0 < clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) := RelB4locAux.clockN_pos P hν hs0 ht0
  have hNinv := b1c_clockN_inv_le P hν ht₁ ht₁₂ (lt_of_lt_of_le zero_lt_one hb) hbt hBz hσ hστ hτB
  have hD : clockA ν (ageAt ν t₁ σ) ^ ((m - 3) / 2) ≤ clockA ν t₂ ^ ((m - 3) / 2) :=
    Real.rpow_le_rpow has0.le hasA (by linarith)
  -- the decomposition `W = W₁ + i E₂`
  have hf₁2 : MemLp f₁ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hf₁.memLp m
  have hf₂2 : MemLp f₂ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hf₂.memLp m
  set E₂ : Planar.L2w m := b1cCellPart hm1 (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) f₂ with hE₂_def
  set W₁ : Planar.L2w m := W - Complex.I • E₂ with hW₁_def
  have hE₂c : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
      (E₂ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
        (fun x => ((f₂ x : ℝ) : ℂ)) (cToPlane z) := by
    filter_upwards [(Planar.volume_ac m).ae_le (b1c_coeFn_cellPart hm1 hc has0 hf₂2)] with z hz hin
    rw [hz]
    simp only [cellZeroExt]
    rw [indicator_of_mem hin]
  have hW₁c : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
      (W₁ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
        (fun x => ((f₁ x : ℝ) : ℂ)) (cToPlane z) := by
    filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_sub W (Complex.I • E₂)),
      (Planar.volume_ac m).ae_le (Lp.coeFn_smul Complex.I E₂), hE₂c, hWc] with z h1 h2 h3 h4 hin
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3 hin, h4 hin, smul_eq_mul]
    simp only [JscaleInv]
    ring
  have hsplit : F_rel τ σ W = F_rel τ σ W₁ + Complex.I • F_rel τ σ E₂ := by
    rw [← map_smul, ← map_add]
    congr 1
    simp [hW₁_def]
  -- domination of the cell data
  have hdom1 : ‖b1cCellPart hm1 (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) f₁‖ ≤ ‖W‖ := by
    refine b1c_norm_cellPart_le_of_dom hm1 hc has0 hf₁2 (fun y => ?_) W hWc
    have h := Complex.abs_re_le_norm (((f₁ y : ℝ) : ℂ) + Complex.I * ((f₂ y : ℝ) : ℂ))
    have hre : (((f₁ y : ℝ) : ℂ) + Complex.I * ((f₂ y : ℝ) : ℂ)).re = f₁ y := by simp
    rwa [hre] at h
  have hdom2 : ‖E₂‖ ≤ ‖W‖ := by
    refine b1c_norm_cellPart_le_of_dom hm1 hc has0 hf₂2 (fun y => ?_) W hWc
    have h := Complex.abs_im_le_norm (((f₁ y : ℝ) : ℂ) + Complex.I * ((f₂ y : ℝ) : ℂ))
    have him : (((f₁ y : ℝ) : ℂ) + Complex.I * ((f₂ y : ℝ) : ℂ)).im = f₂ y := by simp
    rwa [him] at h
  have hL₁ : ‖RelB4locAux.liftC (ν ^ (-2 : ℝ)) m f₁‖ ≤ clockA ν t₂ ^ ((m - 3) / 2) * ‖W‖ :=
    (b1c_norm_liftC_le_cellPart hm1 has1 f₁).trans
      (mul_le_mul hD hdom1 (norm_nonneg _) hD0)
  have hL₂ : ‖RelB4locAux.liftC (ν ^ (-2 : ℝ)) m f₂‖ ≤ clockA ν t₂ ^ ((m - 3) / 2) * ‖W‖ :=
    (b1c_norm_liftC_le_cellPart hm1 has1 f₂).trans
      (mul_le_mul hD hdom2 (norm_nonneg _) hD0)
  have hW₁n : ‖W₁‖ ≤ 2 * ‖W‖ := by
    have h := norm_sub_le W (Complex.I • E₂)
    rw [norm_smul, Complex.norm_I, one_mul] at h
    linarith
  have hE₂n : ‖E₂‖ ≤ 2 * ‖W‖ := by
    have := norm_nonneg W
    linarith
  -- energy of the two flows
  have hω₁t := b1c_liftC_flow_le hKe hs0 hst ht2 hf₁ hω₁ (hEn _ _ hs0 hst ht2 f₁ hf₁ ω₁ hω₁)
  have hω₂t := b1c_liftC_flow_le hKe hs0 hst ht2 hf₂ hω₂ (hEn _ _ hs0 hst ht2 f₂ hf₂ ω₂ hω₂)
  -- the two pinned values
  have hV₁ := hFp σ τ hσ hστ hτB f₁ hf₁ ω₁ hω₁ W₁ hW₁c
  have hV₂ := hFp σ τ hσ hστ hτB f₂ hf₂ ω₂ hω₂ E₂ hE₂c
  have hb₁ := b1c_pinned_norm_le hm1 hc has1 hast hatA hN W₁ f₁ hf₁2 hW₁c
    (ω₁ (ageAt ν t₁ τ)) (hω₁.memX _ hst) (F_rel τ σ W₁) hV₁
  have hb₂ := b1c_pinned_norm_le hm1 hc has1 hast hatA hN E₂ f₂ hf₂2 hE₂c
    (ω₂ (ageAt ν t₁ τ)) (hω₂.memX _ hst) (F_rel τ σ E₂) hV₂
  have hNinv0 : 0 ≤ (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ := inv_nonneg.2 hN.le
  have k₁ := b1c_arith hNinv0 hNinv hp0 heK0 hD0 (norm_nonneg W) hb₁ hω₁t hL₁ hW₁n
  have k₂ := b1c_arith hNinv0 hNinv hp0 heK0 hD0 (norm_nonneg W) hb₂ hω₂t hL₂ hE₂n
  rw [hsplit]
  calc ‖F_rel τ σ W₁ + Complex.I • F_rel τ σ E₂‖
      ≤ ‖F_rel τ σ W₁‖ + ‖Complex.I • F_rel τ σ E₂‖ := norm_add_le _ _
    _ = ‖F_rel τ σ W₁‖ + ‖F_rel τ σ E₂‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := by linarith

end RelRegularityOrg2
end UnforcedLeray.Short.IIIa
