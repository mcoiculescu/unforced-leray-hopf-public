import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.LapIdentify

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1`: `HeatCellL2Bound` (conditional)

Source `the November 2 reference manuscript`, lines 261-288.

`HeatCellL2Bound` follows from the global pointwise Taylor bound `heatTaylorUniform` (strip
`|η| ≤ R+1`), a Gaussian tail bound for the convolution of a field vanishing near the evaluation
point (`|η| ≥ R+1`), and square integrability of `exp(-η²/32)` over the cell.  The pointwise
domination `‖Q_h z‖ ≤ C √h e^{-η²/32}` is assembled here (`heatPointwiseDom`), then integrated
(`heatCellL2Bound_of`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf T (Gaussian tail of the heat convolution; source lines 261-288).** If `‖f‖ ≤ M`
everywhere and `f (z - w) = 0` whenever `|w₂| < s`, then
`‖heatVecConvolution h f z‖ ≤ 2 M e^{-s²/(4h)}`.  Proof: `‖∫ K_h(w) f(z-w)‖ ≤ ∫ K_h(w) ‖f(z-w)‖
≤ M ∫_{|w₂| ≥ s} K_h`; the kernel is `G_h(w₁) G_h(w₂)` with `∫ G_h = 1` and the one-dimensional
tail `∫_{|x| ≥ s} G_h(x) dx ≤ 2 e^{-s²/(4h)}` (variance `2h`; Chernoff). -/
def HeatTailConv : Prop :=
  ∀ (f : Plane → Cyl.Vec2) (M s h : ℝ) (z : Plane), 0 < h → 0 ≤ s → 0 ≤ M →
    (∀ y, ‖f y‖ ≤ M) → (∀ w : Plane, |w.2| < s → f (z - w) = 0) →
    ‖HeatCylinder.heatVecConvolution h f z‖ ≤ 2 * M * Real.exp (-(s ^ 2) / (4 * h))

/-- **Leaf E (elementary inequality; source lines 261-288).** There is `C₀` with
`h⁻¹ · 2 e^{-s²/(4h)} ≤ C₀ √h e^{-s²/16}` for `s ≥ 1`, `0 < h ≤ 1`.  Proof:
`e^{-s²/(4h)} = e^{-s²/(8h)} e^{-s²/(8h)}`, the first factor `≤ e^{-s²/16}`, the second
`≤ e^{-1/(8h)}`, and `sup_{x ≥ 1} x^{3/2} e^{-x/8} < ∞` (`x = 1/h`); `C₀ = 20` works. -/
def HeatTailElem : Prop :=
  ∃ C₀ : ℝ, ∀ s h : ℝ, 1 ≤ s → 0 < h → h ≤ 1 →
    h⁻¹ * (2 * Real.exp (-(s ^ 2) / (4 * h))) ≤ C₀ * Real.sqrt h * Real.exp (-(s ^ 2) / 16)

/-- **Leaf G (Gaussian in `η` is `L²` over the cell; source lines 261-288).**
`eLpNorm (z ↦ e^{-z₂²/32}) 2 (cellMeasure c) < ∞`: `cellMeasure c = (c.toNNReal)⁻¹ • volume.restrict
(Ioc 0 c ×ˢ univ)`, and the integral of `e^{-η²/16}` over the cell is `c ∫ e^{-η²/16} dη`. -/
def GaussCellL2 : Prop :=
  ∀ c : ℝ, 0 < c →
    eLpNorm (fun z : Plane => Real.exp (-(z.2 ^ 2) / 32)) 2 (B0284.cellMeasure c) < ⊤

/-- **Leaf B (cylinder-smooth fields are bounded; source lines 261-288).** Continuous, `c`-periodic
in `q`, zero for `|η| > R`: bounded by the maximum over the compact box `[-c/2, c/2] × [-R, R]`. -/
def CylSmoothBdd : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Plane → Cyl.Vec2, Sob.IsCylSmooth c f →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z‖ ≤ M

theorem iterD_comm_lap {c : ℝ} {T : Plane → Cyl.Vec2} (hT : Sob.IsCylSmooth c T)
    (vs L : List Plane) :
    Sob.iterD vs (Sob.iterD L T) = Sob.iterD L (Sob.iterD vs T) := by
  rw [← iterD_append_eq T vs L, iterD_perm hT.smooth (List.perm_append_comm), iterD_append_eq]

/-- Pointwise Gaussian domination of the quotient (strip by Taylor, tail by leaves T, E). -/
theorem heatPointwiseDom (hTail : HeatTailConv) (hE : HeatTailElem) (hB : CylSmoothBdd)
    (c : ℝ) (hc : 0 < c) (f : Plane → Cyl.Vec2) (hf : Sob.IsCylSmooth c f) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ z : Plane,
      ‖h⁻¹ • (HeatCylinder.heatVecConvolution h f z - f z)
        - (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f z
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f z)‖
        ≤ C * Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := by
  set L1 : List Plane := [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] with hL1
  set L2 : List Plane := [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] with hL2
  obtain ⟨C1, hC1⟩ := heatTaylorUniform c hc f hf
  obtain ⟨C0, hC0⟩ := hE
  obtain ⟨M, hM0, hM⟩ := hB c hc f hf
  obtain ⟨R, hR⟩ := hf.bounded
  obtain ⟨R1, hR1⟩ := (hf.iterD L1).bounded
  obtain ⟨R2, hR2⟩ := (hf.iterD L2).bounded
  set Rm : ℝ := max (max (max R R1) R2) 0 with hRm
  have hRm0 : 0 ≤ Rm := le_max_right _ _
  have hRR : R ≤ Rm := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hRR1 : R1 ≤ Rm := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hRR2 : R2 ≤ Rm := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨|C1| * Real.exp ((Rm + 1) ^ 2 / 32) + |C0| * M * Real.exp (Rm ^ 2 / 16), ?_⟩
  intro h h0 h1 z
  have hsq : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
  have hex : 0 < Real.exp (-(z.2 ^ 2) / 32) := Real.exp_pos _
  have hA : 0 ≤ |C1| * Real.exp ((Rm + 1) ^ 2 / 32) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hBn : 0 ≤ |C0| * M * Real.exp (Rm ^ 2 / 16) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hM0) (Real.exp_pos _).le
  by_cases hz : |z.2| < Rm + 1
  · -- strip
    have h1' := hC1 h h0 h1 z
    have hz2 : z.2 ^ 2 ≤ (Rm + 1) ^ 2 := by
      have := sq_abs z.2
      rw [← this]
      exact pow_le_pow_left₀ (abs_nonneg _) hz.le 2
    have hge : 1 ≤ Real.exp ((Rm + 1) ^ 2 / 32) * Real.exp (-(z.2 ^ 2) / 32) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc _ ≤ C1 * Real.sqrt h := h1'
      _ ≤ |C1| * Real.sqrt h := mul_le_mul_of_nonneg_right (le_abs_self _) hsq
      _ ≤ |C1| * Real.sqrt h * (Real.exp ((Rm + 1) ^ 2 / 32) * Real.exp (-(z.2 ^ 2) / 32)) :=
          le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hsq) hge
      _ = (|C1| * Real.exp ((Rm + 1) ^ 2 / 32)) * Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := by
          ring
      _ ≤ _ := by
          have : 0 ≤ Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := mul_nonneg hsq hex.le
          nlinarith [mul_nonneg hBn this]
  · -- tail
    push_neg at hz
    have hzR : R < |z.2| := by linarith
    have hf0 : f z = 0 := hR z hzR
    have hl1 : Sob.iterD L1 f z = 0 := hR1 z (by linarith)
    have hl2 : Sob.iterD L2 f z = 0 := hR2 z (by linarith)
    rw [hf0, hl1, hl2, sub_zero, add_zero, sub_zero]
    set s : ℝ := |z.2| - Rm with hs
    have hs1 : 1 ≤ s := by rw [hs]; linarith
    have hs0 : 0 ≤ s := by linarith
    have hconv := hTail f M s h z h0 hs0 hM0 hM (fun w hw => by
      apply hR
      have : |z.2| - |w.2| ≤ |z.2 - w.2| := by
        have := abs_sub_abs_le_abs_sub z.2 w.2
        have h2 := abs_sub_abs_le_abs_sub (z.2 - w.2) (-w.2)
        simp only [sub_neg_eq_add, sub_add_cancel, abs_neg] at h2
        linarith
      show R < |(z - w).2|
      simp only [Prod.snd_sub]
      linarith)
    have hel := hC0 s h hs1 h0 h1
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h0.le]
    have hexp : Real.exp (-(s ^ 2) / 16) ≤
        Real.exp (Rm ^ 2 / 16) * Real.exp (-(z.2 ^ 2) / 32) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h3 : z.2 ^ 2 = |z.2| ^ 2 := (sq_abs _).symm
      have h4 : |z.2| = s + Rm := by rw [hs]; ring
      rw [h3, h4]
      nlinarith [sq_nonneg (s - Rm)]
    calc h⁻¹ * ‖HeatCylinder.heatVecConvolution h f z‖
        ≤ h⁻¹ * (2 * M * Real.exp (-(s ^ 2) / (4 * h))) :=
          mul_le_mul_of_nonneg_left hconv (inv_nonneg.2 h0.le)
      _ = M * (h⁻¹ * (2 * Real.exp (-(s ^ 2) / (4 * h)))) := by ring
      _ ≤ M * (C0 * Real.sqrt h * Real.exp (-(s ^ 2) / 16)) := mul_le_mul_of_nonneg_left hel hM0
      _ ≤ M * (|C0| * Real.sqrt h * Real.exp (-(s ^ 2) / 16)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsq)
            (Real.exp_pos _).le
      _ ≤ M * (|C0| * Real.sqrt h * (Real.exp (Rm ^ 2 / 16) * Real.exp (-(z.2 ^ 2) / 32))) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) hsq)
      _ = (|C0| * M * Real.exp (Rm ^ 2 / 16)) * Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := by
          ring
      _ ≤ _ := by
          have : 0 ≤ Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := mul_nonneg hsq hex.le
          nlinarith [mul_nonneg hA this]

/-- **`HeatCellL2Bound` from the three leaves.** -/
theorem heatCellL2Bound_of (hTail : HeatTailConv) (hE : HeatTailElem) (hG : GaussCellL2)
    (hB : CylSmoothBdd) : HeatCellL2Bound := by
  intro c hc T hT hΔ vs
  set f := Sob.iterD vs T with hfdef
  have hf : Sob.IsCylSmooth c f := hT.iterD vs
  have hlap : Sob.iterD vs (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
      + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x) =
      fun z => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f z
        + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f z := by
    rw [iterD_add_fun (Sob.contDiff_iterD hT.smooth _) (Sob.contDiff_iterD hT.smooth _)]
    funext z
    have a := iterD_comm_lap hT vs [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))]
    have b := iterD_comm_lap hT vs [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))]
    rw [a, b]
  obtain ⟨C, hC⟩ := heatPointwiseDom hTail hE hB c hc f hf
  have hGc := hG c hc
  set E : ℝ≥0∞ := eLpNorm (fun z : Plane => Real.exp (-(z.2 ^ 2) / 32)) 2 (B0284.cellMeasure c)
    with hEdef
  refine ⟨|C| * E.toReal, ?_⟩
  intro h h0 h1
  rw [hlap]
  have hsq : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
  have hmono : eLpNorm (fun z => h⁻¹ • (HeatCylinder.heatVecConvolution h f z - f z)
        - (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f z
          + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f z)) 2 (B0284.cellMeasure c)
      ≤ eLpNorm (fun z : Plane => (|C| * Real.sqrt h) • Real.exp (-(z.2 ^ 2) / 32)) 2
        (B0284.cellMeasure c) := by
    apply eLpNorm_mono_ae
    refine Filter.Eventually.of_forall (fun z => ?_)
    have := hC h h0 h1 z
    have hex := (Real.exp_pos (-(z.2 ^ 2) / 32)).le
    simp only [smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) hsq) hex)]
    calc _ ≤ C * Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) := this
      _ ≤ |C| * Real.sqrt h * Real.exp (-(z.2 ^ 2) / 32) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsq) hex
  refine hmono.trans (le_of_eq ?_)
  have e := eLpNorm_const_smul (|C| * Real.sqrt h) (fun z : Plane => Real.exp (-(z.2 ^ 2) / 32)) 2
    (B0284.cellMeasure c)
  rw [show (fun z : Plane => (|C| * Real.sqrt h) • Real.exp (-(z.2 ^ 2) / 32)) =
    (|C| * Real.sqrt h) • (fun z : Plane => Real.exp (-(z.2 ^ 2) / 32)) from rfl, e,
    Real.enorm_of_nonneg (mul_nonneg (abs_nonneg C) hsq)]
  rw [show |C| * E.toReal * Real.sqrt h = (|C| * Real.sqrt h) * E.toReal by ring,
    ENNReal.ofReal_mul (mul_nonneg (abs_nonneg C) hsq), ENNReal.ofReal_toReal hGc.ne]

end UnforcedLeray.Short.PartI
