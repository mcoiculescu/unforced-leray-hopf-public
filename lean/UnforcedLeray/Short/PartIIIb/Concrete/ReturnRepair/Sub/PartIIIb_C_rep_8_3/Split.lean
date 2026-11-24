import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.AffMJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.AyBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.L2Conv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.Support
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels

/-!
# `PartIII-b:C/rep/8/3/2`: `GRBound` from the Gaussian-replacement leaves (source 5484-5498)

Source of record: `the November 2 reference manuscript` (73 pages).

`grBound_of` proves `GRBound` from the leaves of `Defs.lean` (`GaussSumEA`, `RingAffGenSub`,
`RingAffGenPt`, `TrainSliceSmooth`, `TrainGaussCell`), the conormal size `AffMJet`
(`M(A_T) ≤ P_ν ε³ N`, source 5396-5413) and the measurability `GRMeas` of `ringAff`, with the
accepted `ayBound`, `bmatBound` (`|A^y| ≤ s^{5/2}M`, `|B| ≤ (1+μ)s^{3/2}M`), `eaCMeas`,
`eac_bmat_zero` and the body conversion `chartL2Conv` (source 5055-5079).

At one regime (`gr_regime`): for `s > 0`, `ringAff - E_{A_T}` is the chart coefficient
`s·(ringAffGen(v - ΣV_j, p_cyl - Σp_j))_{(r,z)}`; on `0 < s ≤ T = 1.1/ν` it is pointwise
`≤ 12(1+μ+T)M s^{5/2}(|w| + |D²w| + |∇q|)`, and it vanishes for `s > T`; the young-train cell
bound and `ChartL2Conv` give `‖ringAff - E_{A_T}‖ ≤ 96ν⁻⁴ M E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Algebra of the chart coefficient -/

theorem gr_merOf_sub (u v : Vec3) : merOf u - merOf v = merOf (u - v) := by
  ext i
  fin_cases i <;> simp [merOf]

theorem gr_frob_zero : frob (0 : Mat3) = 0 := by
  simp [frob]

theorem gr_frob_nonneg (A : Mat3) : 0 ≤ frob A := Real.sqrt_nonneg _

theorem gr_flatHessNorm_nonneg (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : 0 ≤ flatHessNorm V x := by
  unfold flatHessNorm
  positivity

theorem gr_trainGaussJet_nonneg (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) :
    0 ≤ trainGaussJet L s x := by
  unfold trainGaussJet
  have := gr_flatHessNorm_nonneg (trainDV L s) x
  positivity

/-- `ringAffCoef - EAcoef` is the chart coefficient of the difference of the two expressions. -/
theorem gr_coef_sub (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (vv : ℝ → ℝ × ℝ → ℝ × ℝ)
    (pp : ℝ → ℝ × ℝ → ℝ) (p : Chart) :
    ringAffCoef ν μ χf A vv pp p - EAcoef ν μ χf A p =
      merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
        (ringAffGen ν μ χf A vv pp p.1 p.2 - eA ν μ χf A p.1 p.2))) := by
  rw [EAcoef_eq, ringAffCoef, gr_merOf_sub, smul_sub, smul_sub]

theorem gr_rpow32 {s : ℝ} (hs : 0 < s) : s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem gr_rpow52 {s : ℝ} (hs : 0 < s) : s * s ^ (3 / 2 : ℝ) = s ^ (5 / 2 : ℝ) := by
  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]

theorem gr_rpow52_sq {s : ℝ} (hs : 0 ≤ s) : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
  rw [← Real.rpow_mul_natCast hs, ← Real.rpow_natCast s 5]
  norm_num

/-- `‖s^{-1/2}·s^{3/2}g‖ = s‖g‖` for `s > 0`. -/
theorem gr_norm_coef {s : ℝ} (hs : 0 < s) (g : Vec3) :
    ‖merOf ((Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • g))‖ = s * ‖merOf g‖ := by
  rw [affMerOf_smul, affMerOf_smul, norm_smul, norm_smul, gr_rpow32 hs]
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hq,
    abs_of_pos (mul_pos hs hq), ← mul_assoc, ← mul_assoc]
  congr 1
  field_simp

/-! ## 2. One regime -/

section Regime

/-- **The Gaussian replacement at one regime** (source 5484-5498): from the leaves, the jet sizes
`ayBound`, `bmatBound` and a young-train cell bound `E`, for any `A ∈ 𝒜` (here `A = A_T`),
`‖ringAffCoef(v, p_cyl) - E_A‖ ≤ 96ν⁻⁴M(A)E`. -/
theorem gr_regime (L : ReturnLevel) (μ as : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hχ : IsSourceCutoffC χf) (hν1 : L.ν ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hA : IsAffElem as A)
    (hmeas : AEStronglyMeasurable (ringAffCoef L.ν μ χf A (trainV L) (trainP L))
      (srcMeasure (cOf L.ν)))
    (h1 : GaussSumEA) (h3 : RingAffGenSub) (h5 : RingAffGenPt) (h6 : TrainSliceSmooth)
    {E : ℝ} (hE : 0 ≤ E)
    (hcell : ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / L.ν →
      ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν)) ≤
        ENNReal.ofReal (E ^ 2)) :
    eLpNorm (ringAffCoef L.ν μ χf A (trainV L) (trainP L) - EAcoef L.ν μ χf A)
        2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (96 * L.ν⁻¹ ^ 4 * affM L.ν χf A * E) := by
  have hν : 0 < L.ν := L.ν_pos
  have hT1 : 1 ≤ (11 / 10) / L.ν := by
    rw [le_div_iff₀ hν]; linarith
  generalize hTc : (11 / 10) / L.ν = Tc at hT1 hcell
  have hT0 : 0 < Tc := lt_of_lt_of_le one_pos hT1
  set M := affM L.ν χf A with hMdef
  have hM0 : 0 ≤ M := affM_nonneg L.ν χf A
  set F : Chart → Merid := ringAffCoef L.ν μ χf A (trainV L) (trainP L) - EAcoef L.ν μ χf A with hFdef
  -- the coefficient identity on `s > 0`
  have hgen : ∀ (s : ℝ) (x : ℝ × ℝ), 0 < s →
      ringAffGen L.ν μ χf A (trainV L) (trainP L) s x - eA L.ν μ χf A s x =
        ringAffGen L.ν μ χf A (trainDV L) (trainDP L) s x := by
    intro s x hs
    obtain ⟨hg2, hgp, heA⟩ := h1 L.ν s hν hs
    obtain ⟨ht2, htp⟩ := h6 L s hs.le
    rw [heA]
    exact h3 L.ν μ χf A (trainV L) (gaussV L.ν) (trainP L) (gaussP L.ν) s x ht2 hg2 htp hgp
  have hnorm : ∀ (s : ℝ) (x : ℝ × ℝ), 0 < s →
      ‖F (s, x)‖ = s * ‖merOf (ringAffGen L.ν μ χf A (trainDV L) (trainDP L) s x)‖ := by
    intro s x hs
    have e1 : F (s, x) = merOf ((Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) •
        (ringAffGen L.ν μ χf A (trainV L) (trainP L) s x - eA L.ν μ χf A s x))) := by
      rw [hFdef, Pi.sub_apply]
      exact gr_coef_sub L.ν μ χf A (trainV L) (trainP L) (s, x)
    rw [e1, hgen s x hs, gr_norm_coef hs]
  -- pointwise bound on `0 < s ≤ T`
  have hpt : ∀ (s : ℝ) (x : ℝ × ℝ), 0 < s → s ≤ Tc →
      ‖F (s, x)‖ ≤ (12 * (1 + μ + Tc) * M) * s ^ (5 / 2 : ℝ) * trainGaussJet L s x := by
    intro s x hs hsT
    have hB := bmatBound as χf hχ L.ν μ hν hμ0 A hA s hs (by rw [hTc]; exact hsT)
    have hC := ayBound as χf hχ L.ν hν A hA s hs (by rw [hTc]; exact hsT)
    have hP := h5 L.ν μ χf A (trainDV L) (trainDP L) s x hν.le
    set b := frob (Bmat L.ν μ χf A s)
    set a := frob (Ay L.ν χf A s)
    set w := ‖trainDV L s x‖
    set H := flatHessNorm (trainDV L s) x
    set g := ‖mgrad (trainDP L s) x‖
    have hb0 : 0 ≤ b := gr_frob_nonneg _
    have ha0 : 0 ≤ a := gr_frob_nonneg _
    have hw0 : 0 ≤ w := norm_nonneg _
    have hH0 : 0 ≤ H := gr_flatHessNorm_nonneg _ _
    have hg0 : 0 ≤ g := norm_nonneg _
    have hG : trainGaussJet L s x = w + H + g := rfl
    have h32 : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    have h52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    -- `ν a H ≤ a H`
    have hνaH : L.ν * a * H ≤ a * H := by
      have := mul_le_mul_of_nonneg_right hν1 (mul_nonneg ha0 hH0)
      linarith [this]
    have hstep : 12 * (b * w + L.ν * a * H + a * g) ≤
        12 * ((1 + μ) * s ^ (3 / 2 : ℝ) * M * w + s ^ (5 / 2 : ℝ) * M * (H + g)) := by
      have e1 : b * w ≤ (1 + μ) * s ^ (3 / 2 : ℝ) * M * w := mul_le_mul_of_nonneg_right hB hw0
      have e2 : a * (H + g) ≤ s ^ (5 / 2 : ℝ) * M * (H + g) :=
        mul_le_mul_of_nonneg_right hC (add_nonneg hH0 hg0)
      nlinarith [e1, e2, hνaH]
    have hsT' : s * s ^ (5 / 2 : ℝ) ≤ Tc * s ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsT h52
    have h52' := gr_rpow52 hs
    have hμ0' : 0 ≤ 1 + μ := by linarith
    have hX : 0 ≤ (1 + μ) * M := mul_nonneg hμ0' hM0
    calc ‖F (s, x)‖ = s * ‖merOf (ringAffGen L.ν μ χf A (trainDV L) (trainDP L) s x)‖ :=
          hnorm s x hs
      _ ≤ s * (12 * (b * w + L.ν * a * H + a * g)) := mul_le_mul_of_nonneg_left hP hs.le
      _ ≤ s * (12 * ((1 + μ) * s ^ (3 / 2 : ℝ) * M * w + s ^ (5 / 2 : ℝ) * M * (H + g))) :=
          mul_le_mul_of_nonneg_left hstep hs.le
      _ = 12 * ((1 + μ) * M * (s * s ^ (3 / 2 : ℝ)) * w +
            M * (s * s ^ (5 / 2 : ℝ)) * (H + g)) := by ring
      _ ≤ 12 * ((1 + μ) * M * s ^ (5 / 2 : ℝ) * (w + H + g) +
            M * (Tc * s ^ (5 / 2 : ℝ)) * (w + H + g)) := by
          rw [h52']
          have f1 : (1 + μ) * M * s ^ (5 / 2 : ℝ) * w ≤
              (1 + μ) * M * s ^ (5 / 2 : ℝ) * (w + H + g) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hX h52)
          have f2 : M * (s * s ^ (5 / 2 : ℝ)) * (H + g) ≤ M * (Tc * s ^ (5 / 2 : ℝ)) * (H + g) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsT' hM0) (add_nonneg hH0 hg0)
          have f3 : M * (Tc * s ^ (5 / 2 : ℝ)) * (H + g) ≤
              M * (Tc * s ^ (5 / 2 : ℝ)) * (w + H + g) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 (mul_nonneg hT0.le h52))
          linarith
      _ = (12 * (1 + μ + Tc) * M) * s ^ (5 / 2 : ℝ) * trainGaussJet L s x := by
          rw [hG]; ring
  -- support
  have hsupp : ∀ s : ℝ, Tc < s → ∀ x : ℝ × ℝ, F (s, x) = 0 := by
    intro s hs x
    have hs0 : 0 < s := lt_trans hT0 hs
    obtain ⟨hB, hC⟩ := eac_bmat_zero χf hχ L.ν μ hν A s (by rw [hTc]; exact hs)
    have hP := h5 L.ν μ χf A (trainDV L) (trainDP L) s x hν.le
    rw [hB, hC, gr_frob_zero] at hP
    have h0 : ‖merOf (ringAffGen L.ν μ χf A (trainDV L) (trainDP L) s x)‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      simpa using hP
    have := hnorm s x hs0
    rw [h0, mul_zero] at this
    exact norm_eq_zero.1 this
  -- cell bound
  set D : ℝ := 12 * (1 + μ + Tc) * M * E with hDdef
  have hK0 : 0 ≤ 12 * (1 + μ + Tc) * M := by
    have : 0 ≤ 1 + μ + Tc := by linarith
    positivity
  have hD0 : 0 ≤ D := mul_nonneg hK0 hE
  have hcellF : ∀ s : ℝ, 0 < s → s ≤ Tc →
      ∫⁻ x, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν)) ≤
        ENNReal.ofReal (D ^ 2 * s ^ 5) := by
    intro s hs hsT
    have h52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    have hpt2 : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ≤
        ENNReal.ofReal ((12 * (1 + μ + Tc) * M) ^ 2 * s ^ 5) *
          ENNReal.ofReal (trainGaussJet L s x ^ 2) := by
      intro x
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 := norm_nonneg (F (s, x))
      have hG0 := gr_trainGaussJet_nonneg L s x
      have hb := hpt s x hs hsT
      have hsq := pow_le_pow_left₀ h0 hb 2
      calc ‖F (s, x)‖ ^ 2
          ≤ ((12 * (1 + μ + Tc) * M) * s ^ (5 / 2 : ℝ) * trainGaussJet L s x) ^ 2 := hsq
        _ = (12 * (1 + μ + Tc) * M) ^ 2 * (s ^ (5 / 2 : ℝ)) ^ 2 * trainGaussJet L s x ^ 2 := by
            ring
        _ = (12 * (1 + μ + Tc) * M) ^ 2 * s ^ 5 * trainGaussJet L s x ^ 2 := by
            rw [gr_rpow52_sq hs.le]
    calc ∫⁻ x, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν))
        ≤ ∫⁻ x, ENNReal.ofReal ((12 * (1 + μ + Tc) * M) ^ 2 * s ^ 5) *
            ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν)) :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal ((12 * (1 + μ + Tc) * M) ^ 2 * s ^ 5) *
            ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((12 * (1 + μ + Tc) * M) ^ 2 * s ^ 5) * ENNReal.ofReal (E ^ 2) :=
          mul_le_mul_of_nonneg_left (hcell s hs hsT) bot_le
      _ = ENNReal.ofReal (D ^ 2 * s ^ 5) := by
          rw [← ENNReal.ofReal_mul (by positivity), hDdef]
          congr 1
          ring
  have hFmeas : AEStronglyMeasurable F (srcMeasure (cOf L.ν)) :=
    hmeas.sub (eaCMeas as χf hχ L.ν μ hν A hA)
  obtain ⟨-, hbd⟩ := chartL2Conv (cOf L.ν) Tc D F (cOf_pos hν) hT1 hD0 hFmeas hsupp hcellF
  refine hbd.trans (ENNReal.ofReal_le_ofReal ?_)
  -- `D T³ = 12(1+μ+T) M E T³ ≤ 96 ν⁻⁴ M E`
  have hu : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hTu : Tc = (11 / 10) * L.ν⁻¹ := by rw [← hTc, div_eq_mul_inv]
  have h1 : 1 + μ + Tc ≤ 4 * L.ν⁻¹ := by rw [hTu]; linarith
  have h3 : Tc ^ 3 ≤ 2 * L.ν⁻¹ ^ 3 := by
    rw [hTu, mul_pow]
    have : (0 : ℝ) ≤ L.ν⁻¹ ^ 3 := by positivity
    nlinarith
  have hME : 0 ≤ M * E := mul_nonneg hM0 hE
  have hT3 : 0 ≤ Tc ^ 3 := by positivity
  have hpos1 : 0 ≤ 1 + μ + Tc := by linarith
  calc D * Tc ^ 3 = 12 * (M * E) * ((1 + μ + Tc) * Tc ^ 3) := by rw [hDdef]; ring
    _ ≤ 12 * (M * E) * ((4 * L.ν⁻¹) * (2 * L.ν⁻¹ ^ 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul h1 h3 hT3 (by positivity)
    _ = 96 * L.ν⁻¹ ^ 4 * M * E := by ring

end Regime

/-! ## 3. Along the sequence -/

/-- The constants: `96ν⁻⁴M·(C_cν^{-k_c}δ) ≤ 96C_c(|C_J|+1)ν^{-(k_c+k_J+4)}(ε³δ + Y)·N` when
`M ≤ C_Jν^{-k_J}ε³N`. -/
theorem gr_final {ν ε δ Y Cc CJ M : ℝ} {kc kJ : ℕ} {N : ℝ≥0∞} (hν : 0 < ν) (hε : 0 < ε)
    (hCc : 0 < Cc) (hδ : 0 < δ) (hY : 0 ≤ Y)
    (hM : ENNReal.ofReal M ≤ ENNReal.ofReal (CJ * ν⁻¹ ^ kJ * ε ^ 3) * N) :
    ENNReal.ofReal (96 * ν⁻¹ ^ 4 * M * (Cc * ν⁻¹ ^ kc * δ)) ≤
      ENNReal.ofReal (96 * Cc * (|CJ| + 1) * ν⁻¹ ^ (kc + kJ + 4) * (ε ^ 3 * δ + Y)) * N := by
  have hQ0 : 0 ≤ 96 * ν⁻¹ ^ 4 * (Cc * ν⁻¹ ^ kc * δ) := by positivity
  calc ENNReal.ofReal (96 * ν⁻¹ ^ 4 * M * (Cc * ν⁻¹ ^ kc * δ))
      = ENNReal.ofReal (96 * ν⁻¹ ^ 4 * (Cc * ν⁻¹ ^ kc * δ)) * ENNReal.ofReal M := by
        rw [← ENNReal.ofReal_mul hQ0]; congr 1; ring
    _ ≤ ENNReal.ofReal (96 * ν⁻¹ ^ 4 * (Cc * ν⁻¹ ^ kc * δ)) *
          (ENNReal.ofReal (CJ * ν⁻¹ ^ kJ * ε ^ 3) * N) :=
        mul_le_mul_of_nonneg_left hM bot_le
    _ = ENNReal.ofReal (96 * ν⁻¹ ^ 4 * (Cc * ν⁻¹ ^ kc * δ) * (CJ * ν⁻¹ ^ kJ * ε ^ 3)) * N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hQ0]
    _ ≤ ENNReal.ofReal (96 * Cc * (|CJ| + 1) * ν⁻¹ ^ (kc + kJ + 4) * (ε ^ 3 * δ + Y)) * N := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        rw [pow_add, pow_add]
        have hCJ : CJ ≤ |CJ| + 1 := by linarith [le_abs_self CJ]
        have hP : 0 ≤ ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4 := by positivity
        have hbase : 0 ≤ 96 * Cc * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) * (ε ^ 3 * δ) := by
          positivity
        have hc : 0 ≤ 96 * Cc * (|CJ| + 1) * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) := by positivity
        calc 96 * ν⁻¹ ^ 4 * (Cc * ν⁻¹ ^ kc * δ) * (CJ * ν⁻¹ ^ kJ * ε ^ 3)
            = (96 * Cc * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) * (ε ^ 3 * δ)) * CJ := by ring
          _ ≤ (96 * Cc * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) * (ε ^ 3 * δ)) * (|CJ| + 1) :=
            mul_le_mul_of_nonneg_left hCJ hbase
          _ = 96 * Cc * (|CJ| + 1) * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) * (ε ^ 3 * δ) := by ring
          _ ≤ 96 * Cc * (|CJ| + 1) * (ν⁻¹ ^ kc * ν⁻¹ ^ kJ * ν⁻¹ ^ 4) * (ε ^ 3 * δ + Y) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hY) hc

/-- **`GRBound` from the leaves** (source 5484-5498): the young-train comparison, the lattice-sum
and linearity identities, the pointwise size, the conormal size `M(A_T) ≤ P_νε³N` and the
measurability of `ringAff`. -/
theorem grBound_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : GaussSumEA) (h3 : RingAffGenSub) (h5 : RingAffGenPt) (h6 : TrainSliceSmooth)
    (h4 : TrainGaussCell) (hJ : D.AffMJet) (hM : D.GRMeas) : D.GRBound := by
  obtain ⟨Cc, kc, Csig, bsig, ν₀, hCc, hb, hν₀, hcell⟩ := h4
  obtain ⟨CJ, kJ, hJ⟩ := hJ
  have hM' := hM hst.chiF
  refine ⟨96 * Cc * (|CJ| + 1), kc + kJ + 4, Csig, bsig, hb, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  filter_upwards [hJ, hM', hst.pins, hst.actual, hsmall,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne,
    D.eventually_mu_mem_Ioo hst.omega_ne hst.sigma_pos hst.sigma_lt] with
    n hJn hMn hpn hact hsm hνε hμn
  intro z hz T
  have hLj := rep9_3_ljOp_spec D.Pl D.K (D.level n) (D.mu n z) (hpn z hz).lj T
  have hA : IsAffElem D.K.as (LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
      (gRate D.Pl) (D.level n).ν (D.level n).ε (D.mu n z) D.K.χo D.K.χy T) := by
    rw [← hLj]; exact affIota_mem _ _
  have hMJ := hJn z hz T
  rw [hLj] at hMJ
  have hbuc : UnforcedLeray.Short.PartI.IsBUCTrain (D.level n).train := hact.regime.train_buc
  obtain ⟨hμ0, hμ1⟩ := hμn z hz
  have hE0 : 0 ≤ Cc * (D.level n).ν⁻¹ ^ kc * deltaBase Csig bsig (D.level n).ν := by
    have := (D.level n).ν_pos
    have : 0 < deltaBase Csig bsig (D.level n).ν := Real.exp_pos _
    positivity
  have hreg := gr_regime (D.level n) (D.mu n z) D.K.as D.K.χf _ hst.chiF hνε.1 hμ0.le
    (by linarith) hA (hMn z hz T) h1 h3 h5 h6 hE0 (hcell (D.level n) hbuc hsm.le)
  refine hreg.trans ?_
  exact gr_final (D.level n).ν_pos (D.level n).ε_pos hCc (Real.exp_pos _)
    (mul_nonneg (Real.rpow_nonneg (D.level n).ε_pos.le _) (Real.exp_pos _).le) hMJ

end UnforcedLeray.Short.PartIIIb.Concrete
