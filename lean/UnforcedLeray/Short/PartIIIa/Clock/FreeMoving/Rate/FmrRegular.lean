import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrBracket
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIsoRadial
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBP
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrDeriv
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrVelGap
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrVelBdd

/-!
# Part III-a, task `PartIII-a:T21/c2/2/9`: `FmrRegular`

Source of record: `the November 2 reference manuscript`, lines 2937-2958, 270-288.
Assembles `FmrRegular` from `fmrDeriv`, `fmrIBP`, `fmrBracket`, `fmrIsoRadial`, `fmrVelGap`, and
`fmrVelBdd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

private lemma abs_movWeightDt_le {ν m a : ℝ} (hν : 0 ≤ ν) (hm : 0 ≤ m) (ha : 0 < a)
    (x : B0579.Plane) :
    |movWeightDt ν m a x| ≤ (ν * m / a) * movWeight m a x := by
  set r := x.1 ^ 2 + x.2 ^ 2 with hr_def
  have hr : 0 ≤ r := by positivity
  set w := 1 + r / a with hw_def
  have hw : 0 < w := by positivity
  have hpow : w ^ m = w * w ^ (m - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hw.ne']
    ring_nf
  have hrw : r / a ≤ w := by linarith
  have h1 : movWeightDt ν m a x = -((ν * m / a) * (r / a) * w ^ (m - 1)) := by
    unfold movWeightDt
    rw [← hr_def, ← hw_def]
    ring
  have hpow0 : 0 ≤ w ^ (m - 1) := Real.rpow_nonneg hw.le _
  have hνma : 0 ≤ ν * m / a := by positivity
  rw [h1, abs_neg, abs_of_nonneg (by positivity)]
  unfold movWeight
  rw [← hr_def, ← hw_def, hpow]
  calc (ν * m / a) * (r / a) * w ^ (m - 1)
      ≤ (ν * m / a) * w * w ^ (m - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrw hνma) hpow0
    _ = (ν * m / a) * (w * w ^ (m - 1)) := by ring

private lemma integrableOn_movWeightDt {c ν m a : ℝ} {g : B0579.Plane → ℝ}
    (hν : 0 ≤ ν) (hm : 0 ≤ m) (ha : 0 < a) (hg : Continuous g)
    (hIw : IntegrableOn (fun x => g x ^ 2 * movWeight m a x) (B0579.cell c)) :
    IntegrableOn (fun x => g x ^ 2 * movWeightDt ν m a x) (B0579.cell c) := by
  have hD_cont : Continuous (fun x : B0579.Plane => movWeightDt ν m a x) := by
    unfold movWeightDt
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) (fun x => Or.inl ?_))
    have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := by positivity
    linarith
  refine Integrable.mono' (hIw.const_mul (ν * m / a))
    (((hg.pow 2).mul hD_cont).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (ae_of_all _ fun x _ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc g x ^ 2 * |movWeightDt ν m a x|
      ≤ g x ^ 2 * ((ν * m / a) * movWeight m a x) :=
        mul_le_mul_of_nonneg_left (abs_movWeightDt_le hν hm ha x) (sq_nonneg _)
    _ = (ν * m / a) * (g x ^ 2 * movWeight m a x) := by ring

private lemma rpow_neg_three_halves_div_sqrt {a : ℝ} (ha : 0 < a) :
    a ^ (-(3 / 2) : ℝ) / Real.sqrt a = 1 / a ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ha, show (-(3 / 2) : ℝ) - 1 / 2 = -2 by norm_num,
    Real.rpow_neg ha.le, Real.rpow_two, one_div]

theorem fmrRegular : FmrRegular := by
  intro m hm ε hε b hb
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hε' : 0 < 2 * ε / m := div_pos (by linarith) hm0
  obtain ⟨ν₁, hν₁, Hgap⟩ := fmrVelGap b hb (2 * ε / m) hε'
  refine ⟨ν₁, hν₁, fun ν hν tr htr t s T ht hts hsT hθs ω hω => ?_⟩
  have hν0 : 0 < ν := hν.1
  let c := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  obtain ⟨M, hM⟩ := fmrVelBdd ν c hν0 hc tr htr T
  have hM' : ∃ M : ℝ, ∀ σ ∈ Icc t T, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M :=
    ⟨M, fun σ hσ x => hM σ ⟨ht.trans hσ.1, hσ.2⟩ x⟩
  obtain ⟨hint, hcont, hderiv⟩ := fmrDeriv c ν m t T tr.v ω hc hν0 ht hm0.le hω hM'
  refine ⟨fun σ hσ => hint σ ⟨hσ.1, hσ.2.trans hsT⟩,
    hcont.mono (Icc_subset_Icc le_rfl hsT),
    ⟨movRate ν c m tr.v ω, fun τ hτ => ⟨hderiv τ ⟨hτ.1, hτ.2.trans_le hsT⟩, ?_⟩⟩⟩
  have hτ0 : 0 ≤ τ := ht.trans hτ.1
  have hτs : τ ≤ s := hτ.2.le
  have hτT : τ ∈ Icc t T := ⟨hτ.1, hτs.trans hsT⟩
  have hτ0T : τ ∈ Icc 0 T := ⟨hτ0, hτs.trans hsT⟩
  let a := clockA ν τ
  have ha1 : 1 ≤ a := fd_clockA_ge_one hν0 hτ0
  have ha : 0 < a := by linarith
  have has : a ≤ clockA ν s := by
    change 1 + ν * τ ≤ 1 + ν * s; nlinarith
  have hθτ : b ≤ clockTheta ν τ := by
    refine hθs.trans ?_
    unfold clockTheta
    exact inv_anti₀ (mul_pos hν0 ha) (mul_le_mul_of_nonneg_left has hν0.le)
  have hνa_le : b * (ν * a) ≤ 1 := by
    have hθτ' : b ≤ (ν * a)⁻¹ := hθτ
    have := mul_le_mul_of_nonneg_right hθτ' (mul_pos hν0 ha).le
    rwa [inv_mul_cancel₀ (mul_pos hν0 ha).ne'] at this
  have hν_div_a : ν / a ≤ 1 / (b * a ^ 2) := by
    rw [div_le_div_iff₀ ha (mul_pos hb (sq_pos_of_pos ha))]
    nlinarith
  let g := ω τ
  have hg : CylSmoothDecay c g := hω.slice τ hτT
  have hMτ : ∃ M : ℝ, ∀ x : B0579.Plane, |tr.v τ x 0| + |tr.v τ x 1| ≤ M :=
    ⟨M, hM τ hτ0T⟩
  obtain ⟨hI_ibp1, hI_ibp2, h_ibp⟩ := fmrIBP ν c tr τ hτ0 hc hν0 hMτ m a hm0.le ha g hg
  have hI_w : IntegrableOn (fun x => g x ^ 2 * movWeight m a x) (B0579.cell c) := hint τ hτT
  have hI_dt : IntegrableOn (fun x => g x ^ 2 * movWeightDt ν m a x) (B0579.cell c) :=
    integrableOn_movWeightDt hν0.le hm0.le ha hg.smooth.continuous hI_w
  -- Pointwise bound on the cell
  have hpt : ∀ x ∈ B0579.cell c,
      g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
        (3 * ν / a) * (g x ^ 2 * movWeight m a x) +
        g x ^ 2 * movWeightDt ν m a x ≤
      2 * ((normGrowthConst m / b + ε) / a ^ 2) * (g x ^ 2 * movWeight m a x) := by
    intro x hx
    have hW0 : 0 ≤ movWeight m a x := by
      unfold movWeight
      exact Real.rpow_nonneg (by positivity) _
    have hbr := fmrBracket m hm1 ν a hν0.le ha x
    have hCm0 : 0 ≤ m ^ 2 + 3 * m + 3 := by positivity
    have hbr' : ν * lapP (movWeight m a) x + (3 * ν / a) * movWeight m a x + movWeightDt ν m a x ≤
        2 * (normGrowthConst m / b / a ^ 2) * movWeight m a x := by
      calc ν * lapP (movWeight m a) x + (3 * ν / a) * movWeight m a x + movWeightDt ν m a x
          ≤ (ν / a) * (m ^ 2 + 3 * m + 3) * movWeight m a x := hbr
        _ ≤ (1 / (b * a ^ 2)) * (m ^ 2 + 3 * m + 3) * movWeight m a x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hν_div_a hCm0) hW0
        _ = 2 * (normGrowthConst m / b / a ^ 2) * movWeight m a x := by
          unfold normGrowthConst; ring
    obtain ⟨hiso0, hpd0, hpd1⟩ := fmrIsoRadial m hm0.le ν τ ha x
    have hgap := Hgap ν hν tr htr τ hτ0 hθτ x hx
    have htr_eq : tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
        tr.v τ x 1 * B0579.pd 1 (movWeight m a) x =
        (tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1) * B0579.pd 0 (movWeight m a) x +
        (tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2) * B0579.pd 1 (movWeight m a) x := by
      change (UnforcedLeray.B0146.isoVelocity ν τ x).1 * B0579.pd 0 (movWeight m a) x +
        (UnforcedLeray.B0146.isoVelocity ν τ x).2 * B0579.pd 1 (movWeight m a) x = 0 at hiso0
      linarith
    have htr_le : tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
        tr.v τ x 1 * B0579.pd 1 (movWeight m a) x ≤
        2 * (ε / a ^ 2) * movWeight m a x := by
      change |B0579.pd 0 (movWeight m a) x| ≤ m / Real.sqrt a * movWeight m a x at hpd0
      change |B0579.pd 1 (movWeight m a) x| ≤ m / Real.sqrt a * movWeight m a x at hpd1
      change |tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1| +
        |tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2| ≤
        (2 * ε / m) * a ^ (-(3 / 2) : ℝ) at hgap
      rw [htr_eq]
      have h1 : (tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1) *
          B0579.pd 0 (movWeight m a) x ≤
          |tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1| *
            (m / Real.sqrt a * movWeight m a x) :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hpd0 (abs_nonneg _))
      have h2 : (tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2) *
          B0579.pd 1 (movWeight m a) x ≤
          |tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2| *
            (m / Real.sqrt a * movWeight m a x) :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hpd1 (abs_nonneg _))
      have hmW : 0 ≤ m / Real.sqrt a * movWeight m a x :=
        mul_nonneg (div_nonneg hm0.le (Real.sqrt_nonneg _)) hW0
      have h3 : (|tr.v τ x 0 - (UnforcedLeray.B0146.isoVelocity ν τ x).1| +
          |tr.v τ x 1 - (UnforcedLeray.B0146.isoVelocity ν τ x).2|) *
            (m / Real.sqrt a * movWeight m a x) ≤
          (2 * ε / m * a ^ (-(3 / 2) : ℝ)) * (m / Real.sqrt a * movWeight m a x) :=
        mul_le_mul_of_nonneg_right hgap hmW
      have h4 : (2 * ε / m * a ^ (-(3 / 2) : ℝ)) * (m / Real.sqrt a * movWeight m a x) =
          2 * (ε / a ^ 2) * movWeight m a x := by
        calc (2 * ε / m * a ^ (-(3 / 2) : ℝ)) * (m / Real.sqrt a * movWeight m a x)
            = (2 * ε / m * m) * (a ^ (-(3 / 2) : ℝ) / Real.sqrt a) * movWeight m a x := by ring
          _ = 2 * ε * (1 / a ^ 2) * movWeight m a x := by
            rw [div_mul_cancel₀ _ hm0.ne', rpow_neg_three_halves_div_sqrt ha]
          _ = 2 * (ε / a ^ 2) * movWeight m a x := by ring
      linarith
    have hrhs_eq : 2 * (normGrowthConst m / b / a ^ 2) * movWeight m a x +
        2 * (ε / a ^ 2) * movWeight m a x =
        2 * ((normGrowthConst m / b + ε) / a ^ 2) * movWeight m a x := by ring
    have hsum : (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
        (3 * ν / a) * movWeight m a x + movWeightDt ν m a x ≤
        2 * ((normGrowthConst m / b + ε) / a ^ 2) * movWeight m a x := by
      linarith
    calc g x ^ 2 * (ν * lapP (movWeight m a) x +
            (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
              tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
          (3 * ν / a) * (g x ^ 2 * movWeight m a x) +
          g x ^ 2 * movWeightDt ν m a x
        = g x ^ 2 * ((ν * lapP (movWeight m a) x +
            (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
              tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
          (3 * ν / a) * movWeight m a x + movWeightDt ν m a x) := by ring
      _ ≤ g x ^ 2 * (2 * ((normGrowthConst m / b + ε) / a ^ 2) * movWeight m a x) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = 2 * ((normGrowthConst m / b + ε) / a ^ 2) * (g x ^ 2 * movWeight m a x) := by ring
  -- Integrate the pointwise bound over the cell
  have hI_12 : IntegrableOn (fun x =>
      g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
        (3 * ν / a) * (g x ^ 2 * movWeight m a x)) (B0579.cell c) :=
    hI_ibp1.add (hI_w.const_mul (3 * ν / a))
  have hI_lhs : IntegrableOn (fun x =>
      g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
        (3 * ν / a) * (g x ^ 2 * movWeight m a x) +
        g x ^ 2 * movWeightDt ν m a x) (B0579.cell c) :=
    hI_12.add hI_dt
  have hI_rhs : IntegrableOn (fun x =>
      2 * ((normGrowthConst m / b + ε) / a ^ 2) * (g x ^ 2 * movWeight m a x)) (B0579.cell c) :=
    hI_w.const_mul _
  have hint_le := setIntegral_mono_on hI_lhs hI_rhs (B0579.measurableSet_cell c) hpt
  have hint_lhs_eq : (∫ x in B0579.cell c,
      (g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x)) +
        (3 * ν / a) * (g x ^ 2 * movWeight m a x) +
        g x ^ 2 * movWeightDt ν m a x)) =
      ((∫ x in B0579.cell c, g x ^ 2 * (ν * lapP (movWeight m a) x +
          (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
            tr.v τ x 1 * B0579.pd 1 (movWeight m a) x))) +
        (3 * ν / a) * (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x)) +
        (∫ x in B0579.cell c, g x ^ 2 * movWeightDt ν m a x) := by
    rw [integral_add hI_12 hI_dt, integral_add hI_ibp1 (hI_w.const_mul (3 * ν / a)),
      integral_const_mul]
  have hint_rhs_eq : (∫ x in B0579.cell c,
      2 * ((normGrowthConst m / b + ε) / a ^ 2) * (g x ^ 2 * movWeight m a x)) =
      2 * ((normGrowthConst m / b + ε) / a ^ 2) *
        (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x) :=
    integral_const_mul _ _
  rw [hint_lhs_eq, hint_rhs_eq] at hint_le
  -- Combine with IBP and multiply by a^3
  change 3 * ν * a ^ 2 * (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x) +
      a ^ 3 * (∫ x in B0579.cell c, g x ^ 2 * movWeightDt ν m a x) +
      2 * a ^ 3 * (∫ x in B0579.cell c,
        g x * (ν * lapP g x - (tr.v τ x 0 * B0579.pd 0 g x + tr.v τ x 1 * B0579.pd 1 g x)) *
          movWeight m a x) ≤
    2 * ((normGrowthConst m / b + ε) / a ^ 2) *
      (a ^ 3 * ∫ x in B0579.cell c, g x ^ 2 * movWeight m a x)
  have ha3 : 0 ≤ a ^ 3 := by positivity
  have h3νa : 3 * ν * a ^ 2 = a ^ 3 * (3 * ν / a) := by
    have : a ≠ 0 := ha.ne'
    field_simp
  calc 3 * ν * a ^ 2 * (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x) +
        a ^ 3 * (∫ x in B0579.cell c, g x ^ 2 * movWeightDt ν m a x) +
        2 * a ^ 3 * (∫ x in B0579.cell c,
          g x * (ν * lapP g x - (tr.v τ x 0 * B0579.pd 0 g x + tr.v τ x 1 * B0579.pd 1 g x)) *
            movWeight m a x)
      = a ^ 3 * ((3 * ν / a) * (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x) +
          (∫ x in B0579.cell c, g x ^ 2 * movWeightDt ν m a x) +
          2 * ∫ x in B0579.cell c,
            g x * (ν * lapP g x - (tr.v τ x 0 * B0579.pd 0 g x + tr.v τ x 1 * B0579.pd 1 g x)) *
              movWeight m a x) := by
        rw [h3νa]; ring
    _ ≤ a ^ 3 * (((∫ x in B0579.cell c, g x ^ 2 * (ν * lapP (movWeight m a) x +
            (tr.v τ x 0 * B0579.pd 0 (movWeight m a) x +
              tr.v τ x 1 * B0579.pd 1 (movWeight m a) x))) +
          (3 * ν / a) * (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x)) +
          (∫ x in B0579.cell c, g x ^ 2 * movWeightDt ν m a x)) := by
        refine mul_le_mul_of_nonneg_left ?_ ha3
        linarith [h_ibp]
    _ ≤ a ^ 3 * (2 * ((normGrowthConst m / b + ε) / a ^ 2) *
          (∫ x in B0579.cell c, g x ^ 2 * movWeight m a x)) :=
        mul_le_mul_of_nonneg_left hint_le ha3
    _ = 2 * ((normGrowthConst m / b + ε) / a ^ 2) *
          (a ^ 3 * ∫ x in B0579.cell c, g x ^ 2 * movWeight m a x) := by ring

end UnforcedLeray.Short.IIIa
