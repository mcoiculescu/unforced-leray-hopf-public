import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Units.B0123
import NonUniqueEuler.P.Infra.ODE.Gronwall

/-!
# Target `PartI:C05/2`: `mildComplementCocycle`

Source of record: `the November 2 reference manuscript`, the iteration over
blocks in the proof of `lem:short-diffusion-complement`.

Method. Write `A = e^{(∫_r^t β)D}`. Splitting the Duhamel identity of `U(·,s)x` at `r` gives
`U(t,s)x = A(U(r,s)x) + ∫_r^t e^{(∫_u^t β)D} B(u) U(u,s)x du`, and the Duhamel identity of
`U(·,r)y` with `y = U(r,s)x` gives the same formula with `U(u,r)y`. The difference `D(t)` of the
two therefore satisfies `D(t) = ∫_r^t e^{(∫_u^t β)D} B(u) D(u) du`, so `‖D(t)‖ ≤ M ∫_r^t ‖D(u)‖ du`
with `M` a bound for `‖B(u)‖`, and the integral Gronwall inequality with zero constant gives
`D ≡ 0` on `[r,t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- A bounded measurable real function is interval integrable. -/
theorem mcc_intervalIntegrable_beta {β : ℝ → ℝ} (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1) (a b : ℝ) :
    IntervalIntegrable β volume a b := by
  refine IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := (1 : ℝ)))
    hβm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  show ‖β x‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hβ x).1], (hβ x).2⟩

theorem mcc_uIcc_sub_of_le {a b c d : ℝ} (h1 : a ≤ c) (h2 : c ≤ d) (h3 : d ≤ b) :
    Set.uIcc c d ⊆ Set.uIcc a b := by
  rw [Set.uIcc_of_le (h1.trans (h2.trans h3)), Set.uIcc_of_le h2]
  exact Set.Icc_subset_Icc h1 h3

/-- Semigroup splitting of the free group over `[u,t]` at `r`. -/
theorem mcc_expD_split {β : ℝ → ℝ} (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {u r t : ℝ} (hur : u ≤ r) (hrt : r ≤ t) :
    B0123.expD (∫ v in u..t, β v) =
      (B0123.expD (∫ v in r..t, β v)).comp (B0123.expD (∫ v in u..r, β v)) := by
  have hsplit : ∫ v in u..t, β v = (∫ v in r..t, β v) + ∫ v in u..r, β v := by
    linarith [intervalIntegral.integral_add_adjacent_intervals
      (mcc_intervalIntegrable_beta hβm hβ u r) (mcc_intervalIntegrable_beta hβm hβ r t)]
  have hnn1 : 0 ≤ ∫ v in u..r, β v := intervalIntegral.integral_nonneg hur fun v _ => (hβ v).1
  have hnn2 : 0 ≤ ∫ v in r..t, β v := intervalIntegral.integral_nonneg hrt fun v _ => (hβ v).1
  rw [hsplit, B0123.expD_add hnn2 hnn1]

/-- Splitting of the Duhamel identity of `U(·,s)x` at the intermediate time `r`. -/
theorem mcc_split_identity {β : ℝ → ℝ} (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {B : ℝ → B0010.XG →L[ℂ] B0010.XG} {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hint : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u) (B r (U r s x))) volume s t)
    (hdu : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      U t s x = B0123.expD (∫ u in s..t, β u) x +
        ∫ r in s..t, B0123.expD (∫ u in r..t, β u) (B r (U r s x)))
    {s r t : ℝ} (hsr : s ≤ r) (hrt : r ≤ t) (x : B0010.XG) :
    U t s x = B0123.expD (∫ u in r..t, β u) (U r s x) +
      ∫ u in r..t, B0123.expD (∫ v in u..t, β v) (B u (U u s x)) := by
  have hst : s ≤ t := hsr.trans hrt
  have hsplit : ∫ v in s..t, β v = (∫ v in r..t, β v) + ∫ v in s..r, β v := by
    linarith [intervalIntegral.integral_add_adjacent_intervals
      (mcc_intervalIntegrable_beta hβm hβ s r) (mcc_intervalIntegrable_beta hβm hβ r t)]
  have hnn1 : 0 ≤ ∫ v in s..r, β v := intervalIntegral.integral_nonneg hsr fun v _ => (hβ v).1
  have hnn2 : 0 ≤ ∫ v in r..t, β v := intervalIntegral.integral_nonneg hrt fun v _ => (hβ v).1
  have hGsplit : ∫ u in s..t, B0123.expD (∫ v in u..t, β v) (B u (U u s x)) =
      (∫ u in s..r, B0123.expD (∫ v in u..t, β v) (B u (U u s x))) +
        ∫ u in r..t, B0123.expD (∫ v in u..t, β v) (B u (U u s x)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hint s t hst x).mono_set (mcc_uIcc_sub_of_le le_rfl hsr hrt))
      ((hint s t hst x).mono_set (mcc_uIcc_sub_of_le hsr hrt le_rfl))).symm
  have hA : ∫ u in s..r, B0123.expD (∫ v in u..t, β v) (B u (U u s x)) =
      ∫ u in s..r, B0123.expD (∫ v in r..t, β v)
        (B0123.expD (∫ v in u..r, β v) (B u (U u s x))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hsr] at hu
    show B0123.expD (∫ v in u..t, β v) (B u (U u s x)) = _
    rw [mcc_expD_split hβm hβ hu.2 hrt]
    rfl
  have hcomm : B0123.expD (∫ v in r..t, β v) (U r s x) =
      B0123.expD (∫ v in r..t, β v) (B0123.expD (∫ v in s..r, β v) x) +
        ∫ u in s..r, B0123.expD (∫ v in r..t, β v)
          (B0123.expD (∫ v in u..r, β v) (B u (U u s x))) := by
    conv_lhs => rw [hdu s r hsr x]
    rw [map_add]
    congr 1
    exact (ContinuousLinearMap.intervalIntegral_comp_comm _ (hint s r hsr x)).symm
  have hEsplit : B0123.expD (∫ v in s..t, β v) x =
      B0123.expD (∫ v in r..t, β v) (B0123.expD (∫ v in s..r, β v) x) := by
    rw [hsplit, B0123.expD_add hnn2 hnn1, ContinuousLinearMap.comp_apply]
  rw [hdu s t hst x, hGsplit, hEsplit, hA, hcomm]
  abel

/-- Cocycle property for a mild evolution given the Duhamel identity, via Gronwall. -/
theorem mcc_cocycle_core {β : ℝ → ℝ} (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {B : ℝ → B0010.XG →L[ℂ] B0010.XG} {M : ℝ} (hBM : ∀ u, ‖B u‖ ≤ M)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hcont : ∀ (s : ℝ) (x : B0010.XG), ContinuousOn (fun t => U t s x) (Ici s))
    (hint : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u) (B r (U r s x))) volume s t)
    (hdu : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      U t s x = B0123.expD (∫ u in s..t, β u) x +
        ∫ r in s..t, B0123.expD (∫ u in r..t, β u) (B r (U r s x)))
    {s r t : ℝ} (hsr : s ≤ r) (hrt : r ≤ t) (x : B0010.XG) :
    U t s x = U t r (U r s x) := by
  have key : ∀ t' : ℝ, r ≤ t' →
      U t' s x - U t' r (U r s x) = ∫ u in r..t',
        B0123.expD (∫ v in u..t', β v) (B u (U u s x - U u r (U r s x))) := by
    intro t' ht'
    have h1 := mcc_split_identity hβm hβ (B := B) (U := U) hint hdu hsr ht' x
    have h2 := hdu r t' ht' (U r s x)
    have hintV : IntervalIntegrable (fun u => B0123.expD (∫ v in u..t', β v) (B u (U u s x)))
        volume r t' :=
      (hint s t' (hsr.trans ht') x).mono_set (mcc_uIcc_sub_of_le hsr ht' le_rfl)
    have hintW : IntervalIntegrable
        (fun u => B0123.expD (∫ v in u..t', β v) (B u (U u r (U r s x)))) volume r t' :=
      hint r t' ht' (U r s x)
    rw [h1, h2, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hintV hintW]
    exact intervalIntegral.integral_congr fun u _ => by simp only [map_sub]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hBM 0)
  have hDc : ContinuousOn (fun u => U u s x - U u r (U r s x)) (Ici r) :=
    ((hcont s x).mono (Ici_subset_Ici.2 hsr)).sub (hcont r (U r s x))
  have hnD : ContinuousOn (fun u => ‖U u s x - U u r (U r s x)‖) (Icc r t) :=
    (hDc.mono Icc_subset_Ici_self).norm
  have hbd : ∀ t' ∈ Icc r t,
      ‖U t' s x - U t' r (U r s x)‖ ≤ ∫ u in r..t', M * ‖U u s x - U u r (U r s x)‖ := by
    intro t' ht'
    rw [key t' ht'.1]
    refine intervalIntegral.norm_integral_le_of_norm_le ht'.1
      (Filter.Eventually.of_forall fun u hu => ?_) ?_
    · have hBu := hBM u
      calc ‖B0123.expD (∫ v in u..t', β v) (B u (U u s x - U u r (U r s x)))‖
          ≤ ‖B0123.expD (∫ v in u..t', β v)‖ * ‖B u (U u s x - U u r (U r s x))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖B u‖ * ‖U u s x - U u r (U r s x)‖) :=
            mul_le_mul (B0123.norm_expD_le _) (ContinuousLinearMap.le_opNorm (B u) _)
              (norm_nonneg _) zero_le_one
        _ ≤ 1 * (M * ‖U u s x - U u r (U r s x)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBu (norm_nonneg _)) zero_le_one
        _ = M * ‖U u s x - U u r (U r s x)‖ := one_mul _
    · have hc : ContinuousOn (fun u => M * ‖U u s x - U u r (U r s x)‖) (uIcc r t') := by
        rw [Set.uIcc_of_le ht'.1]
        exact continuousOn_const.mul (hnD.mono (Icc_subset_Icc le_rfl ht'.2))
      exact hc.intervalIntegrable
  have hG := NonUniqueEuler.LinODE.int_gronwall
    (u := fun u => ‖U u s x - U u r (U r s x)‖) (b := fun _ => M) (c := 0)
    (α := r) (β := t) hnD continuousOn_const (fun _ _ => hM0) le_rfl
    (fun x' hx' => by simpa only [zero_add] using hbd x' hx')
  have h0 := hG t ⟨hrt, le_rfl⟩
  simp only [zero_add, zero_mul] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- Norm bound on the generator `B_b` for `0 ≤ b ≤ 1`. -/
theorem mcc_norm_B_le (lam : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (κ : ℂ) (Rf : B0010.XG →L[ℂ] B0010.XG) {b : ℝ} (hb : 0 ≤ b ∧ b ≤ 1) :
    ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q - (b * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (b : ℂ) • Rf‖ ≤
      ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q‖ + ‖κ‖ + ‖Rf‖ := by
  have hbc : ‖(b : ℂ) * κ‖ ≤ ‖κ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hA : ‖((b : ℂ) * κ) • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ ‖κ‖ := by
    rw [norm_smul]
    calc ‖(b : ℂ) * κ‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ ‖κ‖ * 1 :=
          mul_le_mul hbc ContinuousLinearMap.norm_id_le (norm_nonneg _) (norm_nonneg _)
      _ = ‖κ‖ := mul_one _
  have hC : ‖(b : ℂ) • Rf‖ ≤ ‖Rf‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have h1 := norm_add_le (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    (b * κ) • (1 : B0010.XG →L[ℂ] B0010.XG)) ((b : ℂ) • Rf)
  have h2 := norm_sub_le (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q)
    ((b * κ) • (1 : B0010.XG →L[ℂ] B0010.XG))
  linarith

/-- **Target `PartI:C05/2`** (source lines 1048-1052): cocycle of the mild complementary
evolution. -/
theorem mildComplementCocycle : MildComplementCocycle := by
  intro lam q l _hseed qd _hl hq hqd β hβm hβ U hU s r t hsr hrt
  have hU' : IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U :=
    hU
  have hBM : ∀ u, ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
      (β u * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
        (β u : ℂ) • seedRf l q qd hq hqd)‖ ≤
      ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q‖ +
        ‖seedKappa l q hq‖ + ‖seedRf l q qd hq hqd‖ :=
    fun u => mcc_norm_B_le lam l q _ _ (hβ u)
  refine ContinuousLinearMap.ext fun x => ?_
  show U t s x = U t r (U r s x)
  exact mcc_cocycle_core hβm hβ (B := fun u => Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
      l.smulRight q - (β u * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
        (β u : ℂ) • seedRf l q qd hq hqd) (hBM) (U := U)
    (fun s' x' => hU'.cont s' x') (fun s' t' hst x' => hU'.integrable s' t' hst x')
    (fun s' t' hst x' => hU'.duhamel s' t' hst x') hsr hrt x

end UnforcedLeray.Short.PartI
