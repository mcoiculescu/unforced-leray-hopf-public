import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.lineInterpR

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace CgiEtaProof

/-- The `η`-derivative of `v` along the line `t ↦ (s, (q, t))` (SP 1932, chain rule). -/
theorem hasDerivAt_eta {v : Coord → ℂ} (hv : Differentiable ℝ v) (s q t : ℝ) :
    HasDerivAt (fun t : ℝ => v (s, (q, t))) (cdv 2 v (s, (q, t))) t := by
  have h := (hasDerivAt_const t s).prodMk ((hasDerivAt_const t q).prodMk (hasDerivAt_id' t))
  have hc : cdir 2 = ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := rfl
  have hl : HasDerivAt (fun t : ℝ => ((s, (q, t)) : Coord)) (cdir 2) t := by
    rw [hc]; exact h
  exact (hv (s, (q, t))).hasFDerivAt.comp_hasDerivAt t hl

theorem contDiff_cdv {v : Coord → ℂ} (hv : ContDiff ℝ ∞ v) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j v) := by
  unfold cdv
  exact (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem diff_of_contDiff {v : Coord → ℂ} (hv : ContDiff ℝ ∞ v) : Differentiable ℝ v :=
  hv.differentiable (by simp)

/-- `L^r` norm as a lintegral power. -/
theorem eLpNorm_eq_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {r : ℝ} (hr : 1 < r)
    (f : α → ℂ) : eLpNorm f (ENNReal.ofReal r) μ = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (zero_lt_one.trans hr)).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (zero_lt_one.trans hr).le]

/-- The `η`-slice `L^r` norm of `f` over the line through `(s, q)`. -/
def sl (r : ℝ) (f : Coord → ℂ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ => f (z.1, (z.2, t))) (ENNReal.ofReal r) volume

/-- The measure `ds ⊗ (dq restricted to the cell)` on the `(s, q)` plane. -/
def muT (c : ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume.restrict (Ico (-c / 2) (c / 2)))

theorem meas_slice_lintegral {F : Coord → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun z : ℝ × ℝ => ∫⁻ t, F (z.1, (z.2, t))) := by
  have hmap : Measurable (fun p : (ℝ × ℝ) × ℝ => ((p.1.1, (p.1.2, p.2)) : Coord)) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  exact Measurable.lintegral_prod_right' (f := fun p : (ℝ × ℝ) × ℝ => F (p.1.1, (p.1.2, p.2)))
    (hF.comp hmap)

theorem meas_sl {f : Coord → ℂ} (hf : Measurable f) {r : ℝ} (hr : 1 < r) :
    Measurable (sl r f) := by
  have hfun : sl r f = fun z : ℝ × ℝ => (∫⁻ t, ‖f (z.1, (z.2, t))‖ₑ ^ r) ^ (1 / r) := by
    funext z
    exact eLpNorm_eq_rpow hr _
  rw [hfun]
  exact (meas_slice_lintegral (F := fun x => ‖f x‖ₑ ^ r) (hf.enorm.pow_const r)).pow_const _

/-- Fubini from `cylMeas c = ds ⊗ (dq/c dη on the cell)` to `muT c`. -/
theorem lintegral_cylMeas (c : ℝ) {F : Coord → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(cylMeas c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ z, (∫⁻ t, F (z.1, (z.2, t))) ∂(muT c) := by
  have inner : ∀ s : ℝ, ∫⁻ y, F (s, y) ∂(UnforcedLeray.Cyl.avgμ c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ t, F (s, (q, t)) := by
    intro s
    have hm : Measurable (fun y : ℝ × ℝ => ((s, y) : Coord)) :=
      measurable_const.prodMk measurable_id
    rw [UnforcedLeray.Cyl.lintegral_avgμ,
      UnforcedLeray.Cyl.lintegral_cell_eq (f := fun y : ℝ × ℝ => F (s, y))
        ((hF.comp hm).aemeasurable)]
  have hΦ : Measurable (fun z : ℝ × ℝ => ∫⁻ t, F (z.1, (z.2, t))) :=
    meas_slice_lintegral hF
  unfold cylMeas
  rw [lintegral_prod F hF.aemeasurable]
  simp only [inner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  unfold muT
  rw [lintegral_prod _ hΦ.aemeasurable]

/-- Cylinder `L^r` norm as a constant times the `(s,q)`-plane norm of the `η`-slices. -/
theorem cylNorm_eq {c r : ℝ} (hr : 1 < r) {f : Coord → ℂ} (hf : Measurable f) :
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) =
      ENNReal.ofReal c⁻¹ ^ (1 / r) * (∫⁻ z, sl r f z ^ r ∂(muT c)) ^ (1 / r) := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hpos : (0 : ℝ) ≤ 1 / r := (div_pos zero_lt_one (zero_lt_one.trans hr)).le
  have hint : (∫⁻ z, (∫⁻ t, ‖f (z.1, (z.2, t))‖ₑ ^ r) ∂(muT c)) =
      ∫⁻ z, sl r f z ^ r ∂(muT c) := by
    refine lintegral_congr fun z => ?_
    unfold sl
    rw [eLpNorm_eq_rpow hr, one_div, ENNReal.rpow_inv_rpow hr0]
  have h1 := lintegral_cylMeas c (F := fun x => ‖f x‖ₑ ^ r) (hf.enorm.pow_const r)
  rw [eLpNorm_eq_rpow hr, h1, hint, ENNReal.mul_rpow_of_nonneg _ _ hpos]

/-- Minkowski's inequality in `L^r(μ)` for ENNReal-valued functions with a pointwise domination
`A ≤ a B + b E`. -/
theorem mink_enn {α : Type*} [MeasurableSpace α] {μ : Measure α} {r : ℝ} (hr : 1 ≤ r)
    {A B E : α → ℝ≥0∞} (_hA : Measurable A) (hB : Measurable B) (hE : Measurable E)
    {a b : ℝ≥0∞} (h : ∀ x, A x ≤ a * B x + b * E x) :
    (∫⁻ x, A x ^ r ∂μ) ^ (1 / r) ≤
      a * (∫⁻ x, B x ^ r ∂μ) ^ (1 / r) + b * (∫⁻ x, E x ^ r ∂μ) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hpos : (0 : ℝ) ≤ 1 / r := (div_pos zero_lt_one hr0).le
  have hpow : ∀ x : ℝ≥0∞, (x ^ r) ^ (1 / r) = x := fun x => by
    rw [one_div]; exact ENNReal.rpow_rpow_inv hr0.ne' x
  have hmul : ∀ (k : ℝ≥0∞) (G : α → ℝ≥0∞), Measurable G →
      ∫⁻ x, (k * G x) ^ r ∂μ = k ^ r * ∫⁻ x, G x ^ r ∂μ := by
    intro k G hG
    have hk : ∀ x, (k * G x) ^ r = k ^ r * G x ^ r := fun x => ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    simp only [hk]
    exact lintegral_const_mul'' _ (hG.pow_const r).aemeasurable
  have hmono : (∫⁻ x, A x ^ r ∂μ) ≤ ∫⁻ x, (a * B x + b * E x) ^ r ∂μ :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (h x) hr0.le
  have hM : (∫⁻ x, (a * B x + b * E x) ^ r ∂μ) ^ (1 / r) ≤
      (∫⁻ x, (a * B x) ^ r ∂μ) ^ (1 / r) + (∫⁻ x, (b * E x) ^ r ∂μ) ^ (1 / r) :=
    ENNReal.lintegral_Lp_add_le (f := fun x => a * B x) (g := fun x => b * E x)
      (measurable_const.mul hB).aemeasurable (measurable_const.mul hE).aemeasurable hr
  calc (∫⁻ x, A x ^ r ∂μ) ^ (1 / r) ≤ (∫⁻ x, (a * B x + b * E x) ^ r ∂μ) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hmono hpos
    _ ≤ _ := hM
    _ = a * (∫⁻ x, B x ^ r ∂μ) ^ (1 / r) + b * (∫⁻ x, E x ^ r ∂μ) ^ (1 / r) := by
        rw [hmul a B hB, hmul b E hE, ENNReal.mul_rpow_of_nonneg _ _ hpos,
          ENNReal.mul_rpow_of_nonneg _ _ hpos, hpow, hpow]

end CgiEtaProof

open CgiEtaProof

/-- **Leaf (A, `η` direction).** Slice-wise (`s`, `q` fixed, line in `η`) `LineInterpR`, then
Minkowski/Fubini over `cylMeas c`: for nice `w`, `‖∂_η w‖ ≤ C (λ⁻¹‖w‖ + λ ‖∂_η² w‖)`. -/
theorem cgiAprioriEta_proof : UnforcedLeray.Short.IIb.CgiAprioriEta := by
  intro r hr
  have hLI : UnforcedLeray.Short.IIb.LineInterpR := lineInterpR_proof
  obtain ⟨C, hC, hL⟩ := hLI r hr
  refine ⟨C, hC, fun c hc w hw lam hlam => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := hr.le
  have hwS : ContDiff ℝ ∞ w := hw.smooth
  have hwD : ContDiff ℝ ∞ (cdv 2 w) := contDiff_cdv hwS 2
  have hwDD : ContDiff ℝ ∞ (cdv 2 (cdv 2 w)) := contDiff_cdv hwD 2
  have hwd : Differentiable ℝ w := diff_of_contDiff hwS
  have hwDd : Differentiable ℝ (cdv 2 w) := diff_of_contDiff hwD
  -- slice-wise one-dimensional interpolation
  have hslice : ∀ z : ℝ × ℝ, sl r (cdv 2 w) z ≤
      ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * sl r w z +
        ENNReal.ofReal lam * sl r (cdv 2 (cdv 2 w)) z) := by
    intro z
    have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hC).ne'
    have hl0 : ENNReal.ofReal lam⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hlam)).ne'
    have hl1 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.2 hlam).ne'
    by_cases hfin : sl r w z < ⊤ ∧ sl r (cdv 2 (cdv 2 w)) z < ⊤
    · obtain ⟨h1, h2⟩ := hfin
      have hline : ContDiff ℝ ∞ (fun t : ℝ => ((z.1, (z.2, t)) : Coord)) :=
        contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
      have hg : ContDiff ℝ 2 (fun t : ℝ => w (z.1, (z.2, t))) :=
        (hwS.comp hline).of_le (by simp)
      have hd1 : deriv (fun t : ℝ => w (z.1, (z.2, t))) = fun t => cdv 2 w (z.1, (z.2, t)) :=
        funext fun t => (hasDerivAt_eta hwd z.1 z.2 t).deriv
      have hd2 : deriv (deriv (fun t : ℝ => w (z.1, (z.2, t)))) =
          fun t => cdv 2 (cdv 2 w) (z.1, (z.2, t)) := by
        rw [hd1]
        exact funext fun t => (hasDerivAt_eta hwDd z.1 z.2 t).deriv
      have key := hL (fun t : ℝ => w (z.1, (z.2, t))) hg (by exact h1)
        (by rw [hd2]; exact h2) lam hlam
      rw [hd2, hd1] at key
      exact key
    · have hRHS : ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * sl r w z +
          ENNReal.ofReal lam * sl r (cdv 2 (cdv 2 w)) z) = ⊤ := by
        rcases not_and_or.1 hfin with h | h
        · rw [not_lt, top_le_iff] at h
          rw [h, ENNReal.mul_top hl0, top_add, ENNReal.mul_top hC0]
        · rw [not_lt, top_le_iff] at h
          rw [h, ENNReal.mul_top hl1, add_top, ENNReal.mul_top hC0]
      rw [hRHS]
      exact le_top
  -- Minkowski over the `(s, q)` plane
  have hmeasA : Measurable (sl r (cdv 2 w)) := meas_sl hwD.continuous.measurable hr
  have hmeasB : Measurable (sl r w) := meas_sl hwS.continuous.measurable hr
  have hmeasE : Measurable (sl r (cdv 2 (cdv 2 w))) := meas_sl hwDD.continuous.measurable hr
  have hmink := mink_enn (μ := muT c) (r := r) hr1 hmeasA hmeasB hmeasE
    (a := ENNReal.ofReal C * ENNReal.ofReal lam⁻¹) (b := ENNReal.ofReal C * ENNReal.ofReal lam)
    (fun z => (hslice z).trans (le_of_eq (by ring)))
  unfold cylNorm
  rw [cylNorm_eq (c := c) hr hwD.continuous.measurable,
    cylNorm_eq (c := c) hr hwS.continuous.measurable,
    cylNorm_eq (c := c) hr hwDD.continuous.measurable]
  refine le_trans (mul_le_mul_of_nonneg_left hmink zero_le) (le_of_eq ?_)
  ring

end UnforcedLeray.Short.IIb
