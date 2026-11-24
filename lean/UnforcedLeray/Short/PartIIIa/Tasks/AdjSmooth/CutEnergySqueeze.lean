import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace SqueezeAux

/-- Continuity of the energy on `[t, r₃]`, for a fixed `r₃ ∈ (t, s)`. -/
lemma cont_on_Icc
    {t s ν K : ℝ} {P Y : ℕ → ℝ → ℝ} {E : ℝ → ℝ} (hts : t < s) (hν : 0 < ν) (hK : 0 ≤ K)
    (hP : ∀ n, ContinuousOn (P n) (Ico t s)) (hY : ∀ n, ContinuousOn (Y n) (Ico t s))
    (hP0 : ∀ n, ∀ ρ ∈ Ico t s, 0 ≤ P n ρ) (hY0 : ∀ n, ∀ ρ ∈ Ico t s, 0 ≤ Y n ρ)
    (hmono : ∀ ρ ∈ Ico t s, Monotone fun n => Y n ρ)
    (hlim : ∀ ρ ∈ Ico t s, Tendsto (fun n => P n ρ) atTop (𝓝 (E ρ)))
    (hEint : ∀ r ∈ Ico t s, IntervalIntegrable E volume t r)
    (hder : ∀ n, ∀ ρ ∈ Ioo t s, ∃ D : ℝ, HasDerivAt (P n) D ρ ∧
      ν * Y n ρ - K * (1 + E ρ) ≤ D ∧ D ≤ 3 * ν * Y n ρ + K * (1 + E ρ))
    {r3 : ℝ} (hr3 : r3 ∈ Ioo t s) :
    ContinuousOn E (Icc t r3) := by
  obtain ⟨hr3t, hr3s⟩ := hr3
  have hr3' : r3 ∈ Ico t s := ⟨hr3t.le, hr3s⟩
  have hsub : Icc t r3 ⊆ Ico t s := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr3s⟩
  have hIoc : Ioc t r3 ⊆ Ioo t s := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr3s⟩
  have hIocIco : Ioc t r3 ⊆ Ico t s := hIoc.trans Ioo_subset_Ico_self
  -- derivatives
  have hD : ∀ n, ∀ ρ ∈ Ioo t s, HasDerivAt (P n) (deriv (P n) ρ) ρ ∧
      ν * Y n ρ - K * (1 + E ρ) ≤ deriv (P n) ρ ∧
        deriv (P n) ρ ≤ 3 * ν * Y n ρ + K * (1 + E ρ) := by
    intro n ρ hρ
    obtain ⟨D, hD1, hD2, hD3⟩ := hder n ρ hρ
    have e : deriv (P n) ρ = D := hD1.deriv
    rw [e]
    exact ⟨hD1, hD2, hD3⟩
  -- integrability on (t, r₃]
  have hYint : ∀ n, IntegrableOn (Y n) (Ioc t r3) := fun n =>
    (((hY n).mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hEI : IntegrableOn E (Ioc t r3) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr3t.le).1 (hEint r3 hr3')
  have hOne : IntegrableOn (fun ρ => 1 + E ρ) (Ioc t r3) :=
    (integrableOn_const (μ := volume) (C := (1 : ℝ)) measure_Ioc_lt_top.ne).add hEI
  have hLint : ∀ n, IntegrableOn (fun ρ => ν * Y n ρ - K * (1 + E ρ)) (Ioc t r3) := fun n =>
    ((hYint n).const_mul ν).sub (hOne.const_mul K)
  have hUint : ∀ n, IntegrableOn (fun ρ => 3 * ν * Y n ρ + K * (1 + E ρ)) (Ioc t r3) := fun n =>
    ((hYint n).const_mul (3 * ν)).add (hOne.const_mul K)
  have hDmeas : ∀ n, Measurable (deriv (P n)) := fun n => measurable_deriv _
  have hDint : ∀ n, IntegrableOn (deriv (P n)) (Ioc t r3) := by
    intro n
    refine Integrable.mono' (g := fun ρ => |ν * Y n ρ - K * (1 + E ρ)| +
        |3 * ν * Y n ρ + K * (1 + E ρ)|) ((hLint n).abs.add (hUint n).abs)
      (hDmeas n).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun ρ hρ => ?_)
    obtain ⟨-, h1, h2⟩ := hD n ρ (hIoc hρ)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (ν * Y n ρ - K * (1 + E ρ)),
      le_abs_self (ν * Y n ρ - K * (1 + E ρ)), neg_abs_le (3 * ν * Y n ρ + K * (1 + E ρ)),
      le_abs_self (3 * ν * Y n ρ + K * (1 + E ρ)), abs_nonneg (ν * Y n ρ - K * (1 + E ρ)),
      abs_nonneg (3 * ν * Y n ρ + K * (1 + E ρ))]
  have hIv : ∀ f : ℝ → ℝ, IntegrableOn f (Ioc t r3) → ∀ r1 r2, t ≤ r1 → r1 ≤ r2 → r2 ≤ r3 →
      IntervalIntegrable f volume r1 r2 := fun f hf r1 r2 h1 h12 h2 =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h12).2 (hf.mono_set (Ioc_subset_Ioc h1 h2))
  -- fundamental theorem on subintervals
  have hFTC : ∀ n, ∀ r1 r2, t ≤ r1 → r1 ≤ r2 → r2 ≤ r3 →
      ∫ x in r1..r2, deriv (P n) x = P n r2 - P n r1 := by
    intro n r1 r2 h1 h12 h2
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h12 ?_ ?_
      (hIv _ (hDint n) r1 r2 h1 h12 h2)
    · exact (hP n).mono (fun x hx => ⟨h1.trans hx.1, (hx.2.trans h2).trans_lt hr3s⟩)
    · intro x hx
      exact (hD n x ⟨h1.trans_lt hx.1, (hx.2.trans_le h2).trans hr3s⟩).1
  -- the nonnegativity of the limit
  have hE0 : ∀ ρ ∈ Ico t s, 0 ≤ E ρ := fun ρ hρ =>
    ge_of_tendsto' (hlim ρ hρ) (fun n => hP0 n ρ hρ)
  -- the uniform bound on P n r₃
  obtain ⟨C, hC⟩ := (hlim r3 hr3').bddAbove_range
  have hPC : ∀ n, P n r3 ≤ C := fun n => hC (Set.mem_range_self n)
  -- uniform bound on the time integral of Y n
  have hYnorm : ∀ n, ν * ∫ x in Ioc t r3, Y n x ≤ C + K * ∫ x in Ioc t r3, (1 + E x) := by
    intro n
    have h1 : ∫ x in Ioc t r3, ν * Y n x ≤
        ∫ x in Ioc t r3, (deriv (P n) x + K * (1 + E x)) := by
      refine setIntegral_mono_on ((hYint n).const_mul ν) ((hDint n).add (hOne.const_mul K))
        measurableSet_Ioc ?_
      intro x hx
      have := (hD n x (hIoc hx)).2.1
      linarith
    have hF := hFTC n t r3 le_rfl hr3t.le le_rfl
    rw [intervalIntegral.integral_of_le hr3t.le] at hF
    have hPt := hP0 n t ⟨le_rfl, hts⟩
    rw [integral_const_mul, integral_add (hDint n) (hOne.const_mul K), integral_const_mul, hF]
      at h1
    linarith [hPC n]
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = (C + K * ∫ x in Ioc t r3, (1 + E x)) / ν := ⟨_, rfl⟩
  have hIntY : ∀ n, ∫ x in Ioc t r3, Y n x ≤ Bd := by
    intro n
    rw [hBd, le_div_iff₀ hν]
    linarith [hYnorm n]
  -- the lower-integral of the sup
  obtain ⟨Yb, hYb⟩ : ∃ Yb : ℝ → ℝ≥0∞, ∀ ρ, Yb ρ = ⨆ n, ENNReal.ofReal (Y n ρ) :=
    ⟨fun ρ => ⨆ n, ENNReal.ofReal (Y n ρ), fun _ => rfl⟩
  have hYbfun : Yb = fun ρ => ⨆ n, ENNReal.ofReal (Y n ρ) := funext hYb
  have hmeasY : ∀ n, AEMeasurable (fun ρ => ENNReal.ofReal (Y n ρ))
      (volume.restrict (Ioc t r3)) := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hY n).mono hIocIco).aestronglyMeasurable measurableSet_Ioc).aemeasurable
  have hmonoY : ∀ᵐ ρ ∂(volume.restrict (Ioc t r3)), Monotone fun n => ENNReal.ofReal (Y n ρ) :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun ρ hρ a b hab =>
      ENNReal.ofReal_le_ofReal (hmono ρ (hIocIco hρ) hab))
  have hlint : ∫⁻ ρ in Ioc t r3, Yb ρ = ⨆ n, ∫⁻ ρ in Ioc t r3, ENNReal.ofReal (Y n ρ) := by
    simp only [hYb]
    exact lintegral_iSup' hmeasY hmonoY
  have hbdY : ∀ n, ∫⁻ ρ in Ioc t r3, ENNReal.ofReal (Y n ρ) ≤ ENNReal.ofReal Bd := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hYint n)
      (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun ρ hρ => hY0 n ρ (hIocIco hρ)))]
    exact ENNReal.ofReal_le_ofReal (hIntY n)
  have hfin : ∫⁻ ρ in Ioc t r3, Yb ρ ≠ ⊤ := by
    rw [hlint]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun n => hbdY n)
  have hmeasYb : AEMeasurable Yb (volume.restrict (Ioc t r3)) := by
    rw [hYbfun]
    exact AEMeasurable.iSup hmeasY
  have hYbae : ∀ᵐ ρ ∂(volume.restrict (Ioc t r3)), Yb ρ ≠ ⊤ :=
    (ae_lt_top' hmeasYb hfin).mono fun ρ hρ => hρ.ne
  -- the dominating function
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ ρ, h ρ = 3 * ν * (Yb ρ).toReal + K * (1 + E ρ) :=
    ⟨_, fun _ => rfl⟩
  have hhfun : h = fun ρ => 3 * ν * (Yb ρ).toReal + K * (1 + E ρ) := funext hh
  have hT : IntegrableOn (fun ρ => (Yb ρ).toReal) (Ioc t r3) :=
    integrable_toReal_of_lintegral_ne_top hmeasYb hfin
  have hhI : IntegrableOn h (Ioc t r3) := by
    rw [hhfun]
    exact (hT.const_mul (3 * ν)).add (hOne.const_mul K)
  have hIvh : ∀ r1 r2, t ≤ r1 → r1 ≤ r2 → r2 ≤ r3 → IntervalIntegrable h volume r1 r2 :=
    fun r1 r2 h1 h12 h2 => hIv h hhI r1 r2 h1 h12 h2
  -- the bound of the increments of P n by the integral of h
  have hbound : ∀ n, ∀ r1 r2, t ≤ r1 → r1 ≤ r2 → r2 ≤ r3 →
      |P n r2 - P n r1| ≤ ∫ x in r1..r2, h x := by
    intro n r1 r2 h1 h12 h2
    have hsubI : Ioc r1 r2 ⊆ Ioc t r3 := Ioc_subset_Ioc h1 h2
    have e1 : P n r2 - P n r1 = ∫ x in Ioc r1 r2, deriv (P n) x := by
      rw [← hFTC n r1 r2 h1 h12 h2, intervalIntegral.integral_of_le h12]
    rw [intervalIntegral.integral_of_le h12, e1]
    have up : ∫ x in Ioc r1 r2, deriv (P n) x ≤ ∫ x in Ioc r1 r2, h x := by
      refine setIntegral_mono_ae_restrict ((hDint n).mono_set hsubI) (hhI.mono_set hsubI) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubI hYbae,
        ae_restrict_mem measurableSet_Ioc] with ρ hρY hρI
      have hρ' : ρ ∈ Ioo t s := hIoc (hsubI hρI)
      have hYle : Y n ρ ≤ (Yb ρ).toReal := by
        have h1' : ENNReal.ofReal (Y n ρ) ≤ Yb ρ := by
          rw [hYb ρ]
          exact le_iSup (fun n => ENNReal.ofReal (Y n ρ)) n
        have h2' := ENNReal.toReal_mono hρY h1'
        rwa [ENNReal.toReal_ofReal (hY0 n ρ (Ioo_subset_Ico_self hρ'))] at h2'
      rw [hh ρ]
      have hu := (hD n ρ hρ').2.2
      have hmul : 3 * ν * Y n ρ ≤ 3 * ν * (Yb ρ).toReal :=
        mul_le_mul_of_nonneg_left hYle (by positivity)
      linarith
    have lo : -∫ x in Ioc r1 r2, h x ≤ ∫ x in Ioc r1 r2, deriv (P n) x := by
      rw [← integral_neg]
      refine setIntegral_mono_on (hhI.mono_set hsubI).neg ((hDint n).mono_set hsubI)
        measurableSet_Ioc ?_
      intro ρ hρ
      have hρ' : ρ ∈ Ioo t s := hIoc (hsubI hρ)
      have hd := (hD n ρ hρ').2.1
      have hYn : 0 ≤ ν * Y n ρ := mul_nonneg hν.le (hY0 n ρ (Ioo_subset_Ico_self hρ'))
      have hYb0 : 0 ≤ 3 * ν * (Yb ρ).toReal :=
        mul_nonneg (by positivity) ENNReal.toReal_nonneg
      rw [hh ρ]
      linarith
    exact abs_le.2 ⟨by linarith, by linarith⟩
  -- Lipschitz bound for the limit
  have hlip : ∀ r1 r2, t ≤ r1 → r1 ≤ r2 → r2 ≤ r3 → |E r2 - E r1| ≤ ∫ x in r1..r2, h x := by
    intro r1 r2 h1 h12 h2
    have hr1 : r1 ∈ Ico t s := ⟨h1, (h12.trans h2).trans_lt hr3s⟩
    have hr2 : r2 ∈ Ico t s := ⟨h1.trans h12, h2.trans_lt hr3s⟩
    have hT1 := ((hlim r2 hr2).sub (hlim r1 hr1)).abs
    exact le_of_tendsto hT1 (Eventually.of_forall fun n => hbound n r1 r2 h1 h12 h2)
  -- the primitive of h is continuous
  have hsplit : ∀ a b, t ≤ a → a ≤ b → b ≤ r3 →
      ∫ x in a..b, h x = (∫ x in t..b, h x) - ∫ x in t..a, h x := by
    intro a b ha hab hb
    exact (intervalIntegral.integral_interval_sub_left (hIvh t b le_rfl (le_trans ha hab)
      hb) (hIvh t a le_rfl ha (le_trans hab hb))).symm
  have hFint : IntegrableOn h (uIcc t r3) := by
    rw [uIcc_of_le hr3t.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioc' (by simp) (by simp)).2 hhI
  have hFc : ContinuousOn (fun x => ∫ u in t..x, h u) (Icc t r3) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := t) (b := r3) hFint
    rwa [uIcc_of_le hr3t.le] at this
  intro r hr
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.1 (hFc r hr) ε hε
  refine ⟨δ, hδ, fun {x} hx hxr => ?_⟩
  have hF' := hδF hx hxr
  rw [Real.dist_eq] at hF' ⊢
  have key : |E x - E r| ≤ |(∫ u in t..x, h u) - ∫ u in t..r, h u| := by
    rcases le_total x r with hxr' | hrx
    · have h1 := hlip x r hx.1 hxr' hr.2
      rw [hsplit x r hx.1 hxr' hr.2] at h1
      have h2 : (∫ u in t..r, h u) - ∫ u in t..x, h u ≤
          |(∫ u in t..x, h u) - ∫ u in t..r, h u| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      rw [abs_sub_comm (E x)]
      exact h1.trans h2
    · have h1 := hlip r x hr.1 hrx hx.2
      rw [hsplit r x hr.1 hrx hx.2] at h1
      exact h1.trans (le_abs_self _)
  exact lt_of_le_of_lt key hF'

end SqueezeAux

theorem cutEnergySqueeze : UnforcedLeray.Short.IIIa.CutEnergySqueeze := by
  intro t s ν K P Y E hts hν hK hP hY hP0 hY0 hmono hlim hEint hder r hr
  have hr3 : (r + s) / 2 ∈ Ioo t s := ⟨by linarith [hr.1, hr.2], by linarith [hr.2]⟩
  have hc := SqueezeAux.cont_on_Icc hts hν hK hP hY hP0 hY0 hmono hlim hEint hder hr3
  have hrI : r ∈ Icc t ((r + s) / 2) := ⟨hr.1, by linarith [hr.2]⟩
  have hmem : Icc t ((r + s) / 2) ∈ 𝓝[Ico t s] r := by
    refine mem_nhdsWithin.2 ⟨Iio ((r + s) / 2), isOpen_Iio, ?_, fun x hx => ⟨hx.2.1, hx.1.le⟩⟩
    show r < (r + s) / 2
    linarith [hr.2]
  exact (hc r hrI).mono_of_mem_nhdsWithin hmem

end UnforcedLeray.Short.IIIa
