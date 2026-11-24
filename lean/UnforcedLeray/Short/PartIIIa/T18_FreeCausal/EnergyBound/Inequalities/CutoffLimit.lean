import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.RampFamily

/-!
# Part III-a, task `PartIII-a:T18/3/2/2` (cutoffLimit): scalar cutoff limit

Source: `the November 2 reference manuscript` lines 3541-3552.
This file holds the compiled integrability helpers for the cutoff limit. The main theorem

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A compact subset of `(0,∞)` lies in some `Icc a b` with `0 < a`. -/
theorem compact_Ioi_bounds {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ K ⊆ Icc a b := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, 1, one_pos, by simp [h]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn h continuousOn_id
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn h continuousOn_id
    refine ⟨x, y, hK0 hx, fun z hz => ⟨?_, ?_⟩⟩
    · exact isMinOn_iff.1 hmin z hz
    · exact isMaxOn_iff.1 hmax z hz

/-- Integrability of a cutoff times a locally integrable function, on `(0,∞)`. -/
theorem integrable_cutoff_mul {ψ g : ℝ → ℝ} {a b : ℝ} (hψ : ContDiff ℝ 1 ψ) (ha : 0 < a)
    (hsupp : tsupport ψ ⊆ Icc a b) (hg : IntegrableOn g (Icc a b)) :
    IntegrableOn (fun s => ψ s * g s) (Ioi 0) := by
  have hcont : ContinuousOn ψ (Icc a b) := hψ.continuous.continuousOn
  have h1 : IntegrableOn (fun s => g s * ψ s) (Icc a b) :=
    hg.mul_continuousOn hcont isCompact_Icc
  have h2 : IntegrableOn (fun s => ψ s * g s) (Icc a b) := by
    simpa only [mul_comm] using h1
  have hsub : Function.support (fun s => ψ s * g s) ⊆ Icc a b :=
    (Function.support_mul_subset_left ψ g).trans ((subset_tsupport ψ).trans hsupp)
  have hI : Integrable (fun s => ψ s * g s) := (integrableOn_iff_integrable_of_support_subset hsub).1 h2
  exact hI.integrableOn


/-- Integrability of a continuous cutoff times a locally integrable function. -/
theorem integrable_contcutoff_mul {φ g : ℝ → ℝ} {a b : ℝ} (hφ : Continuous φ) (ha : 0 < a)
    (hsupp : tsupport φ ⊆ Icc a b) (hg : IntegrableOn g (Icc a b)) :
    IntegrableOn (fun s => φ s * g s) (Ioi 0) := by
  have h1 : IntegrableOn (fun s => φ s * g s) (Icc a b) :=
    hg.continuousOn_mul hφ.continuousOn isCompact_Icc |>.congr_fun (fun _ _ => rfl) measurableSet_Icc
  have hsub : Function.support (fun s => φ s * g s) ⊆ Icc a b :=
    (Function.support_mul_subset_left φ g).trans ((subset_tsupport φ).trans hsupp)
  exact ((integrableOn_iff_integrable_of_support_subset hsub).1 h1).integrableOn

/-- `s^r * g` is integrable on `[a,b]`, `a > 0`. -/
theorem intOn_rpow_mul {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hg : IntegrableOn g (Icc a b))
    (r : ℝ) : IntegrableOn (fun s => s ^ r * g s) (Icc a b) := by
  refine IntegrableOn.continuousOn_mul (g := fun s => s ^ r) ?_ hg isCompact_Icc
  exact fun s hs => (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt (lt_of_lt_of_le ha hs.1)))).continuousWithinAt

theorem ofReal_integral_le_lintegral' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) :
    ENNReal.ofReal (∫ x, h x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
  have hp : Integrable (fun x => max (h x) 0) μ := hh.pos_part
  calc ENNReal.ofReal (∫ x, h x ∂μ) ≤ ENNReal.ofReal (∫ x, max (h x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hh hp (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (h x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall fun x => le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
        congr 1
        funext x
        rcases le_total (h x) 0 with h0 | h0
        · rw [max_eq_right h0, ENNReal.ofReal_of_nonpos h0]; simp
        · rw [max_eq_left h0]

/-- The real combination `2k s^{-3/2}A + (2ν-θ) s^{-1/2}N`. -/
def cutG (k ν θ : ℝ) (A N : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * k * (s ^ (-3 / 2 : ℝ) * A s) + (2 * ν - θ) * (s ^ (-1 / 2 : ℝ) * N s)

/-- Per-cutoff scalar inequality (Young absorbed). -/
theorem cutoff_young {k ν α θ : ℝ} {A N M Q ψ : ℝ → ℝ} {a b : ℝ}
    (hθ : 0 < θ) (hθ2 : θ ≤ 2 * ν) (hα : 2 * k ≤ α)
    (hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M s ∧ 0 ≤ Q s)
    (hA : IntegrableOn A (Icc a b)) (hN : IntegrableOn N (Icc a b))
    (hQ : IntegrableOn Q (Icc a b))
    (hY : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 2 * M s ≤ θ * N s + θ⁻¹ * Q s)
    (hψ : ContDiff ℝ 1 ψ) (ha : 0 < a) (hsupp : tsupport ψ ⊆ Icc a b) (hψ0 : ∀ s, 0 ≤ ψ s)
    (hW : (∫ s in Ioi (0 : ℝ), ψ s * (α * s ^ (-3 / 2 : ℝ) * A s + 2 * ν * s ^ (-1 / 2 : ℝ) * N s))
        ≤ (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * M s) :
    Integrable (fun s => ψ s * cutG k ν θ A N s) (volume.restrict (Ioi (0 : ℝ))) ∧
    ∫ s in Ioi (0 : ℝ), ψ s * cutG k ν θ A N s ≤
      (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) +
        θ⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
  have iA : Integrable (fun s => ψ s * (s ^ (-3 / 2 : ℝ) * A s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hA _)
  have iN : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * N s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hN _)
  have iQ : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hQ _)
  have hP1 : 0 ≤ ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s) := by
    refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    exact mul_nonneg (hψ0 s) (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (hnn s).1)
  have hM : 2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * M s ≤
      θ * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s)) +
        θ⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
    have hle : ∫ s in Ioi (0 : ℝ), 2 * (ψ s * s ^ (-1 / 2 : ℝ) * M s) ≤
        ∫ s in Ioi (0 : ℝ), (θ * (ψ s * (s ^ (-1 / 2 : ℝ) * N s)) +
          θ⁻¹ * (ψ s * (s ^ (-1 / 2 : ℝ) * Q s))) := by
      refine integral_mono_of_nonneg ?_ ((iN.const_mul θ).add (iQ.const_mul θ⁻¹)) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have := mul_nonneg (hψ0 s) (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ))
        have := mul_nonneg this (hnn s).2.2.1
        simp only [Pi.zero_apply]
        linarith
      · filter_upwards [hY, ae_restrict_mem measurableSet_Ioi] with s hs1 hs
        have hr := mul_nonneg (hψ0 s) (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ))
        have := mul_le_mul_of_nonneg_left hs1 hr
        nlinarith [this]
    rw [integral_add (iN.const_mul θ) (iQ.const_mul θ⁻¹)] at hle
    simp only [integral_const_mul] at hle
    exact hle
  have e1 : (∫ s in Ioi (0 : ℝ), ψ s * (α * s ^ (-3 / 2 : ℝ) * A s + 2 * ν * s ^ (-1 / 2 : ℝ) * N s))
      = α * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s)) +
        2 * ν * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul α) (iN.const_mul _)]
    congr 1; funext s; ring
  have e2 : (∫ s in Ioi (0 : ℝ), ψ s * cutG k ν θ A N s)
      = 2 * k * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s)) +
        (2 * ν - θ) * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA.const_mul (2 * k)) (iN.const_mul (2 * ν - θ))]
    congr 1; funext s; unfold cutG; ring
  refine ⟨?_, ?_⟩
  · have := (iA.const_mul (2 * k)).add (iN.const_mul (2 * ν - θ))
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply, cutG]; ring
  · rw [e2]
    have h3 := mul_nonneg (sub_nonneg.2 hα) hP1
    rw [e1] at hW
    linarith [hW, hM, h3]

/-- Derivative term of a ramp cutoff. -/
theorem ramp_deriv_bound {C δ : ℝ} {A ψ : ℝ → ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hA : ∀ s, 0 ≤ A s)
    (hb : ∀ s, deriv ψ s ≤ C / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s)
    (hint : Integrable (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) (volume.restrict (Ioi (0 : ℝ)))) :
    ENNReal.ofReal (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) ≤
      ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
  refine (ofReal_integral_le_lintegral' hint).trans ?_
  have hmeas : MeasurableSet (Ioo (0 : ℝ) (3 * δ)) := measurableSet_Ioo
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s))
      ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) (3 * δ)).indicator
          (fun s => ENNReal.ofReal (2 * C) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hmem : s ∈ Icc δ (2 * δ)
        · have hIoo : s ∈ Ioo (0 : ℝ) (3 * δ) := ⟨hs0, by linarith [hmem.2]⟩
          rw [Set.indicator_of_mem hIoo, ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          have hd := hb s
          rw [Set.indicator_of_mem hmem] at hd
          have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
            rw [← Real.rpow_add_one hs0.ne']; norm_num
          have hr0 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
          have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s := mul_nonneg hr0 (hA s)
          have h1 : s ^ (-1 / 2 : ℝ) * A s ≤ 2 * δ * (s ^ (-3 / 2 : ℝ) * A s) := by
            rw [hr]
            have : s ≤ 2 * δ := hmem.2
            nlinarith [mul_le_mul_of_nonneg_right this hx]
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          calc deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)
              ≤ C / δ * 1 * (s ^ (-1 / 2 : ℝ) * A s) := mul_le_mul_of_nonneg_right hd hp
            _ ≤ C / δ * 1 * (2 * δ * (s ^ (-3 / 2 : ℝ) * A s)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * C * (s ^ (-3 / 2 : ℝ) * A s) := by field_simp
        · have hd := hb s
          rw [Set.indicator_of_notMem hmem, mul_zero] at hd
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          have : deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd hp
          rw [ENNReal.ofReal_of_nonpos this]
          exact zero_le
    _ = ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        have hinter : Ioo (0 : ℝ) (3 * δ) ∩ Ioi 0 = Ioo 0 (3 * δ) :=
          Set.inter_eq_left.2 (fun x hx => hx.1)
        rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas, hinter,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The `[0,∞]`-valued combination, `ofReal(2k) s^{-3/2}A + ofReal(2ν-θ) s^{-1/2}N`. -/
def Gfun (k ν θ : ℝ) (A N : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * k) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) +
    ENNReal.ofReal (2 * ν - θ) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)

theorem ofReal_mul_Gfun {k ν θ ψs s : ℝ} {A N : ℝ → ℝ} (hk : 0 < k) (hθ2 : θ ≤ 2 * ν)
    (hA : 0 ≤ A s) (hN : 0 ≤ N s) (hs : 0 < s) (hψ : 0 ≤ ψs) :
    ENNReal.ofReal ψs * Gfun k ν θ A N s = ENNReal.ofReal (ψs * cutG k ν θ A N s) := by
  have h1 : 0 ≤ s ^ (-3 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs.le _) hA
  have h2 : 0 ≤ s ^ (-1 / 2 : ℝ) * N s := mul_nonneg (Real.rpow_nonneg hs.le _) hN
  have h3 : 0 ≤ 2 * k := by linarith
  have h4 : 0 ≤ 2 * ν - θ := by linarith
  unfold Gfun cutG
  rw [← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h4,
    ← ENNReal.ofReal_add (mul_nonneg h3 h1) (mul_nonneg h4 h2), ← ENNReal.ofReal_mul hψ]

theorem cutoffLimit : CutoffLimit := by
  intro k ν α θ A N M Q hk hν hθ hθ2 hα hnn hAm hNm hQm hloc hY hZ hW
  obtain ⟨C, hC, hramp⟩ := rampFamily
  obtain ⟨δ0, hδ0, hfin⟩ := hZ
  set R : ℝ≥0∞ := ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) with hR
  by_cases hRtop : R = ⊤
  · rw [hRtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top
  obtain ⟨d, hdpos, hd2, hdlim⟩ : ∃ d : ℕ → ℝ, (∀ n, 0 < d n) ∧ (∀ n, 2 * d n < (n : ℝ) + 3) ∧
      Tendsto d atTop (𝓝 0) := by
    refine ⟨fun n => 1 / ((n : ℝ) + 1), fun n => by positivity, fun n => ?_,
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    show 2 * (1 / ((n : ℝ) + 1)) < (n : ℝ) + 3
    linarith
  have hex : ∀ n : ℕ, ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      (∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) ∧ (∀ s ∈ Icc (2 * d n) ((n : ℝ) + 3), ψ s = 1) ∧
      ∀ s, deriv ψ s ≤ C / d n * (Icc (d n) (2 * d n)).indicator (fun _ => (1 : ℝ)) s :=
    fun n => hramp (d n) ((n : ℝ) + 3) (hdpos n) (hd2 n)
  choose ψ hψ using hex
  have hbound : ∀ n : ℕ, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s ≤
      ENNReal.ofReal (2 * C) * (∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        + ENNReal.ofReal θ⁻¹ * R := by
    intro n
    obtain ⟨hc1, hcs, hts, hb01, hone, hder⟩ := hψ n
    have hψ0 : ∀ s, 0 ≤ ψ n s := fun s => (hb01 s).1
    obtain ⟨a, b0, ha, hab⟩ := compact_Ioi_bounds hcs hts
    have hsupp : tsupport (ψ n) ⊆ Icc a (max b0 (a + 1)) :=
      hab.trans (Icc_subset_Icc le_rfl (le_max_left _ _))
    have hab' : a < max b0 (a + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    obtain ⟨hA, hN, hQ⟩ := hloc a _ ha hab'
    obtain ⟨hint, hle⟩ := cutoff_young hθ hθ2 hα hnn hA hN hQ hY hc1 ha hsupp hψ0
      (hW (ψ n) hc1 hcs hts hψ0)
    have iQ : Integrable (fun s => ψ n s * (s ^ (-1 / 2 : ℝ) * Q s))
        (volume.restrict (Ioi (0 : ℝ))) :=
      integrable_cutoff_mul hc1 ha hsupp (intOn_rpow_mul ha hQ _)
    have hDint : Integrable (fun s => deriv (ψ n) s * (s ^ (-1 / 2 : ℝ) * A s))
        (volume.restrict (Ioi (0 : ℝ))) :=
      integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) ha
        (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul ha hA _)
    have s1 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s * cutG k ν θ A N s) :=
      setLIntegral_congr_fun measurableSet_Ioi fun s hs =>
        ofReal_mul_Gfun hk hθ2 (hnn s).1 (hnn s).2.1 hs (hψ0 s)
    have s2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s * cutG k ν θ A N s) =
        ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ n s * cutG k ν θ A N s) := by
      refine (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
      have h1 := mul_nonneg (Real.rpow_nonneg hs0 (-3 / 2 : ℝ)) (hnn s).1
      have h2 := mul_nonneg (Real.rpow_nonneg hs0 (-1 / 2 : ℝ)) (hnn s).2.1
      have h3 : 0 ≤ 2 * ν - θ := by linarith
      have : 0 ≤ cutG k ν θ A N s := by
        unfold cutG
        exact add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg h3 h2)
      exact mul_nonneg (hψ0 s) this
    have s4 := ramp_deriv_bound (hdpos n) hC (fun s => (hnn s).1) hder hDint
    have s5 : ENNReal.ofReal (θ⁻¹ * ∫ s in Ioi (0 : ℝ), ψ n s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
        ENNReal.ofReal θ⁻¹ * R := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hθ.le)]
      refine mul_le_mul_right ((ofReal_integral_le_lintegral' iQ).trans ?_) _
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      apply ENNReal.ofReal_le_ofReal
      have h1 := mul_nonneg (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ)) (hnn s).2.2.2
      nlinarith [(hb01 s).2, (hb01 s).1]
    rw [s1, s2]
    exact (ENNReal.ofReal_le_ofReal hle).trans (ENNReal.ofReal_add_le.trans (add_le_add s4 s5))
  -- Fatou
  have hGm : Measurable (Gfun k ν θ A N) := by
    unfold Gfun
    have h1 : Measurable fun s : ℝ => s ^ (-3 / 2 : ℝ) * A s := by fun_prop
    have h2 : Measurable fun s : ℝ => s ^ (-1 / 2 : ℝ) * N s := by fun_prop
    exact (h1.ennreal_ofReal.const_mul _).add (h2.ennreal_ofReal.const_mul _)
  have hLHS : ENNReal.ofReal (2 * k) * (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal (2 * ν - θ) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)
      = ∫⁻ s in Ioi (0 : ℝ), Gfun k ν θ A N s := by
    have h1 : Measurable fun s : ℝ => s ^ (-3 / 2 : ℝ) * A s := by fun_prop
    unfold Gfun
    rw [lintegral_add_left (h1.ennreal_ofReal.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfat : ∫⁻ s in Ioi (0 : ℝ), Gfun k ν θ A N s ≤
      liminf (fun n => ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s) atTop := by
    have hmeasn : ∀ n, Measurable (fun s => ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s) :=
      fun n => ((hψ n).1.continuous.measurable.ennreal_ofReal).mul hGm
    calc ∫⁻ s in Ioi (0 : ℝ), Gfun k ν θ A N s
        = ∫⁻ s in Ioi (0 : ℝ),
            liminf (fun n => ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s) atTop := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
          have hs0 : (0 : ℝ) < s := hs
          have e1 : ∀ᶠ n : ℕ in atTop, 2 * d n < s :=
            (tendsto_order.1 (hdlim.const_mul 2)).2 s (by simpa using hs0)
          have e2 : ∀ᶠ n : ℕ in atTop, s ≤ (n : ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop s
          have hev : ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s = Gfun k ν θ A N s := by
            filter_upwards [e1, e2] with n h1 h2
            rw [(hψ n).2.2.2.2.1 s ⟨h1.le, by linarith⟩]
            simp
          have : Tendsto (fun n => ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s) atTop
              (𝓝 (Gfun k ν θ A N s)) :=
            tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
          exact this.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hmeasn
  -- the tail of the zero-entrance integral
  have hE : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
      atTop (𝓝 0) := by
    have hE0 : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)
        ∂(volume.restrict (Ioo 0 δ0))) atTop (𝓝 0) := by
      refine tendsto_setLIntegral_zero (μ := volume.restrict (Ioo 0 δ0))
        (f := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) hfin.ne ?_
      have hup : Tendsto (fun n => ENNReal.ofReal (3 * d n)) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (hdlim.const_mul 3)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => zero_le) (fun n => ?_)
      show (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * d n)) ≤ ENNReal.ofReal (3 * d n)
      calc (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * d n)) ≤ volume (Ioo 0 (3 * d n)) :=
            Measure.restrict_le_self _
        _ = ENNReal.ofReal (3 * d n) := by simp
    have hev : ∀ᶠ n : ℕ in atTop, 3 * d n < δ0 :=
      (tendsto_order.1 (hdlim.const_mul 3)).2 δ0 (by simpa using hδ0)
    refine hE0.congr' (hev.mono fun n hn => ?_)
    rw [Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.2 (Ioo_subset_Ioo le_rfl hn.le)]
  have hlim : Tendsto (fun n => ENNReal.ofReal (2 * C) *
        (∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        + ENNReal.ofReal θ⁻¹ * R) atTop (𝓝 (ENNReal.ofReal θ⁻¹ * R)) := by
    have := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * C)) hE
      (Or.inr ENNReal.ofReal_ne_top)).add_const (ENNReal.ofReal θ⁻¹ * R)
    simpa using this
  rw [hLHS]
  calc ∫⁻ s in Ioi (0 : ℝ), Gfun k ν θ A N s
      ≤ liminf (fun n => ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ n s) * Gfun k ν θ A N s) atTop :=
        hfat
    _ ≤ liminf (fun n => ENNReal.ofReal (2 * C) *
        (∫⁻ s in Ioo 0 (3 * d n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        + ENNReal.ofReal θ⁻¹ * R) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal θ⁻¹ * R := hlim.liminf_eq

end UnforcedLeray.Short.IIIa
