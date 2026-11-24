import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.PairDeriv

/-!
# `PartIII-a:T21/2/7/2/1/1/7/3`: the time one-letter identity in space-time `STTimeIdentity`

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.
For `Ψ ∈ C_c^∞((t,s) × ℝ²)` we need `∫ (∂_rΨ) G0 = -∫ Ψ G1`.

Route: Fubini on `ℝ × ℝ²` (`integral_prod`) splits both integrals.  The `r`-integrand
`Ξ r = ∫_x ∂_rΨ G0 + ∫_x Ψ G1` vanishes outside `(a, b)` with `t < a ≤ b < s`, and on `[a, b]` it
equals the derivative `g r` of the pairing `h(r) = ∫_x Ψ(r,x) Φ j r x` (`pairDeriv`).  The fundamental
theorem of calculus gives `∫_a^b g = h(b) - h(a) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem stTimeIdentity : UnforcedLeray.Short.IIIa.STTimeIdentity := by
  intro c m t s Φ j G0 G1 hc hts hΦ hG0m hG1m hG0L hG1L hG0eq hG1eq
  unfold STStepIdentity
  intro Ψ hΨ hΨc hΨU
  have hdir : stDir 0 = (1, (0, 0)) := by simp [stDir]
  rw [hdir]
  have hΨcont : Continuous Ψ := hΨ.continuous
  have hKc : IsCompact (tsupport Ψ) := hΨc.isCompact
  have hKU : tsupport Ψ ⊆ stSlab t s := hΨU
  -- the directional derivative and its bounds
  have hDc : Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (1, (0, 0))) :=
    (hΨ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (1, (0, 0))) :=
    hΨc.fderiv_apply ℝ (1, (0, 0))
  obtain ⟨CD, hCD⟩ := hDc.bounded_above_of_compact_support hDcs
  have hD0 : ∀ p : ℝ × (ℝ × ℝ), p ∉ tsupport Ψ → fderiv ℝ Ψ p (1, (0, 0)) = 0 := by
    intro p hp
    have h0 : fderiv ℝ Ψ p = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
    rw [h0]
    rfl
  obtain ⟨CΨ, hCΨ⟩ := hΨcont.bounded_above_of_compact_support hΨc
  -- integrability of the two pieces on the support
  have hG0I : IntegrableOn G0 (tsupport Ψ) := by
    have : IsFiniteMeasure (volume.restrict (tsupport Ψ)) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    exact (hG0L _ hKc hKU).integrable (by norm_num)
  have hG1I : IntegrableOn G1 (tsupport Ψ) := by
    have : IsFiniteMeasure (volume.restrict (tsupport Ψ)) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    exact (hG1L _ hKc hKU).integrable (by norm_num)
  have hint : ∀ (φ : ℝ × (ℝ × ℝ) → ℝ) (G : ℝ × (ℝ × ℝ) → ℂ), Continuous φ →
      (∃ C : ℝ, ∀ p, ‖φ p‖ ≤ C) → (∀ p, p ∉ tsupport Ψ → φ p = 0) →
      IntegrableOn G (tsupport Ψ) → Integrable (fun p => φ p • G p) := by
    intro φ G hφc hφb hφ0 hG
    obtain ⟨C, hC⟩ := hφb
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := tsupport Ψ) (Integrable.bdd_smul hG C hφc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)) ?_
    intro p hp
    simp [hφ0 p hp]
  have hA : Integrable (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (1, (0, 0)) • G0 p) :=
    hint (fun p => fderiv ℝ Ψ p (1, (0, 0))) G0 hDc ⟨CD, hCD⟩ hD0 hG0I
  have hB : Integrable (fun p : ℝ × (ℝ × ℝ) => Ψ p • G1 p) :=
    hint Ψ G1 hΨcont ⟨CΨ, hCΨ⟩ (fun p hp => image_eq_zero_of_notMem_tsupport hp) hG1I
  refine ⟨hA, hB, ?_⟩
  -- the `r`-projection of the support lies strictly inside `(t, s)`, away from the ends
  obtain ⟨a, b, hta, hab, hbs, hK⟩ : ∃ a b : ℝ, t < a ∧ a ≤ b ∧ b < s ∧
      ∀ p ∈ tsupport Ψ, a < p.1 ∧ p.1 < b := by
    rcases (tsupport Ψ).eq_empty_or_nonempty with he | hne
    · exact ⟨(t + s) / 2, (t + s) / 2, by linarith, le_rfl, by linarith,
        fun p hp => by simp [he] at hp⟩
    · obtain ⟨p0, hp0, hmin⟩ := hKc.exists_isMinOn hne continuous_fst.continuousOn
      obtain ⟨p1, hp1, hmax⟩ := hKc.exists_isMaxOn hne continuous_fst.continuousOn
      have h0 : t < p0.1 := (hKU hp0).1.1
      have h0' : p0.1 < s := (hKU hp0).1.2
      have h1 : t < p1.1 := (hKU hp1).1.1
      have h1' : p1.1 < s := (hKU hp1).1.2
      have hm : p0.1 ≤ p1.1 := isMinOn_iff.mp hmin p1 hp1
      refine ⟨(t + p0.1) / 2, (p1.1 + s) / 2, by linarith, by linarith, by linarith,
        fun p hp => ?_⟩
      have hp0p : p0.1 ≤ p.1 := isMinOn_iff.mp hmin p hp
      have hpp : p.1 ≤ p1.1 := isMaxOn_iff.mp hmax p hp
      constructor <;> linarith
  -- Ψ and its `r`-derivative vanish off `(a, b)`
  have hz : ∀ r : ℝ, r ∉ Ioo a b → ∀ x : ℝ × ℝ, (r, x) ∉ tsupport Ψ := by
    intro r hr x hx
    exact hr ⟨(hK _ hx).1, (hK _ hx).2⟩
  have hΨz : ∀ r : ℝ, r ∉ Ioo a b → ∀ x : ℝ × ℝ, Ψ (r, x) = 0 :=
    fun r hr x => image_eq_zero_of_notMem_tsupport (hz r hr x)
  have hDz : ∀ r : ℝ, r ∉ Ioo a b → ∀ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) = 0 :=
    fun r hr x => hD0 (r, x) (hz r hr x)
  -- the pairing derivative on (t, s)
  obtain ⟨hHD, hgc⟩ := pairDeriv c m t s Φ j Ψ hc hts hΦ hΨ hΨc hΨU
  have huI : uIcc a b ⊆ Ioo t s := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Ioo hta hbs
  -- the `r`-integrals of the two pieces
  have e1 : ∫ p : ℝ × (ℝ × ℝ), fderiv ℝ Ψ p (1, (0, 0)) • G0 p =
      ∫ r : ℝ, ∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x) :=
    integral_prod _ hA
  have e2 : ∫ p : ℝ × (ℝ × ℝ), Ψ p • G1 p = ∫ r : ℝ, ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x) :=
    integral_prod _ hB
  have hLA : Integrable (fun r : ℝ => ∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) :=
    hA.integral_prod_left
  have hLB : Integrable (fun r : ℝ => ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) :=
    hB.integral_prod_left
  -- the inner integral vanishes outside `(a, b)`
  have hvan : ∀ r : ℝ, r ∉ Ioc a b →
      (∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
        ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x) = 0 := by
    intro r hr
    have hr' : r ∉ Ioo a b := fun h => hr ⟨h.1, h.2.le⟩
    have h1 : ∀ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x) = 0 := fun x => by
      rw [hDz r hr' x]
      simp
    have h2 : ∀ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x) = 0 := fun x => by
      rw [hΨz r hr' x]
      simp
    simp [h1, h2]
  -- on `(t, s)` the inner integral is the derivative `g r` of `pairDeriv`
  have hΞ : ∀ r ∈ Ioo t s,
      (∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
        ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x) =
      (∫ x : ℝ × ℝ, ((fderiv ℝ Ψ (r, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r x) +
        ∫ x : ℝ × ℝ, (Ψ (r, x) : ℂ) * Φ (j + 1) r x := by
    intro r hr
    have ha : (∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) =
        ∫ x : ℝ × ℝ, ((fderiv ℝ Ψ (r, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r x := by
      apply integral_congr_ae
      filter_upwards [hG0eq r hr] with x hx
      have hx' : G0 (r, x) = Φ j r x := hx
      rw [Complex.real_smul, hx']
    have hb : (∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) =
        ∫ x : ℝ × ℝ, (Ψ (r, x) : ℂ) * Φ (j + 1) r x := by
      apply integral_congr_ae
      filter_upwards [hG1eq r hr] with x hx
      have hx' : G1 (r, x) = Φ (j + 1) r x := hx
      rw [Complex.real_smul, hx']
    rw [ha, hb]
  -- the total `r`-integral vanishes
  have hzero_all : ∫ r : ℝ, ((∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
      ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) = 0 := by
    have h1 : ∫ r in Ioc a b, ((∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
        ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) =
        ∫ r : ℝ, ((∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
        ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => hvan r hr)
    have hcong : ∫ r in a..b, ((∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (1, (0, 0)) • G0 (r, x)) +
        ∫ x : ℝ × ℝ, Ψ (r, x) • G1 (r, x)) =
        ∫ r in a..b, ((∫ x : ℝ × ℝ, ((fderiv ℝ Ψ (r, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r x) +
          ∫ x : ℝ × ℝ, (Ψ (r, x) : ℂ) * Φ (j + 1) r x) :=
      intervalIntegral.integral_congr (fun r hr => hΞ r (huI hr))
    have hgint : IntervalIntegrable (fun r : ℝ =>
        (∫ x : ℝ × ℝ, ((fderiv ℝ Ψ (r, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r x) +
          ∫ x : ℝ × ℝ, (Ψ (r, x) : ℂ) * Φ (j + 1) r x) volume a b :=
      ContinuousOn.intervalIntegrable (hgc.mono huI)
    have hFTC : ∫ r in a..b, ((∫ x : ℝ × ℝ, ((fderiv ℝ Ψ (r, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r x) +
          ∫ x : ℝ × ℝ, (Ψ (r, x) : ℂ) * Φ (j + 1) r x) =
        (∫ x : ℝ × ℝ, (Ψ (b, x) : ℂ) * Φ j b x) - ∫ x : ℝ × ℝ, (Ψ (a, x) : ℂ) * Φ j a x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hHD r (huI hr)) hgint
    have hfa : (∫ x : ℝ × ℝ, (Ψ (a, x) : ℂ) * Φ j a x) = 0 := by
      have h : ∀ x : ℝ × ℝ, Ψ (a, x) = 0 := hΨz a (fun h => lt_irrefl a h.1)
      simp [h]
    have hfb : (∫ x : ℝ × ℝ, (Ψ (b, x) : ℂ) * Φ j b x) = 0 := by
      have h : ∀ x : ℝ × ℝ, Ψ (b, x) = 0 := hΨz b (fun h => lt_irrefl b h.2)
      simp [h]
    rw [← h1, ← intervalIntegral.integral_of_le hab, hcong, hFTC, hfa, hfb, sub_zero]
  have hkey : (∫ p : ℝ × (ℝ × ℝ), fderiv ℝ Ψ p (1, (0, 0)) • G0 p) +
      ∫ p : ℝ × (ℝ × ℝ), Ψ p • G1 p = 0 := by
    rw [e1, e2, ← integral_add hLA hLB]
    exact hzero_all
  exact eq_neg_of_add_eq_zero_left hkey

end UnforcedLeray.Short.IIIa
