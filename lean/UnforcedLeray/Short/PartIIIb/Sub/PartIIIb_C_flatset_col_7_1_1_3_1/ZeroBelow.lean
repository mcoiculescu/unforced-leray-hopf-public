import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3.Reduction

/-!
# Vanishing below `s₀` and global smoothness of `SmoothRep`
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

Source of record `the November 2 reference manuscript` 1650-1656, 1684-1689.
In `ClassicalCtx`, the smooth representative `b` agrees with `duhamel ν μ G` on `s > 0`
(by continuity, `q`-periodicity and `ageμOpenPos`), where `G` is supported in `s ≥ s₀ > 0`
(`lerayDriving`).  Hence `b` vanishes on `s < s₀`, is globally `C^∞` on `Chart`, and is globally
`c`-periodic in `q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The Duhamel integral vanishes for `0 < s < s₀` when `G` is supported in `s ≥ s₀`. -/
theorem duhamel_eq_zero_of_lt {ν μ s0 s1 : ℝ} {G : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, G p ≠ 0 → p.1 ∈ Icc s0 s1) {p : Chart} (hp0 : 0 < p.1) (hps : p.1 < s0)
    (i : Fin 2) : duhamel ν μ G p i = 0 := by
  unfold duhamel
  have hcongr : EqOn
      (fun σ : ℝ => (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2)
      (fun _ => (0 : ℂ)) (uIoc 0 p.1) := by
    intro σ hσ
    rw [uIoc_of_le hp0.le] at hσ
    have hσlt : σ < s0 := lt_of_le_of_lt hσ.2 hps
    have hGz : (fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
      funext z
      have h0 : G (σ, z) = 0 := by
        by_contra hne
        have hm := (hsupp (σ, z) hne).1
        exact not_le.2 hσlt hm
      simp [h0]
    dsimp only
    rw [hGz, UnforcedLeray.B0225.planeHeat_zero, smul_zero]
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ hcongr), intervalIntegral.integral_zero]

/-- On `s > 0`, any `SmoothRep` of `R0 g` agrees pointwise with `duhamel ν μ G`. -/
theorem smoothRep_eq_duhamel {c ν μ : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c} {g : Hsp c}
    (hctx : ClassicalCtx c ν μ hc R0 g) {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G)
    (hPep : PepsRep c g G) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hbe : b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ)
    (i : Fin 2) : b (s, x) i = duhamel ν μ G (s, x) i := by
  by_contra hne
  have hν : 0 < ν := hctx.1
  have hbr := duhamelBridge c ν μ hc R0 g G hctx hG hPep
  have hae : ∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ j : Fin 2, b p j = duhamel ν μ G p j := by
    filter_upwards [hbe, hbr] with p e1 e2 j
    rw [e1, e2]
  set H : Chart → ℂ := fun p => duhamel ν μ G p i with hH
  set B : Chart → ℂ := fun p => b p i with hB
  have hBc : ContinuousOn B (Ioi (0 : ℝ) ×ˢ univ) := (hb.2.1 i).continuousOn
  have hHc : ContinuousOn H (Ioi (0 : ℝ) ×ˢ univ) := (duhamelSmooth c ν μ G hG hν i).continuousOn
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hdiff : ContinuousOn (fun p => B p - H p) (Ioi (0 : ℝ) ×ˢ univ) := hBc.sub hHc
  have hVo : IsOpen ((Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩
      (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ) :=
    hdiff.isOpen_inter_preimage hopen (isOpen_compl_singleton (x := (0 : ℂ)))
  have hper : ∀ p : Chart, 0 < p.1 → B (p.1, (p.2.1 + c, p.2.2)) - H (p.1, (p.2.1 + c, p.2.2)) =
      B p - H p := by
    intro ⟨s', q, η⟩ hp
    simp only at hp ⊢
    have h1 := hb.2.2.1 s' q η hp
    have h2 := duhamelPeriodic c ν μ G hG s' q η hp
    simp only [hB, hH, h1, h2]
  have hperZ : ∀ (n : ℤ) (p : Chart), 0 < p.1 →
      B (p.1, (p.2.1 + n * c, p.2.2)) - H (p.1, (p.2.1 + n * c, p.2.2)) = B p - H p := by
    intro n p hp
    induction n using Int.induction_on generalizing p with
    | zero => simp
    | succ k ih =>
      have h1 := hper (p.1, (p.2.1 + ((k : ℤ) : ℝ) * c, p.2.2)) hp
      have h2 := ih p hp
      simp only [Int.cast_add, Int.cast_one, Int.cast_natCast] at h1 h2 ⊢
      have e : p.2.1 + ((k : ℝ) + 1) * c = p.2.1 + (k : ℝ) * c + c := by ring
      rw [e]
      exact h1.trans h2
    | pred k ih =>
      have h1 := hper (p.1, (p.2.1 + (-(k : ℤ) - 1 : ℤ) * c, p.2.2)) hp
      have h2 := ih p hp
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast] at h1 h2 ⊢
      have e : p.2.1 + (-(k : ℝ) - 1) * c + c = p.2.1 + -(k : ℝ) * c := by ring
      rw [e] at h1
      rw [h1] at h2
      exact h2
  have hne' : B (s, x) - H (s, x) ≠ 0 := sub_ne_zero.2 hne
  set n : ℤ := ⌊(x.1 + c / 2) / c⌋
  have hn1 : (n : ℝ) ≤ (x.1 + c / 2) / c := Int.floor_le _
  have hn2 : (x.1 + c / 2) / c < n + 1 := Int.lt_floor_add_one _
  have hq1 : -(c / 2) ≤ x.1 + (-n : ℤ) * c := by
    push_cast
    have := (le_div_iff₀ hc).1 hn1
    linarith
  have hq2 : x.1 + (-n : ℤ) * c < c / 2 := by
    push_cast
    have := (div_lt_iff₀ hc).1 hn2
    linarith
  have hp' := hperZ (-n) (s, x) hs
  simp only at hp'
  set p' : Chart := (s, (x.1 + (-n : ℤ) * c, x.2))
  have hp'V : p' ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩
      (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ := by
    refine ⟨⟨hs, mem_univ _⟩, ?_⟩
    show B p' - H p' ≠ 0
    rw [hp']; exact hne'
  have hcl : p' ∈ closure (Ioi (0 : ℝ) ×ˢ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [closure_prod_eq, closure_prod_eq, closure_Ioi, closure_Ioo (by linarith), closure_univ]
    exact ⟨le_of_lt hs, ⟨hq1, hq2.le⟩, mem_univ _⟩
  obtain ⟨w, hwV, hwS⟩ := mem_closure_iff.1 hcl _ hVo hp'V
  set W := (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩ (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ ∩
    (Ioi (0 : ℝ) ×ˢ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)))
  have hWo : IsOpen W := hVo.inter (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ))
  have hWpos : 0 < ageμ c (-3 / 2) W :=
    ageμOpenPos c (-3 / 2) hc W hWo inter_subset_right ⟨w, hwV, hwS⟩
  have hnull : ageμ c (-3 / 2) {p : Chart | ¬ ∀ j : Fin 2, b p j = duhamel ν μ G p j} = 0 := hae
  have hsub : W ⊆ {p : Chart | ¬ ∀ j : Fin 2, b p j = duhamel ν μ G p j} := by
    intro p hp hall
    apply hp.1.2
    show B p - H p = 0
    simp only [hB, hH, hall i, sub_self]
  exact absurd (measure_mono_null hsub hnull) hWpos.ne'

/-- In `ClassicalCtx`, the smooth representative `b` vanishes on `p.1 < s₀` for some `s₀ > 0`. -/
theorem smoothRep_zero_below {c ν μ : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c} {g : Hsp c}
    (hctx : ClassicalCtx c ν μ hc R0 g) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hbe : b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ p : Chart, p.1 < s0 → b p = 0 := by
  obtain ⟨G, hG, hPep⟩ := lerayDriving c hc g hctx.2.2.2
  obtain ⟨s0, s1, hs0, hsupp⟩ := hG.2.2.1
  refine ⟨s0, hs0, fun p hp => ?_⟩
  rcases le_or_gt p.1 0 with hp0 | hp0
  · exact hb.2.2.2.2 p hp0
  · funext i
    rw [show p = (p.1, p.2) from rfl, smoothRep_eq_duhamel hctx hG hPep hb hbe hp0 p.2 i]
    exact duhamel_eq_zero_of_lt hsupp hp0 hp i

/-- Since `b` is `C^∞` on `s > 0` and vanishes on `s < s₀` (`s₀ > 0`), it is globally `C^∞`. -/
theorem smoothRep_contDiff {c : ℝ} {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b) {s0 : ℝ}
    (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : Chart => b p i) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases lt_or_ge 0 p.1 with hp | hp
  ·exact (hb.2.1 i).contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  · have hlt : p.1 < s0 := lt_of_le_of_lt hp hs0
    have hev : (fun q : Chart => b q i) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
      filter_upwards [((isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hlt, mem_univ _⟩)] with q hq
      rw [hz q hq.1, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Global `c`-periodicity in `q` of a `SmoothRep`. -/
theorem smoothRep_periodic {c : ℝ} {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (s q η : ℝ) : b (s, (q + c, η)) = b (s, (q, η)) := by
  rcases lt_or_ge 0 s with hs | hs
  · exact hb.2.2.1 s q η hs
  · rw [hb.2.2.2.2 (s, (q + c, η)) hs, hb.2.2.2.2 (s, (q, η)) hs]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
