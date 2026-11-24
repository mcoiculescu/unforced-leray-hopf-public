import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Basic

/-!
# Helpers for `PartII-a:N05/2/2/1`: local integrability and unfolding against tests

* `locallyIntegrable_of_periodic`: a `q`-periodic function integrable on every `η`-bounded part of
  one `q`-cell `ℝ × (0, c] × [-R, R]` is locally integrable on `ℝ × ℝ²`.
* `integral_mul_test_eq_cell`: `∫_{ℝ³} F φ = ∫_cell F · perT c φ` for `q`-periodic, locally
  integrable `F` vanishing for `s ≤ 0` and continuous compactly supported real `φ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.Short.IIb (Coord cpd cdir)

theorem integrableOn_translate {c : ℝ} {F : Coord → ℂ} (hper : ∀ x, F (x + qv c) = F x)
    {S : Set Coord} (hS : IntegrableOn F S) (m : ℤ) :
    IntegrableOn F ((fun x => x + qv (-(m * c))) ⁻¹' S) := by
  have hmp := measurePreserving_add_right (volume : Measure Coord) (qv (-(m * c)))
  have hme : MeasurableEmbedding (fun x : Coord => x + qv (-(m * c))) :=
    (MeasurableEquiv.addRight (qv (-(m * c)))).measurableEmbedding
  have hcomp : (F ∘ fun x : Coord => x + qv (-(m * c))) = F := by
    funext x
    simp only [Function.comp]
    have := periodic_int hper (-m) x
    rw [show ((-m : ℤ) : ℝ) * c = -(m * c) by push_cast; ring] at this
    exact this
  have := (hmp.integrableOn_comp_preimage hme (f := F) (s := S)).2 hS
  rwa [hcomp] at this

theorem locallyIntegrable_of_periodic {c : ℝ} (hc : 0 < c) {F : Coord → ℂ}
    (hper : ∀ x, F (x + qv c) = F x)
    (hcell : ∀ R : ℝ, IntegrableOn F (univ ×ˢ (Ioc 0 c ×ˢ Icc (-R) R))) :
    LocallyIntegrable F volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨T, hT⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hK.isBounded
  obtain ⟨N, hN⟩ := exists_nat_ge (|T| / c)
  have hN' : |T| ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  set S : ℕ → Set Coord := fun k =>
    (fun x => x + qv (-((((k : ℤ) - N - 1 : ℤ) : ℝ) * c))) ⁻¹'
      (univ ×ˢ (Ioc 0 c ×ˢ Icc (-|T|) |T|)) with hSdef
  have hSint : ∀ k ∈ Finset.range (2 * N + 1), IntegrableOn F (S k) :=
    fun k _ => integrableOn_translate hper (hcell |T|) _
  have hU := (integrableOn_finset_iUnion (s := Finset.range (2 * N + 1)) (t := S)).2 hSint
  refine hU.mono_set fun x hx => ?_
  have hxT := hT hx
  rw [Metric.mem_closedBall, dist_zero_right] at hxT
  have hq : |x.2.1| ≤ |T| := by
    calc |x.2.1| = ‖x.2.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2‖ := norm_fst_le x.2
      _ ≤ ‖x‖ := norm_snd_le x
      _ ≤ T := hxT
      _ ≤ |T| := le_abs_self T
  have he : |x.2.2| ≤ |T| := by
    calc |x.2.2| = ‖x.2.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2‖ := norm_snd_le x.2
      _ ≤ ‖x‖ := norm_snd_le x
      _ ≤ T := hxT
      _ ≤ |T| := le_abs_self T
  -- the cell index `m = ⌈q/c⌉ - 1`
  set m : ℤ := ⌈x.2.1 / c⌉ - 1 with hm
  have hm1 : (m : ℝ) * c < x.2.1 := by
    have h1 : ((⌈x.2.1 / c⌉ : ℤ) : ℝ) < x.2.1 / c + 1 := Int.ceil_lt_add_one _
    have h2 : (m : ℝ) < x.2.1 / c := by rw [hm]; push_cast; linarith
    rwa [lt_div_iff₀ hc] at h2
  have hm2 : x.2.1 ≤ (m : ℝ) * c + c := by
    have h1 : x.2.1 / c ≤ ((⌈x.2.1 / c⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : x.2.1 / c ≤ (m : ℝ) + 1 := by rw [hm]; push_cast; linarith
    rw [div_le_iff₀ hc] at h2
    linarith
  have hqa := abs_le.1 hq
  have hmlo : -(N : ℤ) - 1 ≤ m := by
    have h3 : (-(N : ℝ)) * c ≤ ((m : ℝ) + 1) * c := by
      have := hqa.1
      nlinarith
    have h4 : -(N : ℝ) ≤ (m : ℝ) + 1 := le_of_mul_le_mul_right h3 hc
    have : -(N : ℤ) ≤ m + 1 := by exact_mod_cast h4
    omega
  have hmhi : m ≤ (N : ℤ) - 1 := by
    have h3 : (m : ℝ) < N := by
      have := lt_of_mul_lt_mul_right (by linarith : (m : ℝ) * c < (N : ℝ) * c) hc.le
      exact this
    have : m < (N : ℤ) := by exact_mod_cast h3
    omega
  rw [mem_iUnion₂]
  refine ⟨(m + N + 1).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]
    omega
  · have hk : (((m + N + 1).toNat : ℤ) - N - 1 : ℤ) = m := by omega
    simp only [hSdef, mem_preimage, mem_prod, mem_univ, true_and, add_qv_snd_fst,
      add_qv_snd_snd, mem_Ioc, mem_Icc]
    rw [hk]
    refine ⟨⟨by linarith, by linarith⟩, abs_le.1 he⟩

/-- `∫_{ℝ³} F φ = ∫_cell F · perT c φ` for `q`-periodic locally integrable `F` vanishing for
`s ≤ 0` and continuous compactly supported real `φ`. -/
theorem integral_mul_test_eq_cell {c : ℝ} (hc : 0 < c) {F : Coord → ℂ}
    (hper : ∀ x, F (x + qv c) = F x) (hpos : ∀ x : Coord, x.1 ≤ 0 → F x = 0)
    (hloc : LocallyIntegrable F volume) {φ : Coord → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) :
    ∫ x, F x * (φ x : ℂ) = ∫ x in UnforcedLeray.B0220.cell c, F x * (perT c φ x : ℂ) := by
  obtain ⟨R, hR0, hR⟩ := exists_qbound hφs
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + c) / c)
  have hN' : R + c ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  set v : ℕ → Coord := fun k => qv ((((k : ℤ) - N : ℤ) : ℝ) * c) with hv
  have hφ0 : ∀ x : Coord, R < |x.2.1| → φ x = 0 := fun x hx => eq_zero_of_qbound hR hx
  -- translated tests are continuous and compactly supported
  have htc : ∀ k : ℕ, Continuous fun x : Coord => ((φ (x + v k) : ℝ) : ℂ) :=
    fun k => Complex.continuous_ofReal.comp (hφc.comp (continuous_id.add continuous_const))
  have hts : ∀ k : ℕ, HasCompactSupport fun x : Coord => ((φ (x + v k) : ℝ) : ℂ) := by
    intro k
    have h1 : HasCompactSupport fun x : Coord => φ (x + v k) := hφs.comp_homeomorph (Homeomorph.addRight (v k))
    exact h1.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  have hFt : ∀ k : ℕ, Integrable fun x : Coord => F x * ((φ (x + v k) : ℝ) : ℂ) := by
    intro k
    have := hloc.integrable_smul_right_of_hasCompactSupport (htc k) (hts k)
    simpa [smul_eq_mul] using this
  set G : Coord → ℂ := fun x => F x * (perT c φ x : ℂ) with hG
  have hGsum : ∀ x : Coord, |x.2.1| ≤ c →
      G x = ∑ k ∈ Finset.range (2 * N + 1), F x * ((φ (x + v k) : ℝ) : ℂ) := by
    intro x hx
    simp only [hG]
    rw [perT_eq_sum hc hφ0 hN' hx]
    push_cast
    rw [Finset.mul_sum]
    simp only [hv, Int.cast_sub, Int.cast_natCast]
  have hGper : ∀ᵐ x : Coord, G (x + qv c) = G x :=
    Eventually.of_forall fun x => by simp only [hG, hper x, perT_periodic]
  have hGpos : ∀ x : Coord, x.1 ≤ 0 → G x = 0 := fun x hx => by simp [hG, hpos x hx]
  have hGint : IntegrableOn G (Ioi 0 ×ˢ (Ioc (-c) c ×ˢ univ)) := by
    have hsum : Integrable fun x : Coord =>
        ∑ k ∈ Finset.range (2 * N + 1), F x * ((φ (x + v k) : ℝ) : ℂ) :=
      integrable_finsetSum _ fun k _ => hFt k
    refine hsum.integrableOn.congr_fun (fun x hx => (hGsum x ?_).symm)
      (measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ))
    rw [abs_le]
    exact ⟨by linarith [hx.2.1.1], hx.2.1.2⟩
  rw [← integral_qCut_mul hc hGper hGpos hGint]
  -- expand the window sum
  have hexp : (fun x : Coord => (qCut c x.2.1 : ℂ) * G x) =
      fun x => ∑ k ∈ Finset.range (2 * N + 1),
        (qCut c x.2.1 : ℂ) * (F x * ((φ (x + v k) : ℝ) : ℂ)) := by
    funext x
    by_cases hx : |x.2.1| ≤ c
    · rw [hGsum x hx, Finset.mul_sum]
    · have hq : x.2.1 ∉ Ioc (-c) c := by
        intro h
        exact hx (abs_le.2 ⟨h.1.le, h.2⟩)
      simp [qCut_eq_zero_of_not_mem hc hq]
  have hqt : ∀ k : ℕ, Integrable fun x : Coord =>
      (qCut c x.2.1 : ℂ) * (F x * ((φ (x + v k) : ℝ) : ℂ)) := by
    intro k
    refine ((hFt k).bdd_mul (c := 1) ?_ ?_)
    · exact (Complex.continuous_ofReal.comp ((qCut_contDiff c).continuous.comp
        (continuous_fst.comp continuous_snd))).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_qCut_le_one c _
  rw [hexp, integral_finsetSum _ fun k _ => hqt k]
  -- translate each term
  have htr : ∀ k : ℕ, ∫ x, (qCut c x.2.1 : ℂ) * (F x * ((φ (x + v k) : ℝ) : ℂ)) =
      ∫ x, (qCut c (x.2.1 - (((k : ℤ) - N : ℤ) : ℝ) * c) : ℂ) * (F x * (φ x : ℂ)) := by
    intro k
    rw [← integral_add_right_eq_self (fun x : Coord =>
      (qCut c (x.2.1 - (((k : ℤ) - N : ℤ) : ℝ) * c) : ℂ) * (F x * (φ x : ℂ))) (v k)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hv, add_qv_snd_fst, add_sub_cancel_right]
    rw [periodic_int hper]
  simp_rw [htr]
  have hqt' : ∀ k ∈ Finset.range (2 * N + 1), Integrable fun x : Coord =>
      (qCut c (x.2.1 - (((k : ℤ) - N : ℤ) : ℝ) * c) : ℂ) * (F x * (φ x : ℂ)) := by
    intro k _
    have hF0 : Integrable fun x : Coord => F x * (φ x : ℂ) := by
      have := hloc.integrable_smul_right_of_hasCompactSupport
        (Complex.continuous_ofReal.comp hφc) (hφs.comp_left (g := ((↑) : ℝ → ℂ)) (by simp))
      simpa [smul_eq_mul] using this
    refine hF0.bdd_mul (c := 1) ?_ ?_
    · exact (Complex.continuous_ofReal.comp ((qCut_contDiff c).continuous.comp
        ((continuous_fst.comp continuous_snd).sub continuous_const))).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_qCut_le_one c _
  rw [← integral_finsetSum _ hqt']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Finset.sum_mul]
  by_cases hx : φ x = 0
  · simp [hx]
  · have hq : |x.2.1| ≤ N * c := by
      have := hR x (subset_tsupport _ hx)
      linarith
    have hs := sum_qCut hc N hq
    have hs' : ∑ k ∈ Finset.range (2 * N + 1),
        (qCut c (x.2.1 - (((k : ℤ) - N : ℤ) : ℝ) * c) : ℂ) = 1 := by
      have : ∑ k ∈ Finset.range (2 * N + 1), (qCut c (x.2.1 - (((k : ℤ) - N : ℤ) : ℝ) * c) : ℂ) =
          ((∑ k ∈ Finset.range (2 * N + 1), qCut c (x.2.1 - ((k : ℝ) - N) * c) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [this, hs, Complex.ofReal_one]
    rw [hs', one_mul]

end UnforcedLeray.Short.PartIIa.FBCLL
