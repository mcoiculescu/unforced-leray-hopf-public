import UnforcedLeray.Lib.EvolutionFamilies.DysonRight

/-!
# Mild solutions: variation of constants, uniqueness and residual transfer (INF08 T8.8)

Scoping note `scoping/INF07-INF08-INF09-Evolution.md`, §5, target T8.8 (`paper/main.tex`,
lines 1768-1790, 1828-1840 and the mild formulations of Sections 4, 6 and 9; blueprint B0116,
B0117, B0125, B0126, B0137, B0357, B0362).

For an evolution family `F` on `[a,b]`, bounded interactions `A, A₁, A₂` and an integrable source
`ρ` on `(s,b]`:

* `dyson_inhom` (variation of constants): with `U = dyson F A`,
  `∫_s^τ U(τ,r) ρ(r) dr = ∫_s^τ F(τ,r) ρ(r) dr + ∫_s^τ F(τ,q) A(q) ∫_s^q U(q,r) ρ(r) dr dq`;
* `mild_unique`: a continuous mild solution `z(t) = F(t,s) z(s) + ∫_s^t F(t,r)(A(r) z(r) + ρ(r)) dr`
  is `z(t) = U(t,s) z(s) + ∫_s^t U(t,r) ρ(r) dr`;
* `mild_transfer` (the signature of the scoping note, with the continuity of `z` and the
  integrability of `ρ` made explicit): a mild solution relative to `F` with interaction `A₁` is
  a mild solution relative to `dyson F A₂` with interaction `A₁ - A₂`.

The hypotheses "`z` continuous on `[s,b]`" and "`ρ` integrable on `(s,b]`" are needed for the
integrals to carry their meaning (otherwise a non-integrable integrand integrates to `0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}

namespace BoundedPert

/-- The identity interaction `A(r) = 1`. -/
def one : BoundedPert X a b where
  A := fun _ => 1
  meas _ := aestronglyMeasurable_const
  bdd := ⟨1, fun _ _ => ContinuousLinearMap.norm_id_le⟩

@[simp] theorem one_A (r : ℝ) : (one : BoundedPert X a b).A r = 1 := rfl

/-- The difference of two interactions. -/
def sub (A₁ A₂ : BoundedPert X a b) : BoundedPert X a b where
  A r := A₁.A r - A₂.A r
  meas x := (A₁.meas x).sub (A₂.meas x)
  bdd := ⟨A₁.C + A₂.C, fun r hr => (norm_sub_le _ _).trans (add_le_add (A₁.norm_le hr)
    (A₂.norm_le hr))⟩

@[simp] theorem sub_A (A₁ A₂ : BoundedPert X a b) (r : ℝ) :
    (sub A₁ A₂).A r = A₁.A r - A₂.A r := rfl

end BoundedPert

variable [CompleteSpace X]

/-- **Fubini on the triangle** with an integrable majorant `‖G(q,r)‖ ≤ g(r)`. -/
theorem integral_triangle_swap_of_integrable {s t : ℝ} (hst : s ≤ t) {G : ℝ → ℝ → X}
    {g : ℝ → ℝ} (hG : AEStronglyMeasurable (Function.uncurry G) (triMeasure s t))
    (hg : IntegrableOn g (Ioc s t))
    (hK : ∀ q r, s < r → r < q → q ≤ t → ‖G q r‖ ≤ g r) :
    ∫ q in s..t, (∫ r in s..q, G q r) = ∫ r in s..t, (∫ q in r..t, G q r) := by
  set μ : Measure ℝ := volume.restrict (Ioc s t) with hμ
  set f : ℝ → ℝ → X := fun q r => lowerTri.indicator (Function.uncurry G) (q, r) with hf_def
  have hfun : Function.uncurry f = lowerTri.indicator (Function.uncurry G) := by
    ext p; rfl
  have hf : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [hfun]
    have hgi : Integrable (fun p : ℝ × ℝ => ‖g p.2‖) (μ.prod μ) :=
      (Integrable.comp_snd hg.norm μ)
    refine hgi.mono' ((aestronglyMeasurable_indicator_iff measurableSet_lowerTri).mpr hG) ?_
    rw [hμ, Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    by_cases hpS : p ∈ lowerTri
    · rw [indicator_of_mem hpS]
      exact (hK p.1 p.2 hp.2.1 hpS hp.1.2).trans (le_abs_self _)
    · rw [indicator_of_notMem hpS, norm_zero]
      exact norm_nonneg _
  have hswap := integral_integral_swap hf
  have hL : ∫ q in s..t, (∫ r in s..q, G q r) = ∫ q, ∫ r, f q r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    have hfq : (fun r => f q r) = (Iio q).indicator (G q) := by
      ext r
      simp only [hf_def, lowerTri, indicator_apply, mem_ofPred_eq, mem_Iio,
        Function.uncurry_apply_pair]
    have hset : Ioc s t ∩ Iio q = Ioo s q := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, h3.le.trans hq.2⟩, h3⟩
    rw [intervalIntegral.integral_of_le hq.1.le, integral_Ioc_eq_integral_Ioo, hfq,
      setIntegral_indicator measurableSet_Iio, hset]
  have hR : ∫ r in s..t, (∫ q in r..t, G q r) = ∫ r, ∫ q, f q r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hfr : (fun q => f q r) = (Ioi r).indicator (fun q => G q r) := by
      ext q
      simp only [hf_def, lowerTri, indicator_apply, mem_ofPred_eq, mem_Ioi,
        Function.uncurry_apply_pair]
    have hset : Ioc s t ∩ Ioi r = Ioc r t := by
      ext q
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hr.1.trans h1, h2⟩, h1⟩
    rw [intervalIntegral.integral_of_le hr.2, hfr, setIntegral_indicator measurableSet_Ioi, hset]
  rw [hL, hswap, hR]

namespace EvolutionFamily

variable (L : EvolutionFamily X a b)

/-- `r ↦ L(t,r) ρ(r)` is interval integrable for an integrable `ρ`. -/
theorem intervalIntegrable_apply {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {ρ : ℝ → X}
    (hρ : IntegrableOn ρ (Ioc s t)) : IntervalIntegrable (fun r => L.U t r (ρ r)) volume s t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  refine (hρ.norm.const_mul L.M).mono' ?_ ?_
  · exact aestronglyMeasurable_clm_apply (L := fun r => L.U t r) (fun v =>
      ((L.continuousOn_snd ht v).mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl))).aestronglyMeasurable
        measurableSet_Ioc) hρ.aestronglyMeasurable
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr =>
      L.norm_apply_le (hs.trans hr.1.le) hr.2 ht _

/-- **Continuity of a Duhamel integral with an integrable source**: `t ↦ ∫_s^t L(t,r) ρ(r) dr`
is continuous on `[s,b]`. -/
theorem continuousOn_integral_apply {s : ℝ} (hs : a ≤ s) {ρ : ℝ → X}
    (hρ : IntegrableOn ρ (Ioc s b)) :
    ContinuousOn (fun t => ∫ r in s..t, L.U t r (ρ r)) (Icc s b) := by
  intro t₀ ht₀
  have hrepr : ∀ t ∈ Icc s b, ∫ r in s..t, L.U t r (ρ r) =
      ∫ r in Ioc s b, (Ioc s t).indicator (fun r => L.U t r (ρ r)) r := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht.1, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioc le_rfl ht.2)]
  have hlim : Tendsto (fun t => ∫ r in Ioc s b, (Ioc s t).indicator (fun r => L.U t r (ρ r)) r)
      (𝓝[Icc s b] t₀) (𝓝 (∫ r in Ioc s b, (Ioc s t₀).indicator (fun r => L.U t₀ r (ρ r)) r)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun r => L.M * ‖ρ r‖) ?_ ?_
      (hρ.norm.const_mul L.M) ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine ((aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr ?_).restrict
      exact aestronglyMeasurable_clm_apply (L := fun r => L.U t r) (fun v =>
        ((L.continuousOn_snd ht.2 v).mono
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl))).aestronglyMeasurable
          measurableSet_Ioc)
        (hρ.aestronglyMeasurable.mono_measure (Measure.restrict_mono
          (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
      by_cases hrt : r ∈ Ioc s t
      · rw [indicator_of_mem hrt]
        exact L.norm_apply_le (hs.trans hr.1.le) hrt.2 ht.2 _
      · rw [indicator_of_notMem hrt, norm_zero]
        exact mul_nonneg L.M_nonneg (norm_nonneg _)
    · have hev : ∀ᵐ r ∂(volume.restrict (Ioc s b)), r ∈ Ioc s b :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hev, ae_restrict_of_ae (ae_ne_real t₀)] with r hr hrt₀
      rcases lt_or_gt_of_ne hrt₀ with hlt | hgt
      · -- `r < t₀`: eventually `r < t`
        have hev1 : ∀ᶠ t in 𝓝[Icc s b] t₀, r < t :=
          (continuous_id.continuousWithinAt.tendsto).eventually (lt_mem_nhds hlt)
        rw [indicator_of_mem (s := Ioc s t₀) ⟨hr.1, hlt.le⟩]
        have hc : ContinuousWithinAt (fun t => L.U t r (ρ r)) (Icc s b) t₀ := by
          have h1 : ContinuousWithinAt (fun t => L.U t r (ρ r)) (Icc r b) t₀ :=
            (L.continuousOn_fst (hs.trans hr.1.le) (ρ r)) t₀ ⟨hlt.le, ht₀.2⟩
          refine h1.mono_of_mem_nhdsWithin ?_
          filter_upwards [self_mem_nhdsWithin, hev1] with t ht h
          exact ⟨h.le, ht.2⟩
        refine hc.tendsto.congr' ?_
        filter_upwards [hev1, self_mem_nhdsWithin] with t h ht
        exact (indicator_of_mem (s := Ioc s t) ⟨hr.1, h.le⟩ (fun r => L.U t r (ρ r))).symm
      · have hev1 : ∀ᶠ t in 𝓝[Icc s b] t₀, t < r :=
          (continuous_id.continuousWithinAt.tendsto).eventually (gt_mem_nhds hgt)
        rw [indicator_of_notMem (s := Ioc s t₀) (fun h => absurd h.2 (not_le.mpr hgt))]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev1] with t h
        exact (indicator_of_notMem (s := Ioc s t) (fun h' => absurd h'.2 (not_le.mpr h))
          (fun r => L.U t r (ρ r))).symm
  have := hlim.congr' (eventually_nhdsWithin_of_forall fun t ht => (hrepr t ht).symm)
  rw [ContinuousWithinAt, hrepr t₀ ht₀]
  exact this

end EvolutionFamily

variable (F : EvolutionFamily X a b) (A : BoundedPert X a b)

/-- **Variation of constants** (INF08 T8.8; inhomogeneous Duhamel formula): for
`U = dyson F A` and an integrable source `ρ`,
`∫_s^τ U(τ,r) ρ(r) dr = ∫_s^τ F(τ,r) ρ(r) dr + ∫_s^τ F(τ,q) A(q) ∫_s^q U(q,r) ρ(r) dr dq`. -/
theorem dyson_inhom {s τ : ℝ} (hs : a ≤ s) (hsτ : s ≤ τ) (hτ : τ ≤ b) {ρ : ℝ → X}
    (hρ : IntegrableOn ρ (Ioc s τ)) :
    ∫ r in s..τ, (dyson F A).U τ r (ρ r) =
      (∫ r in s..τ, F.U τ r (ρ r)) +
        ∫ q in s..τ, F.U τ q (A.A q (∫ r in s..q, (dyson F A).U q r (ρ r))) := by
  set U := dyson F A with hU
  have hiU := U.intervalIntegrable_apply hs hsτ hτ hρ
  have hiF := F.intervalIntegrable_apply hs hsτ hτ hρ
  have h1 : (∫ r in s..τ, U.U τ r (ρ r)) - ∫ r in s..τ, F.U τ r (ρ r) =
      ∫ r in s..τ, ∫ q in r..τ,
        F.U τ q (A.A q (U.U q r ((BoundedPert.one : BoundedPert X a b).A r (ρ r)))) := by
    rw [← intervalIntegral.integral_sub hiU hiF]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hsτ] at hr
    simp only [BoundedPert.one_A, one_apply_eq_self]
    rw [hU, dyson_left F A ⟨hs.trans hr.1, hr.2, hτ⟩ (ρ r)]
    abel
  have h2 := integral_triangle_swap_of_integrable hsτ
    (G := fun q r => F.U τ q (A.A q (U.U q r ((BoundedPert.one : BoundedPert X a b).A r (ρ r)))))
    (g := fun r => F.M * A.C * (U.M * ((BoundedPert.one : BoundedPert X a b).C * ‖ρ r‖)))
    (F.aestronglyMeasurable_iterated U A BoundedPert.one hs hτ hρ.aestronglyMeasurable)
    (((hρ.norm.const_mul _).const_mul _).const_mul _)
    (fun q r hr hrq hq => F.norm_iterated_le U A BoundedPert.one hs hτ hr.le hrq.le hq _)
  have h3 : ∫ q in s..τ, (∫ r in s..q,
        F.U τ q (A.A q (U.U q r ((BoundedPert.one : BoundedPert X a b).A r (ρ r))))) =
      ∫ q in s..τ, F.U τ q (A.A q (∫ r in s..q, U.U q r (ρ r))) := by
    refine intervalIntegral.integral_congr fun q hq => ?_
    rw [uIcc_of_le hsτ] at hq
    simp only [BoundedPert.one_A, one_apply_eq_self]
    exact ((F.U τ q).comp (A.A q)).intervalIntegral_comp_comm
      (U.intervalIntegrable_apply hs hq.1 (hq.2.trans hτ)
        (hρ.mono_set (Ioc_subset_Ioc le_rfl hq.2)))
  rw [← h3, h2, ← h1]
  abel

/-- **Uniqueness and representation of mild solutions** (INF08 T8.8; B0116, B0117): if `z` is
continuous on `[s,b]`, `ρ` is integrable on `(s,b]` and
`z(t) = F(t,s) z(s) + ∫_s^t F(t,r) (A(r) z(r) + ρ(r)) dr` on `[s,b]`, then
`z(t) = U(t,s) z(s) + ∫_s^t U(t,r) ρ(r) dr` with `U = dyson F A`. -/
theorem mild_unique {s : ℝ} (hs : a ≤ s) {z ρ : ℝ → X} (hzc : ContinuousOn z (Icc s b))
    (hρ : IntegrableOn ρ (Ioc s b))
    (hz : ∀ t ∈ Icc s b, z t = F.U t s (z s) + ∫ r in s..t, F.U t r (A.A r (z r) + ρ r)) :
    ∀ t ∈ Icc s b, z t = (dyson F A).U t s (z s) + ∫ r in s..t, (dyson F A).U t r (ρ r) := by
  set U := dyson F A with hU
  set w : ℝ → X := fun t => U.U t s (z s) + ∫ r in s..t, U.U t r (ρ r) with hw
  have hIc : ContinuousOn (fun t => ∫ r in s..t, U.U t r (ρ r)) (Icc s b) :=
    U.continuousOn_integral_apply hs hρ
  have hwc : ContinuousOn w (Icc s b) := (U.continuousOn_fst hs (z s)).add hIc
  have hweq : ∀ t ∈ Icc s b, w t = F.U t s (z s) + ∫ r in s..t, F.U t r (A.A r (w r) + ρ r) := by
    intro t ht
    have hρt : IntegrableOn ρ (Ioc s t) := hρ.mono_set (Ioc_subset_Ioc le_rfl ht.2)
    have hi1 : IntervalIntegrable (fun r => F.U t r (A.A r (U.U r s (z s)))) volume s t :=
      F.intervalIntegrable_integrand A hs ht.1 ht.2
        ((U.continuousOn_fst hs (z s)).mono (Icc_subset_Icc le_rfl ht.2))
    have hi2 : IntervalIntegrable (fun r => F.U t r (A.A r (∫ q in s..r, U.U r q (ρ q))))
        volume s t :=
      F.intervalIntegrable_integrand A hs ht.1 ht.2 (hIc.mono (Icc_subset_Icc le_rfl ht.2))
    have hi3 := F.intervalIntegrable_apply hs ht.1 ht.2 hρt
    have hsplit : ∫ r in s..t, F.U t r (A.A r (w r) + ρ r) =
        (∫ r in s..t, F.U t r (A.A r (U.U r s (z s)))) +
          ((∫ r in s..t, F.U t r (ρ r)) +
            ∫ r in s..t, F.U t r (A.A r (∫ q in s..r, U.U r q (ρ q)))) := by
      rw [← intervalIntegral.integral_add hi3 hi2, ← intervalIntegral.integral_add hi1
        (hi3.add hi2)]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [hw, map_add]
      abel
    rw [hsplit, ← dyson_inhom F A hs ht.1 ht.2 hρt, ← add_assoc]
    simp only [hw]
    rw [hU, dyson_left F A ⟨hs, ht.1, ht.2⟩ (z s)]
  have hzero := F.eq_zero_of_volterra A hs (w := fun t => z t - w t) (hzc.sub hwc)
    (fun t ht => ?_)
  · intro t ht
    exact sub_eq_zero.mp (hzero t ht)
  · have hρt : IntegrableOn ρ (Ioc s t) := hρ.mono_set (Ioc_subset_Ioc le_rfl ht.2)
    have hj : ∀ v : ℝ → X, ContinuousOn v (Icc s t) →
        IntervalIntegrable (fun r => F.U t r (A.A r (v r) + ρ r)) volume s t := by
      intro v hv
      have h := (F.intervalIntegrable_integrand A hs ht.1 ht.2 hv).add
        (F.intervalIntegrable_apply hs ht.1 ht.2 hρt)
      refine h.congr ?_
      exact fun r _ => by simp only [map_add]
    rw [hz t ht, hweq t ht, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hj z (hzc.mono (Icc_subset_Icc le_rfl ht.2)))
        (hj w (hwc.mono (Icc_subset_Icc le_rfl ht.2)))]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [map_sub, map_add]
    abel

/-- **Residual transfer** (INF08 T8.8 `mild_transfer`; B0116, B0125, B0137): a continuous mild
solution relative to `F` with interaction `A₁` and integrable source `ρ` is a mild solution
relative to `dyson F A₂` with interaction `A₁ - A₂`. -/
theorem mild_transfer (A₁ A₂ : BoundedPert X a b) {z ρ : ℝ → X} {s : ℝ} (hs : a ≤ s)
    (hzc : ContinuousOn z (Icc s b)) (hρ : IntegrableOn ρ (Ioc s b))
    (hz : ∀ t ∈ Icc s b, z t = F.U t s (z s) + ∫ r in s..t, F.U t r (A₁.A r (z r) + ρ r)) :
    ∀ t ∈ Icc s b, z t = (dyson F A₂).U t s (z s) +
      ∫ r in s..t, (dyson F A₂).U t r ((A₁.A r - A₂.A r) (z r) + ρ r) := by
  set ρ' : ℝ → X := fun r => (A₁.A r - A₂.A r) (z r) + ρ r with hρ'
  have hρ'i : IntegrableOn ρ' (Ioc s b) := by
    refine Integrable.add ?_ hρ
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hzc
    refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ ((BoundedPert.sub A₁ A₂).C * K) ?_
    · exact aestronglyMeasurable_clm_apply (L := (BoundedPert.sub A₁ A₂).A)
        (fun v => ((BoundedPert.sub A₁ A₂).meas v).mono_measure
          (Measure.restrict_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl)) le_rfl))
        ((hzc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
      exact ((BoundedPert.sub A₁ A₂).A r).le_opNorm _ |>.trans (mul_le_mul
        ((BoundedPert.sub A₁ A₂).norm_le ⟨hs.trans hr.1.le, hr.2⟩)
        (hK r (Ioc_subset_Icc_self hr)) (norm_nonneg _) (BoundedPert.C_nonneg _))
  refine mild_unique F A₂ hs hzc hρ'i fun t ht => ?_
  rw [hz t ht]
  congr 1
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [sub_apply]
  congr 1
  abel

/-- **Lipschitz dependence on the interaction** (INF08 T8.2 `norm_dyson_sub_dyson_le`; B0108,
B0657): if `‖A₁(r) - A₂(r)‖ ≤ δ` on `[a,b]`, then
`‖U₁(t,s) - U₂(t,s)‖ ≤ M₂ M₁ δ (t - s)` with `Uᵢ = dyson F Aᵢ` and `Mᵢ` their bounds on the
triangle. Proof: `mild_transfer` with `z = U₁(·,s)x` and `ρ = 0`. -/
theorem norm_dyson_sub_dyson_le (A₁ A₂ : BoundedPert X a b) {δ : ℝ}
    (hδ : ∀ r ∈ Icc a b, ‖A₁.A r - A₂.A r‖ ≤ δ) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t)
    (ht : t ≤ b) :
    ‖(dyson F A₁).U t s - (dyson F A₂).U t s‖ ≤
      (dyson F A₂).M * (dyson F A₁).M * δ * (t - s) := by
  set U₁ := dyson F A₁
  set U₂ := dyson F A₂
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ s ⟨hs, hst.trans ht⟩)
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have := U₁.M_nonneg; have := U₂.M_nonneg; have : 0 ≤ t - s := by linarith
    positivity) fun x => ?_
  have hsb : s ≤ b := hst.trans ht
  have hmild := mild_transfer F A₁ A₂ hs (z := fun τ => U₁.U τ s x) (ρ := fun _ => 0)
    (U₁.continuousOn_fst hs x) integrableOn_zero (fun τ hτ => by
      simp only [add_zero]
      rw [U₁.U_diag s ⟨hs, hsb⟩, one_apply_eq_self]
      exact dyson_left F A₁ ⟨hs, hτ.1, hτ.2⟩ x) t ⟨hst, ht⟩
  simp only [add_zero] at hmild
  rw [U₁.U_diag s ⟨hs, hsb⟩, one_apply_eq_self] at hmild
  rw [sub_apply, hmild, add_sub_cancel_left]
  calc ‖∫ r in s..t, U₂.U t r ((A₁.A r - A₂.A r) (U₁.U r s x))‖
      ≤ ∫ r in s..t, U₂.M * δ * U₁.M * ‖x‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le hst (ae_of_all _ fun r hr => ?_)
          intervalIntegrable_const
        calc ‖U₂.U t r ((A₁.A r - A₂.A r) (U₁.U r s x))‖
            ≤ U₂.M * ‖(A₁.A r - A₂.A r) (U₁.U r s x)‖ :=
              U₂.norm_apply_le (hs.trans hr.1.le) hr.2 ht _
          _ ≤ U₂.M * (δ * (U₁.M * ‖x‖)) := by
              refine mul_le_mul_of_nonneg_left (((A₁.A r - A₂.A r).le_opNorm _).trans
                (mul_le_mul (hδ r ⟨hs.trans hr.1.le, hr.2.trans ht⟩)
                  (U₁.norm_apply_le hs hr.1.le (hr.2.trans ht) x) (norm_nonneg _) hδ0))
                U₂.M_nonneg
          _ = U₂.M * δ * U₁.M * ‖x‖ := by ring
    _ = U₂.M * U₁.M * δ * (t - s) * ‖x‖ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

end UnforcedLeray.Evolution
