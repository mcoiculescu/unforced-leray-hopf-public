import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.PeriodicBoxBound

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma slc_lintegral_eq_sq (g : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ = (eLpNorm g 2 μ) ^ (2 : ℝ) := by
  show ∫⁻ x, pbF g x ∂μ = (eLpNorm g 2 μ) ^ (2 : ℝ)
  rw [pb_eLpNorm_two, ← ENNReal.rpow_mul]
  norm_num

lemma slc_tri (μ : Measure (ℝ × ℝ)) (a b : ℝ × ℝ → ℂ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    eLpNorm a 2 μ ≤ eLpNorm (a - b) 2 μ + eLpNorm b 2 μ := by
  have h := eLpNorm_add_le (ha.sub hb).aestronglyMeasurable hb.aestronglyMeasurable
    (one_le_two : (1 : ℝ≥0∞) ≤ 2)
  rw [sub_add_cancel] at h
  exact h

theorem stLocL2Of : UnforcedLeray.Short.IIIa.STLocL2Of := by
  intro c m t s f G hc hts hfreg htend hGm hGae
  intro K hK hKsub
  classical
  have hK' : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  have hK'sub : Prod.fst '' K ⊆ Ioo t s := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hKsub hp).1
  -- a bounded box containing the second components
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK2.isBounded
  have hsub : K ⊆ (Prod.fst '' K) ×ˢ sliceBox R := by
    intro p hp
    refine mem_prod.2 ⟨mem_image_of_mem Prod.fst hp, ?_⟩
    have h1 : ‖p.2‖ ≤ R := hR p.2 ⟨p, hp, rfl⟩
    have h2 : ‖p.2.1‖ ≤ R := (norm_fst_le _).trans h1
    have h3 : ‖p.2.2‖ ≤ R := (norm_snd_le _).trans h1
    rw [Real.norm_eq_abs] at h2 h3
    exact ⟨abs_le.1 h2, abs_le.1 h3⟩
  -- the periodic box bound
  obtain ⟨M, hMtop, hMb⟩ := periodicBoxBound c m R hc
  -- a uniform bound on the cell norms over the projection
  have hS : ∃ S : ℝ≥0∞, S ≠ ⊤ ∧ ∀ r ∈ Prod.fst '' K, xNorm c (-m) (f r) ≤ S := by
    let U : ℝ → Set ℝ := fun x =>
      {r' | r' ∈ Ioo t s → xNorm c (-m) (f r') ≤ xNorm c (-m) (f x) + 1}
    have hU : ∀ x ∈ Prod.fst '' K, U x ∈ 𝓝 x := by
      intro x hx
      have hxI : x ∈ Ioo t s := hK'sub hx
      have hEq : 𝓝[Ioo t s] x = 𝓝 x := nhdsWithin_eq_nhds.2 (Ioo_mem_nhds hxI.1 hxI.2)
      have hT : Tendsto (fun r' => xNorm c (-m) (f r' - f x)) (𝓝 x) (𝓝 0) := by
        have := htend x hxI
        rwa [hEq] at this
      have hev := hT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
      have key : ∀ᶠ r' in 𝓝 x, r' ∈ U x := by
        filter_upwards [hev, Ioo_mem_nhds hxI.1 hxI.2] with r' hr' hr'I
        intro _
        have hlt : xNorm c (-m) (f r' - f x) < 1 := hr'
        have htri : xNorm c (-m) (f r') ≤ xNorm c (-m) (f r' - f x) + xNorm c (-m) (f x) :=
          slc_tri _ _ _ (hfreg r' hr'I).2 (hfreg x hxI).2
        calc xNorm c (-m) (f r') ≤ xNorm c (-m) (f r' - f x) + xNorm c (-m) (f x) := htri
          _ ≤ 1 + xNorm c (-m) (f x) := add_le_add_left hlt.le _
          _ = xNorm c (-m) (f x) + 1 := add_comm _ _
      exact key
    obtain ⟨T, hTK, hcov⟩ := hK'.elim_nhds_subcover U hU
    refine ⟨∑ x ∈ T, (xNorm c (-m) (f x) + 1), ?_, ?_⟩
    · refine ENNReal.sum_ne_top.2 ?_
      intro x hx
      have hxI : x ∈ Ioo t s := hK'sub (hTK x hx)
      exact ENNReal.add_ne_top.2 ⟨(hfreg x hxI).2.eLpNorm_lt_top.ne, ENNReal.one_ne_top⟩
    · intro r hr
      obtain ⟨x, hxT, hrU⟩ := mem_iUnion₂.1 (hcov hr)
      have hle : xNorm c (-m) (f r) ≤ xNorm c (-m) (f x) + 1 := hrU (hK'sub hr)
      calc xNorm c (-m) (f r) ≤ xNorm c (-m) (f x) + 1 := hle
        _ ≤ ∑ y ∈ T, (xNorm c (-m) (f y) + 1) :=
          Finset.single_le_sum (f := fun y => xNorm c (-m) (f y) + 1)
            (fun _ _ => zero_le) hxT
  obtain ⟨S, hStop, hSb⟩ := hS
  -- the slice bound
  have hinner : ∀ r ∈ Prod.fst '' K,
      ∫⁻ x, ‖G (r, x)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (sliceBox R)) ≤ (M * S) ^ (2 : ℝ) := by
    intro r hr
    have hrI : r ∈ Ioo t s := hK'sub hr
    have hcongr : ∫⁻ x, ‖G (r, x)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (sliceBox R))
        = ∫⁻ x, ‖f r x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (sliceBox R)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (hGae r hrI)] with x hx
      simp only [hx]
    rw [hcongr, slc_lintegral_eq_sq]
    have h0 : M * xNorm c (-m) (f r) ≤ M * S := by
      gcongr
      exact hSb r hr
    have h1 : eLpNorm (f r) 2 (volume.restrict (sliceBox R)) ≤ M * S :=
      (hMb (f r) (hfreg r hrI).1 (hfreg r hrI).2.aestronglyMeasurable).2.trans h0
    exact ENNReal.rpow_le_rpow h1 (by norm_num)
  have hC : (M * S) ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hMtop hStop)
  have hVol : volume (Prod.fst '' K) < ⊤ := hK'.measure_lt_top
  have hvol : (volume : Measure (ℝ × (ℝ × ℝ))) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    rfl
  have hprod : ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(volume.restrict ((Prod.fst '' K) ×ˢ sliceBox R))
      = ∫⁻ r, (∫⁻ x, ‖G (r, x)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (sliceBox R)))
          ∂(volume.restrict (Prod.fst '' K)) := by
    have hsplit : (volume : Measure (ℝ × (ℝ × ℝ))).restrict ((Prod.fst '' K) ×ˢ sliceBox R)
        = ((volume : Measure ℝ).restrict (Prod.fst '' K)).prod
            ((volume : Measure (ℝ × ℝ)).restrict (sliceBox R)) := by
      rw [hvol, Measure.prod_restrict]
    rw [hsplit]
    exact lintegral_prod _ (hGm.enorm.pow_const _).aemeasurable
  have hbound : ∫⁻ r, (∫⁻ x, ‖G (r, x)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (sliceBox R)))
      ∂(volume.restrict (Prod.fst '' K)) ≤ (M * S) ^ (2 : ℝ) * volume (Prod.fst '' K) := by
    calc _ ≤ ∫⁻ _r, (M * S) ^ (2 : ℝ) ∂(volume.restrict (Prod.fst '' K)) :=
          lintegral_mono_ae ((ae_restrict_iff' hK'.isClosed.measurableSet).2
            (ae_of_all _ fun r hr => hinner r hr))
      _ = (M * S) ^ (2 : ℝ) * volume (Prod.fst '' K) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  have hfin : ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(volume.restrict K) < ⊤ := by
    calc ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(volume.restrict K)
        ≤ ∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂(volume.restrict ((Prod.fst '' K) ×ˢ sliceBox R)) :=
          lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
      _ = _ := hprod
      _ ≤ (M * S) ^ (2 : ℝ) * volume (Prod.fst '' K) := hbound
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hVol
  have hMem : MemLp G 2 (volume.restrict K) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using hfin
  exact hMem
