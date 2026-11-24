import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# Continuity of the duality pairing (`LadPairCont`, SP 3074-3075)

Weighted Cauchy-Schwarz `|∫_{C_c} F G| ≤ ‖F‖_{X_{m,c}} ‖G‖_{X_{-m,c}}` (complex valued), and the
increment bound `P(r') - P(r) = ∫ (w r' - w r) φ r' + ∫ w r (φ r' - φ r)` with the strong continuity
of both flows.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace PairContAux

/-- Complex analogue of `B0579.eLpNorm_cellMeasure`. -/
lemma eLpNorm_cellMeasure_cx (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    eLpNorm f 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x) 2
        (volume.restrict (B0579.cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have e : ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (B0579.jb x ^ (m / 2)) := by
    rw [← Real.enorm_eq_ofReal h0]; simp [enorm]
  rw [mul_pow, e, ← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

lemma memLp_scaled {c m : ℝ} {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F x) 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hF.1.mono_ac (B0579.ac_cellMeasure c m))
    exact (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)).aestronglyMeasurable
  · rw [← eLpNorm_cellMeasure_cx]; exact hF.2

lemma holder {c m : ℝ} {F G : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c m))
    (hG : MemLp G 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun x => F x * G x) (B0579.cell c) ∧
      ‖∫ x in B0579.cell c, F x * G x‖ ≤
        (eLpNorm F 2 (B0579.cellMeasure c m)).toReal *
          (eLpNorm G 2 (B0579.cellMeasure c (-m))).toReal := by
  have hA := memLp_scaled hF
  have hB := memLp_scaled hG
  have hprod : (fun x => (((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F x) *
      (((B0579.jb x ^ (-m / 2) : ℝ) : ℂ) * G x)) = fun x => F x * G x := by
    funext x
    have : ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * ((B0579.jb x ^ (-m / 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, B0579.jb_rpow_mul]
      have : m / 2 + -m / 2 = 0 := by ring
      rw [this, Real.rpow_zero]; simp
    calc _ = (((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * ((B0579.jb x ^ (-m / 2) : ℝ) : ℂ)) *
          (F x * G x) := by ring
      _ = _ := by rw [this, one_mul]
  have hI : Integrable (fun x => F x * G x) (volume.restrict (B0579.cell c)) := by
    rw [← hprod]; exact hA.integrable_mul hB
  refine ⟨hI, ?_⟩
  have h1 : eLpNorm (fun x => F x * G x) 1 (volume.restrict (B0579.cell c)) ≤
      eLpNorm F 2 (B0579.cellMeasure c m) * eLpNorm G 2 (B0579.cellMeasure c (-m)) := by
    rw [eLpNorm_cellMeasure_cx, eLpNorm_cellMeasure_cx, ← hprod]
    have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hB.1 hA.1
      (μ := volume.restrict (B0579.cell c)) (φ := fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F x)
    exact this
  have h2 : ‖∫ x in B0579.cell c, F x * G x‖ₑ ≤
      eLpNorm F 2 (B0579.cellMeasure c m) * eLpNorm G 2 (B0579.cellMeasure c (-m)) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm]; exact h1
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hF.2.ne hG.2.ne) h2
  rw [ENNReal.toReal_mul] at h3
  simpa [toReal_enorm] using h3

end PairContAux

open PairContAux in
theorem ladPairCont : LadPairCont := by
  intro ν c m tr t s g φ f w u hts hφ hw
  intro r hr
  have hwm : ∀ r' ∈ Icc t s, MemLp (w r') 2 (B0579.cellMeasure c m) := fun r' h => hw.memX r' h.1
  have hφm : ∀ r' ∈ Icc t s, MemLp (φ r') 2 (B0579.cellMeasure c (-m)) := fun r' h => hφ.memX r' h
  set a : ℝ → ℝ := fun r' => (xNorm c m (w r' - w r)).toReal with ha
  set b : ℝ → ℝ := fun r' => (xNorm c (-m) (φ r' - φ r)).toReal with hb
  have ha0 : Tendsto a (𝓝[Icc t s] r) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (w r' - w r)) (𝓝[Icc t s] r) (𝓝 0) :=
      (hw.strongCont r hr.1).mono_left (nhdsWithin_mono _ (fun x hx => hx.1))
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [ha, Function.comp_def] using this
  have hb0 : Tendsto b (𝓝[Icc t s] r) (𝓝 0) := by
    have h1 := hφ.strongCont r hr
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [hb, Function.comp_def] using this
  set Nφ := (xNorm c (-m) (φ r)).toReal
  set Nw := (xNorm c m (w r)).toReal
  have hbound : ∀ r' ∈ Icc t s, ‖ladPair c w φ r' - ladPair c w φ r‖ ≤
      a r' * (Nφ + b r') + Nw * b r' := by
    intro r' hr'
    have hd1 : MemLp (w r' - w r) 2 (B0579.cellMeasure c m) := (hwm r' hr').sub (hwm r hr)
    have hd2 : MemLp (φ r' - φ r) 2 (B0579.cellMeasure c (-m)) := (hφm r' hr').sub (hφm r hr)
    obtain ⟨i1, n1⟩ := holder hd1 (hφm r' hr')
    obtain ⟨i2, n2⟩ := holder (hwm r hr) hd2
    obtain ⟨i3, -⟩ := holder (hwm r' hr') (hφm r' hr')
    obtain ⟨i4, -⟩ := holder (hwm r hr) (hφm r hr)
    have hsplit : ladPair c w φ r' - ladPair c w φ r =
        (∫ x in B0579.cell c, (w r' - w r) x * φ r' x) +
          ∫ x in B0579.cell c, w r x * (φ r' - φ r) x := by
      unfold ladPair
      rw [← integral_sub i3 i4, ← integral_add i1 i2]
      congr 1; funext x; simp only [Pi.sub_apply]; ring
    have hφn : (xNorm c (-m) (φ r')).toReal ≤ Nφ + b r' := by
      have hle : xNorm c (-m) (φ r') ≤ xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r) := by
        have : φ r' = φ r + (φ r' - φ r) := by abel
        unfold xNorm
        calc eLpNorm (φ r') 2 _ = eLpNorm (φ r + (φ r' - φ r)) 2 _ := by rw [← this]
          _ ≤ _ := eLpNorm_add_le (hφm r hr).1 hd2.1 (by norm_num)
      have hfin : xNorm c (-m) (φ r) + xNorm c (-m) (φ r' - φ r) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨(hφm r hr).2.ne, hd2.2.ne⟩
      have := ENNReal.toReal_mono hfin hle
      have e1 : xNorm c (-m) (φ r) ≠ ⊤ := (hφm r hr).2.ne
      have e2 : xNorm c (-m) (φ r' - φ r) ≠ ⊤ := hd2.2.ne
      rwa [ENNReal.toReal_add e1 e2] at this
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine n1.trans ?_
      exact mul_le_mul_of_nonneg_left hφn ENNReal.toReal_nonneg
    · exact n2
  have hlim : Tendsto (fun r' => a r' * (Nφ + b r') + Nw * b r') (𝓝[Icc t s] r) (𝓝 0) := by
    have h1 : Tendsto (fun r' => Nφ + b r') (𝓝[Icc t s] r) (𝓝 (Nφ + 0)) :=
      (tendsto_const_nhds (x := Nφ)).add hb0
    have h2 : Tendsto (fun r' => Nw * b r') (𝓝[Icc t s] r) (𝓝 (Nw * 0)) :=
      (tendsto_const_nhds (x := Nw)).mul hb0
    have := (ha0.mul h1).add h2
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbound) hlim

end UnforcedLeray.Short.IIIa
