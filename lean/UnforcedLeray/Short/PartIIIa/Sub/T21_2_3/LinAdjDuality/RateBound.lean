import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ChiBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjGradInt

/-!
# `PartIII-a:T21/2/3/1/14` (`ladRateBound`): a dominating function for the rate (SP 3074-3075)

For `r ∈ [t, s)`, `R ≥ 1`, `ρ ∈ (t, r)`, `LadRateSplit` writes `ladRate R ρ` as
`∫ w χ_R χ - ∫ (u·∇E) χ_R φ + ladComm R ρ`; the three pieces are bounded by the `X_m`-`X_{-m}`
Cauchy-Schwarz pairing, with `‖w‖, ‖φ‖` bounded on compact intervals (strong continuity),
`‖χ‖ ≤ M` (`ladChiBound`), `‖u‖₂` bounded by `ladVelLip`, and the commutator bounded by
`K(‖w‖‖φ‖ + Σ_k ‖w‖‖∂_kφ‖)`, whose time integrability is `ladAdjGradInt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace RateBoundAux

/-- Cauchy-Schwarz for the unweighted pairing of `X_m` and `X_{-m}`, in norms. -/
lemma cs_norm (c m : ℝ) {F G : ℝ × ℝ → ℂ} (hF : MemLp F 2 (B0579.cellMeasure c m))
    (hG : MemLp G 2 (B0579.cellMeasure c (-m))) :
    ∫ x in B0579.cell c, ‖F x‖ * ‖G x‖ ≤
      (xNorm c m F).toReal * (xNorm c (-m) G).toReal := by
  have hF' : MemLp (fun x => ‖F x‖) 2 (B0579.cellMeasure c m) := hF.norm
  have hG' : MemLp (fun x => ‖G x‖) 2 (B0579.cellMeasure c (-m)) := hG.norm
  have h := B0579.abs_integral_mul_le c m (hF'.toLp (fun x => ‖F x‖)) (hG'.toLp (fun x => ‖G x‖))
  have h1 : ∀ᵐ x ∂(B0579.cellMeasure c m), (hF'.toLp (fun x => ‖F x‖)) x = ‖F x‖ :=
    hF'.coeFn_toLp
  have h2 : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), (hG'.toLp (fun x => ‖G x‖)) x = ‖G x‖ :=
    hG'.coeFn_toLp
  have h1' := (B0579.ac_cellMeasure c m).ae_le h1
  have h2' := ((B0579.ac_cellMeasure c m).trans (B0579.cellMeasure_ac_cellMeasure c m (-m)) |>.ae_le
    h2)
  have e : ∫ x in B0579.cell c, (hF'.toLp (fun x => ‖F x‖)) x * (hG'.toLp (fun x => ‖G x‖)) x =
      ∫ x in B0579.cell c, ‖F x‖ * ‖G x‖ := by
    refine integral_congr_ae ?_
    filter_upwards [h1', h2'] with x hx1 hx2
    simp only [hx1, hx2]
  have nf : ‖hF'.toLp (fun x => ‖F x‖)‖ = (xNorm c m F).toReal := by
    rw [Lp.norm_toLp, xNorm, eLpNorm_norm]
  have ng : ‖hG'.toLp (fun x => ‖G x‖)‖ = (xNorm c (-m) G).toReal := by
    rw [Lp.norm_toLp, xNorm, eLpNorm_norm]
  rw [e, nf, ng] at h
  exact (le_abs_self _).trans h

/-- Cauchy-Schwarz with a cutoff `|h| ≤ 1`. -/
lemma cs_cut (c m : ℝ) {F G : ℝ × ℝ → ℂ} {h : ℝ × ℝ → ℝ} (hh : Continuous h)
    (h1 : ∀ x, |h x| ≤ 1) (hF : MemLp F 2 (B0579.cellMeasure c m))
    (hG : MemLp G 2 (B0579.cellMeasure c (-m))) :
    ‖∫ x in B0579.cell c, F x * ((h x : ℂ) * G x)‖ ≤
      (xNorm c m F).toReal * (xNorm c (-m) G).toReal := by
  have hhG : MemLp (fun x => (h x : ℂ) * G x) 2 (B0579.cellMeasure c (-m)) := by
    refine hG.mono ((Complex.continuous_ofReal.comp hh).aestronglyMeasurable.mul hG.1) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 x)
  have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hF hhG
  have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hF hG
  refine (norm_integral_le_integral_norm _).trans ((integral_mono (by simp only [norm_mul] at i1 ⊢; exact i1) i2 ?_).trans (cs_norm c m hF hG))
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := h1 x
  have h0 := norm_nonneg (F x)
  have h2 := norm_nonneg (G x)
  nlinarith [abs_nonneg (h x), mul_nonneg h0 h2]

lemma ofReal_toReal_le {a : ℝ≥0∞} (ha : a ≠ ⊤) {A : ℝ} (hA : 0 ≤ A) (h : a.toReal ≤ A) :
    a ≤ ENNReal.ofReal A := (ENNReal.le_ofReal_iff_toReal_le ha hA).2 h

/-- Continuity of the (real) norm of a strongly continuous family. -/
lemma contOn_norm {c m : ℝ} {S : Set ℝ} (f : ℝ → ℝ × ℝ → ℂ)
    (hmem : ∀ r ∈ S, MemLp (f r) 2 (B0579.cellMeasure c m))
    (hs : ∀ r ∈ S, Tendsto (fun r' => xNorm c m (f r' - f r)) (𝓝[S] r) (𝓝 0)) :
    ContinuousOn (fun r => (xNorm c m (f r)).toReal) S := by
  intro r hr
  have hfin : ∀ r' ∈ S, xNorm c m (f r') ≠ ⊤ := fun r' h => (hmem r' h).eLpNorm_ne_top
  have hd : ∀ r' ∈ S, xNorm c m (f r' - f r) ≠ ⊤ := fun r' h =>
    ((hmem r' h).sub (hmem r hr)).eLpNorm_ne_top
  have ht : Tendsto (fun r' => (xNorm c m (f r' - f r)).toReal) (𝓝[S] r) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hs r hr)
    rw [ENNReal.toReal_zero] at this
    exact this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ ht)
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have e1 : xNorm c m (f r') ≤ xNorm c m (f r' - f r) + xNorm c m (f r) := by
    have := eLpNorm_add_le (p := 2) (μ := B0579.cellMeasure c m)
      ((hmem r' hr').1.sub (hmem r hr).1) (hmem r hr).1 one_le_two
    rw [sub_add_cancel] at this
    exact this
  have e2 : xNorm c m (f r) ≤ xNorm c m (f r' - f r) + xNorm c m (f r') := by
    have := eLpNorm_add_le (p := 2) (μ := B0579.cellMeasure c m)
      ((hmem r hr).1.sub (hmem r' hr').1) (hmem r' hr').1 one_le_two
    rw [sub_add_cancel] at this
    have h3 : eLpNorm (f r - f r') 2 (B0579.cellMeasure c m) =
        eLpNorm (f r' - f r) 2 (B0579.cellMeasure c m) := eLpNorm_sub_comm _ _ _ _
    rw [h3] at this
    exact this
  have t1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hd r' hr', hfin r hr⟩) e1
  have t2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hd r' hr', hfin r' hr'⟩) e2
  rw [ENNReal.toReal_add (hd r' hr') (hfin r hr)] at t1
  rw [ENNReal.toReal_add (hd r' hr') (hfin r' hr')] at t2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

lemma bdd_of_cont {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ ∈ Icc a b, g ρ ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨|C|, abs_nonneg _, fun ρ hρ => (le_abs_self _).trans ((hC ρ hρ).trans (le_abs_self C))⟩

/-- The commutator bound `‖ladComm R ρ‖ ≤ K'/R ∫ |w|(|φ| + |∂₀φ| + |∂₁φ|)` for `R ≥ 1`. -/
lemma comm_bound {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (w φ : ℝ → ℝ × ℝ → ℂ)
    (ρ K C : ℝ) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (hp : ∀ R : ℝ, 0 < R → ∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ K / R)
    (hl : ∀ R : ℝ, 0 < R → ∀ x : ℝ × ℝ, |lapP (ladCut R) x| ≤ K / R ^ 2)
    (hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C)
    (hI : IntegrableOn (fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (B0579.cell c)) :
    ∀ R : ℝ, 1 ≤ R → ‖ladComm tr w φ R ρ‖ ≤ (3 * |ν| * K + 2 * C * K) * R⁻¹ *
      ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
  intro R hR1
  have hR0 : 0 < R := by linarith
  have hq : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖w ρ x * ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
        (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
        ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
        φ ρ x)‖ ≤ (3 * |ν| * K + 2 * C * K) * R⁻¹ *
        (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
    rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
    refine Eventually.of_forall fun x hx => ?_
    have hv := hv x hx
    have hp0 : |B0579.pd 0 (ladCut R) x| ≤ K * R⁻¹ := by
      have := hp R hR0 x 0
      rwa [div_eq_mul_inv] at this
    have hp1 : |B0579.pd 1 (ladCut R) x| ≤ K * R⁻¹ := by
      have := hp R hR0 x 1
      rwa [div_eq_mul_inv] at this
    have hL : |lapP (ladCut R) x| ≤ K * R⁻¹ := by
      have h := hl R hR0 x
      have e : K / R ^ 2 = K * R⁻¹ * R⁻¹ := by ring
      rw [e] at h
      exact h.trans (mul_le_of_le_one_right (mul_nonneg hK0 hq) hq1)
    have hvv : |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| ≤
        2 * C * K * R⁻¹ := by
      calc |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x|
          ≤ |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x| + |tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| :=
            abs_add_le _ _
        _ = |tr.v ρ x 0| * |B0579.pd 0 (ladCut R) x| + |tr.v ρ x 1| * |B0579.pd 1 (ladCut R) x| := by
            rw [abs_mul, abs_mul]
        _ ≤ C * (K * R⁻¹) + C * (K * R⁻¹) :=
            add_le_add (mul_le_mul (hv 0) hp0 (abs_nonneg _) hC0)
              (mul_le_mul (hv 1) hp1 (abs_nonneg _) hC0)
        _ = 2 * C * K * R⁻¹ := by ring
    have hZ := CommVanishAux.comm_pointwise ν C K R _ _ _ _ hK0 hC0 hq hp0 hp1 hL hvv
      (pdCx 0 (φ ρ) x) (pdCx 1 (φ ρ) x) (φ ρ x)
    rw [norm_mul]
    calc ‖w ρ x‖ * ‖(ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
          ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
          φ ρ x‖
        ≤ ‖w ρ x‖ * ((3 * |ν| * K + 2 * C * K) * R⁻¹ *
            (‖φ ρ x‖ + ‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖)) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ = (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
          ring
  unfold ladComm
  calc ‖∫ x in B0579.cell c, w ρ x * ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) *
          pdCx 0 (φ ρ) x + (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) +
          (lapP (ladCut R) x : ℂ) * φ ρ x) +
          ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
          φ ρ x)‖
      ≤ ∫ x in B0579.cell c, (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) :=
        norm_integral_le_of_norm_le (hI.const_mul _) hpt
    _ = _ := integral_const_mul _ _

end RateBoundAux

open RateBoundAux in
/-- **A dominating function for the rate** (SP 3074-3075; `LadRateBound m`). -/
theorem ladRateBound (m : ℝ) (hm : 8 < m) : LadRateBound m := by
  intro ν c tr t s g φ f w u hν hc ht hts hB hφ hf hf0 hw r hr
  have hc0 : 0 < c := by linarith
  have ht0 : 0 ≤ t := ht
  have hrs : r < s := hr.2
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  obtain ⟨C0, hC0b⟩ := hB s (ht.trans hts.le)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans ((hC0b t ⟨ht0, hts.le⟩ _ hx0).1 0)
  -- bounds of `w` and `φ`
  have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t) :=
    contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
  obtain ⟨A, hA0, hA⟩ := bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t r ⊆ Ici t))
  have hφc : ContinuousOn (fun ρ => (xNorm c (-m) (φ ρ)).toReal) (Icc t s) :=
    contOn_norm φ (fun ρ h => hφ.memX ρ h) (fun ρ h => hφ.strongCont ρ h)
  obtain ⟨Bφ, hB0, hBφ⟩ := bdd_of_cont hφc
  obtain ⟨M, hM⟩ := ladChiBound m hm ν c tr t s g φ hν hc ht hts hB hφ
  -- the velocity
  obtain ⟨Cl, hCl⟩ := ladVelLip m hm ν c tr t f w u hc hf0 hw
  have hu2 : ∀ ρ, t ≤ ρ → ∀ j : Fin 2,
      MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) :=
    fun ρ h j => (hw.biotSavart ρ h).1 j
  have hAe : ∀ ρ ∈ Icc t r, xNorm c m (w ρ) ≤ ENNReal.ofReal A := fun ρ hρ =>
    ofReal_toReal_le (hw.memX ρ hρ.1).eLpNorm_ne_top hA0 (hA ρ hρ)
  have hU : ∀ ρ ∈ Icc t r, ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
          eLpNorm (fun x => u t x j) 2 (volume.restrict (B0579.cell c)) := by
    intro ρ hρ j
    have h1 := eLpNorm_add_le (p := 2) (μ := volume.restrict (B0579.cell c))
      ((hu2 ρ hρ.1 j).1.sub (hu2 t le_rfl j).1) (hu2 t le_rfl j).1 one_le_two
    rw [sub_add_cancel] at h1
    have h2 : eLpNorm ((fun x => u ρ x j) - fun x => u t x j) 2
        (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal Cl * xNorm c m (w ρ - w t) :=
      hCl ρ t hρ.1 le_rfl j
    have h3 : xNorm c m (w ρ - w t) ≤ xNorm c m (w ρ) + xNorm c m (w t) :=
      eLpNorm_sub_le (hw.memX ρ hρ.1).1 (hw.memX t le_rfl).1 one_le_two
    have h4 : xNorm c m (w ρ - w t) ≤ ENNReal.ofReal A + ENNReal.ofReal A :=
      h3.trans (add_le_add (hAe ρ hρ) (hAe t ⟨le_rfl, hr.1⟩))
    exact h1.trans (add_le_add (h2.trans (mul_le_mul' le_rfl h4)) le_rfl)
  set Fe : ℝ≥0∞ := ENNReal.ofReal C0 *
    ((ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
        eLpNorm (fun x => u t x 0) 2 (volume.restrict (B0579.cell c))) +
      (ENNReal.ofReal Cl * (ENNReal.ofReal A + ENNReal.ofReal A) +
        eLpNorm (fun x => u t x 1) 2 (volume.restrict (B0579.cell c)))) with hFedef
  have hFe : Fe ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
        (hu2 t le_rfl _).eLpNorm_ne_top⟩
  have hforce : ∀ ρ ∈ Icc t r, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr s C0 ρ hC0b ⟨ht0.trans hρ.1, hρ.2.trans hrs.le⟩ (u ρ)
      (fun j => hu2 ρ hρ.1 j)
    exact ⟨h1, ENNReal.toReal_mono hFe
      (h2.trans (mul_le_mul' le_rfl (add_le_add (hU ρ hρ 0) (hU ρ hρ 1))))⟩
  have hFe0 : 0 ≤ Fe.toReal := ENNReal.toReal_nonneg
  have hK2 : 0 ≤ 3 * |ν| * K + 2 * C0 * K := by positivity
  have h0 := ladAdjGradInt m hm ν c tr t s g φ hν hc ht hts hB hφ r hr 0
  have h1 := ladAdjGradInt m hm ν c tr t s g φ hν hc ht hts hB hφ r hr 1
  refine ⟨fun ρ => (A * |M| + Fe.toReal * Bφ + (3 * |ν| * K + 2 * C0 * K) * (A * Bφ)) +
    (3 * |ν| * K + 2 * C0 * K) * A *
      ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal), ?_, ?_⟩
  · exact intervalIntegrable_const.add ((h0.add h1).const_mul _)
  · intro R hR ρ hρ
    have hρs : ρ ∈ Ioo t s := ⟨hρ.1, hρ.2.trans hrs⟩
    have hρI : ρ ∈ Icc t r := ⟨hρ.1.le, hρ.2.le⟩
    have hρS : ρ ∈ Icc t s := ⟨hρ.1.le, (hρ.2.trans hrs).le⟩
    have hρK : ρ ∈ Ico t s := ⟨hρ.1.le, hρ.2.trans hrs⟩
    have hR0 : 0 < R := by linarith
    have hq : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
    have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    beta_reduce
    rw [ladRateSplit ν c m tr t s f w u φ hc0 ht0 hts hw hφ.jointSmooth R hR0 ρ hρs]
    obtain ⟨hχm, hχn⟩ := hM ρ hρs
    have hχ' : (xNorm c (-m) (ladChi tr φ ρ)).toReal ≤ |M| :=
      ENNReal.toReal_le_of_le_ofReal (abs_nonneg M)
        (hχn.trans (ENNReal.ofReal_le_ofReal (le_abs_self M)))
    have hcut := hK R hR0
    have hcont : Continuous (ladCut R) := (hcut.1 c).continuous
    have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
      rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
    have hwm := hw.memX ρ hρ.1.le
    have hφm := hφ.memX ρ hρS
    -- (a)
    have ea : ‖∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)‖ ≤ A * |M| :=
      (cs_cut c m hcont hcb hwm hχm).trans
        (mul_le_mul (hA ρ hρI) hχ' ENNReal.toReal_nonneg hA0)
    -- (b)
    have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤
        Fe.toReal * Bφ :=
      (cs_cut c m hcont hcb (hforce ρ hρI).1 hφm).trans
        (mul_le_mul (hforce ρ hρI).2 (hBφ ρ hρS) ENNReal.toReal_nonneg hFe0)
    -- (c)
    have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C0 := fun x hx j =>
      (hC0b ρ ⟨ht0.trans hρ.1.le, (hρ.2.trans hrs).le⟩ x hx).1 j
    have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hwm hφm
    have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 0)
    have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 1)
    have hI := (i1.add i2).add i3
    have ec := comm_bound tr w φ ρ K C0 hK0 hC00
      (fun R hR x j => (hK R hR).2.2.2.2.1 x j) (fun R hR x => (hK R hR).2.2.2.2.2 x) hv hI R hR
    have hint : ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) =
        (∫ x in B0579.cell c, ‖w ρ x‖ * ‖φ ρ x‖) +
          (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖) +
          ∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖ := by
      rw [integral_add (f := fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖)
        (g := fun x => ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (i1.add i2) i3,
        integral_add i1 i2]
    have c1 := (cs_norm c m hwm hφm).trans
      (mul_le_mul (hA ρ hρI) (hBφ ρ hρS) ENNReal.toReal_nonneg hA0)
    have c2 := (cs_norm c m hwm (hφ.memH1 ρ hρK 0)).trans
      (mul_le_mul_of_nonneg_right (hA ρ hρI) ENNReal.toReal_nonneg)
    have c3 := (cs_norm c m hwm (hφ.memH1 ρ hρK 1)).trans
      (mul_le_mul_of_nonneg_right (hA ρ hρI) ENNReal.toReal_nonneg)
    have hIle : (∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖)) ≤ A * Bφ +
        A * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
          (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) := by
      rw [hint, mul_add]
      have c2' : (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖) ≤
          A * (eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal := c2
      have c3' : (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) ≤
          A * (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal := c3
      linarith
    have hI0 : 0 ≤ ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := integral_nonneg fun x => by positivity
    have ec' : ‖ladComm tr w φ R ρ‖ ≤ (3 * |ν| * K + 2 * C0 * K) *
        (A * Bφ + A * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
          (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal)) := by
      refine ec.trans ?_
      calc _ ≤ (3 * |ν| * K + 2 * C0 * K) * 1 * _ := by gcongr
        _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hIle hK2
    have hsub := norm_add_le ((∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
      ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) (ladComm tr w φ R ρ)
    have hsub2 := norm_sub_le (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x))
      (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
    nlinarith [hsub, hsub2, ea, eb, ec']

end UnforcedLeray.Short.IIIa
