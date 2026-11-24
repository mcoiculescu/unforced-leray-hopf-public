import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1Deriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutRateBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1TimeCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutSliceProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi

/-!
# `PartIII-a:T21/2/7/2/2/2`: `AdjointH1Gronwall` (`E_1(r) < ∞`)

Source: `the November 2 reference manuscript` (SP) lines 3068-3073.
No time weight is needed: the lower bound of `CutRateBound` integrated on `[r, r']`, with `r' > r`
a good age (`∫⁻‖∂_kφ(r')‖² < ⊤`, which exists because the time integral is finite), bounds
`E_R(r)` uniformly in `R`; monotone convergence `R → ∞` gives `∫⁻‖∂_kφ(r)‖² < ⊤`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace H1GronAux

/-- The slice gradient `∫⁻` of the weighted measure. -/
def gk (c m : ℝ) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) : ℝ≥0∞ :=
  ∫⁻ x, ‖pdCx k Φ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m))

lemma enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

lemma lint_cell (c m : ℝ) (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(B0579.cellMeasure c (-m)) =
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-m)) * f x := by
  unfold B0579.cellMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (B0579.measurable_density (-m)).coe_nnreal_ennreal
    (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  rfl

lemma memLp_of_lt_top {c m : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (h : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) < ⊤) :
    MemLp g 2 (B0579.cellMeasure c (-m)) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

lemma lt_top_of_memLp {c m : ℝ} {g : ℝ × ℝ → ℂ} (h : MemLp g 2 (B0579.cellMeasure c (-m))) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) < ⊤ := by
  have h2 := h.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h2
  simp only [ENNReal.toReal_ofNat] at h2
  by_contra hcon
  have : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) = ⊤ := not_lt_top_iff.1 hcon
  rw [this] at h2
  simp at h2

lemma gradE_eq_toReal {c m : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    gradE c m Φ = ∑ k : Fin 2, (gk c m Φ k).toReal := by
  unfold gradE gk
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
    (((CutSliceAux.contDiff_pdCx hΦ k).continuous.norm.pow 2).aestronglyMeasurable)]
  simp_rw [enorm_sq_eq]

lemma cutE1_le_gk {c m R : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hR : 0 < R)
    (h : ∀ k, gk c m Φ k < ⊤) :
    cutE1 c m R Φ ≤ ∑ k : Fin 2, (gk c m Φ k).toReal := by
  rw [← gradE_eq_toReal hΦ]
  exact CutSliceAux.cutE1_le_gradE hΦ
    (fun k => memLp_of_lt_top (CutSliceAux.contDiff_pdCx hΦ k).continuous (h k)) hR

/-- Monotone convergence `R → ∞`: a uniform bound of the cut energies gives finite `gk`. -/
lemma gk_lt_top_of_bdd {c m B : ℝ} {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (h : ∀ n : ℕ, cutE1 c m ((n : ℝ) + 1) Φ ≤ B) (k : Fin 2) : gk c m Φ k < ⊤ := by
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hnn : ∀ (n : ℕ) (x : ℝ × ℝ), 0 ≤ ladCut ((n : ℝ) + 1) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2) := fun n x =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
  have hterm : ∀ n : ℕ, ∫ x in B0579.cell c, ladCut ((n : ℝ) + 1) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2) ≤ B := by
    intro n
    refine le_trans ?_ (h n)
    unfold cutE1
    exact Finset.single_le_sum (f := fun j : Fin 2 => ∫ x in B0579.cell c,
      ladCut ((n : ℝ) + 1) x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx j Φ x‖ ^ 2))
      (fun j _ => setIntegral_nonneg (B0579.measurableSet_cell c) fun x _ => by
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)))
      (Finset.mem_univ k)
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal (ladCut ((n : ℝ) + 1) x ^ 2) *
    (ENNReal.ofReal (B0579.jb x ^ (-m)) * ‖pdCx k Φ x‖ₑ ^ (2 : ℝ))
  have hFe : ∀ (n : ℕ) (x : ℝ × ℝ), F n x = ENNReal.ofReal (ladCut ((n : ℝ) + 1) x ^ 2 *
      (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)) := by
    intro n x
    simp only [F]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg
      (B0579.jb_pos x).le _), enorm_sq_eq]
  have hFle : ∀ n : ℕ, ∫⁻ x in B0579.cell c, F n x ≤ ENNReal.ofReal B := by
    intro n
    simp_rw [hFe]
    rw [← ofReal_integral_eq_lintegral_ofReal (CutSliceAux.integrableOn_cutE1 (hn1 n) hΦ k)
      (ae_of_all _ (hnn n))]
    exact ENNReal.ofReal_le_ofReal (hterm n)
  have hmono : Monotone F := by
    intro n n' hnn' x
    have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (CutSliceAux.ladCut_nonneg _ _)
      (CutSliceAux.ladCut_le_ladCut (hn1 n) (by linarith) x) 2)) le_rfl
  have hmeas : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp ((CutSliceAux.ladCut_continuous _).pow 2).measurable).mul
      ((ENNReal.measurable_ofReal.comp (B0579.continuous_jb_rpow (-m)).measurable).mul
        ((CutSliceAux.contDiff_pdCx hΦ k).continuous.enorm.measurable.pow_const _))
  have hsup : ∀ x, ⨆ n, F n x =
      ENNReal.ofReal (B0579.jb x ^ (-m)) * ‖pdCx k Φ x‖ₑ ^ (2 : ℝ) := by
    intro x
    apply le_antisymm
    · refine iSup_le fun n => ?_
      exact mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2
        (pow_le_one₀ (CutSliceAux.ladCut_nonneg _ _) (CutSliceAux.ladCut_le_one _ _)))
    · obtain ⟨N, hN⟩ := exists_nat_ge |x.2|
      refine le_iSup_of_le N ?_
      have hle : |x.2| ≤ (N : ℝ) + 1 := by linarith
      have hsq : x.2 ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hle 2
      simp [F, CutSliceAux.ladCut_eq_one_of (R := (N : ℝ) + 1) (hn1 N) hsq]
  have hlt : gk c m Φ k ≤ ENNReal.ofReal B := by
    unfold gk
    rw [lint_cell]
    simp_rw [← hsup]
    rw [lintegral_iSup hmeas hmono]
    exact iSup_le hFle
  exact lt_of_le_of_lt hlt ENNReal.ofReal_lt_top

/-- Measurability in the age of the slice energies, on a sub-interval of the strip. -/
lemma aemeasurable_gk {c m r s t : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hrt : t ≤ r) (k : Fin 2) :
    AEMeasurable (fun ρ => gk c m (φ ρ) k) (volume.restrict (Ioo r s)) := by
  have hsub : Ioo r s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s ×ˢ univ := fun p hp =>
    ⟨⟨hrt.trans hp.1.1.le, hp.1.2⟩, hp.2⟩
  have hc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ‖pdCx k (φ p.1) p.2‖ₑ ^ (2 : ℝ))
      (Ioo r s ×ˢ univ) :=
    (ENNReal.continuous_rpow_const (y := (2 : ℝ))).comp_continuousOn
      ((jointSmooth_pdCx hj k).continuousOn.mono hsub).enorm
  have hm : AEMeasurable (fun p : ℝ × (ℝ × ℝ) => ‖pdCx k (φ p.1) p.2‖ₑ ^ (2 : ℝ))
      ((volume.prod (B0579.cellMeasure c (-m))).restrict (Ioo r s ×ˢ univ)) :=
    hc.aemeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have : SFinite (B0579.cellMeasure c (-m)) := by unfold B0579.cellMeasure; infer_instance
  have hprod : (volume.restrict (Ioo r s)).prod (B0579.cellMeasure c (-m)) =
      (volume.prod (B0579.cellMeasure c (-m))).restrict (Ioo r s ×ˢ univ) := by
    have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := B0579.cellMeasure c (-m))
      (Ioo r s) univ
    rwa [Measure.restrict_univ] at this
  rw [← hprod] at hm
  simpa [gk] using hm.lintegral_prod_right'

end H1GronAux

open H1GronAux in
/-- **`AdjointH1Gronwall`** (SP 3068-3073): the energy `E_1(r)` is finite for every `r ∈ [t, s)`. -/
theorem adjointH1Gronwall (m : ℝ) (hm : 8 < m) : AdjointH1Gronwall m := by
  intro ν hν hν1 tr hb t s ht hts G hG φ hφ hj hI r hr k
  have hc0 : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hper := hφ.periodic
  obtain ⟨M, hM⟩ := adjWeakChiBound m hm ν _ tr t s _ φ hc1 ⟨hν, hc0, ht, hts, hb, hφ, hj⟩
  obtain ⟨CV, hCV⟩ := hb s (ht.trans hts.le)
  obtain ⟨K, hK0, hK⟩ := cutRateBound m ν CV M hν
  have hslice : ∀ ρ ∈ Ico t s, ContDiff ℝ ∞ (φ ρ) := fun ρ hρ => adjContDiff_slice hj hρ
  -- the lower bound of the rate
  have hrate : ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t s,
      -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * R) (φ ρ))) ≤
        cutRate (ν ^ (-2 : ℝ)) m R (φ ρ) (ladDt φ ρ) := by
    intro R hR ρ hρ
    have hρ' : ρ ∈ Ico t s := Ioo_subset_Ico_self hρ
    have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨ht.trans hρ.1.le, hρ.2.le⟩
    obtain ⟨h1, _⟩ := hK _ R (φ ρ) (ladChi tr φ ρ) (ladDt φ ρ)
      (fun x j => tr.v ρ x j) hc0 hR (hslice ρ hρ') (continuous_ladChi tr ht hj hρ)
      (continuous_ladDt hj hρ) (fun x hx j => (hCV ρ hρS x hx).1 j)
      (fun x => by
        have e : ladChi tr φ ρ x = ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x +
            ladTransport tr ρ (φ ρ) x := rfl
        rw [e]
        unfold ladTransport
        ring)
      (hM ρ hρ).1 (hM ρ hρ).2
    have hl := CutSliceAux.cutLap_nonneg (ν ^ (-2 : ℝ)) m R (φ ρ)
    nlinarith [mul_nonneg hν.le hl]
  -- a good age `r'`
  have hmeas : ∀ k : Fin 2, AEMeasurable (fun ρ => gk (ν ^ (-2 : ℝ)) m (φ ρ) k)
      (volume.restrict (Ioo r s)) := fun k => aemeasurable_gk hj hr.1 k
  have hIoo : ∀ k : Fin 2, ∫⁻ ρ in Ioo r s, gk (ν ^ (-2 : ℝ)) m (φ ρ) k < ⊤ := fun k =>
    lt_of_le_of_lt (lintegral_mono_set Ioo_subset_Ioc_self) (hI r hr k)
  have hfin : ∀ k : Fin 2, ∀ᵐ ρ ∂(volume.restrict (Ioo r s)), gk (ν ^ (-2 : ℝ)) m (φ ρ) k < ⊤ :=
    fun k => ae_lt_top' (hmeas k) (hIoo k).ne
  have hB' : ∫⁻ ρ in Ioo r s, (gk (ν ^ (-2 : ℝ)) m (φ ρ) 0 + gk (ν ^ (-2 : ℝ)) m (φ ρ) 1) < ⊤ := by
    rw [lintegral_add_left' (hmeas 0)]
    exact ENNReal.add_lt_top.2 ⟨hIoo 0, hIoo 1⟩
  have hex : ∃ r' ∈ Ioo r s, ∀ k : Fin 2, gk (ν ^ (-2 : ℝ)) m (φ r') k < ⊤ := by
    have h1 : ∀ᵐ ρ ∂(volume.restrict (Ioo r s)),
        ρ ∈ Ioo r s ∧ ∀ k : Fin 2, gk (ν ^ (-2 : ℝ)) m (φ ρ) k < ⊤ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hfin 0, hfin 1] with ρ h0 h1 h2
      exact ⟨h0, fun k => by fin_cases k <;> assumption⟩
    have : (ae (volume.restrict (Ioo r s))).NeBot := by
      rw [ae_neBot]
      intro h
      have := Measure.restrict_eq_zero.1 h
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
      linarith [hr.2]
    obtain ⟨ρ, h⟩ := h1.exists
    exact ⟨ρ, h⟩
  obtain ⟨r', hr'I, hr'g⟩ := hex
  have hr'Ico : ∀ ρ ∈ Icc r r', ρ ∈ Ico t s := fun ρ hρ =>
    ⟨hr.1.trans hρ.1, lt_of_le_of_lt hρ.2 hr'I.2⟩
  -- uniform bound of the integral of the cut energies
  have hint : ∀ R : ℝ, 0 < R →
      ∫ y in r..r', cutE1 (ν ^ (-2 : ℝ)) m R (φ y) ≤
        (∫⁻ ρ in Ioo r s, (gk (ν ^ (-2 : ℝ)) m (φ ρ) 0 + gk (ν ^ (-2 : ℝ)) m (φ ρ) 1)).toReal := by
    intro R hR
    have hcont : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m R (φ y)) (Ioo r r') :=
      (cutE1TimeCont _ m R t s φ hc0 hR hj).1.mono
        (fun ρ hρ => hr'Ico ρ ⟨hρ.1.le, hρ.2.le⟩)
    rw [intervalIntegral.integral_of_le hr'I.1.le, integral_Ioc_eq_integral_Ioo,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun y => CutSliceAux.cutE1_nonneg _ m R (φ y))
        (hcont.aestronglyMeasurable measurableSet_Ioo)]
    refine ENNReal.toReal_mono hB'.ne ?_
    calc ∫⁻ y in Ioo r r', ENNReal.ofReal (cutE1 (ν ^ (-2 : ℝ)) m R (φ y))
        ≤ ∫⁻ y in Ioo r r', (gk (ν ^ (-2 : ℝ)) m (φ y) 0 + gk (ν ^ (-2 : ℝ)) m (φ y) 1) := by
          refine lintegral_mono_ae ?_
          have h' := ae_restrict_of_ae_restrict_of_subset
            (Ioo_subset_Ioo_right hr'I.2.le) ((hfin 0).and (hfin 1))
          filter_upwards [h', ae_restrict_mem measurableSet_Ioo] with y hy hyI
          have hle := cutE1_le_gk (hslice y (hr'Ico y ⟨hyI.1.le, hyI.2.le⟩)) hR
            (fun k => by fin_cases k; exacts [hy.1, hy.2])
          rw [Fin.sum_univ_two] at hle
          calc ENNReal.ofReal (cutE1 (ν ^ (-2 : ℝ)) m R (φ y))
              ≤ ENNReal.ofReal ((gk (ν ^ (-2 : ℝ)) m (φ y) 0).toReal +
                (gk (ν ^ (-2 : ℝ)) m (φ y) 1).toReal) := ENNReal.ofReal_le_ofReal hle
            _ = gk (ν ^ (-2 : ℝ)) m (φ y) 0 + gk (ν ^ (-2 : ℝ)) m (φ y) 1 := by
              rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
                ENNReal.ofReal_toReal hy.1.ne, ENNReal.ofReal_toReal hy.2.ne]
      _ ≤ ∫⁻ y in Ioo r s, (gk (ν ^ (-2 : ℝ)) m (φ y) 0 + gk (ν ^ (-2 : ℝ)) m (φ y) 1) :=
          lintegral_mono_set (Ioo_subset_Ioo_right hr'I.2.le)
  -- the uniform bound of `E_R(r)`
  have hbound : ∀ n : ℕ, cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ r) ≤
      ((gk (ν ^ (-2 : ℝ)) m (φ r') 0).toReal + (gk (ν ^ (-2 : ℝ)) m (φ r') 1).toReal) +
        K * ((r' - r) + (∫⁻ ρ in Ioo r s, (gk (ν ^ (-2 : ℝ)) m (φ ρ) 0 +
          gk (ν ^ (-2 : ℝ)) m (φ ρ) 1)).toReal) := by
    intro n
    have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hcont1 : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ y)) (Icc r r') :=
      (cutE1TimeCont _ m _ t s φ hc0 hR0 hj).1.mono hr'Ico
    have hcont2 : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ y))
        (Icc r r') :=
      (cutE1TimeCont _ m _ t s φ hc0 (by positivity) hj).1.mono hr'Ico
    have hineq := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
      (a := r) (b := r') (g := fun ρ => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ ρ))
      (g' := fun ρ => cutRate (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ ρ) (ladDt φ ρ))
      (φ := fun ρ => -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ ρ))))
      hr'I.1.le hcont1
      (fun x hx => (cutE1Deriv _ m _ t s φ hc0 hR0 hj hper x
        ⟨lt_of_le_of_lt hr.1 hx.1, hx.2.trans hr'I.2⟩).hasDerivWithinAt)
      ((continuousOn_const.add hcont2).const_mul K |>.neg |>.integrableOn_Icc)
      (fun x hx => hrate _ hR1 x ⟨lt_of_le_of_lt hr.1 hx.1, hx.2.trans hr'I.2⟩)
    have hEint : IntervalIntegrable
        (fun y => cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ y)) volume r r' :=
      (hcont2.mono (by rw [uIcc_of_le hr'I.1.le])).intervalIntegrable
    have hval : ∫ y in r..r', -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ y))) =
        -(K * ((r' - r) + ∫ y in r..r',
          cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ y))) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const hEint]
      simp
    rw [hval] at hineq
    have hI2 := hint (2 * ((n : ℝ) + 1)) (by positivity)
    have hr'E := cutE1_le_gk (hslice r' ⟨hr'I.1.le.trans' hr.1, hr'I.2⟩) hR0 hr'g
    rw [Fin.sum_univ_two] at hr'E
    nlinarith [mul_le_mul_of_nonneg_left hI2 hK0]
  exact memLp_of_lt_top (CutSliceAux.contDiff_pdCx (hslice r hr) k).continuous
    (gk_lt_top_of_bdd (hslice r hr) hbound k)

end UnforcedLeray.Short.IIIa
