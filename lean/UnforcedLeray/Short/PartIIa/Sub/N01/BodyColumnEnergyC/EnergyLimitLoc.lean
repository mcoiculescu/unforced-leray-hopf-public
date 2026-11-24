import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4

/-!
# `PartII-a:N01/9/1/4/3`: `energyLimitLoc`

Source `the November 2 reference manuscript`
lines 3426-3430. On `[s₁,s₂] × cell` the density `c⁻¹ s^a` (`a ≤ 0`) of `ageμ c a` is bounded below
by `c⁻¹ s₂^a > 0`, so the strip integral is controlled by the `ageμ` integral; combined with
`|x|² ≤ 2|x - y|² + 2|y|²` and the local finiteness of `(b_k, G_k)` this gives local finiteness
of the limit (the limit fields are measurable, so the `lintegral` is subadditive).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.EnergyLimitLocAux

open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.IIIa (tnorm2 vnorm2)

lemma cell_eq_qCell (c : ℝ) : B0579.cell c = qCell c := by
  unfold B0579.cell qCell
  rw [neg_div]

lemma vnorm2_sq' (u : Fin 2 → ℂ) : vnorm2 u ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Fin.sum_univ_two]

lemma tnorm2_sq' (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ‖T 0 0‖ ^ 2 + ‖T 0 1‖ ^ 2 + (‖T 1 0‖ ^ 2 + ‖T 1 1‖ ^ 2) := by
  unfold tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Fin.sum_univ_two]

lemma sq_tri (x y : ℂ) : ‖x‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖y - x‖ + ‖y‖ := by
    calc ‖x‖ = ‖y - (y - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  nlinarith [norm_nonneg (y - x), norm_nonneg y, norm_nonneg x, sq_nonneg (‖y - x‖ - ‖y‖)]

lemma vnorm2_tri (u v : Fin 2 → ℂ) :
    vnorm2 u ^ 2 ≤ 2 * vnorm2 (fun i => v i - u i) ^ 2 + 2 * vnorm2 v ^ 2 := by
  rw [vnorm2_sq', vnorm2_sq', vnorm2_sq']
  have h0 := sq_tri (u 0) (v 0)
  have h1 := sq_tri (u 1) (v 1)
  linarith

lemma tnorm2_tri (u v : Fin 2 → Fin 2 → ℂ) :
    tnorm2 u ^ 2 ≤ 2 * tnorm2 (fun i j => v i j - u i j) ^ 2 + 2 * tnorm2 v ^ 2 := by
  rw [tnorm2_sq', tnorm2_sq', tnorm2_sq']
  have h00 := sq_tri (u 0 0) (v 0 0)
  have h01 := sq_tri (u 0 1) (v 0 1)
  have h10 := sq_tri (u 1 0) (v 1 0)
  have h11 := sq_tri (u 1 1) (v 1 1)
  linarith

lemma measurable_vnorm2 {α : Type*} [MeasurableSpace α] (f : α → Fin 2 → ℂ)
    (hf : ∀ i, Measurable fun p => f p i) : Measurable fun p => vnorm2 (f p) := by
  unfold vnorm2
  exact (Finset.measurable_sum _ fun i _ => ((hf i).norm.pow_const 2)).sqrt

lemma measurable_tnorm2 {α : Type*} [MeasurableSpace α] (f : α → Fin 2 → Fin 2 → ℂ)
    (hf : ∀ i j, Measurable fun p => f p i j) : Measurable fun p => tnorm2 (f p) := by
  unfold tnorm2
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((hf i j).norm.pow_const 2)).sqrt

/-- The strip integral is finite when the `ageμ c a` integral is (`a ≤ 0`). -/
lemma strip_fin (c a : ℝ) (ha : a ≤ 0) (hc : 0 < c) (s₁ s₂ : ℝ) (hs₁ : 0 < s₁) (hs : s₁ < s₂)
    (E : Chart → ℝ≥0∞) (hE : Measurable E) (hfin : ∫⁻ p, E p ∂(ageμ c a) < ⊤) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, E p < ⊤ := by
  set m : ℝ := c⁻¹ * s₂ ^ a with hm
  have hm0 : 0 < m := mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos (hs₁.trans hs) a)
  rw [lintegral_ageμ hc a hE] at hfin
  have hsub : Icc s₁ s₂ ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ qCell c := by
    rw [cell_eq_qCell]
    exact prod_mono (fun s hs' => lt_of_lt_of_le hs₁ hs'.1) le_rfl
  have hmeasS : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) := by
    rw [cell_eq_qCell]
    exact measurableSet_Icc.prod (by unfold qCell; exact measurableSet_Ico.prod MeasurableSet.univ)
  have h1 : ENNReal.ofReal m * ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, E p ≤
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * E p := by
    rw [← lintegral_const_mul _ hE]
    calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal m * E p
        ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * E p := by
          refine setLIntegral_mono' hmeasS fun p hp => ?_
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hp1 : s₁ ≤ p.1 := hp.1.1
          have hp2 : p.1 ≤ s₂ := hp.1.2
          have : s₂ ^ a ≤ p.1 ^ a :=
            Real.rpow_le_rpow_of_nonpos (hs₁.trans_le hp1) hp2 ha
          exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hc.le)
      _ ≤ _ := lintegral_mono_set hsub
  have h2 : ENNReal.ofReal m * ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, E p < ⊤ :=
    lt_of_le_of_lt h1 hfin
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top (by simpa using hm0)] at h2
  exact lt_irrefl _ h2

/-- Generic local finiteness from `f² ≤ 2d² + 2f_k²`. -/
lemma part_fin (c a : ℝ) (ha : a ≤ 0) (hc : 0 < c) (s₁ s₂ : ℝ) (hs₁ : 0 < s₁) (hs : s₁ < s₂)
    (f fk d : Chart → ℝ) (hf : Measurable f) (hfk : Measurable fk) (hd : Measurable d)
    (hle : ∀ p, f p ^ 2 ≤ 2 * d p ^ 2 + 2 * fk p ^ 2)
    (hdfin : ∫⁻ p, ENNReal.ofReal (d p ^ 2) ∂(ageμ c a) < ⊤)
    (hkfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (fk p ^ 2) < ⊤) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (f p ^ 2) < ⊤ := by
  have hD : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (d p ^ 2) < ⊤ :=
    strip_fin c a ha hc s₁ s₂ hs₁ hs _
      (ENNReal.measurable_ofReal.comp (hd.pow_const 2)) hdfin
  have hpt : ∀ p, ENNReal.ofReal (f p ^ 2) ≤
      2 * ENNReal.ofReal (fk p ^ 2) + 2 * ENNReal.ofReal (d p ^ 2) := by
    intro p
    calc ENNReal.ofReal (f p ^ 2) ≤ ENNReal.ofReal (2 * fk p ^ 2 + 2 * d p ^ 2) :=
          ENNReal.ofReal_le_ofReal (by linarith [hle p])
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp
  calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (f p ^ 2)
      ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          (2 * ENNReal.ofReal (fk p ^ 2) + 2 * ENNReal.ofReal (d p ^ 2)) := lintegral_mono hpt
    _ = 2 * (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (fk p ^ 2)) +
          2 * (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (d p ^ 2)) := by
        have hfm : Measurable fun p => 2 * ENNReal.ofReal (fk p ^ 2) :=
          (ENNReal.measurable_ofReal.comp (hfk.pow_const 2)).const_mul 2
        have hfkm : Measurable fun p => ENNReal.ofReal (fk p ^ 2) :=
          ENNReal.measurable_ofReal.comp (hfk.pow_const 2)
        have hdm : Measurable fun p => ENNReal.ofReal (d p ^ 2) :=
          ENNReal.measurable_ofReal.comp (hd.pow_const 2)
        rw [lintegral_add_left hfm, lintegral_const_mul (2 : ℝ≥0∞) hfkm,
          lintegral_const_mul (2 : ℝ≥0∞) hdm]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.ofNat_lt_top (n := 2)) hkfin,
          ENNReal.mul_lt_top (ENNReal.ofNat_lt_top (n := 2)) hD⟩

end UnforcedLeray.Short.PartIIa.N01.EnergyLimitLocAux

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.IIIa (tnorm2 vnorm2)
open EnergyLimitLocAux

theorem energyLimitLoc : EnergyLimitLoc := by
  intro c hc bk Gk b G hE hL hbm hGm s₁ s₂ hs₁ hs
  obtain ⟨h1, h2⟩ := hL
  have e1 := h1.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))
  have e2 := h2.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))
  obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
  have hbkm := (hE k).measurable
  have hGkm := (hE k).gradMeasurable
  have hloc := (hE k).energyLoc s₁ s₂ hs₁ hs
  have hvm : Measurable fun p => vnorm2 (b p) := measurable_vnorm2 _ hbm
  have htm : Measurable fun p => tnorm2 (G p) := measurable_tnorm2 _ hGm
  have hvkm : Measurable fun p => vnorm2 (bk k p) := measurable_vnorm2 _ hbkm
  have htkm : Measurable fun p => tnorm2 (Gk k p) := measurable_tnorm2 _ hGkm
  have hvd : Measurable fun p => vnorm2 (fun i => bk k p i - b p i) :=
    measurable_vnorm2 (fun p i => bk k p i - b p i) fun i => (hbkm i).sub (hbm i)
  have htd : Measurable fun p => tnorm2 (fun i j => Gk k p i j - G p i j) :=
    measurable_tnorm2 (fun p i j => Gk k p i j - G p i j) fun i j => (hGkm i j).sub (hGm i j)
  have hv_k : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (bk k p) ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) hloc
    nlinarith [sq_nonneg (tnorm2 (Gk k p))]
  have ht_k : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (Gk k p) ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) hloc
    nlinarith [sq_nonneg (vnorm2 (bk k p))]
  have hv := part_fin c (-3 / 2) (by norm_num) hc s₁ s₂ hs₁ hs _ _ _ hvm hvkm hvd
    (fun p => vnorm2_tri (b p) (bk k p)) (lt_trans hk1 ENNReal.one_lt_top) hv_k
  have ht := part_fin c (-1 / 2) (by norm_num) hc s₁ s₂ hs₁ hs _ _ _ htm htkm htd
    (fun p => tnorm2_tri (G p) (Gk k p)) (lt_trans hk2 ENNReal.one_lt_top) ht_k
  have hsplit : ∀ p, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) =
      ENNReal.ofReal (vnorm2 (b p) ^ 2) + ENNReal.ofReal (tnorm2 (G p) ^ 2) := fun p =>
    ENNReal.ofReal_add (by positivity) (by positivity)
  simp_rw [hsplit]
  have hvm' : Measurable fun p => ENNReal.ofReal (vnorm2 (b p) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hvm.pow_const 2)
  rw [lintegral_add_left hvm']
  exact ENNReal.add_lt_top.2 ⟨hv, ht⟩

end UnforcedLeray.Short.PartIIa.N01
