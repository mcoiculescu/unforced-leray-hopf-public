import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_4

/-!
# `outRestrBinTransport` (item `PartIII-b:C/near/delta/8/2/4/4`)

Source of record `the November 2 reference manuscript` 3956-3967 (step (d)) and
2676-2679. The recentring identity `map cellPt μ_H = c • ageμ c (-3/2)` is copied from
`Masked/Proofs/CellPtH.lean` (with renamed helpers, since that file cannot be imported together with
`CellPtHT.lean`). The main proof compares `L²` norms through `eLpNorm_map_measure`, the pointwise bound
`|1_bin(cellPt p) g(cellPt p)| ≤ |χ p| |g'(p)|` a.e., and `eLpNorm_mono_ae`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The recentring of one `q`-coordinate, as in `cellPt`. -/
def ctTx (c q : ℝ) : ℝ := if q < c / 2 then q else q - c

theorem ctTx_measurable (c : ℝ) : Measurable (ctTx c) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id
    (measurable_id.sub_const c)

theorem cellPt_eq_prodMapx (c : ℝ) : cellPt c = Prod.map id (Prod.map (ctTx c) id) := by
  funext p
  obtain ⟨s, q, η⟩ := p
  rfl

/-- The one-dimensional change of variables: `ctTx c` carries `dq` on `(0,c]` to `dq` on `[-c/2,c/2)`
(integral form). -/
theorem ct_lintegralx {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioc (0 : ℝ) c, f (ctTx c q) = ∫⁻ q in Ico (-c / 2) (c / 2), f q := by
  have e0 : volume.restrict (Ioc (0 : ℝ) c) = volume.restrict (Ioo (0 : ℝ) c) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hsplit : Ioo (0 : ℝ) c = Ioo 0 (c / 2) ∪ Ico (c / 2) c :=
    (Ioo_union_Ico_eq_Ioo (show (0 : ℝ) < c / 2 by linarith) (show c / 2 ≤ c by linarith)).symm
  have hdL : Disjoint (Ioo (0 : ℝ) (c / 2)) (Ico (c / 2) c) :=
    Set.disjoint_left.2 fun x hx hx' => not_le.2 hx.2 hx'.1
  have hsplit' : Ico (-c / 2) (c / 2) = Ico (-c / 2) 0 ∪ Ico 0 (c / 2) :=
    (Ico_union_Ico_eq_Ico (show -c / 2 ≤ (0 : ℝ) by linarith) (show (0 : ℝ) ≤ c / 2 by linarith)).symm
  have hdR : Disjoint (Ico (-c / 2) (0 : ℝ)) (Ico (0 : ℝ) (c / 2)) := Set.Ico_disjoint_Ico_same
  have e2 : volume.restrict (Ioo (0 : ℝ) (c / 2)) = volume.restrict (Ico (0 : ℝ) (c / 2)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ico
  have hI : ∫⁻ q in Ico (c / 2) c, f (q - c) = ∫⁻ q in Ico (-c / 2) 0, f q := by
    have key : ∀ q : ℝ, (Ico (c / 2) c).indicator (fun q => f (q - c)) q =
        (Ico (-c / 2) 0).indicator f (q - c) := by
      intro q
      by_cases h : q ∈ Ico (c / 2) c
      · have h' : q - c ∈ Ico (-c / 2) 0 := ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [indicator_of_mem h, indicator_of_mem h']
      · have h' : q - c ∉ Ico (-c / 2) 0 := fun h'' =>
          h ⟨by linarith [h''.1], by linarith [h''.2]⟩
        rw [indicator_of_notMem h, indicator_of_notMem h']
    calc ∫⁻ q in Ico (c / 2) c, f (q - c)
        = ∫⁻ q, (Ico (c / 2) c).indicator (fun q => f (q - c)) q :=
          (lintegral_indicator measurableSet_Ico _).symm
      _ = ∫⁻ q, (Ico (-c / 2) 0).indicator f (q - c) := lintegral_congr key
      _ = ∫⁻ q, (Ico (-c / 2) 0).indicator f q := lintegral_sub_right_eq_self _ c
      _ = ∫⁻ q in Ico (-c / 2) 0, f q := lintegral_indicator measurableSet_Ico _
  have h1 : ∫⁻ q in Ioo (0 : ℝ) (c / 2), f (ctTx c q) = ∫⁻ q in Ioo (0 : ℝ) (c / 2), f q :=
    setLIntegral_congr_fun measurableSet_Ioo fun q hq => by
      rw [ctTx, if_pos hq.2]
  have h2 : ∫⁻ q in Ico (c / 2) c, f (ctTx c q) = ∫⁻ q in Ico (c / 2) c, f (q - c) :=
    setLIntegral_congr_fun measurableSet_Ico fun q hq => by
      rw [ctTx, if_neg (not_lt.2 hq.1)]
  rw [e0, hsplit, lintegral_union measurableSet_Ico hdL, hsplit',
    lintegral_union measurableSet_Ico hdR, h1, h2, hI, e2]
  exact add_comm _ _

/-- The push-forward of `dq|_{(0,c]}` under `ctTx c` is `dq|_{[-c/2,c/2)}`. -/
theorem ct_map_Tx {c : ℝ} (hc : 0 < c) :
    Measure.map (ctTx c) (volume.restrict (Ioc (0 : ℝ) c)) =
      volume.restrict (Ico (-c / 2) (c / 2)) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (ctTx_measurable c)]
  exact ct_lintegralx hc f

/-- The general form: pushing the cell measure with a weight `s^a` in `s` to `c • ageμ c a`. -/
theorem ct_map_cellPtx {c a : ℝ} (hc : 0 < c) :
    Measure.map (cellPt c)
        ((UnforcedLeray.B0220.cellMeasure c).withDensity fun p => ENNReal.ofReal (p.1 ^ a)) =
      ENNReal.ofReal c • ageμ c a := by
  have hcell : (UnforcedLeray.B0220.cellMeasure c).withDensity (fun p => ENNReal.ofReal (p.1 ^ a)) =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod volume) := by
    rw [prod_withDensity_left (measurable_ofReal_rpow a)]
    congr 1
    rw [UnforcedLeray.B0220.cellMeasure, UnforcedLeray.B0220.cell, Measure.volume_eq_prod,
      Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
      Measure.restrict_univ]
  have hq2 : (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) =
      volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) := by
    have h := Measure.prod_restrict (Ico (-c / 2) (c / 2)) (univ : Set ℝ)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
    exact h
  have hmain : Measure.map (cellPt c)
      (((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod volume)) =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [cellPt_eq_prodMapx, ← Measure.map_prod_map _ _ measurable_id
        ((ctTx_measurable c).prodMap measurable_id), Measure.map_id,
      ← Measure.map_prod_map _ _ (ctTx_measurable c) measurable_id, Measure.map_id,
      ct_map_Tx hc, hq2]
  have hR : ENNReal.ofReal c • ageμ c a =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [ageμ, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, UnforcedLeray.Cyl.cell,
      Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_smul]
  rw [hcell, hmain, hR]

/-- **`cellPtHx_eq`** (source 2676-2679): the recentring `cellPt` carries the velocity measure
`s^{-3/2} ds dq dη` on the cell to `c · ageμ c (-3/2)`. -/
theorem cellPtHx_eq (c : ℝ) (hc : 0 < c) : Masked.CellPtH c := by
  show Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
    ENNReal.ofReal c • ageμ c (-3 / 2)
  have ha : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [UnforcedLeray.B0220.measureH, ha]
  exact ct_map_cellPtx hc


/-- `merC` is isometric. -/
theorem norm_merC_aux (b : Merid) : ‖merC b‖ = ‖b‖ := by
  simp [EuclideanSpace.norm_eq, merC, Complex.norm_real]

/-- `merC` is linear. -/
theorem merC_sub_aux (a b : Merid) : merC (a - b) = merC a - merC b := by
  ext i
  simp [merC]

theorem outRestrBinTransport_proof : OutRestrBinTransport := by
  intro c hc l r L χ hm B hB hχ g₁ g₂ g' hG'
  have hcpos : 0 < c := hc
  have hH : Masked.CellPtH c := cellPtHx_eq c hcpos
  have hmap : Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c • ageμ c (-3 / 2) := hH
  have hcm : AEMeasurable (cellPt c) (UnforcedLeray.B0220.measureH c) :=
    (Masked.measurable_cellPt c).aemeasurable
  set g : Hsp c := g₁ - g₂ with hg
  set h : Hsp c := outRestr c (binSet l r L) g with hh
  clear_value h g
  -- the difference `g = g₁ - g₂` pointwise
  have hgae : ∀ᵐ q ∂ageμ c (-3 / 2),
      (g : Chart → Merid) q = ((g₁ : Hsp c) : Chart → Merid) q - ((g₂ : Hsp c) : Chart → Merid) q := by
    rw [hg]
    filter_upwards [Lp.coeFn_sub g₁ g₂] with q hq
    simpa using hq
  have hgcell : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      (g : Chart → Merid) (cellPt c p) =
        ((g₁ : Hsp c) : Chart → Merid) (cellPt c p) - ((g₂ : Hsp c) : Chart → Merid) (cellPt c p) := by
    have hq : ∀ᵐ q ∂(Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)),
        (g : Chart → Merid) q =
          ((g₁ : Hsp c) : Chart → Merid) q - ((g₂ : Hsp c) : Chart → Merid) q := by
      rw [hmap]
      exact Measure.ae_smul_measure hgae _
    exact ae_of_ae_map hcm hq
  -- the restriction `h = 1_bin g`
  have hhae : ∀ᵐ q ∂ageμ c (-3 / 2),
      (h : Chart → Merid) q = ind (binSet l r L) q • (g : Chart → Merid) q := by
    rw [hh]
    exact restrLp_ae (measurableSet_binSet l r L) g
  have hcell : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      (h : Chart → Merid) (cellPt c p) =
        ind (binSet l r L) (cellPt c p) • (g : Chart → Merid) (cellPt c p) := by
    have hq : ∀ᵐ q ∂(Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)),
        (h : Chart → Merid) q = ind (binSet l r L) q • (g : Chart → Merid) q := by
      rw [hmap]
      exact Measure.ae_smul_measure hhae _
    exact ae_of_ae_map (p := fun q => (h : Chart → Merid) q =
        ind (binSet l r L) q • (g : Chart → Merid) q) hcm hq
  -- pointwise domination of the transported restriction by `χ g'`
  have hpt : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      ‖(h : Chart → Merid) (cellPt c p)‖ ≤
        ‖χ p • (g' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p‖ := by
    filter_upwards [hcell, hgcell, hG'] with p h1 h2 h3
    rw [h1, h3, ← merC_sub_aux, ← h2, norm_smul, norm_smul, norm_merC_aux]
    by_cases hp : cellPt c p ∈ binSet l r L
    · have hχp : χ p = 1 := hχ p hp.1 hp.2.1 hp.2.2
      have hind : ind (binSet l r L) (cellPt c p) = 1 := by
        simp [ind, Set.indicator_of_mem hp]
      rw [hind, hχp]
    · have hind : ind (binSet l r L) (cellPt c p) = 0 := by
        simp [ind, Set.indicator_of_notMem hp]
      rw [hind, norm_zero, zero_mul, Real.norm_eq_abs]
      exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
  -- the transport of the restriction along `cellPt`
  have hgm : AEStronglyMeasurable (h : Chart → Merid)
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]
    exact (Lp.aestronglyMeasurable _).smul_measure _
  have e1 : eLpNorm (fun p => (h : Chart → Merid) (cellPt c p)) 2 (UnforcedLeray.B0220.measureH c) =
      eLpNorm (h : Chart → Merid) 2 (ENNReal.ofReal c • ageμ c (-3 / 2)) := by
    rw [← hmap]
    exact (eLpNorm_map_measure hgm hcm).symm
  have hcpos' : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hcpos).ne'
  have e2 : eLpNorm (h : Chart → Merid) 2 (ENNReal.ofReal c • ageμ c (-3 / 2)) =
      ENNReal.ofReal (Real.sqrt c) * eLpNorm (h : Chart → Merid) 2 (ageμ c (-3 / 2)) := by
    rw [eLpNorm_smul_measure_of_ne_zero hcpos']
    have hp : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
    rw [hp, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hcpos.le (by norm_num), smul_eq_mul]
  have e3 : eLpNorm (fun p => χ p • (g' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p)
      2 (UnforcedLeray.B0220.measureH c) =
      eLpNorm (UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g') 2
        (UnforcedLeray.B0220.measureH c) := by
    have hae : (UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g' :
        UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) =ᵐ[UnforcedLeray.B0220.measureH c]
          fun p => χ p • (g' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p :=
      MemLp.coeFn_toLp (UnforcedLeray.Short.PartIIa.memLp_chi_smul (UnforcedLeray.B0220.measureH c) χ hm hB
        (Lp.memLp g'))
    exact eLpNorm_congr_ae hae.symm
  have hA := eLpNorm_mono_ae (p := 2) (μ := UnforcedLeray.B0220.measureH c) hpt
  have hfin : ENNReal.ofReal (Real.sqrt c) * eLpNorm (h : Chart → Merid) 2 (ageμ c (-3 / 2)) ≤
      eLpNorm (UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g') 2
        (UnforcedLeray.B0220.measureH c) := by
    rw [← e2, ← e1, ← e3]
    exact hA
  have hne : eLpNorm (UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g') 2
      (UnforcedLeray.B0220.measureH c) ≠ ⊤ :=
    (Lp.memLp _).2.ne
  have hreal := ENNReal.toReal_mono hne hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg c)] at hreal
  rw [Lp.norm_def h,
    Lp.norm_def (UnforcedLeray.Short.PartIIa.mulChi (UnforcedLeray.B0220.measureH c) χ hm hB g')]
  exact hreal

theorem outRestrBinTransport : OutRestrBinTransport := outRestrBinTransport_proof

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
