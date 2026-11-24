import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# Part II-b, leaf `PartII-b:T12/1/5/8` (`CylCellAverage`): the `q`-average of an `L^r` field

Source of record: `the November 2 reference manuscript`, lines 1727-1731 (the zero
mode `e(eta)` is an `L^r` function of `eta` alone). Target: `CylCellAverage` of `Sub/T12_1_5.lean`.

Proof. Let `S = Ico (-c/2) (c/2)` and `e(eta) = ∫ q in S, f (q, eta)`.
1. Measurability: the cell is `S ×ˢ univ`, so its measure is `(volume.restrict S).prod volume`
   (`cca_cell_prod`). `AEStronglyMeasurable.integral_prod_right'` applied to the swapped field
   gives the a.e.-measurability of `e`.
2. `L^r` bound: Minkowski (`eLpNorm_integral_le`) gives `‖e‖_r ≤ ∫_S ‖f(q, .)‖_r dq`. Hoelder on
   the finite measure `S` (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, exponents `1 ≤ r`) bounds
   this by `c^{1-1/r}` times the `L^r` norm of `q ↦ ‖f(q, .)‖_r` on `S`, whose `r`-th power is the
   `L^r(cell)` integral of `f`, finite by hypothesis.
3. Identity: for `supp χ ⊆ [-R, R]`, `f · χ(z.2)` vanishes off `S ×ˢ Icc (-R) R`, is integrable
   there (`f ∈ L^r ⊂ L^1` on a finite-measure set, times a bounded function), and Fubini
   (`integral_prod_symm`) gives `∫_cell f χ = ∫_eta (∫_S f(q, eta) dq) χ(eta)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The centred cell is `Ico (-c/2) (c/2) ×ˢ univ`, so its Lebesgue measure is a product measure. -/
theorem cca_cell_prod (c : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c) =
      (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (Ico (-c / 2) (c / 2)) univ
  rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
  rw [UnforcedLeray.Cyl.cell]
  exact h.symm

/-- `(X ^ (1/r)) ^ r = X` in `ℝ≥0∞` for `r > 0`. -/
theorem cca_rpow_inv_rpow {r : ℝ} (hr : 0 < r) (X : ℝ≥0∞) : (X ^ (1 / r)) ^ r = X := by
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]

/-- **Leaf `PartII-b:T12/1/5/8`** (the `q`-average of an `L^r` field; Minkowski, Hoelder, Fubini). -/
theorem cylCellAverage : CylCellAverage := by
  unfold CylCellAverage
  intro c r hc hr f hf
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr
  have hpTop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hcell := cca_cell_prod c
  -- `f` is `L^r` on the cell (the normalised measure is a positive multiple of `cellμ`)
  have hfc : MemLp f (ENNReal.ofReal r) (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := hf.smul_measure hct
    have heq : ENNReal.ofReal c • UnforcedLeray.Cyl.avgμ c =
        volume.restrict (UnforcedLeray.Cyl.cell c) := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      rw [smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
        one_smul]
    rw [heq] at h
    exact h
  -- the `L^r(cell)` integral of `‖f‖^r` is finite
  have hΦ : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖f z‖ₑ ^ r < ⊤ := by
    have h1 := hfc.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpTop, hpt] at h1
    rw [← cca_rpow_inv_rpow hr0 (∫⁻ z in UnforcedLeray.Cyl.cell c, ‖f z‖ₑ ^ r)]
    exact ENNReal.rpow_lt_top_of_nonneg hr0.le h1.ne
  -- measurability on the product `S × ℝ`, with `S = Ico (-c/2) (c/2)`
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
    rw [← hcell]
    exact hfc.aestronglyMeasurable
  have hH : AEMeasurable (fun z : ℝ × ℝ => ‖f z‖ₑ ^ r)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) :=
    (hfprod.aemeasurable.enorm).pow_const r
  -- Minkowski's integral inequality for the `q`-average (`η` outer, `q` integrated)
  have hsw : AEStronglyMeasurable (Function.uncurry (fun (η q : ℝ) => f (q, η)))
      ((volume : Measure ℝ).prod (volume.restrict (Ico (-c / 2) (c / 2)))) :=
    hfprod.comp_quasiMeasurePreserving Measure.measurePreserving_swap.quasiMeasurePreserving
  have hM := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
    (μ := (volume : Measure ℝ)) (ν := volume.restrict (Ico (-c / 2) (c / 2)))
    (F := fun (η q : ℝ) => f (q, η)) hsw hp1 hpTop
  -- the `L^r` norm of each section `f(q, .)`, as a function of `q`
  have hGform : ∀ q : ℝ, eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume =
      (∫⁻ η, ‖f (q, η)‖ₑ ^ r) ^ (1 / r) := by
    intro q
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpTop, hpt]
  have hA : AEMeasurable (fun q : ℝ => ∫⁻ η, ‖f (q, η)‖ₑ ^ r)
      (volume.restrict (Ico (-c / 2) (c / 2))) :=
    hH.lintegral_prod_right'
  have hGmeas : AEMeasurable
      (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume)
      (volume.restrict (Ico (-c / 2) (c / 2))) := by
    have heq : (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume) =
        fun q : ℝ => (∫⁻ η, ‖f (q, η)‖ₑ ^ r) ^ (1 / r) := funext hGform
    rw [heq]
    exact hA.pow_const _
  -- `eLpNorm _ 1 = ∫⁻`
  have hL1 : eLpNorm (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume) 1
      (volume.restrict (Ico (-c / 2) (c / 2))) =
      ∫⁻ q, eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume
        ∂(volume.restrict (Ico (-c / 2) (c / 2))) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [enorm_eq_self]
  -- the `L^r(cell)` integral is the iterated `q`-integral of `‖f‖^r`
  have hint : ∫⁻ q, ‖eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume‖ₑ ^ r
      ∂(volume.restrict (Ico (-c / 2) (c / 2))) =
      ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖f z‖ₑ ^ r := by
    calc ∫⁻ q, ‖eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume‖ₑ ^ r
          ∂(volume.restrict (Ico (-c / 2) (c / 2)))
        = ∫⁻ q, ∫⁻ η, ‖f (q, η)‖ₑ ^ r ∂volume ∂(volume.restrict (Ico (-c / 2) (c / 2))) :=
          lintegral_congr fun q => by rw [enorm_eq_self, hGform q, cca_rpow_inv_rpow hr0]
      _ = ∫⁻ z, ‖f z‖ₑ ^ r ∂((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) :=
          (lintegral_prod (fun z : ℝ × ℝ => ‖f z‖ₑ ^ r) hH).symm
      _ = ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖f z‖ₑ ^ r := by rw [hcell]
  have hLpG : eLpNorm (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume)
      (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2))) < ⊤ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpTop, hpt, hint]
    exact ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hr0).le hΦ.ne
  have hpow : (volume.restrict (Ico (-c / 2) (c / 2))) Set.univ ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) < ⊤ := by
    refine ENNReal.rpow_lt_top_of_nonneg ?_
      (measure_lt_top (volume.restrict (Ico (-c / 2) (c / 2))) Set.univ).ne
    rw [ENNReal.toReal_one, hpt]
    have h1 : 1 / r ≤ 1 := (div_le_one hr0).2 hr
    linarith
  -- `e` is `L^r`: measurability from Fubini, the norm bound from Minkowski and Hoelder
  have hLpE : MemLp (fun η : ℝ => ∫ q, f (q, η) ∂(volume.restrict (Ico (-c / 2) (c / 2))))
      (ENNReal.ofReal r) volume := by
    refine ⟨hsw.integral_prod_right', ?_⟩
    calc eLpNorm (fun η : ℝ => ∫ q, f (q, η) ∂(volume.restrict (Ico (-c / 2) (c / 2))))
          (ENNReal.ofReal r) volume
        ≤ ∫⁻ q, eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume
            ∂(volume.restrict (Ico (-c / 2) (c / 2))) := hM
      _ = eLpNorm (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume) 1
            (volume.restrict (Ico (-c / 2) (c / 2))) := hL1.symm
      _ ≤ eLpNorm (fun q : ℝ => eLpNorm (fun η => f (q, η)) (ENNReal.ofReal r) volume)
            (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2))) *
            (volume.restrict (Ico (-c / 2) (c / 2))) Set.univ ^
              (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hGmeas.aestronglyMeasurable
      _ < ⊤ := ENNReal.mul_lt_top hLpG hpow
  refine ⟨fun η : ℝ => ∫ q, f (q, η) ∂(volume.restrict (Ico (-c / 2) (c / 2))), hLpE, ?_⟩
  intro χ hχ
  -- the support of `χ` lies in `[-R, R]`
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hχ.compact.isCompact.isBounded
  have hχzero : ∀ t : ℝ, R < |t| → χ t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR t hmem
    rw [Real.norm_eq_abs] at h1
    linarith
  obtain ⟨M, hMb⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
  -- the finite-measure block `K = Ico ×ˢ Icc (-R) R` carries the integrand
  have hKsub : Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R ⊆ UnforcedLeray.Cyl.cell c := by
    rw [UnforcedLeray.Cyl.cell]
    exact Set.prod_mono subset_rfl (Set.subset_univ _)
  have hKfin : volume (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
      (measure_mono (Set.prod_mono Ico_subset_Icc_self subset_rfl))
  haveI : IsFiniteMeasure (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hKfin⟩
  have hfK : MemLp f (ENNReal.ofReal r)
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)) :=
    MemLp.mono_measure (Measure.restrict_mono hKsub le_rfl) hfc
  have hfK1 : Integrable f (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)) :=
    hfK.integrable hp1
  have hφ : AEStronglyMeasurable (fun z : ℝ × ℝ => ((χ z.2 : ℝ) : ℂ))
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)) :=
    (Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_snd)).aestronglyMeasurable
  have hφb : ∀ᵐ z ∂(volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)),
      ‖((χ z.2 : ℝ) : ℂ)‖ ≤ M :=
    Eventually.of_forall (fun z => by rw [Complex.norm_real]; exact hMb z.2)
  have hgK : Integrable (fun z : ℝ × ℝ => f z * ((χ z.2 : ℝ) : ℂ))
      (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)) :=
    hfK1.mul_bdd hφ hφb
  have hmeasC : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    rw [UnforcedLeray.Cyl.cell]
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hgIntOn : IntegrableOn (fun z : ℝ × ℝ => f z * ((χ z.2 : ℝ) : ℂ))
      (UnforcedLeray.Cyl.cell c) volume := by
    refine IntegrableOn.of_forall_diff_eq_zero hgK hmeasC ?_
    rintro ⟨x1, x2⟩ ⟨hxc, hxK⟩
    have hxR : R < |x2| := by
      by_contra hcon
      push_neg at hcon
      rw [UnforcedLeray.Cyl.cell, Set.mem_prod] at hxc
      exact hxK (Set.mk_mem_prod hxc.1 (abs_le.1 hcon))
    show f (x1, x2) * ((χ x2 : ℝ) : ℂ) = 0
    rw [hχzero x2 hxR]
    simp
  have hgcell : Integrable (fun z : ℝ × ℝ => f z * ((χ z.2 : ℝ) : ℂ))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := hgIntOn
  rw [hcell] at hgcell
  have hfub := integral_prod_symm (fun z : ℝ × ℝ => f z * ((χ z.2 : ℝ) : ℂ)) hgcell
  calc ∫ z in UnforcedLeray.Cyl.cell c, f z * ((χ z.2 : ℝ) : ℂ)
      = ∫ z, f z * ((χ z.2 : ℝ) : ℂ)
          ∂((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
        rw [hcell]
    _ = ∫ y, ∫ x, f (x, y) * ((χ (x, y).2 : ℝ) : ℂ) ∂(volume.restrict (Ico (-c / 2) (c / 2)))
          ∂volume := hfub
    _ = ∫ η, (∫ q, f (q, η) ∂(volume.restrict (Ico (-c / 2) (c / 2)))) * ((χ η : ℝ) : ℂ) := by
        congr 1
        funext η
        rw [← integral_mul_const]

end UnforcedLeray.Short.IIb
