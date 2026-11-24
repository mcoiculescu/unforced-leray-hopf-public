import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_of
import UnforcedLeray.Units.B0226.Distrib
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Approx.Moll.InHr.NiceInHr

/-!
# `flatSlicePairing` (leaf of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/3/2`)

Source `the November 2 reference manuscript` 1650-1656.  For the product test
`Φ = χ(s) s^{3/2} ψ(q,η)` the H-inner product with `h` is computed as an integral over the age
measure: `h` is the lift `merC ∘ f ∘ cellPt` (`measureH` pushes forward to `c • ageμ c (-3/2)`,
`cellPtH_eq`), `cgrad 0 Φ` is the `cellPt`-periodic function `χ(s) s^{3/2} ∂ψ(q,η)`, and the
weight `s^{-3/2}` cancels against `s^{3/2}`; Fubini on `(0,∞) × cell` then gives
`⟨cgrad 0 Φ, h⟩ = ∫ χ(s) divPairing c b ψ s ds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A compactly supported `χ` with support in `(0,∞)` lies in a band `[s0, s1]`, `s0 > 0`. -/
theorem chi_band {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) (hχsupp : tsupport χ ⊆ Ioi (0 : ℝ)) :
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ s : ℝ, χ s ≠ 0 → s ∈ Icc s0 s1 := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, 1, one_pos, fun s hs => ?_⟩
    exfalso
    apply hs
    have hns : s ∉ tsupport χ := by rw [he]; exact notMem_empty s
    exact image_eq_zero_of_notMem_tsupport hns
  · obtain ⟨a, ha, hamin⟩ := hχc.isCompact.exists_isMinOn hne continuousOn_id
    obtain ⟨b, hb, hbmax⟩ := hχc.isCompact.exists_isMaxOn hne continuousOn_id
    refine ⟨a, b, hχsupp ha, fun s hs => ?_⟩
    exact ⟨isMinOn_iff.1 hamin s (subset_tsupport χ hs),
      isMaxOn_iff.1 hbmax s (subset_tsupport χ hs)⟩

/-- The profile test `χ(s) ψ(q,η)`. -/
theorem isProfileTest_chiPsi {c : ℝ} {χ : ℝ → ℝ} (hχs : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχsupp : tsupport χ ⊆ Ioi (0 : ℝ))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    UnforcedLeray.B0226.IsProfileTest c
      (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) := by
  obtain ⟨s0, s1, hs0, hbd⟩ := chi_band hχc hχsupp
  obtain ⟨R, hR⟩ := hψ.band
  have hΨs : ContDiff ℝ ∞ (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) :=
    (hχs.comp contDiff_fst).mul
      (hψ.smooth.comp ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd)))
  refine ⟨hΨs, ?_, ?_⟩
  · intro p
    show χ p.1 * ψ (p.2.1 + c, p.2.2) = χ p.1 * ψ (p.2.1, p.2.2)
    exact congrArg (fun t => χ p.1 * t) (hψ.periodic (p.2.1, p.2.2))
  · refine ⟨s0, s1, R, hs0, ?_⟩
    intro p hp
    have hp' : χ p.1 * ψ (p.2.1, p.2.2) ≠ 0 := hp
    refine ⟨hbd p.1 (left_ne_zero_of_mul hp'), ?_⟩
    by_contra hlt
    exact (right_ne_zero_of_mul hp') (hR (p.2.1, p.2.2) (not_le.1 hlt))

/-- Partial derivatives of `χ(s) ψ(q,η)` in the `(s,q,η)` coordinates. -/
theorem fderiv_chiPsi {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {ψ : ℝ × ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (p v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => χ p.1 * ψ (p.2.1, p.2.2)) p v
      = χ p.1 * fderiv ℝ ψ p.2 v.2 + ψ p.2 * (deriv χ p.1 * v.1) := by
  have h1 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => χ p.1)
      (deriv χ p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hχ p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => ψ (p.2.1, p.2.2))
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hψ p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h4 : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => χ p.1 * ψ (p.2.1, p.2.2)) p
      = χ p.1 • ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        + ψ p.2 • (deriv χ p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) :=
    (h1.mul h2).fderiv
  rw [h4]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    smul_eq_mul]

/-- `∂_q (χ(s) ψ)` at `p` is `χ(s) ∂_qψ(q,η)`. -/
theorem dQ_chiPsi {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {ψ : ℝ × ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (p : UnforcedLeray.B0220.Profile) :
    Axi.dQ (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) p
      = χ p.1 * B0579.pd 0 ψ p.2 := by
  unfold Axi.dQ
  rw [fderiv_chiPsi hχ hψ]
  simp [B0579.pd, B0579.dir]

/-- `∂_η (χ(s) ψ)` at `p` is `χ(s) ∂_ηψ(q,η)`. -/
theorem dEta_chiPsi {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {ψ : ℝ × ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (p : UnforcedLeray.B0220.Profile) :
    Axi.dEta (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) p
      = χ p.1 * B0579.pd 1 ψ p.2 := by
  unfold Axi.dEta
  rw [fderiv_chiPsi hχ hψ]
  simp [B0579.pd, B0579.dir]

/-- `c`-periodicity of the cylinder derivatives, used on the recentred cell. -/
theorem pd_cellPt {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (j : Fin 2) (q η : ℝ) :
    B0579.pd j ψ ((if q < c / 2 then q else q - c), η) = B0579.pd j ψ (q, η) := by
  split_ifs with h
  · rfl
  · have h2 := (hψ.pd j).periodic (q - c, η)
    dsimp only at h2
    rw [sub_add_cancel] at h2
    exact h2.symm

/-- The `i`-th component of `(s,ξ,η) ↦ χ(s) s^{3/2} ∂_i ψ(ξ,η)`. -/
def sliceK (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (i : Fin 2) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  χ x.1 * x.1 ^ (3 / 2 : ℝ) * B0579.pd i ψ x.2

/-- The chart field `∑_i sliceK_i(x) b_i(x)` whose age integral is the slice pairing. -/
def sliceH (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (b : Chart → Fin 2 → ℂ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2, ((sliceK χ ψ i x : ℝ) : ℂ) * b x i

theorem sliceK_cellPt {c : ℝ} {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (i : Fin 2)
    (p : UnforcedLeray.B0220.Profile) :
    sliceK χ ψ i (NearInst.cellPt c p)
      = χ p.1 * p.1 ^ (3 / 2 : ℝ) * B0579.pd i ψ (p.2.1, p.2.2) := by
  unfold sliceK NearInst.cellPt
  dsimp only
  exact congrArg (fun t => χ p.1 * p.1 ^ (3 / 2 : ℝ) * t) (pd_cellPt hψ i p.2.1 p.2.2)

theorem cgrad_zero_apply (Φ : UnforcedLeray.B0220.Profile → ℝ) (p : UnforcedLeray.B0220.Profile) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p
      = !₂[((Axi.dQ Φ p : ℝ) : ℂ), ((Axi.dEta Φ p : ℝ) : ℂ)] := by
  unfold UnforcedLeray.Short.PartIIa.cgrad
  rw [show UnforcedLeray.B0226.Deps 0 Φ p = Axi.dQ Φ p from congrFun (UnforcedLeray.B0226.Deps_zero Φ) p]

theorem inner_cgrad_merC (Φ : UnforcedLeray.B0220.Profile → ℝ) (p : UnforcedLeray.B0220.Profile)
    (v : UnforcedLeray.B0220.Merid) :
    inner ℂ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ p) (NearInst.merC v)
      = ((Axi.dQ Φ p : ℝ) : ℂ) * ((v 0 : ℝ) : ℂ) + ((Axi.dEta Φ p : ℝ) : ℂ) * ((v 1 : ℝ) : ℂ) := by
  rw [cgrad_zero_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two, NearInst.merC]
  ring

theorem measurableSet_cyl_cell (c : ℝ) : MeasurableSet (Cyl.cell c) := by
  unfold Cyl.cell
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- The age measure is concentrated on the cell in the `q`-coordinate. -/
theorem ae_ageμ_cell {c : ℝ} (hc : 0 < c) (a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), x.2 ∈ Cyl.cell c := by
  unfold Axi.ageμ Cyl.avgμ Cyl.cellμ
  rw [Measure.prod_smul_right]
  apply Measure.ae_smul_measure
  have hres : (((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a))) =
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).restrict univ :=
    Measure.restrict_univ.symm
  rw [hres, Measure.prod_restrict]
  exact (ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_cyl_cell c))).mono
    fun x hx => hx.2

theorem sliceK_continuous {χ : ℝ → ℝ} (hχs : ContDiff ℝ ∞ χ) {ψ : ℝ × ℝ → ℝ} {c : ℝ}
    (hψ : B0579.IsCylTest c ψ) (i : Fin 2) : Continuous (sliceK χ ψ i) := by
  unfold sliceK
  exact ((hχs.continuous.comp continuous_fst).mul
    (continuous_fst.rpow_const fun _ => Or.inr (by norm_num))).mul
    ((hψ.pd i).continuous.comp continuous_snd)

theorem pd_eq_zero_of_large {R : ℝ} {ψ : ℝ × ℝ → ℝ} (hR : ∀ y : ℝ × ℝ, R < |y.2| → ψ y = 0)
    (y : ℝ × ℝ) (hy : R < |y.2|) (j : Fin 2) : B0579.pd j ψ y = 0 := by
  have hopen : IsOpen {z : ℝ × ℝ | R < |z.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hy] with z hz using hR z hz
  have hf : fderiv ℝ ψ y = 0 := by
    rw [hev.fderiv_eq]
    simp
  unfold B0579.pd
  rw [hf]
  rfl

theorem sliceH_measurable {χ : ℝ → ℝ} (hχs : ContDiff ℝ ∞ χ) {ψ : ℝ × ℝ → ℝ} {c : ℝ}
    (hψ : B0579.IsCylTest c ψ) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b) :
    Measurable (sliceH χ ψ b) := by
  unfold sliceH
  rw [show (fun x : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ((sliceK χ ψ i x : ℝ) : ℂ) * b x i)
      = fun x => ((sliceK χ ψ 0 x : ℝ) : ℂ) * b x 0 + ((sliceK χ ψ 1 x : ℝ) : ℂ) * b x 1 from
    funext fun x => by rw [Fin.sum_univ_two]]
  exact ((Complex.measurable_ofReal.comp (sliceK_continuous hχs hψ 0).measurable).mul
    (hb.1 0)).add ((Complex.measurable_ofReal.comp (sliceK_continuous hχs hψ 1).measurable).mul
    (hb.1 1))

theorem sliceH_integrable {c : ℝ} (hc : 0 < c) {χ : ℝ → ℝ} (hχs : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχsupp : tsupport χ ⊆ Ioi (0 : ℝ))
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (a : ℝ) : Integrable (sliceH χ ψ b) (Axi.ageμ c a) := by
  obtain ⟨s0, s1, hs0, hbd⟩ := chi_band hχc hχsupp
  obtain ⟨R, hR⟩ := hψ.band
  set K : Set (ℝ × (ℝ × ℝ)) := Icc s0 s1 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : K ⊆ Ioi (0 : ℝ) ×ˢ univ := fun x hx => ⟨lt_of_lt_of_le hs0 hx.1.1, trivial⟩
  have hbc : ∀ i : Fin 2, ContinuousOn (fun x : ℝ × (ℝ × ℝ) => b x i) K := fun i =>
    (hb.2.1 i).continuousOn.mono hKsub
  have hHc : ContinuousOn (sliceH χ ψ b) K := by
    unfold sliceH
    have e : (fun x : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ((sliceK χ ψ i x : ℝ) : ℂ) * b x i)
        = fun x => ((sliceK χ ψ 0 x : ℝ) : ℂ) * b x 0 + ((sliceK χ ψ 1 x : ℝ) : ℂ) * b x 1 :=
      funext fun x => by rw [Fin.sum_univ_two]
    rw [e]
    exact ((Complex.continuous_ofReal.comp (sliceK_continuous hχs hψ 0)).continuousOn.mul
      (hbc 0)).add ((Complex.continuous_ofReal.comp (sliceK_continuous hχs hψ 1)).continuousOn.mul
      (hbc 1))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hHc
  have hKW : K ⊆ Icc s0 s1 ×ˢ (univ ×ˢ Icc (-R) R) := fun x hx =>
    ⟨hx.1, trivial, hx.2.2⟩
  have hfin : Axi.ageμ c a K ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (measure_mono hKW) (UnforcedLeray.Short.IIb.NiceInHrHelp.ageμ_window_lt_top hc a s0 s1 R hs0))
  refine Integrable.mono' (g := K.indicator (fun _ : ℝ × (ℝ × ℝ) => C))
    ((integrable_indicator_iff hKc.measurableSet).2
    (integrableOn_const (C := C) hfin)) (sliceH_measurable hχs hψ hb).aestronglyMeasurable ?_
  filter_upwards [ae_ageμ_cell hc a] with x hx
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
    exact hC x hxK
  · rw [indicator_of_notMem hxK]
    have hcase : χ x.1 = 0 ∨ R < |x.2.2| := by
      by_contra hne
      push_neg at hne
      apply hxK
      have hq := hx
      unfold Cyl.cell at hq
      have hx1 : x.1 ∈ Icc s0 s1 := hbd x.1 hne.1
      have hx2 : x.2.1 ∈ Icc (-(c / 2)) (c / 2) := ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
      have hx3 : x.2.2 ∈ Icc (-R) R := abs_le.1 hne.2
      exact ⟨hx1, hx2, hx3⟩
    have hz : sliceH χ ψ b x = 0 := by
      rcases hcase with h0 | h1
      · simp [sliceH, sliceK, h0, Fin.sum_univ_two]
      · simp [sliceH, sliceK, pd_eq_zero_of_large hR x.2 h1 0, pd_eq_zero_of_large hR x.2 h1 1,
          Fin.sum_univ_two]
    rw [hz, norm_zero]


/-- The slice-pairing identity: the `H`-inner product of `cgrad 0 Φ` with `h` is the
`χ`-weighted slice divergence (source 1650-1656). -/
theorem inner_eq_slice {c : ℝ} (hc : 0 < c) (f : Hsp c)
    (h : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (b : Chart → Fin 2 → ℂ) (χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ)
    (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχsupp : tsupport χ ⊆ Ioi (0 : ℝ))
    (hψ : B0579.IsCylTest c ψ) (hb : SmoothRep c b)
    (Φ : UnforcedLeray.B0226.ProfileTest c)
    (hu : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (UnforcedLeray.B0220.measureH c))
    (hΦ : ∀ p : UnforcedLeray.B0220.Profile, Φ.1 p = χ p.1 * p.1 ^ (3 / 2 : ℝ) * ψ (p.2.1, p.2.2))
    (hh : (h : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (f (NearInst.cellPt c p))))
    (hbe : b =ᵐ[Axi.ageμ c (-3 / 2)] NearInst.velC f) :
    inner ℂ (hu.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1)) h
      = ∫ s, χ s • divPairing c b ψ s := by
  have hχd : Differentiable ℝ χ := hχs.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hΨp := isProfileTest_chiPsi hχs hχc hχsupp hψ
  have hΦeq : Φ.1 = UnforcedLeray.B0226.ageScale (3 / 2)
      (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) := by
    funext p
    rw [hΦ p]
    simp only [UnforcedLeray.B0226.ageScale]
    ring
  have hdQ : ∀ p : UnforcedLeray.B0220.Profile,
      Axi.dQ Φ.1 p = sliceK χ ψ 0 (NearInst.cellPt c p) := by
    intro p
    rw [sliceK_cellPt hψ, hΦeq, UnforcedLeray.B0226.dQ_ageScale (3 / 2) hΨp, dQ_chiPsi hχd hψd]
    show _ = χ p.1 * p.1 ^ (3 / 2 : ℝ) * B0579.pd 0 ψ p.2
    ring
  have hdEta : ∀ p : UnforcedLeray.B0220.Profile,
      Axi.dEta Φ.1 p = sliceK χ ψ 1 (NearInst.cellPt c p) := by
    intro p
    rw [sliceK_cellPt hψ, hΦeq, UnforcedLeray.B0226.dEta_ageScale (3 / 2) hΨp, dEta_chiPsi hχd hψd]
    show _ = χ p.1 * p.1 ^ (3 / 2 : ℝ) * B0579.pd 1 ψ p.2
    ring
  have hpt : ∀ (p : UnforcedLeray.B0220.Profile) (v : UnforcedLeray.B0220.Merid),
      inner ℂ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 p) (NearInst.merC v)
        = ((sliceK χ ψ 0 (NearInst.cellPt c p) : ℝ) : ℂ) * ((v 0 : ℝ) : ℂ)
          + ((sliceK χ ψ 1 (NearInst.cellPt c p) : ℝ) : ℂ) * ((v 1 : ℝ) : ℂ) := by
    intro p v
    rw [inner_cgrad_merC, hdQ, hdEta]
  have hbμ : ∀ᵐ p ∂(UnforcedLeray.B0220.measureH c), ∀ i : Fin 2,
      b (NearInst.cellPt c p) i = NearInst.velC f (NearInst.cellPt c p) i := by
    have hmap : Measure.map (NearInst.cellPt c) (UnforcedLeray.B0220.measureH c)
        = ENNReal.ofReal c • Axi.ageμ c (-3 / 2) :=
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc
    have h1 : ∀ᵐ x ∂(Measure.map (NearInst.cellPt c) (UnforcedLeray.B0220.measureH c)),
        ∀ i : Fin 2, b x i = NearInst.velC f x i := by
      rw [hmap]
      apply Measure.ae_smul_measure
      filter_upwards [hbe] with x hx i
      exact congrFun hx i
    exact ae_of_ae_map
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c).aemeasurable h1
  have hL2 : inner ℂ (hu.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1)) h
      = ∫ p, sliceH χ ψ b (NearInst.cellPt c p) ∂(UnforcedLeray.B0220.measureH c) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hh, hbμ] with p h1 h2 h3
    rw [h1, h2, hpt]
    simp only [sliceH, Fin.sum_univ_two, h3 0, h3 1]
    rfl
  have hmap : Measure.map (NearInst.cellPt c) (UnforcedLeray.B0220.measureH c)
      = ENNReal.ofReal c • Axi.ageμ c (-3 / 2) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc
  rw [hL2, ← integral_map
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c).aemeasurable
    (sliceH_measurable hχs hψ hb).aestronglyMeasurable, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le]
  have hfub : ∫ z, sliceH χ ψ b z ∂(Axi.ageμ c (-3 / 2))
      = ∫ x, ∫ y, sliceH χ ψ b (x, y) ∂(Cyl.avgμ c)
          ∂((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))) :=
    integral_prod _ (sliceH_integrable hc hχs hχc hχsupp hψ hb (-3 / 2))
  rw [hfub, integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_rpow _)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hstep : ∫ x, (ENNReal.ofReal (x ^ (-3 / 2 : ℝ))).toReal •
      (∫ y, sliceH χ ψ b (x, y) ∂(Cyl.avgμ c)) ∂(volume.restrict (Ioi (0 : ℝ)))
      = ∫ x in Ioi (0 : ℝ), (c⁻¹ : ℝ) • (χ x • divPairing c b ψ x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx0 : 0 < x := hx
    have hxr : x ^ (-3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hxrC : ((x ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hxr
    have hA : ∫ y, sliceH χ ψ b (x, y) ∂(Cyl.avgμ c)
        = (c⁻¹ : ℝ) • (((χ x * x ^ (3 / 2 : ℝ) : ℝ) : ℂ) * divPairing c b ψ x) := by
      unfold Cyl.avgμ Cyl.cellμ
      rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le), cyl_cell_eq]
      congr 1
      have hfun : ∀ y : ℝ × ℝ, sliceH χ ψ b (x, y)
          = ((χ x * x ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (b (x, y) 0 * (B0579.pd 0 ψ y : ℂ)
            + b (x, y) 1 * (B0579.pd 1 ψ y : ℂ)) := by
        intro y
        simp only [sliceH, sliceK, Fin.sum_univ_two]
        push_cast
        ring
      simp only [hfun]
      rw [integral_const_mul]
      rfl
    rw [hA, ENNReal.toReal_ofReal (Real.rpow_nonneg hx0.le _)]
    simp only [Complex.real_smul]
    push_cast
    linear_combination ((c⁻¹ : ℂ) * (χ x : ℂ) * divPairing c b ψ x) * hxrC
  rw [hstep, integral_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hχsupp h)), zero_smul]

/-- **`flatSlicePairing`** (source 1650-1656). -/
theorem flatSlicePairing : FlatSlicePairing := by
  intro c hc f h b χ ψ hχs hχc hχsupp hψ hb Φ hu hΦ hh hbe hinner
  rw [inner_eq_slice hc f h b χ ψ hχs hχc hχsupp hψ hb Φ hu hΦ hh hbe] at hinner
  exact hinner

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
