import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.ZeroBelow
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue

/-!
# Pairing inequality on `IsMeridTest` from `r0TransposeIdentity`
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

Source of record `the November 2 reference manuscript` 1650-1656, 1684-1689.
For any `ζ : Profile → MeridC` satisfying `IsMeridTest c ζ` and `‖ζ p‖ ≤ vnorm2 (b p)`,
`r0TransposeIdentity` and `pairHChart` rewrite `pairH c (T0flat f') (resolventTest ν μ ζ)` as the
chart integral against `b`, while Cauchy-Schwarz and `‖PepsC 0 c f'‖ ≤ ‖f'‖` bound the right-hand
side by `c · √(Gn · A)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)
open UnforcedLeray.Short.PartIIa (IsMeridTest PepsC T0flat solenoidalHC)

/-- `b p` packaged as an element of `MeridC = EuclideanSpace ℂ (Fin 2)`. -/
def bm (b : Chart → Fin 2 → ℂ) (p : Profile) : MeridC := WithLp.toLp 2 (b p)

theorem norm_bm (b : Chart → Fin 2 → ℂ) (p : Profile) : ‖bm b p‖ = vnorm2 (b p) := by
  unfold bm vnorm2
  rw [EuclideanSpace.norm_eq]

theorem vnorm2_velC (f : Chart → Merid) (p : Chart) :
    vnorm2 (NearInst.velC f p) = ‖f p‖ := by
  have h := vnorm2_velC_sub f 0 p
  have h0 : NearInst.velC (0 : Chart → Merid) p = 0 := by
    funext i; simp [NearInst.velC]
  simpa [h0] using h

theorem measurable_vnorm2_sq {b : Chart → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i) :
    Measurable fun p : Chart => ENNReal.ofReal (vnorm2 (b p) ^ 2) := by
  unfold vnorm2
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.pow_const ?_ 2
  refine Measurable.sqrt ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (hb i).norm.pow_const 2

/-- For a lift `f'` of `g : Hsp c`, `‖f'‖² = c ∫ vnorm2(velC g)² d(ageμ c (-3/2))`. -/
theorem norm_sq_lift_eq {c : ℝ} (hc : 0 < c) (g : Hsp c) (f' : HSpace c MeridC)
    (hf' : (f' : Profile → MeridC) =ᵐ[measureH c]
      fun p => NearInst.merC (g (NearInst.cellPt c p))) :
    ENNReal.ofReal (‖f'‖ ^ 2) =
      ENNReal.ofReal c *
        ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2)) := by
  rw [ofReal_sq_norm_eq_lintegral f']
  set gm : Chart → EuclideanSpace ℝ (Fin 2) := (Lp.aestronglyMeasurable g).mk ⇑g
  have hgm_meas : Measurable gm := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable
  have hgm_ae : (⇑g) =ᵐ[ageμ c (-3 / 2)] gm := (Lp.aestronglyMeasurable g).ae_eq_mk
  have hmap : Measure.map (NearInst.cellPt c) (measureH c) ≤
      ENNReal.ofReal c • ageμ c (-3 / 2) := by
    rw [CellMap.map_cellPt_measureH hc, neg_div]
  have hac := Measure.absolutelyContinuous_of_le_smul hmap
  have hgm_H : ∀ᵐ p ∂(measureH c), g (NearInst.cellPt c p) = gm (NearInst.cellPt c p) :=
    ae_of_ae_map (CellMap.measurable_cellPt' c).aemeasurable (hac.ae_le hgm_ae)
  have h1 : ∫⁻ p, ENNReal.ofReal (‖(f' : Profile → MeridC) p‖ ^ 2) ∂(measureH c) =
      ∫⁻ p, ENNReal.ofReal (‖gm (NearInst.cellPt c p)‖ ^ 2) ∂(measureH c) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf', hgm_H] with p hp1 hp2
    rw [hp1, hp2, wp_norm_merC]
  have h2 : ∫⁻ p, ENNReal.ofReal (‖gm (NearInst.cellPt c p)‖ ^ 2) ∂(measureH c) =
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (‖gm x‖ ^ 2) ∂(ageμ c (-3 / 2)) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring]
    exact CellMap.lintegral_cellPt hc (fun x => ENNReal.ofReal (‖gm x‖ ^ 2))
      (ENNReal.measurable_ofReal.comp (hgm_meas.norm.pow_const 2))
  have h3 : ∫⁻ x, ENNReal.ofReal (‖gm x‖ ^ 2) ∂(ageμ c (-3 / 2)) =
      ∫⁻ x, ENNReal.ofReal (vnorm2 (NearInst.velC g x) ^ 2) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgm_ae] with x hx
    rw [← hx, vnorm2_velC]
  rw [h1, h2, h3]

/-- For `ζ` bounded by `vnorm2 ∘ b` and `b` periodic, `‖Z‖² ≤ c ∫ vnorm2(b)² d(ageμ c (-3/2))`. -/
theorem norm_sq_test_le {c : ℝ} (hc : 0 < c) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    {ζ : Profile → MeridC} {Z : HSpace c MeridC}
    (hZ : (Z : Profile → MeridC) =ᵐ[measureH c] ζ)
    (hζb : ∀ p : Profile, ‖ζ p‖ ≤ vnorm2 (b p)) :
    ENNReal.ofReal (‖Z‖ ^ 2) ≤
      ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)) := by
  rw [ofReal_sq_norm_eq_lintegral Z]
  have hper : ∀ p : Profile, vnorm2 (b (NearInst.cellPt c p)) = vnorm2 (b p) := by
    intro ⟨s, q, η⟩
    by_cases h : q < c / 2
    · simp [NearInst.cellPt, h]
    · have h1 := smoothRep_periodic hb s (q - c) η
      have e : q - c + c = q := by ring
      rw [e] at h1
      simp [NearInst.cellPt, h, ← h1]
  have hle : ∫⁻ p, ENNReal.ofReal (‖(Z : Profile → MeridC) p‖ ^ 2) ∂(measureH c) ≤
      ∫⁻ p, ENNReal.ofReal (vnorm2 (b (NearInst.cellPt c p)) ^ 2) ∂(measureH c) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hZ] with p hp
    rw [hp, hper p]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hζb p) 2)
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring,
    ← CellMap.lintegral_cellPt hc (fun x => ENNReal.ofReal (vnorm2 (b x) ^ 2))
      (measurable_vnorm2_sq hb.1)]
  exact hle

/-- Invariance of `resolventTest ν μ ζ` under `cellPt c` for `IsMeridTest c ζ`. -/
theorem resolventTest_cellPt_of_isMeridTest {c ν μ : ℝ} {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) (p : Profile) :
    resolventTest ν μ ζ (NearInst.cellPt c p) = resolventTest ν μ ζ p := by
  have hshift : ∀ x : Profile, ζ (x + (0, -c, 0)) = ζ x := by
    intro ⟨s, q, η⟩
    have h1 := hζ.periodic (s, (q + -c, η))
    have e : q + -c + c = q := by ring
    dsimp only at h1
    rw [e] at h1
    show ζ (s + 0, q + -c, η + 0) = ζ (s, q, η)
    simp [h1.symm]
  by_cases h : p.2.1 < c / 2
  · simp [NearInst.cellPt, h]
  · have hc' : NearInst.cellPt c p = p + (0, -c, 0) := by
      have h' : NearInst.cellPt c p = (p.1, p.2.1 + -c, p.2.2) := by
        simp [NearInst.cellPt, h, sub_eq_add_neg]
      rw [h']
      exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [hc']
    exact resolventTest_add_cellPt ν μ c ζ hshift p

/-- Integrability of `p.1^(-3/2) • inner ℂ (resolventTest ν μ ζ p) (merC (u p))` on the cell. -/
theorem resolventTest_integrableOn_of_isMeridTest {c : ℝ} (ν μ : ℝ) (hc : 0 < c)
    {ζ : Profile → MeridC} (hζ : IsMeridTest c ζ) (u : Hsp c) :
    IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
        inner ℂ (resolventTest ν μ ζ p) (NearInst.merC (u p)))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hζ.band
  have hζ0 : ∀ p : Profile, (p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|) → ζ p = 0 := by
    intro p hp
    by_contra hne
    obtain ⟨⟨h1, h2⟩, h3⟩ := hband p hne
    rcases hp with h | h | h <;> linarith
  have hU : IsOpen {x : Profile | x.1 < s0 ∨ s1 < x.1 ∨ L < |x.2.2|} := by
    rw [Set.ofPred_or, Set.ofPred_or]
    exact (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hΘ0 : ∀ p : Profile, (p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|) →
      resolventTest ν μ ζ p = 0 := by
    intro p hp
    apply wp_resolvent_zero
    exact Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx => hζ0 x hx)
  exact wp_piece_integrable hc hs0 _ (wp_resolvent_continuous hζ.smooth) hΘ0 u

/-- **Main test pairing inequality**: for any `ζ` with `IsMeridTest c ζ` and `‖ζ p‖ ≤ vnorm2 (b p)`,
the chart pairing of `resolventTest ν μ ζ` with `bm b` is bounded by `c · √(Gn · A)`. -/
theorem smoothRep_test_pairing {c ν μ : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c} {g : Hsp c}
    (hctx : ClassicalCtx c ν μ hc R0 g) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hbe : b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) (hζb : ∀ p : Profile, ‖ζ p‖ ≤ vnorm2 (b p)) :
    ENNReal.ofReal
        (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          (p.1 ^ (-(3 / 2 : ℝ))) * (inner ℂ (resolventTest ν μ ζ p) (bm b p)).re) ≤
      ENNReal.ofReal c *
        ((∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))) *
          (∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2)))) ^ (1 / 2 : ℝ) := by
  obtain ⟨f', hf'⟩ := cplxLift c hc g
  have hB := hctx.2.2.1 g f' hf'
  have htr := r0TransposeIdentity c ν μ hc hctx.1 hctx.2.1 (PepsC 0 c f') ζ hζ
  have hBdef : T0flat hc ν (μ : ℂ) f' =
      UnforcedLeray.B0225.R0 hc ν (μ : ℂ) (PepsC 0 c f') := rfl
  have hint := resolventTest_integrableOn_of_isMeridTest ν μ hc hζ (R0 g)
  have hchart := pairHChart c hc (R0 g) (T0flat hc ν (μ : ℂ) f') hB (resolventTest ν μ ζ)
    (resolventTest_cellPt_of_isMeridTest hζ) hint
  -- replace `merC (R0 g p)` with `bm b p` a.e. on `Ioi 0 ×ˢ B0579.cell c`
  have hac := volCyl_ac_ageμ hc (-3 / 2)
  have hbe' : ∀ᵐ p ∂((volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)),
      b p = NearInst.velC (R0 g) p := hac.ae_le hbe
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (resolventTest ν μ ζ p) (NearInst.merC ((R0 g) p)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        (p.1 ^ (-(3 / 2 : ℝ))) • inner ℂ (resolventTest ν μ ζ p) (bm b p) := by
    refine integral_congr_ae ?_
    filter_upwards [hbe'] with p hp
    have hbm : NearInst.merC ((R0 g) p) = bm b p := by
      ext i
      simp [NearInst.merC, bm, hp, NearInst.velC]
    rw [hbm]
  have hint_bm : IntegrableOn (fun p : Chart => (p.1 ^ (-(3 / 2 : ℝ))) •
        inner ℂ (resolventTest ν μ ζ p) (bm b p)) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    refine hint.congr ?_
    filter_upwards [hbe'] with p hp
    have hbm : NearInst.merC ((R0 g) p) = bm b p := by
      ext i
      simp [NearInst.merC, bm, hp, NearInst.velC]
    rw [hbm]
  have hre_eq : (pairH c (PepsC 0 c f' : Profile → MeridC) ζ).re =
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        (p.1 ^ (-(3 / 2 : ℝ))) * (inner ℂ (resolventTest ν μ ζ p) (bm b p)).re := by
    rw [← htr, ← hBdef, hchart, hcongr]
    have hre := integral_re hint_bm
    simpa [RCLike.re_eq_complex_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im] using hre.symm
  -- bound the RHS via `Z` and `f'`
  have hZm : MemLp ζ 2 (measureH c) := (memLp_test_A0adj c ν ζ hζ).1
  set Z : HSpace c MeridC := hZm.toLp ζ
  have hZae : (Z : Profile → MeridC) =ᵐ[measureH c] ζ := hZm.coeFn_toLp
  have hpairZ : pairH c (PepsC 0 c f' : Profile → MeridC) ζ = inner ℂ Z (PepsC 0 c f') :=
    pairH_eq_inner (PepsC 0 c f') Z hZae
  have hPeps_le : ‖PepsC 0 c f'‖ ≤ ‖f'‖ := Submodule.norm_starProjection_apply_le _ f'
  have hre_le : (pairH c (PepsC 0 c f' : Profile → MeridC) ζ).re ≤ ‖Z‖ * ‖f'‖ := by
    rw [hpairZ]
    calc (inner ℂ Z (PepsC 0 c f')).re
        ≤ ‖inner ℂ Z (PepsC 0 c f')‖ := Complex.re_le_norm _
      _ ≤ ‖Z‖ * ‖PepsC 0 c f'‖ := norm_inner_le_norm _ _
      _ ≤ ‖Z‖ * ‖f'‖ := mul_le_mul_of_nonneg_left hPeps_le (norm_nonneg _)
  rw [← hre_eq]
  refine (ENNReal.ofReal_le_ofReal hre_le).trans ?_
  have hsq : ENNReal.ofReal (‖Z‖ * ‖f'‖) =
      (ENNReal.ofReal (‖f'‖ ^ 2) * ENNReal.ofReal (‖Z‖ ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow]
    have : ‖f'‖ ^ 2 * ‖Z‖ ^ 2 = (‖Z‖ * ‖f'‖) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq, norm_sq_lift_eq hc g f' hf']
  have hZle := norm_sq_test_le hc hb hZae hζb
  set Gn := ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC g p) ^ 2) ∂(ageμ c (-3 / 2))
  set A := ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2) ∂(ageμ c (-3 / 2))
  calc (ENNReal.ofReal c * Gn * ENNReal.ofReal (‖Z‖ ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal c * Gn * (ENNReal.ofReal c * A)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ((ENNReal.ofReal c) ^ 2 * (Gn * A)) ^ (1 / 2 : ℝ) := by
        congr 1; ring
    _ = ((ENNReal.ofReal c) ^ 2) ^ (1 / 2 : ℝ) * (Gn * A) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal c * (Gn * A) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast (ENNReal.ofReal c) 2, ← ENNReal.rpow_mul]
        norm_num

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
