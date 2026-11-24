import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtInvH
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4

/-!
# `PartII-a:N01/9/2/3/2`: `InnerZetaUnwind`

Source `the November 2 reference manuscript` lines 1669-1676.
With `ζ = s^{1/2}Φ` (a.e.), the `H`-pairing is `⟪ζ, f⟫ = ∫_{(0,∞)×cell} Σᵢ (fᵢ(cellPtInv x)/s) Φᵢ(x)`:
the weight `s^{-3/2}` against `s^{1/2}` leaves `s^{-1}`; `cellPtInv` is the Lebesgue-measure
preserving recentring of `q` from `[-c/2,c/2)` to `(0,c]` (`Φ` is `c`-periodic in `q`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure weightH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv)

/-- The inverse recentring of one `q`-coordinate: `q ↦ q` for `q > 0`, `q ↦ q + c` otherwise. -/
def ctInvT (c q : ℝ) : ℝ := if 0 < q then q else q + c

theorem ctInvT_measurable (c : ℝ) : Measurable (ctInvT c) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_id
    (measurable_id.add_const c)

theorem cellPtInv_eq_prodMap (c : ℝ) :
    cellPtInv c = Prod.map id (Prod.map (ctInvT c) id) := by
  funext x
  obtain ⟨s, q, η⟩ := x
  rfl

theorem ctInvT_ctT {c q : ℝ} (hq : q ∈ Ioc (0 : ℝ) c) :
    ctInvT c (UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT c q) = q := by
  obtain ⟨hq1, hq2⟩ := hq
  unfold ctInvT UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT
  split_ifs <;> first | (exfalso; linarith) | ring

theorem ctInvT_map {c : ℝ} (hc : 0 < c) :
    Measure.map (ctInvT c) (volume.restrict (Ico (-c / 2) (c / 2))) =
      volume.restrict (Ioc (0 : ℝ) c) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF (ctInvT_measurable c)]
  have h : ∫⁻ q in Ioc (0 : ℝ) c, F (ctInvT c (UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT c q))
      = ∫⁻ q in Ico (-c / 2) (c / 2), F (ctInvT c q) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.ct_lintegral_T hc (fun q => F (ctInvT c q))
  rw [← h]
  exact setLIntegral_congr_fun measurableSet_Ioc fun q hq => by rw [ctInvT_ctT hq]

theorem cellPtInv_map {c : ℝ} (hc : 0 < c) :
    Measure.map (cellPtInv c) (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)) =
      cellMeasure c := by
  have hL : (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) :
      Measure (ℝ × (ℝ × ℝ))) =
      (volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume.restrict (Set.univ : Set ℝ))) := by
    unfold UnforcedLeray.B0579.cell
    rw [neg_div, Measure.volume_eq_prod, Measure.volume_eq_prod, Measure.prod_restrict,
      Measure.prod_restrict]
  have hR : cellMeasure c =
      (volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod (volume.restrict (Set.univ : Set ℝ))) := by
    unfold cellMeasure UnforcedLeray.B0220.cell
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod, Measure.prod_restrict,
      Measure.prod_restrict]
  rw [hL, hR, cellPtInv_eq_prodMap,
    ← Measure.map_prod_map _ _ measurable_id ((ctInvT_measurable c).prodMap measurable_id),
    Measure.map_id, ← Measure.map_prod_map _ _ (ctInvT_measurable c) measurable_id, Measure.map_id,
    ctInvT_map hc]

/-- The kernel `Σᵢ (fᵢ(p)/s) Φᵢ(p)` on the profile cell. -/
def unwindKernel (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f : Profile → MeridC) (p : Profile) : ℂ :=
  ∑ i : Fin 2, (f p i / (p.1 : ℂ)) * (Φ p.1 p.2 i : ℂ)

theorem integrand_cell (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f : Profile → MeridC) (a : Profile)
    (ha : 0 < a.1) :
    (weightH a).toReal • inner ℂ (UnforcedLeray.Short.PartIIa.N01.zetaFn Φ a) (f a) =
      unwindKernel Φ f a := by
  have hw : (weightH a).toReal = a.1 ^ (-(3 / 2 : ℝ)) := by
    unfold weightH
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _)
  have hk : a.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt a.1 = a.1⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha, show (-(3 / 2 : ℝ) + 1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hkC : ((a.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt a.1 : ℝ) : ℂ) = ((a.1 : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, hk, Complex.ofReal_inv]
  rw [hw]
  unfold UnforcedLeray.Short.PartIIa.N01.zetaFn unwindKernel
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, Complex.real_smul,
    map_mul, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (((Φ a.1 a.2 0 : ℝ) : ℂ) * f a 0 + ((Φ a.1 a.2 1 : ℝ) : ℂ) * f a 1) * hkC

theorem innerZetaUnwind : UnforcedLeray.Short.PartIIa.N01.InnerZetaUnwind := by
  intro c hc Φ hΦ ζ hζ f
  have hcell_pos : ∀ᵐ a ∂(cellMeasure c), 0 < a.1 := by
    unfold cellMeasure
    filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with a ha
    exact ha.1
  have hcell_ne : ∀ᵐ a ∂(cellMeasure c), weightH a ≠ 0 := by
    filter_upwards [hcell_pos] with a ha
    unfold weightH
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha _)).ne'
  have hw : Measurable weightH := UnforcedLeray.B0220.measurable_weightH
  have hζcell : ∀ᵐ a ∂(cellMeasure c), ζ a = UnforcedLeray.Short.PartIIa.N01.zetaFn Φ a :=
    (withDensity_absolutelyContinuous' hw.aemeasurable hcell_ne).ae_le hζ
  have hpoint : (fun a => (weightH a).toReal • inner ℂ (ζ a) (f a)) =ᵐ[cellMeasure c]
      unwindKernel Φ f := by
    filter_upwards [hζcell, hcell_pos] with a h1 h2
    rw [h1]
    exact integrand_cell Φ f a h2
  have hIntH : Integrable (fun a => inner ℂ (ζ a) (f a)) (measureH c) := L2.integrable_inner ζ f
  have hIntC : Integrable (fun a => (weightH a).toReal • inner ℂ (ζ a) (f a)) (cellMeasure c) := by
    have h := hIntH
    unfold measureH at h
    rw [integrable_withDensity_iff_integrable_smul' hw
      (UnforcedLeray.B0226.ae_weightH_lt_top c)] at h
    exact h
  have hKint : Integrable (unwindKernel Φ f) (cellMeasure c) := hIntC.congr hpoint
  have hmap : Measure.map (cellPtInv c)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)) = cellMeasure c :=
    cellPtInv_map hc
  have hmp : MeasurePreserving (cellPtInv c)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)) (cellMeasure c) :=
    ⟨measurable_cellPtInv c, hmap⟩
  have hper : ∀ (x : Chart) (i : Fin 2), Φ (cellPtInv c x).1 (cellPtInv c x).2 i = Φ x.1 x.2 i := by
    rintro ⟨s, q, η⟩ i
    by_cases h : 0 < q
    · have e : (if 0 < q then q else q + c) = q := if_pos h
      simp only [cellPtInv, e]
    · have e : (if 0 < q then q else q + c) = q + c := if_neg h
      simp only [cellPtInv, e]
      exact hΦ.periodic s (q, η) i
  have hfun : (fun p : Chart => ∑ i : Fin 2, (UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c
      (f : Profile → MeridC) p i / (p.1 : ℂ)) * (Φ p.1 p.2 i : ℂ)) =
      unwindKernel Φ f ∘ cellPtInv c := by
    funext x
    simp only [Function.comp_apply, unwindKernel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF, ← hper x i]
    rfl
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hfun]
    exact (hmp.integrable_comp hKint.aestronglyMeasurable).2 hKint
  · rw [L2.inner_def]
    have e1 : ∫ a, inner ℂ (ζ a) (f a) ∂(measureH c) =
        ∫ a, (weightH a).toReal • inner ℂ (ζ a) (f a) ∂(cellMeasure c) := by
      unfold measureH
      exact integral_withDensity_eq_integral_toReal_smul hw
        (UnforcedLeray.B0226.ae_weightH_lt_top c) _
    have e2 : ∫ a, (weightH a).toReal • inner ℂ (ζ a) (f a) ∂(cellMeasure c) =
        ∫ a, unwindKernel Φ f a ∂(cellMeasure c) := integral_congr_ae hpoint
    have e3 : ∫ a, unwindKernel Φ f a ∂(cellMeasure c) =
        ∫ x, unwindKernel Φ f (cellPtInv c x)
          ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)) := by
      rw [← hmap]
      exact integral_map (measurable_cellPtInv c).aemeasurable
        (by rw [hmap]; exact hKint.aestronglyMeasurable)
    rw [e1, e2, e3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (congrFun hfun x).symm)

end UnforcedLeray.Short.PartIIa.N01
