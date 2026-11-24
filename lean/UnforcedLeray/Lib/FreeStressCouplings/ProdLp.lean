import UnforcedLeray.Lib.BochnerTime.Slices
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `L^q(ν × μ; F) ≃ L^q(ν; L^q(μ; F))` (INF10 F1, Fubini isometry)


§4 bypass **B9** and §5 Level F, target **F1**; blueprint units **B0459**, **B0473**, **B0474**
(tex 7698-7812).  The manuscript's phase space is the Bochner space
`Y₂ = L²(ℝ/Pℤ; L²(ℝ³; ℂ³))` (tex 7313-7317, decision D2).  The concrete diagonalisations of
`A = -νΔ` and `B = T₀ - 3/4` act on the joint variable `(τ, y)`, so they need the identification
of the Bochner space with the `L²` space of the product.  This file builds it for
`1 ≤ q < ∞`: `prodLpEquiv : Lp F q (ν.prod μ) ≃ₗᵢ[ℂ] Lp (Lp F q μ) q ν`, `f ↦ (t ↦ f(t, ·))`.

The forward map and the norm identity are `BochnerTime.stronglyMeasurable_toPath_Lq` (INF14 T5,
`Lib/BochnerTime/Slices.lean`).  Surjectivity: the range of an isometry is closed, and it
contains the indicator functions `1_s(t) c` (`c ∈ L^q(μ)`), which span a dense subspace
(Mathlib `Lp.induction`).

## Main results

* `ae_memLp_slice`: the slices of a product `L^q` function are a.e. in `L^q`;
* `ae_eq_prod_iff`: a.e. equality on the product is a.e. equality of a.e. slices;
* `prodLpEquiv`, with `prodLpEquiv_ae` (the slice formula) and `prodLpEquiv_symm_ae`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.FreeStress

open UnforcedLeray.BochnerTime

/-- `2 ≠ ∞`, as an instance for the `L²` case of the results below. -/
instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

variable {τ α F : Type*} [MeasurableSpace τ] [MeasurableSpace α] {ν : Measure τ} {μ : Measure α}
  [NormedAddCommGroup F] {q : ℝ≥0∞}

/-- The slices of a product `L^q` function are a.e. in `L^q`. -/
theorem ae_memLp_slice [SFinite μ] [SFinite ν] [hq1 : Fact (1 ≤ q)] [hq : Fact (q ≠ ∞)]
    {f : τ × α → F} (hf : MemLp f q (ν.prod μ)) : ∀ᵐ t ∂ν, MemLp (fun x => f (t, x)) q μ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1.out).ne'
  set f' : τ × α → F := hf.1.mk f with hf'_def
  have hf' : StronglyMeasurable f' := hf.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[ν.prod μ] f' := hf.1.ae_eq_mk
  have hslices : ∀ᵐ t ∂ν, (fun x => f (t, x)) =ᵐ[μ] fun x => f' (t, x) :=
    Measure.ae_ae_of_ae_prod hff'
  have hm : Measurable fun z : τ × α => ‖f' z‖ₑ ^ q.toReal := hf'.enorm.pow_const _
  have hR : eLpNorm f q (ν.prod μ) ^ q.toReal = ∫⁻ t, ∫⁻ x, ‖f' (t, x)‖ₑ ^ q.toReal ∂μ ∂ν := by
    rw [eLpNorm_congr_ae hff', eLpNorm_rpow_eq_lintegral hq0 hq.out,
      lintegral_prod _ hm.aemeasurable]
  have hfin : ∀ᵐ t ∂ν, ∫⁻ x, ‖f' (t, x)‖ₑ ^ q.toReal ∂μ < ∞ := by
    refine ae_lt_top hm.lintegral_prod_right' ?_
    rw [← hR]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hf.eLpNorm_ne_top
  filter_upwards [hslices, hfin] with t ht htf
  have hmem : MemLp (fun x => f' (t, x)) q μ :=
    ⟨(hf'.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq.out).2 htf⟩
  exact hmem.ae_eq ht.symm

/-- A.e. equality on a product is a.e. equality of a.e. slices (for a.e. strongly measurable
functions). -/
theorem ae_eq_prod_iff [SFinite μ] [SFinite ν] {f g : τ × α → F}
    (hf : AEStronglyMeasurable f (ν.prod μ)) (hg : AEStronglyMeasurable g (ν.prod μ)) :
    f =ᵐ[ν.prod μ] g ↔ ∀ᵐ t ∂ν, (fun x => f (t, x)) =ᵐ[μ] fun x => g (t, x) := by
  have hf' := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hg' := Measure.ae_ae_of_ae_prod hg.ae_eq_mk
  have hset : MeasurableSet {z : τ × α | hf.mk f z = hg.mk g z} :=
    hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk
  constructor
  · intro h
    have h2 : hf.mk f =ᵐ[ν.prod μ] hg.mk g := hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk)
    have h3 := (Measure.ae_prod_iff_ae_ae hset).1 h2
    filter_upwards [hf', hg', h3] with t h1 h2 h3
    have e1 : (fun y => f (t, y)) =ᵐ[μ] fun y => hf.mk f (t, y) := h1
    have e2 : (fun y => g (t, y)) =ᵐ[μ] fun y => hg.mk g (t, y) := h2
    have e3 : (fun y => hf.mk f (t, y)) =ᵐ[μ] fun y => hg.mk g (t, y) := h3
    exact e1.trans (e3.trans e2.symm)
  · intro h
    refine hf.ae_eq_mk.trans (EventuallyEq.trans ?_ hg.ae_eq_mk.symm)
    refine (Measure.ae_prod_iff_ae_ae hset).2 ?_
    filter_upwards [hf', hg', h] with t h1 h2 h3
    have e1 : (fun y => f (t, y)) =ᵐ[μ] fun y => hf.mk f (t, y) := h1
    have e2 : (fun y => g (t, y)) =ᵐ[μ] fun y => hg.mk g (t, y) := h2
    exact e1.symm.trans (h3.trans e2)

variable [NormedSpace ℂ F]

section Equiv

variable [MeasurableSpace.CountablyGenerated α] [SFinite μ] [SFinite ν]
  [TopologicalSpace.SeparableSpace F] [hq1 : Fact (1 ≤ q)] [hq : Fact (q ≠ ∞)]

theorem memLp_toPathLq (f : Lp F q (ν.prod μ)) : MemLp (toPathLq q μ f) q ν := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1.out).ne'
  obtain ⟨hmeas, hnorm⟩ := stronglyMeasurable_toPath_Lq (Lp.memLp f)
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq.out, hnorm]
  exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (Lp.eLpNorm_ne_top f)

theorem toPathLq_add_ae (f g : Lp F q (ν.prod μ)) :
    toPathLq q μ ⇑(f + g) =ᵐ[ν] toPathLq q μ ⇑f + toPathLq q μ ⇑g := by
  filter_upwards [Measure.ae_ae_of_ae_prod (Lp.coeFn_add f g), ae_memLp_slice (Lp.memLp f),
    ae_memLp_slice (Lp.memLp g)] with t ht hft hgt
  rw [Pi.add_apply, toPathLq_congr_ae ht, toPathLq_of_memLp hft, toPathLq_of_memLp hgt,
    ← MemLp.toLp_add hft hgt]
  exact toPathLq_of_memLp (f := ⇑f + ⇑g) (hft.add hgt)

theorem toPathLq_smul_ae (c : ℂ) (f : Lp F q (ν.prod μ)) :
    toPathLq q μ ⇑(c • f) =ᵐ[ν] c • toPathLq q μ ⇑f := by
  filter_upwards [Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c f), ae_memLp_slice (Lp.memLp f)]
    with t ht hft
  rw [Pi.smul_apply, toPathLq_congr_ae ht, toPathLq_of_memLp hft, ← MemLp.toLp_const_smul]
  exact toPathLq_of_memLp (f := c • ⇑f) (hft.const_smul c)

theorem norm_toLp_toPathLq (f : Lp F q (ν.prod μ)) :
    ‖(memLp_toPathLq f).toLp _‖ = ‖f‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1.out).ne'
  have hqr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hq.out⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply ENNReal.rpow_left_injective hqr
  change eLpNorm (toPathLq q μ f) q ν ^ q.toReal = eLpNorm f q (ν.prod μ) ^ q.toReal
  rw [eLpNorm_rpow_eq_lintegral hq0 hq.out]
  exact (stronglyMeasurable_toPath_Lq (Lp.memLp f)).2

/-- The slice map `f ↦ (t ↦ f(t, ·))` as a linear isometry. -/
def curryLpₗᵢ : Lp F q (ν.prod μ) →ₗᵢ[ℂ] Lp (Lp F q μ) q ν where
  toFun f := (memLp_toPathLq f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (toPathLq_add_ae f g)
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (toPathLq_smul_ae c f)
  norm_map' := norm_toLp_toPathLq

theorem curryLpₗᵢ_ae (f : Lp F q (ν.prod μ)) :
    (curryLpₗᵢ f : τ → Lp F q μ) =ᵐ[ν] toPathLq q μ f :=
  (memLp_toPathLq f).coeFn_toLp

/-- The product function `(t, x) ↦ 1_s(t) c(x)`. -/
theorem memLp_indicator_prod {s : Set τ} (hs : MeasurableSet s) (hνs : ν s < ∞)
    (c : Lp F q μ) :
    MemLp (fun z : τ × α => s.indicator (fun _ => (c : α → F) z.2) z.1) q (ν.prod μ) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1.out).ne'
  have hc := (Lp.memLp c)
  have hmeas : AEStronglyMeasurable
      (fun z : τ × α => s.indicator (fun _ => (c : α → F) z.2) z.1) (ν.prod μ) := by
    have h1 : AEStronglyMeasurable (fun z : τ × α => (c : α → F) z.2) (ν.prod μ) :=
      AEStronglyMeasurable.comp_snd hc.1
    have h2 : (fun z : τ × α => s.indicator (fun _ => (c : α → F) z.2) z.1) =
        (s ×ˢ (univ : Set α)).indicator (fun z : τ × α => (c : α → F) z.2) := by
      funext z
      by_cases hz : z.1 ∈ s
      · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ s ×ˢ (univ : Set α) from ⟨hz, trivial⟩)]
      · rw [indicator_of_notMem hz,
          indicator_of_notMem (show z ∉ s ×ˢ (univ : Set α) from fun h => hz h.1)]
    rw [h2]
    exact h1.indicator (hs.prod MeasurableSet.univ)
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq.out]
  have hcf : ∫⁻ x, ‖(c : α → F) x‖ₑ ^ q.toReal ∂μ < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hq.out).1 hc.2
  have heq : (fun z : τ × α => ‖s.indicator (fun _ => (c : α → F) z.2) z.1‖ₑ ^ q.toReal) =
      fun z => s.indicator (fun _ => (1 : ℝ≥0∞)) z.1 * ‖(c : α → F) z.2‖ₑ ^ q.toReal := by
    funext z
    by_cases hzs : z.1 ∈ s
    · rw [indicator_of_mem hzs, indicator_of_mem hzs, one_mul]
    · rw [indicator_of_notMem hzs, indicator_of_notMem hzs, zero_mul, enorm_zero]
      exact ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hq0 hq.out)
  rw [heq, lintegral_prod_mul ((measurable_const.indicator hs).aemeasurable)
    ((AEStronglyMeasurable.enorm hc.1).pow_const _), lintegral_indicator_const hs, one_mul]
  exact ENNReal.mul_lt_top hνs hcf

theorem toPathLq_eq_of_slice {f : τ × α → F} {t : τ} {h : α → F} (hh : MemLp h q μ)
    (heq : (fun x => f (t, x)) = h) : toPathLq q μ f t = hh.toLp h := by
  have hm : MemLp (fun x => f (t, x)) q μ := heq ▸ hh
  rw [toPathLq_of_memLp hm]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun heq x)

theorem curryLpₗᵢ_indicator {s : Set τ} (hs : MeasurableSet s) (hνs : ν s < ∞)
    (c : Lp F q μ) :
    curryLpₗᵢ ((memLp_indicator_prod hs hνs c).toLp _) = indicatorConstLp q hs hνs.ne c := by
  apply Lp.ext
  refine (curryLpₗᵢ_ae _).trans (EventuallyEq.trans ?_ indicatorConstLp_coeFn.symm)
  have hslice := Measure.ae_ae_of_ae_prod (memLp_indicator_prod hs hνs c).coeFn_toLp
  filter_upwards [hslice] with t ht
  rw [toPathLq_congr_ae (g := fun z : τ × α => s.indicator (fun _ => (c : α → F) z.2) z.1) ht]
  by_cases hts : t ∈ s
  · rw [indicator_of_mem hts, toPathLq_eq_of_slice (Lp.memLp c)
      (funext fun x => by simp only [indicator_of_mem hts]), Lp.toLp_coeFn]
  · rw [indicator_of_notMem hts, toPathLq_eq_of_slice (MemLp.zero : MemLp (0 : α → F) q μ)
      (funext fun x => by simp only [indicator_of_notMem hts, Pi.zero_apply]), MemLp.toLp_zero]

theorem curryLpₗᵢ_surjective [CompleteSpace F] :
    Function.Surjective (curryLpₗᵢ : Lp F q (ν.prod μ) →ₗᵢ[ℂ] Lp (Lp F q μ) q ν) := by
  have hclosed : IsClosed (range (curryLpₗᵢ : Lp F q (ν.prod μ) →ₗᵢ[ℂ] Lp (Lp F q μ) q ν)) :=
    curryLpₗᵢ.isometry.isClosedEmbedding.isClosed_range
  intro G
  refine Lp.induction hq.out (fun G => G ∈ range curryLpₗᵢ) ?_ ?_ hclosed G
  · intro c s hs hνs
    refine ⟨(memLp_indicator_prod hs hνs c).toLp _, ?_⟩
    rw [curryLpₗᵢ_indicator hs hνs c]
    rfl
  · rintro f g hf hg - ⟨f', hf'⟩ ⟨g', hg'⟩
    exact ⟨f' + g', by rw [map_add, hf', hg']⟩

/-- **The Fubini isometry** `L^q(ν × μ; F) ≃ L^q(ν; L^q(μ; F))`, `f ↦ (t ↦ f(t, ·))`
(`1 ≤ q < ∞`, `α` countably generated, `μ, ν` s-finite, `F` separable). -/
def prodLpEquiv [CompleteSpace F] : Lp F q (ν.prod μ) ≃ₗᵢ[ℂ] Lp (Lp F q μ) q ν :=
  LinearIsometryEquiv.ofSurjective curryLpₗᵢ curryLpₗᵢ_surjective

theorem prodLpEquiv_apply [CompleteSpace F] (f : Lp F q (ν.prod μ)) :
    prodLpEquiv f = (memLp_toPathLq f).toLp _ := rfl

/-- The slice formula: for a.e. `t`, `(prodLpEquiv f) t = f(t, ·)` a.e. -/
theorem prodLpEquiv_ae [CompleteSpace F] (f : Lp F q (ν.prod μ)) :
    ∀ᵐ t ∂ν, ((prodLpEquiv f t : Lp F q μ) : α → F) =ᵐ[μ] fun x => f (t, x) := by
  filter_upwards [curryLpₗᵢ_ae f, ae_memLp_slice (Lp.memLp f)] with t ht hmem
  change ((curryLpₗᵢ f t : Lp F q μ) : α → F) =ᵐ[μ] _
  rw [ht, toPathLq_of_memLp hmem]
  exact hmem.coeFn_toLp

/-- The slice formula for the inverse: for a.e. `t`, `(prodLpEquiv.symm G)(t, ·) = G t` a.e. -/
theorem prodLpEquiv_symm_ae [CompleteSpace F] (G : Lp (Lp F q μ) q ν) :
    ∀ᵐ t ∂ν, (fun x => (prodLpEquiv.symm G : τ × α → F) (t, x)) =ᵐ[μ] (G t : α → F) := by
  have h := prodLpEquiv_ae (prodLpEquiv.symm G)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with t ht using ht.symm

end Equiv

end UnforcedLeray.FreeStress
