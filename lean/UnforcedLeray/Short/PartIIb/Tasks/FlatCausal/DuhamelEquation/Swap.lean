import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# Part II-b, task `PartII-b:T12/7/8` (`DeqSwap`): Fubini swap

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Route: replace `G` by a strongly measurable representative `G'` only for measurability (the
slices of `G` and `G'` agree a.e. in `t`, and `flatHeat` only sees a.e. classes). Integrability
of the joint integrand comes from `deqAbsIntegrable` (`PartII-b:T12/7/7`). Then swap
`∫ x ∫ t` into `∫ t ∫ x`, split `x = (s, z)` with `integral_prod`, and identify the inner
`(s, z)`-integral with the pairing `deqPair`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Helper definitions -/

/-- The total weight `Σ_i ‖P_i(x)‖` of the planar transpose at `x`. -/
def deqswS (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) : ℝ :=
  ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖

/-- The Duhamel integrand `(x, t) ↦ 1_{0<t<x.1} (t/x.1)^μ t⁻¹ e^{ν(x.1-t)Δ} G(t,·)(x.2)`. -/
def deqswF (ν : ℝ) (μ : ℂ) (G : CProf) (x : Coord) (t : ℝ) : CMerid :=
  duhamelS.indicator (duhamelBody ν μ G) (x, t)

/-- The integrand of `DeqAbsIntegrable`, as a function of `p = (t, (s, z))`. -/
def deqswB (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (p : ℝ × Coord) : ℝ :=
  if 0 < p.1 ∧ p.1 < p.2.1 then
    ‖(((p.1 / p.2.1 : ℝ) : ℂ) ^ μ)‖ * p.1⁻¹ *
      ‖flatHeat (ν * (p.2.1 - p.1)) (fun w => G (p.1, w)) p.2.2‖ *
      ∑ i : Fin 2, ‖flatTranspose ν μ Ψ p.2 i‖
  else 0

/-- The pairing integrand `(t, x) ↦ Σ_i F(x, t)_i P(x)_i`. -/
def deqswK (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (p : ℝ × Coord) : ℂ :=
  ∑ i : Fin 2, deqswF ν μ G p.2 p.1 i * flatTranspose ν μ Ψ p.2 i

/-! ## Elementary lemmas -/

theorem deqsw_heat_congr {θ : ℝ} {f f' : ℝ × ℝ → CMerid} (z : ℝ × ℝ)
    (h : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), f w = f' w) :
    flatHeat θ f z = flatHeat θ f' z := by
  unfold flatHeat
  refine integral_congr_ae ?_
  filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae h]
    with w hw
  have hw' : f (z - w) = f' (z - w) := hw
  show flatHeatKernel θ w • f (z - w) = flatHeatKernel θ w • f' (z - w)
  rw [hw']

theorem deqsw_slice_ae {G G' : CProf} (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), 0 < t → G (t, y) = G' (t, y) := by
  have h' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      0 < z.1 → G z = G' z := h
  exact Measure.ae_ae_of_ae_prod h'

theorem deqsw_F_ae (ν : ℝ) (μ : ℂ) {G G' : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : Coord, deqswF ν μ G x t = deqswF ν μ G' x t := by
  filter_upwards [deqsw_slice_ae h] with t ht x
  by_cases hm : (x, t) ∈ duhamelS
  · have h0 : 0 < t := (show 0 < t ∧ t < x.1 from hm).1
    have hy : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), G (t, y) = G' (t, y) := by
      filter_upwards [ht] with y hy using hy h0
    unfold deqswF
    rw [indicator_of_mem hm, indicator_of_mem hm]
    unfold duhamelBody
    rw [deqsw_heat_congr (θ := ν * (x.1 - t)) (f := fun z => G (t, z)) (f' := fun z => G' (t, z)) x.2 hy]
  · unfold deqswF
    rw [indicator_of_notMem hm, indicator_of_notMem hm]

theorem deqsw_F_sm (ν : ℝ) (μ : ℂ) {G' : CProf} (hG' : StronglyMeasurable G') :
    StronglyMeasurable (fun p : ℝ × Coord => deqswF ν μ G' p.2 p.1) := by
  have h1 : StronglyMeasurable (fun q : Coord × ℝ => duhamelS.indicator (duhamelBody ν μ G') q) :=
    (stronglyMeasurable_duhamelBody ν μ hG').indicator measurableSet_duhamelS
  exact h1.comp_measurable (measurable_snd.prodMk measurable_fst)

theorem deqsw_K_sm (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) {G' : CProf}
    (hG' : StronglyMeasurable G') (hΨ : IsPlanarSolTest Ψ) :
    StronglyMeasurable (fun p : ℝ × Coord => deqswK ν μ G' Ψ p) := by
  unfold deqswK
  have hcoord : ∀ i : Fin 2, StronglyMeasurable
      (fun p : ℝ × Coord => deqswF ν μ G' p.2 p.1 i * flatTranspose ν μ Ψ p.2 i) := by
    intro i
    have hc : Continuous (fun u : CMerid => u i) := PiLp.continuous_apply 2 _ i
    have hP : Continuous (fun x : Coord => flatTranspose ν μ Ψ x i) :=
      (deqTransposeTest ν μ hΨ i).1
    have h1 : StronglyMeasurable (fun p : ℝ × Coord => deqswF ν μ G' p.2 p.1 i) :=
      hc.comp_stronglyMeasurable (deqsw_F_sm ν μ hG')
    have h2 : StronglyMeasurable (fun p : ℝ × Coord => flatTranspose ν μ Ψ p.2 i) :=
      hP.stronglyMeasurable.comp_measurable measurable_snd
    exact h1.mul h2
  simp only [Fin.sum_univ_two]
  exact (hcoord 0).add (hcoord 1)

theorem deqsw_F_zero (ν : ℝ) (μ : ℂ) (G : CProf) {t : ℝ} {x : Coord}
    (h : ¬ (0 < t ∧ t < x.1)) : deqswF ν μ G x t = 0 := by
  unfold deqswF
  rw [indicator_of_notMem (show (x, t) ∉ duhamelS from h)]

theorem deqsw_K_zero (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (t : ℝ) (x : Coord)
    (h : ¬ (0 < t ∧ t < x.1)) : deqswK ν μ G Ψ (t, x) = 0 := by
  unfold deqswK
  simp [deqsw_F_zero ν μ G h]

theorem deqsw_norm_eq (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (t : ℝ) (x : Coord) :
    ‖deqswF ν μ G x t‖ * deqswS ν μ Ψ x = deqswB ν μ G Ψ (t, x) := by
  by_cases hm : 0 < t ∧ t < x.1
  · have hmem : (x, t) ∈ duhamelS := hm
    unfold deqswF deqswS deqswB
    dsimp only
    rw [indicator_of_mem hmem, if_pos hm]
    unfold duhamelBody
    have hinv : ‖((t⁻¹ : ℝ) : ℂ)‖ = t⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hm.1.le)]
    rw [norm_smul, norm_mul, hinv]
  · have hmem : (x, t) ∉ duhamelS := hm
    unfold deqswF deqswS deqswB
    dsimp only
    rw [indicator_of_notMem hmem, if_neg hm]
    simp

theorem deqsw_sum_le (F : CMerid) (P : Fin 2 → ℂ) :
    ‖∑ i : Fin 2, F i * P i‖ ≤ ‖F‖ * ∑ i : Fin 2, ‖P i‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le F i) (norm_nonneg _)

theorem deqsw_K_bound (ν : ℝ) (μ : ℂ) (G : CProf) (Ψ : Coord → Fin 2 → ℝ) (p : ℝ × Coord) :
    ‖deqswK ν μ G Ψ p‖ ≤ deqswB ν μ G Ψ p := by
  obtain ⟨t, x⟩ := p
  have h := deqsw_sum_le (deqswF ν μ G x t) (fun i => flatTranspose ν μ Ψ x i)
  have h2 := deqsw_norm_eq ν μ G Ψ t x
  unfold deqswK
  exact h.trans (le_of_eq h2)

theorem deqsw_pair_integral (P : Fin 2 → ℂ) (Φ : ℝ → CMerid) (hΦ : Integrable Φ) :
    ∑ i : Fin 2, (∫ t, Φ t) i * P i = ∫ t, ∑ i : Fin 2, Φ t i * P i := by
  set L : CMerid →L[ℂ] ℂ := ∑ i : Fin 2, P i • (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ) with hLdef
  have hL : ∀ u : CMerid, L u = ∑ i : Fin 2, u i * P i := by
    intro u
    simp [hLdef, mul_comm]
  calc ∑ i : Fin 2, (∫ t, Φ t) i * P i = L (∫ t, Φ t) := (hL _).symm
    _ = ∫ t, L (Φ t) := (L.integral_comp_comm hΦ).symm
    _ = ∫ t, ∑ i : Fin 2, Φ t i * P i := integral_congr_ae (Eventually.of_forall fun t => hL _)

/-! ## The swap -/

/-- **Task `PartII-b:T12/7/8`** (`DeqSwap`): Fubini swap for the causal Duhamel pairing. -/
theorem deqSwap : DeqSwap := by
  intro r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  obtain ⟨G', hG's, hGG'⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  have hint : Integrable (deqswB ν μ G Ψ) (volume : Measure (ℝ × Coord)) :=
    deqAbsIntegrable r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  -- joint measurability of the pairing integrand, through the representative `G'`
  have hT := deqsw_F_ae ν μ hGG'
  have hKae : (fun p : ℝ × Coord => deqswK ν μ G' Ψ p) =ᵐ[(volume : Measure (ℝ × Coord))]
      (fun p : ℝ × Coord => deqswK ν μ G Ψ p) := by
    have hq : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure Coord)),
        ∀ x : Coord, deqswF ν μ G x p.1 = deqswF ν μ G' x p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hT
    filter_upwards [hq] with p hp
    unfold deqswK
    rw [(hp p.2).symm]
  have hKm : AEStronglyMeasurable (fun p : ℝ × Coord => deqswK ν μ G Ψ p)
      (volume : Measure (ℝ × Coord)) :=
    (deqsw_K_sm ν μ Ψ hG's hΨ).aestronglyMeasurable.congr hKae
  have hKint : Integrable (fun p : ℝ × Coord => deqswK ν μ G Ψ p)
      (volume : Measure (ℝ × Coord)) :=
    Integrable.mono' hint hKm (Eventually.of_forall fun p => deqsw_K_bound ν μ G Ψ p)
  -- for a.e. `x`, either the planar transpose vanishes at `x` or the slice is integrable
  have hslice : ∀ᵐ x ∂(volume : Measure Coord),
      deqswS ν μ Ψ x = 0 ∨ Integrable (fun t => deqswF ν μ G x t) := by
    have hB : ∀ᵐ x ∂(volume : Measure Coord), Integrable (fun t => deqswB ν μ G Ψ (t, x)) :=
      hint.prod_left_ae
    filter_upwards [hB] with x hx
    by_cases hS : deqswS ν μ Ψ x = 0
    · exact Or.inl hS
    · right
      have hm : AEStronglyMeasurable (fun t => deqswF ν μ G x t) (volume : Measure ℝ) := by
        have h1 : StronglyMeasurable (fun t : ℝ => deqswF ν μ G' x t) :=
          (deqsw_F_sm ν μ hG's).comp_measurable (measurable_id.prodMk measurable_const)
        exact h1.aestronglyMeasurable.congr (by
          filter_upwards [deqsw_F_ae ν μ hGG'] with t ht using (ht x).symm)
      have hdiv : Integrable (fun t => deqswB ν μ G Ψ (t, x) / deqswS ν μ Ψ x) :=
        hx.div_const _
      refine hdiv.mono' hm (Eventually.of_forall fun t => ?_)
      exact ((eq_div_iff hS).2 (deqsw_norm_eq ν μ G Ψ t x)).le
  -- the `x`-slice identity
  have hx_eq : ∀ᵐ x ∂(volume : Measure Coord),
      ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i =
        ∫ t, deqswK ν μ G Ψ (t, x) := by
    filter_upwards [hslice] with x hx
    rcases hx with hS | hI
    · unfold deqswS at hS
      have hP : ∀ i, flatTranspose ν μ Ψ x i = 0 := fun i =>
        norm_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg _)).1 hS i
          (Finset.mem_univ i))
      simp [deqswK, hP]
    · rw [flatDuhamel_eq_integral]
      exact deqsw_pair_integral (fun i => flatTranspose ν μ Ψ x i) (fun t => deqswF ν μ G x t) hI
  have hLHS : ∫ x, ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i =
      ∫ x, ∫ t, deqswK ν μ G Ψ (t, x) := integral_congr_ae hx_eq
  rw [hLHS]
  -- Fubini: swap the order of integration
  have hsw : Integrable (Function.uncurry fun (x : Coord) (t : ℝ) => deqswK ν μ G Ψ (t, x))
      ((volume : Measure Coord).prod (volume : Measure ℝ)) := hKint.swap
  rw [integral_integral_swap hsw]
  -- the integrand vanishes for `t ≤ 0`
  have hK0 : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → ∫ x : Coord, deqswK ν μ G Ψ (t, x) = 0 := by
    intro t ht
    have h0 : ∀ x : Coord, deqswK ν μ G Ψ (t, x) = 0 := fun x =>
      deqsw_K_zero ν μ G Ψ t x (fun h => ht (mem_Ioi.2 h.1))
    simp [h0]
  have hL : ∫ t : ℝ, ∫ x : Coord, deqswK ν μ G Ψ (t, x) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Coord, deqswK ν μ G Ψ (t, x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hK0).symm
  rw [hL]
  have ht_int : ∀ᵐ t ∂(volume : Measure ℝ),
      Integrable (fun x : Coord => deqswK ν μ G Ψ (t, x)) := hKint.prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae ht_int, ae_restrict_mem measurableSet_Ioi]
    with t hti htpos
  have ht : 0 < t := htpos
  have hvol : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    rfl
  rw [hvol] at hti ⊢
  rw [integral_prod _ hti]
  -- the inner `(s, z)`-integral is the pairing `deqPair`, restricted to `s > t`
  have hin : ∀ s : ℝ, ∫ z : ℝ × ℝ, deqswK ν μ G Ψ (t, (s, z)) =
      (Ioi t).indicator (fun s' : ℝ => (((t / s' : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
        deqPair ν μ (fun z => G (t, z)) Ψ t s') s := by
    intro s
    by_cases hts : t < s
    · rw [indicator_of_mem (mem_Ioi.2 hts)]
      have hpt : ∀ z : ℝ × ℝ, deqswK ν μ G Ψ (t, (s, z)) =
          (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
            ∑ i : Fin 2, flatHeat (ν * (s - t)) (fun w => G (t, w)) z i *
              flatTranspose ν μ Ψ (s, z) i := by
        intro z
        have hmem : ((s, z), t) ∈ duhamelS := (show 0 < t ∧ t < s from ⟨ht, hts⟩)
        simp only [deqswK, deqswF, indicator_of_mem hmem, duhamelBody, PiLp.smul_apply,
          smul_eq_mul, Finset.mul_sum, mul_assoc]
      simp_rw [hpt]
      rw [integral_const_mul]
      rfl
    · rw [indicator_of_notMem (fun h => hts (mem_Ioi.1 h))]
      have hz : ∀ z : ℝ × ℝ, deqswK ν μ G Ψ (t, (s, z)) = 0 := fun z =>
        deqsw_K_zero ν μ G Ψ t (s, z) (fun h => hts h.2)
      simp [hz]
  simp only [hin]
  rw [integral_indicator measurableSet_Ioi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  ring

end UnforcedLeray.Short.IIb
