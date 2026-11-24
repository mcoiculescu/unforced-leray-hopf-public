import UnforcedLeray.Short.PartIIa.Sub.N02_3_7
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
From `ZeroWindowBound` applied to `g = opS f_z` (smooth, band-supported in the same band as `f`),
`R = 2L`, exactly as `GCEWin0`:
* the window integrand `winP L g ^ 2` is the indicator of `{|η| ≤ 2L}` of `‖zPrimC g‖²`;
* `(2L)^{1/2} ≤ 2 L^{1/2}`;
* `‖opS f_z p‖ = ‖(opS f p) 1‖ ≤ ‖opS f p‖` pointwise, so the two `L²` integrals are dominated by
  the integrals of `‖opS f‖²` and `η²‖opS f‖²`, which are `zMom c 1 0 f` and `zMom c 1 1 f`.
The band of `opS f_z` is that of `f`: where `opS f_z p ≠ 0` we have `∂_s f_z p ≠ 0`, so `p` is not in
the open complement of the band, where `f_z` vanishes identically near `p`.
So `K = 2C`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

open ZeroGradCutErrorAux

namespace GCEWin1Aux

/-- A function vanishing outside the closed band has zero `s`-derivative outside the band. -/
theorem pdS_eq_zero_of_not_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Profile → E) (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (p : Profile)
    (hp : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) : pdS F p = 0 := by
  have hU : IsOpen ({q : Profile | q.1 < s0} ∪ {q : Profile | s1 < q.1} ∪
      {q : Profile | L < |q.2.2|}) := by
    have h1 : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
    have h2 : IsOpen {q : Profile | s1 < q.1} := isOpen_lt continuous_const continuous_fst
    have h3 : IsOpen {q : Profile | L < |q.2.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))
    exact (h1.union h2).union h3
  have h3 : p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2| := by
    by_contra h'
    push_neg at h'
    exact hp ⟨⟨h'.1, h'.2.1⟩, h'.2.2⟩
  have hpU : p ∈ ({q : Profile | q.1 < s0} ∪ {q : Profile | s1 < q.1} ∪
      {q : Profile | L < |q.2.2|}) := by
    rcases h3 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hev : F =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    by_contra hne
    obtain ⟨h1, h2⟩ := hb q hne
    rcases hq with (hq | hq) | hq
    · exact absurd h1.1 (not_le.2 hq)
    · exact absurd h1.2 (not_le.2 hq)
    · exact absurd h2 (not_le.2 hq)
  unfold pdS
  rw [hev.fderiv_eq (𝕜 := ℝ)]
  simp

/-- The band of `opS F` is the band of `F`. -/
theorem band_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Profile → E) (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∀ p : Profile, opS F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  intro p hp
  by_contra hq
  apply hp
  unfold opS
  rw [pdS_eq_zero_of_not_band F s0 s1 L hb p hq, smul_zero]

/-- Smoothness of `opS F` for smooth `F`. -/
theorem contDiff_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Profile → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (opS F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ F p (1, 0, 0)) :=
    h1.clm_apply contDiff_const
  exact contDiff_fst.smul h2

/-- The first component of the derivative is the derivative of the first component. -/
theorem fderiv_proj1 (f : Profile → MeridC) (hf : Differentiable ℝ f) (p v : Profile) :
    fderiv ℝ (fun r => f r 1) p v = fderiv ℝ f p v 1 := by
  have hd : fderiv ℝ (fun r => f r 1) p =
      ((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ f p) :=
    (((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp p
      (hf p).hasFDerivAt).fderiv
  rw [hd]
  rfl

/-- The `S`-derivative of the component `f_z` is the component of `opS f`. -/
theorem opS_proj1 (f : Profile → MeridC) (hf : Differentiable ℝ f) (p : Profile) :
    opS (fun r => f r 1) p = (opS f p) 1 := by
  unfold opS pdS
  rw [fderiv_proj1 f hf p (1, 0, 0)]
  simp

theorem winP_sq (L : ℝ) (g : Profile → ℂ) (p : Profile) :
    winP L g p ^ 2 = {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p := by
  unfold winP
  by_cases h : |p.2.2| ≤ 2 * L
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

theorem two_rpow_half_le' : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
  calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

end GCEWin1Aux

open GCEWin1Aux in
/-- **Window bound, `S¹` part** (`GCEWin1`). -/
theorem gCEWin1 : UnforcedLeray.Short.PartIIa.ZeroGradCutErrorAux.GCEWin1 := by
  unfold ZeroGradCutErrorAux.GCEWin1
  intro hW
  obtain ⟨C, hC, hB⟩ := hW
  refine ⟨2 * C, by linarith, fun c L f hc hL hf => ?_⟩
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hfz : ContDiff ℝ ∞ (fun r => f r 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hfd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hb1 : ∀ p : Profile, (fun r => f r 1) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    fun p hp => hb p (fun h => hp (by simp [h]))
  -- the band function `g = opS f_z`
  have hgS : ContDiff ℝ ∞ (opS (fun r => f r 1)) := contDiff_opS hfz
  have hgb1 : ∀ p : Profile, opS (fun r => f r 1) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    band_opS (fun r => f r 1) s0 s1 L0 hb1
  have hgb : ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ p : Profile, opS (fun r => f r 1) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
    ⟨s0, s1, L0, hs0, hgb1⟩
  -- the window bound with `R = 2L`
  have hBw := hB c (2 * L) (opS (fun r => f r 1)) hc (by linarith) hgS hgb
  -- pointwise comparison with the `S f` components
  have hcomp : ∀ p : Profile, ‖opS (fun r => f r 1) p‖ ≤ ‖opS f p‖ := fun p => by
    rw [opS_proj1 f hfd p]
    exact PiLp.norm_apply_le (opS f p) 1
  have hsq : ∀ p : Profile, ‖opS (fun r => f r 1) p‖ ^ 2 ≤ ‖opS f p‖ ^ 2 := fun p => by
    have h1 := hcomp p
    have h0 : 0 ≤ ‖opS (fun r => f r 1) p‖ := norm_nonneg _
    nlinarith
  -- integrability
  have hgc : Continuous (opS (fun r => f r 1)) := hgS.continuous
  have hfc : Continuous (opS f) := (contDiff_opS hf.smooth).continuous
  have hbf : ∀ p : Profile, opS f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    band_opS f s0 s1 L0 hb
  have ig : Integrable (fun p : Profile => ‖opS (fun r => f r 1) p‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 0 hgc hgb1
  have ig1 : Integrable (fun p : Profile => p.2.2 ^ 2 * ‖opS (fun r => f r 1) p‖ ^ 2)
      (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1 hgc hgb1
  have iF : Integrable (fun p : Profile => ‖opS f p‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 0 hfc hbf
  have iF1 : Integrable (fun p : Profile => p.2.2 ^ 2 * ‖opS f p‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1 hfc hbf
  have hA : (∫ p, ‖opS (fun r => f r 1) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ (∫ p, ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun p => sq_nonneg _) _ (by norm_num)
    exact integral_mono ig iF hsq
  have hB' : (∫ p, p.2.2 ^ 2 * ‖opS (fun r => f r 1) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ (∫ p, p.2.2 ^ 2 * ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun p => by positivity) _ (by norm_num)
    exact integral_mono ig1 iF1 fun p => mul_le_mul_of_nonneg_left (hsq p) (sq_nonneg _)
  -- the moments `zMom c 1 j f`
  have z10 : zMom c 1 0 f = (∫ p, ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    unfold zMom
    simp [Function.iterate_one]
  have z11 : zMom c 1 1 f = (∫ p, p.2.2 ^ 2 * ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    unfold zMom
    simp [Function.iterate_one]
  have hLHS : (∫ p, winP L (fun r => (opS (fun r' => f r' 1)) r) p ^ 2 ∂(measureH c))
      = ∫ p, {p : Profile | |p.2.2| ≤ 2 * L}.indicator
          (fun p => ‖zPrimC (opS (fun r => f r 1)) p‖ ^ 2) p ∂(measureH c) := by
    simp only [winP_sq]
  rw [hLHS, z10, z11]
  have hpow : (2 * L) ^ (1 / 2 : ℝ) ≤ 2 * L ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hL.le]
    exact mul_le_mul_of_nonneg_right two_rpow_half_le' (Real.rpow_nonneg hL.le _)
  have hr : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL.le _
  calc (∫ p, {p : Profile | |p.2.2| ≤ 2 * L}.indicator
          (fun p => ‖zPrimC (opS (fun r => f r 1)) p‖ ^ 2) p ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ C * (2 * L) ^ (1 / 2 : ℝ) *
          ((∫ p, ‖opS (fun r => f r 1) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖opS (fun r => f r 1) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := hBw
    _ ≤ C * (2 * L ^ (1 / 2 : ℝ)) *
          ((∫ p, ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) (add_le_add hA hB')
          (add_nonneg (Real.rpow_nonneg (integral_nonneg fun p => sq_nonneg _) _)
            (Real.rpow_nonneg (integral_nonneg fun p => by positivity) _))
          (mul_nonneg hC (mul_nonneg (by norm_num) hr))
    _ = 2 * C * L ^ (1 / 2 : ℝ) *
          ((∫ p, ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖opS f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := by ring

end UnforcedLeray.Short.PartIIa
