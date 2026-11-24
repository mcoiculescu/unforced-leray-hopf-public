import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of

/-!
# `ZetaPhiSolenoidal` (organizer task `PartIII-b:C/flatset/col/7/3/4`)

Source of record `the November 2 reference manuscript` lines 1650-1656, 1684-1689.

For a flat test `Φ`, the class `ζ_Φ = s^{1/2}Φ` lies in `H = L²(s^{-3/2} ds dq dη)` and is
orthogonal to every gradient `cgrad 0 ψ = (∂_qψ, ∂_ηψ)` of a profile test `ψ`: the
`H`-inner product is `∫ s^{-1}(Φ·∇ψ)`, which vanishes slice by slice in `s` because `div Φ = 0`
and the `(q,η)`-integration by parts closes (`q`-periodicity, compact `η`-support).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile cell weightH cellMeasure)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0579 (IsCylTest pd)
open UnforcedLeray.Short.IIIa (IsFlatTest)
open UnforcedLeray.Short.PartIIa (cgrad solenoidalHC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest Deps)

/-- Measurability of the cell `s > 0`, `q ∈ (0,c]`, `η ∈ ℝ`. -/
theorem measurableSet_cell' (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)

/-- Support of a flat test: a `s₁ > 0` band and an `η`-cutoff `R`. -/
theorem flat_support {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    ∃ s1 s2 R : ℝ, 0 < s1 ∧ ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2),
      ¬ (s ∈ Icc s1 s2 ∧ x.2 ∈ Icc (-R) R) → Φ s x i = 0 := by
  obtain ⟨s1, s2, R, hs1, h⟩ := hΦ.support
  refine ⟨s1, s2, R, hs1, fun s x i hx => h s x i ?_⟩
  rcases lt_or_ge s s1 with h1 | h1
  · exact Or.inl h1
  rcases lt_or_ge s2 s with h2 | h2
  · exact Or.inr (Or.inl h2)
  rcases lt_or_ge R |x.2| with h3 | h3
  · exact Or.inr (Or.inr h3)
  exact (hx ⟨⟨h1, h2⟩, abs_le.1 h3⟩).elim

/-- Integrability over the profile cell of a continuous function vanishing off a compact box. -/
theorem integrableOn_cell_of_zero {c s1 s2 R : ℝ} {g : Profile → ℝ}
    (hg : ContinuousOn g (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)))
    (hz : ∀ p : Profile, ¬ (p.1 ∈ Icc s1 s2 ∧ p.2.2 ∈ Icc (-R) R) → g p = 0) :
    IntegrableOn g (cell c) := by
  have hK : IsCompact (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  refine (hg.integrableOn_compact hK).of_forall_sdiff_eq_zero (measurableSet_cell' c) ?_
  rintro p ⟨hp1, hp2⟩
  apply hz p
  rintro h
  apply hp2
  exact ⟨h.1, ⟨Ioc_subset_Icc_self hp1.2.1, h.2⟩⟩

/-- Integrability on the `(q,η)`-window `(0,c] × ℝ` of a continuous function vanishing for
large `|η|`. -/
theorem integrableOn_window {c : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hR : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    IntegrableOn g (Ioc 0 c ×ˢ univ) := by
  obtain ⟨R, hR⟩ := hR
  have hK : IsCompact (Icc 0 c ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  refine (hg.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
    (measurableSet_Ioc.prod MeasurableSet.univ) ?_
  rintro x ⟨hx1, hx2⟩
  apply hR x
  by_contra h
  exact hx2 ⟨Ioc_subset_Icc_self hx1.1, abs_le.1 (not_lt.1 h)⟩

/-- `∫_{(0,c]×ℝ} ∂_q w = 0` by periodicity in `q`. -/
theorem integral_pd0_window {c : ℝ} (hc : 0 < c) {w : ℝ × ℝ → ℝ} (hw : IsCylTest c w) :
    ∫ x in Ioc 0 c ×ˢ univ, pd 0 w x = 0 := by
  have hint := integrableOn_window (c := c) (hw.pd 0).continuous (hw.pd 0).band
  unfold IntegrableOn at hint
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun η => ?_)).trans (integral_zero _ _)
  rw [← intervalIntegral.integral_of_le hc.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _ => UnforcedLeray.B0579.hasDerivAt_fst hw.differentiable q η)
      (((hw.pd 0).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
  have h : w (c, η) = w (0, η) := by
    have := hw.periodic (0, η)
    simpa using this
  simp [h]

/-- `∫_{(0,c]×ℝ} ∂_η w = 0` by compact support in `η`. -/
theorem integral_pd1_window {c : ℝ} {w : ℝ × ℝ → ℝ} (hw : IsCylTest c w) :
    ∫ x in Ioc 0 c ×ˢ univ, pd 1 w x = 0 := by
  have hint := integrableOn_window (c := c) (hw.pd 1).continuous (hw.pd 1).band
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (integral_zero _ _)
  rw [Measure.restrict_univ]
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun η => UnforcedLeray.B0579.hasDerivAt_snd hw.differentiable q η)
    (((hw.pd 1).continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      ((hw.pd 1).hasCompactSupport_slice q))
    ((hw.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (hw.hasCompactSupport_slice q))

/-- Slice derivative in `q` of a profile function is the profile derivative `∂_q`. -/
theorem pd0_slice {ψ : Profile → ℝ} (hψ : Differentiable ℝ ψ) (s : ℝ) (y : ℝ × ℝ) :
    pd 0 (fun z => ψ (s, z)) y = Axi.dQ ψ (s, y) := by
  have h : HasFDerivAt (fun z : ℝ × ℝ => ψ (s, z))
      ((fderiv ℝ ψ (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
    (hψ (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [UnforcedLeray.B0579.pd, h.fderiv]
  rfl

/-- Slice derivative in `η` of a profile function is the profile derivative `∂_η`. -/
theorem pd1_slice {ψ : Profile → ℝ} (hψ : Differentiable ℝ ψ) (s : ℝ) (y : ℝ × ℝ) :
    pd 1 (fun z => ψ (s, z)) y = Axi.dEta ψ (s, y) := by
  have h : HasFDerivAt (fun z : ℝ × ℝ => ψ (s, z))
      ((fderiv ℝ ψ (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
    (hψ (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [UnforcedLeray.B0579.pd, h.fderiv]
  rfl

/-- Each `s`-slice of the flat pairing `∫ (Φ·∇ψ)` vanishes (integration by parts on `(0,c]×ℝ`,
using `div Φ = 0`). -/
theorem slice_integral_zero {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : IsFlatTest c Φ) {ψ : Profile → ℝ} (hψ : IsProfileTest c ψ) (s : ℝ) :
    ∫ y in Ioc 0 c ×ˢ univ, (Φ s y 0 * Axi.dQ ψ (s, y) + Φ s y 1 * Axi.dEta ψ (s, y)) = 0 := by
  obtain ⟨s1, s2, R, hs1, hz⟩ := flat_support hΦ
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hslice : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((s, z) : Profile)) :=
    contDiff_const.prodMk contDiff_id
  have hψs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ψ (s, z)) := hψ.smooth.comp hslice
  have hΦs0 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Φ s z 0) := (hΦ.smooth 0).comp hslice
  have hΦs1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Φ s z 1) := (hΦ.smooth 1).comp hslice
  have hψsd : Differentiable ℝ (fun z : ℝ × ℝ => ψ (s, z)) := hψs.differentiable (by simp)
  have hΦ0d : Differentiable ℝ (fun z : ℝ × ℝ => Φ s z 0) := hΦs0.differentiable (by simp)
  have hΦ1d : Differentiable ℝ (fun z : ℝ × ℝ => Φ s z 1) := hΦs1.differentiable (by simp)
  have e : ∀ y : ℝ × ℝ, ψ (s, (y.1 + c, y.2)) = ψ (s, y) := fun y => by
    have h := hψ.periodic (s, y)
    dsimp only at h
    exact h
  have hw0 : IsCylTest c (fun y : ℝ × ℝ => Φ s y 0 * ψ (s, y)) :=
    { smooth := hΦs0.mul hψs
      periodic := fun y => by
        rw [hΦ.periodic, e y]
      band := ⟨R, fun y hy => by
        rw [hz s y 0 (fun h => absurd (abs_le.2 (Set.mem_Icc.1 h.2)) (not_le.2 hy)), zero_mul]⟩ }
  have hw1 : IsCylTest c (fun y : ℝ × ℝ => Φ s y 1 * ψ (s, y)) :=
    { smooth := hΦs1.mul hψs
      periodic := fun y => by
        rw [hΦ.periodic, e y]
      band := ⟨R, fun y hy => by
        rw [hz s y 1 (fun h => absurd (abs_le.2 (Set.mem_Icc.1 h.2)) (not_le.2 hy)), zero_mul]⟩ }
  have key : ∀ y : ℝ × ℝ, Φ s y 0 * Axi.dQ ψ (s, y) + Φ s y 1 * Axi.dEta ψ (s, y) =
      pd 0 (fun y => Φ s y 0 * ψ (s, y)) y + pd 1 (fun y => Φ s y 1 * ψ (s, y)) y := by
    intro y
    have e0 : pd 0 (fun y => Φ s y 0 * ψ (s, y)) y =
        pd 0 (fun y => Φ s y 0) y * ψ (s, y) + Φ s y 0 * pd 0 (fun z => ψ (s, z)) y :=
      UnforcedLeray.B0579.pd_mul hΦ0d hψsd 0 y
    have e1 : pd 1 (fun y => Φ s y 1 * ψ (s, y)) y =
        pd 1 (fun y => Φ s y 1) y * ψ (s, y) + Φ s y 1 * pd 1 (fun z => ψ (s, z)) y :=
      UnforcedLeray.B0579.pd_mul hΦ1d hψsd 1 y
    rw [e0, e1, pd0_slice hψd s y, pd1_slice hψd s y]
    linear_combination (-(ψ (s, y))) * hΦ.divFree s y
  have hI0 : IntegrableOn (fun y => pd 0 (fun y => Φ s y 0 * ψ (s, y)) y)
      (Ioc 0 c ×ˢ univ) := integrableOn_window (hw0.pd 0).continuous (hw0.pd 0).band
  have hI1 : IntegrableOn (fun y => pd 1 (fun y => Φ s y 1 * ψ (s, y)) y)
      (Ioc 0 c ×ˢ univ) := integrableOn_window (hw1.pd 1).continuous (hw1.pd 1).band
  calc ∫ y in Ioc 0 c ×ˢ univ, (Φ s y 0 * Axi.dQ ψ (s, y) + Φ s y 1 * Axi.dEta ψ (s, y))
      = ∫ y in Ioc 0 c ×ˢ univ, (pd 0 (fun y => Φ s y 0 * ψ (s, y)) y
          + pd 1 (fun y => Φ s y 1 * ψ (s, y)) y) :=
        setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) (fun y _ => key y)
    _ = 0 := by
        rw [integral_add hI0 hI1, integral_pd0_window hc hw0, integral_pd1_window hw1, add_zero]

/-- The real integrand `s^{-3/2}·(Dψ·ζ)` of the `H`-pairing of `cgrad 0 ψ` with `ζ_Φ`. -/
def gZ (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (ψ : Profile → ℝ) (p : Profile) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * (Axi.dQ ψ p * (Real.sqrt p.1 * Φ p.1 p.2 0) +
    Axi.dEta ψ p * (Real.sqrt p.1 * Φ p.1 p.2 1))

theorem gZ_slice {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    {ψ : Profile → ℝ} (hψ : IsProfileTest c ψ) (s : ℝ) :
    ∫ y in Ioc 0 c ×ˢ univ, gZ Φ ψ (s, y) = 0 := by
  have hfac : ∀ y : ℝ × ℝ, gZ Φ ψ (s, y) = (s ^ (-(3 / 2 : ℝ)) * Real.sqrt s) *
      (Φ s y 0 * Axi.dQ ψ (s, y) + Φ s y 1 * Axi.dEta ψ (s, y)) := fun y => by
    simp only [gZ]
    ring
  calc ∫ y in Ioc 0 c ×ˢ univ, gZ Φ ψ (s, y)
      = ∫ y in Ioc 0 c ×ˢ univ, (s ^ (-(3 / 2 : ℝ)) * Real.sqrt s) *
          (Φ s y 0 * Axi.dQ ψ (s, y) + Φ s y 1 * Axi.dEta ψ (s, y)) :=
        setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) (fun y _ => hfac y)
    _ = 0 := by
        rw [integral_const_mul, slice_integral_zero hc hΦ hψ s, mul_zero]

theorem gZ_contOn {c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    {ψ : Profile → ℝ} (hψ : IsProfileTest c ψ) (hs1 : 0 < s1) :
    ContinuousOn (gZ Φ ψ) (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) := by
  have hA : ContinuousOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)))
      (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    continuous_fst.continuousOn.rpow_const (fun p hp =>
      Or.inl (lt_of_lt_of_le hs1 (Set.mem_Icc.1 hp.1).1).ne')
  have hdQ : Continuous (fun p : Profile => Axi.dQ ψ p) :=
    (hψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdE : Continuous (fun p : Profile => Axi.dEta ψ p) :=
    (hψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsq : Continuous (fun p : Profile => Real.sqrt p.1) :=
    Real.continuous_sqrt.comp continuous_fst
  have hΦ0 : Continuous (fun p : Profile => Φ p.1 p.2 0) := (hΦ.smooth 0).continuous
  have hΦ1 : Continuous (fun p : Profile => Φ p.1 p.2 1) := (hΦ.smooth 1).continuous
  have hB : Continuous (fun p : Profile => Axi.dQ ψ p * (Real.sqrt p.1 * Φ p.1 p.2 0) +
      Axi.dEta ψ p * (Real.sqrt p.1 * Φ p.1 p.2 1)) :=
    (hdQ.mul (hsq.mul hΦ0)).add (hdE.mul (hsq.mul hΦ1))
  exact hA.mul hB.continuousOn

theorem gZ_zero_off {s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hz : ∀ (s : ℝ) (x : ℝ × ℝ) (i : Fin 2), ¬ (s ∈ Icc s1 s2 ∧ x.2 ∈ Icc (-R) R) → Φ s x i = 0)
    (ψ : Profile → ℝ) (p : Profile) (h : ¬ (p.1 ∈ Icc s1 s2 ∧ p.2.2 ∈ Icc (-R) R)) :
    gZ Φ ψ p = 0 := by
  simp [gZ, hz p.1 p.2 0 h, hz p.1 p.2 1 h]

/-- The `s`-integrated pairing of `gZ` vanishes (Fubini over `s` and the slice lemma). -/
theorem gZ_integral_zero {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : IsFlatTest c Φ) {ψ : Profile → ℝ} (hψ : IsProfileTest c ψ) :
    ∫ p in cell c, gZ Φ ψ p = 0 := by
  obtain ⟨s1, s2, R, hs1, hz⟩ := flat_support hΦ
  have hint : IntegrableOn (gZ Φ ψ) (cell c) :=
    integrableOn_cell_of_zero (gZ_contOn (c := c) (s1 := s1) (s2 := s2) (R := R) hΦ hψ hs1)
      (fun p hp => gZ_zero_off hz ψ p hp)
  have hint' : IntegrableOn (gZ Φ ψ) (Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hint
  have hgoal : ∫ p in cell c, gZ Φ ψ p = ∫ x in Ioi (0 : ℝ), ∫ y in Ioc 0 c ×ˢ univ, gZ Φ ψ (x, y) := by
    rw [cell, Measure.volume_eq_prod]
    exact setIntegral_prod _ hint'
  rw [hgoal]
  calc ∫ x in Ioi (0 : ℝ), ∫ y in Ioc 0 c ×ˢ univ, gZ Φ ψ (x, y)
      = ∫ x in Ioi (0 : ℝ), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi (fun s _ => gZ_slice hc hΦ hψ s)
    _ = 0 := by simp

/-- The complex-valued pairing of `cgrad 0 ψ` with `ζ_Φ` at a point. -/
theorem inner_cgrad_zeta (ψ : Profile → ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (a : Profile) :
    inner ℂ (cgrad 0 ψ a) (zetaPhi Φ a) =
      ((Axi.dQ ψ a * (Real.sqrt a.1 * Φ a.1 a.2 0) +
        Axi.dEta ψ a * (Real.sqrt a.1 * Φ a.1 a.2 1) : ℝ) : ℂ) := by
  unfold cgrad zetaPhi
  simp [Deps, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem zetaPhi_continuous {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    Continuous (zetaPhi Φ) := by
  unfold zetaPhi
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_sqrt.comp continuous_fst).mul (hΦ.smooth i).continuous)

/-- `ζ_Φ` lies in `H`. -/
theorem memLp_zetaPhi {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) :
    MemLp (zetaPhi Φ) 2 (measureH c) := by
  obtain ⟨s1, s2, R, hs1, hz⟩ := flat_support hΦ
  rw [memLp_two_iff_integrable_sq_norm (zetaPhi_continuous hΦ).aestronglyMeasurable]
  rw [measureH, integrable_withDensity_iff_integrable_smul'
    UnforcedLeray.B0220.measurable_weightH (UnforcedLeray.B0226.ae_weightH_lt_top c)]
  have hK : ContinuousOn (fun a : Profile => a.1 ^ (-(3 / 2 : ℝ)) *
      (a.1 * (Φ a.1 a.2 0 ^ 2 + Φ a.1 a.2 1 ^ 2))) (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) := by
    have hA : ContinuousOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)))
        (Icc s1 s2 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
      continuous_fst.continuousOn.rpow_const (fun p hp =>
        Or.inl (lt_of_lt_of_le hs1 (Set.mem_Icc.1 hp.1).1).ne')
    have hB : Continuous (fun p : Profile => p.1 * (Φ p.1 p.2 0 ^ 2 + Φ p.1 p.2 1 ^ 2)) :=
      continuous_fst.mul (((hΦ.smooth 0).continuous.pow 2).add ((hΦ.smooth 1).continuous.pow 2))
    exact hA.mul hB.continuousOn
  have hG : IntegrableOn (fun a : Profile => a.1 ^ (-(3 / 2 : ℝ)) *
      (a.1 * (Φ a.1 a.2 0 ^ 2 + Φ a.1 a.2 1 ^ 2))) (cell c) := by
    refine integrableOn_cell_of_zero hK (fun p hp => ?_)
    rw [hz p.1 p.2 0 hp, hz p.1 p.2 1 hp]
    simp
  show IntegrableOn _ (cell c)
  refine IntegrableOn.congr_fun hG ?_ (measurableSet_cell' c)
  intro a ha
  have ha0 : 0 < a.1 := ha.1
  have hw : (weightH a).toReal = a.1 ^ (-(3 / 2 : ℝ)) := by
    unfold weightH
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg ha0.le _)
  have hnorm : ‖zetaPhi Φ a‖ ^ 2 = a.1 * (Φ a.1 a.2 0 ^ 2 + Φ a.1 a.2 1 ^ 2) := by
    unfold zetaPhi
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt ha0.le]
    ring
  simp only
  rw [hw, hnorm, smul_eq_mul]

/-- Orthogonality of `ζ_Φ` to one generator `cgrad 0 ψ` of `solenoidalHC 0 c`. -/
theorem gen_inner_zero {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    {ψ : Profile → ℝ} (hψ : IsProfileTest c ψ) (hu : MemLp (cgrad 0 ψ) 2 (measureH c))
    (hζ : MemLp (zetaPhi Φ) 2 (measureH c)) :
    inner ℂ (hu.toLp (cgrad 0 ψ)) (hζ.toLp (zetaPhi Φ)) = (0 : ℂ) := by
  have hae : (fun a : Profile => inner ℂ ((hu.toLp (cgrad 0 ψ) : Profile → MeridC) a)
      ((hζ.toLp (zetaPhi Φ) : Profile → MeridC) a)) =ᵐ[measureH c]
      (fun a : Profile => ((Axi.dQ ψ a * (Real.sqrt a.1 * Φ a.1 a.2 0) +
        Axi.dEta ψ a * (Real.sqrt a.1 * Φ a.1 a.2 1) : ℝ) : ℂ)) := by
    filter_upwards [hu.coeFn_toLp, hζ.coeFn_toLp] with a h1 h2
    rw [h1, h2, inner_cgrad_zeta]
  have hpt : ∀ a ∈ cell c, (weightH a).toReal • ((Axi.dQ ψ a * (Real.sqrt a.1 * Φ a.1 a.2 0) +
        Axi.dEta ψ a * (Real.sqrt a.1 * Φ a.1 a.2 1) : ℝ) : ℂ) = ((gZ Φ ψ a : ℝ) : ℂ) := by
    intro a ha
    have ha0 : 0 < a.1 := ha.1
    have hw : (weightH a).toReal = a.1 ^ (-(3 / 2 : ℝ)) := by
      unfold weightH
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg ha0.le _)
    rw [hw, Complex.real_smul]
    unfold gZ
    push_cast
    ring
  rw [L2.inner_def, integral_congr_ae hae, measureH,
    integral_withDensity_eq_integral_toReal_smul UnforcedLeray.B0220.measurable_weightH
      (UnforcedLeray.B0226.ae_weightH_lt_top c), cellMeasure,
    setIntegral_congr_fun (measurableSet_cell' c) hpt, integral_complex_ofReal,
    gZ_integral_zero hc hΦ hψ]
  simp

/-- **Main theorem.** -/
theorem zetaPhiSolenoidal : ZetaPhiSolenoidal := by
  intro c hc Φ hΦ
  have hζ : MemLp (zetaPhi Φ) 2 (measureH c) := memLp_zetaPhi hΦ
  refine ⟨hζ.toLp (zetaPhi Φ), ?_, hζ.coeFn_toLp⟩
  rw [solenoidalHC, Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction (p := fun x _ => inner ℂ x (hζ.toLp (zetaPhi Φ)) = 0) ?_ ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨ψ, hu', rfl⟩ := hx
    exact gen_inner_zero hc hΦ ψ.2 hu' hζ
  · simp
  · intro x y _ _ hx hy
    simp only [inner_add_left, hx, hy, add_zero]
  · intro a x _ hx
    simp only [inner_smul_left, hx, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
