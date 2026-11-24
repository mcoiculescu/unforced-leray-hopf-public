import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Cut

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1P

theorem cellL2Norm_eq_eLpNorm {c : ℝ} {f : Profile → MeridC} (hf : MemLp f 2 (cellMeasure c)) :
    cellL2Norm c f = (eLpNorm f 2 (cellMeasure c)).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  unfold cellL2Norm
  simp [ENNReal.toReal_ofNat]

theorem cellL2Norm_add_le {c : ℝ} {f g : Profile → MeridC} (hf : MemLp f 2 (cellMeasure c))
    (hg : MemLp g 2 (cellMeasure c)) :
    cellL2Norm c (fun p => f p + g p) ≤ cellL2Norm c f + cellL2Norm c g := by
  have hfg : MemLp (fun p => f p + g p) 2 (cellMeasure c) := hf.add hg
  rw [cellL2Norm_eq_eLpNorm hfg, cellL2Norm_eq_eLpNorm hf, cellL2Norm_eq_eLpNorm hg,
    ← ENNReal.toReal_add hf.2.ne hg.2.ne]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.2.ne, hg.2.ne⟩) ?_
  exact eLpNorm_add_le hf.1 hg.1 (by norm_num)

/-! ### Derivatives of near cutoffs -/

theorem qPeriodic_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    {f : Profile → E} (hf : QPeriodic c f) : QPeriodic c (fderiv ℝ f) := by
  intro p
  have e : ∀ x : Profile, (x.1, x.2.1 + c, x.2.2) = x + (0, c, 0) := fun x => by
    ext <;> simp
  have h : (fun x : Profile => f (x + (0, c, 0))) = f := by
    funext x; rw [← e x]; exact hf x
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (0, c, 0) (x := p)
  rw [h] at this
  rw [e]
  exact this.symm

theorem fderiv_support_box {c σ H1 L1 : ℝ} {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {p : Profile} (h : fderiv ℝ χ p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  have hcl : IsClosed {p : Profile | σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
          continuous_const))
  have hts : tsupport χ ⊆ {p : Profile | σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1} :=
    closure_minimal (fun p hp => hχ.support p hp) hcl
  exact hts (support_fderiv_subset ℝ h)

theorem norm_fderiv_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) : ‖fderiv ℝ χ p‖ ≤ cNorm8 χ := by
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous (fderiv ℝ χ) := hχ.smooth.continuous_fderiv (by simp)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hper := qPeriodic_fderiv hχ.periodic
  have hbdd : BddAbove (range fun q : Profile => ‖iteratedFDeriv ℝ 1 χ q‖) := by
    refine ⟨max C0 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : fderiv ℝ χ q' = fderiv ℝ χ q := periodic_reduceIoc_eq _ hper q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : fderiv ℝ χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := fderiv_support_box hχ h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      exact (hC0 q' hq').trans (le_max_left C0 0)
  have h0 : ‖fderiv ℝ χ p‖ = ‖iteratedFDeriv ℝ 1 χ p‖ := (norm_iteratedFDeriv_one _).symm
  rw [h0]
  calc ‖iteratedFDeriv ℝ 1 χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ 1 χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ k ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ :=
        Finset.single_le_sum (fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

theorem abs_pdS_le {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) : |pdS χ p| ≤ cNorm8 χ := by
  have := (fderiv ℝ χ p).le_opNorm ((1, 0, 0) : Profile)
  have h1 : ‖((1, 0, 0) : Profile)‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one] at this
  exact (Real.norm_eq_abs _ ▸ this).trans (norm_fderiv_le_cNorm8 hc hχ p)

theorem abs_pdQ_le {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) : |pdQ χ p| ≤ cNorm8 χ := by
  have := (fderiv ℝ χ p).le_opNorm ((0, 1, 0) : Profile)
  have h1 : ‖((0, 1, 0) : Profile)‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one] at this
  exact (Real.norm_eq_abs _ ▸ this).trans (norm_fderiv_le_cNorm8 hc hχ p)

theorem abs_pdEta_le {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) : |pdEta χ p| ≤ cNorm8 χ := by
  have := (fderiv ℝ χ p).le_opNorm ((0, 0, 1) : Profile)
  have h1 : ‖((0, 0, 1) : Profile)‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one] at this
  exact (Real.norm_eq_abs _ ▸ this).trans (norm_fderiv_le_cNorm8 hc hχ p)

theorem pdS_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {p : Profile} (h : pdS χ p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
  fderiv_support_box hχ (fun h0 => h (by simp [pdS, h0]))

theorem pdQ_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {p : Profile} (h : pdQ χ p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
  fderiv_support_box hχ (fun h0 => h (by simp [pdQ, h0]))

theorem pdEta_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {p : Profile} (h : pdEta χ p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
  fderiv_support_box hχ (fun h0 => h (by simp [pdEta, h0]))

end N05_1_1P

end UnforcedLeray.Short.PartIIa
