import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N1.Unfold
import UnforcedLeray.Lib.SobolevC.CylExtend
import UnforcedLeray.Lib.Sobolev.Cylinder
import UnforcedLeray.Lib.Sobolev.WeakDeriv

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- A field integrable on every strip `cell ∩ {|η| ≤ M}` times a continuous function that vanishes
above some height `R` is integrable on the cell. -/
theorem integrableOn_cell_smul_strip {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : ∀ M : ℝ, IntegrableOn f (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M}))
    {k : ℝ × ℝ → ℝ} (hk : Continuous k) {R : ℝ} (hkR : ∀ z : ℝ × ℝ, R < |z.2| → k z = 0) :
    IntegrableOn (fun z => k z • f z) (Sob.cylCell c) := by
  have hS : IntegrableOn (fun z => k z • f z) (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ R}) := by
    have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
      isCompact_Icc.prod isCompact_Icc
    have hkc : ContinuousOn k (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) := hk.continuousOn
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hK hkc
    refine Integrable.smul_of_top_right (hf R) (memLp_top_of_bound hk.aestronglyMeasurable C ?_)
    refine ae_restrict_of_forall_mem
      ((Sob.measurableSet_cylCell c).inter (Sob.measurableSet_absSnd_le R)) fun x hx => ?_
    exact hC x ⟨Ico_subset_Icc_self hx.1.1, abs_le.mp hx.2⟩
  refine hS.of_forall_sdiff_eq_zero (Sob.measurableSet_cylCell c) fun z hz => ?_
  have h2 : R < |z.2| := by
    by_contra hle
    exact hz.2 ⟨hz.1, not_lt.mp hle⟩
  simp only [hkR z h2, zero_smul]

theorem perExtCylBack : PerExtCylBack := by
  intro c hc vs f g hfm hgm hf hg hw
  have hint : ∀ φ : ℝ × ℝ → ℝ, Sob.IsCylTest c φ →
      IntegrableOn (fun x => Sob.iterDirDeriv vs φ x • f x) (Sob.cylCell c) ∧
      IntegrableOn (fun x => φ x • g x) (Sob.cylCell c) ∧
      ∫ x in Sob.cylCell c, Sob.iterDirDeriv vs φ x • f x
        = (-1 : ℝ) ^ vs.length • (∫ x in Sob.cylCell c, φ x • g x) := by
    intro φ hφ
    obtain ⟨χ, hχs, hχc, hχφ⟩ := cylTestUnfold c hc φ hφ
    have hφeq : Sob.perSum c χ = φ := funext hχφ
    have hχA : (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir).Adm χ :=
      (show ContDiff ℝ ∞ χ ∧ HasCompactSupport χ from ⟨hχs, hχc⟩)
    have hψA := (Sob.wholeSpaceOf (ℝ × ℝ) volume Sob.cylDir).adm_iterDirDeriv hχA vs
    have hψs : ContDiff ℝ ∞ (Sob.iterDirDeriv vs χ) := Sob.contDiff_iterDirDeriv hχs vs
    have hψc : HasCompactSupport (Sob.iterDirDeriv vs χ) := hψA.2
    obtain ⟨Rχ, hAχ, hMχ⟩ := Sob.exists_bound_of_hasCompactSupport hχc
    obtain ⟨Rψ, hAψ, hMψ⟩ := Sob.exists_bound_of_hasCompactSupport hψc
    have hD : Sob.iterDirDeriv vs φ = Sob.perSum c (Sob.iterDirDeriv vs χ) := by
      rw [← hφeq]
      exact Sob.iterDirDeriv_perSum hc hχs hAχ vs
    have hcψ : Continuous (Sob.perSum c (Sob.iterDirDeriv vs χ)) :=
      (Sob.contDiff_perSum hc hψs (fun z hz => hAψ z (subset_tsupport _ hz))).continuous
    have hvψ : ∀ z : ℝ × ℝ, Rψ < |z.2| → Sob.perSum c (Sob.iterDirDeriv vs χ) z = 0 :=
      fun z hz => Sob.perSum_eq_zero hMψ hz
    have hcχ : Continuous (Sob.perSum c χ) :=
      (Sob.contDiff_perSum hc hχs (fun z hz => hAχ z (subset_tsupport _ hz))).continuous
    have hvχ : ∀ z : ℝ × ℝ, Rχ < |z.2| → Sob.perSum c χ z = 0 :=
      fun z hz => Sob.perSum_eq_zero hMχ hz
    have hwid : ∫ x, Sob.iterDirDeriv vs χ x • Sob.perExt hc f x
        = (-1 : ℝ) ^ vs.length • (∫ x, χ x • Sob.perExt hc g x) :=
      hw.identity χ hχA
    have hF : ∫ z in Sob.cylCell c, Sob.perSum c (Sob.iterDirDeriv vs χ) z • f z
        = ∫ z, Sob.iterDirDeriv vs χ z • Sob.perExt hc f z :=
      ((Sob.integral_smul_perExt hc hψs.continuous hψc hfm hf).2).symm
    have hG : ∫ z, χ z • Sob.perExt hc g z = ∫ z in Sob.cylCell c, Sob.perSum c χ z • g z :=
      (Sob.integral_smul_perExt hc hχs.continuous hχc hgm hg).2
    have i1 : IntegrableOn (fun x => Sob.iterDirDeriv vs φ x • f x) (Sob.cylCell c) := by
      rw [hD]
      exact integrableOn_cell_smul_strip hf hcψ hvψ
    have i2 : IntegrableOn (fun x => φ x • g x) (Sob.cylCell c) := by
      rw [← hφeq]
      exact integrableOn_cell_smul_strip hg hcχ hvχ
    have heq : ∫ x in Sob.cylCell c, Sob.iterDirDeriv vs φ x • f x
        = (-1 : ℝ) ^ vs.length • (∫ x in Sob.cylCell c, φ x • g x) := by
      rw [hD, hF, hwid, hG, hφeq]
    exact ⟨i1, i2, heq⟩
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact (hint φ hφ).1
  · exact (hint φ hφ).2.1
  · exact (hint φ hφ).2.2

end UnforcedLeray.Short.PartI
