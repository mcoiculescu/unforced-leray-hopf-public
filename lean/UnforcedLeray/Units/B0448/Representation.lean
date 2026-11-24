import UnforcedLeray.Units.B0448.Fundamental

/-!
# B0448, part 4: the representation `H = K * F` (tex 7677–7679)

Manuscript `paper/main.tex` lines 7663–7679 (blueprint unit B0448): with `H = χW` and
`F = (∂_t − Δ_z + 1)H`, both in `L^q`, "the identity `H = K*F` is distributionally valid. Its
uniqueness follows, for example, because the Fourier symbol `iω + |ξ|² + 1` has no real zero."

Here:

* `kernelConv F X = ∫ K(X − Y) F(Y) dY`, the causal convolution `K * F`;
* `lintegral_triple_lt_top`, `integrable_triple`: for `F ∈ L^p` and `φ ∈ L^{p'}`
  (`1 ≤ p ≤ ∞`), `φ(X) K(X − Y) F(Y)` is integrable on `ST × ST`
  (`‖·‖ ≤ ‖K‖_{L¹} ‖φ‖_{p'} ‖F‖_p`, by Tonelli, translation and Hölder);
* `locallyIntegrable_kernelConv`: `K * F` is locally integrable;
* `ae_eq_kernelConv` (**the identity `H = K * F`**): if `H, F ∈ L^p(ℝ × ℝ³)` and
  `(∂_t − Δ_z + 1)H = F` in `𝓢'`, then `H = K * F` almost everywhere. The proof is the
  manuscript's: `H` is the unique tempered solution (`resolventOp_injective`, symbol without
  real zero), and `K` is the fundamental solution (`integral_kerC_sub_mul_resolventOpT`).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory SchwartzMap Complex
open scoped SchwartzMap ENNReal

/-- The causal convolution `(K * F)(X) = ∫ K(X − Y) F(Y) dY` (tex 7677). -/
def kernelConv (F : ST → ℂ) (X : ST) : ℂ := ∫ Y, kerC (X - Y) * F Y

/-- The conjugate exponent `p' = (1 − 1/p)⁻¹` of `p ∈ [1, ∞]`. -/
abbrev conjExp (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

theorem stronglyMeasurable_triple {F φ : ST → ℂ} (hFm : StronglyMeasurable F)
    (hφm : StronglyMeasurable φ) :
    StronglyMeasurable (fun q : ST × ST => φ q.1 * (kerC (q.1 - q.2) * F q.2)) :=
  (hφm.comp_measurable measurable_fst).mul
    ((measurable_kerC.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
      (hFm.comp_measurable measurable_snd))

/-- **Tonelli–Hölder bound.** For `F ∈ L^p`, `φ ∈ L^{p'}`:
`∫∫ |φ(X)| K(X − Y) |F(Y)| dX dY ≤ ‖K‖_{L¹} ‖φ‖_{p'} ‖F‖_p < ∞`. -/
theorem lintegral_triple_lt_top {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {F φ : ST → ℂ}
    (hFm : StronglyMeasurable F) (hF : MemLp F p) (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ (conjExp p)) :
    ∫⁻ q : ST × ST, ‖φ q.1 * (kerC (q.1 - q.2) * F q.2)‖ₑ ∂(volume.prod volume) < ∞ := by
  have hc : ENNReal.HolderConjugate p (conjExp p) :=
    ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have : ENNReal.HolderTriple (conjExp p) p 1 := hc.symm
  have hmeas : ∀ (f : ST × ST → ℂ), StronglyMeasurable f →
      AEMeasurable (fun q => ‖f q‖ₑ) (volume.prod volume) :=
    fun f hf => hf.measurable.enorm.aemeasurable
  simp_rw [enorm_mul]
  rw [lintegral_prod _ (by
    simpa [enorm_mul] using hmeas _ (stronglyMeasurable_triple hFm hφm))]
  rw [lintegral_lintegral_swap (by
    have h := hmeas _ (stronglyMeasurable_triple hFm hφm)
    simp only [enorm_mul] at h
    exact h)]
  have h1 : ∀ Y : ST, ∫⁻ X, ‖φ X‖ₑ * (‖kerC (X - Y)‖ₑ * ‖F Y‖ₑ) =
      ∫⁻ Z, ‖φ (Z + Y)‖ₑ * (‖kerC Z‖ₑ * ‖F Y‖ₑ) := by
    intro Y
    have h := lintegral_sub_right_eq_self (μ := (volume : Measure ST))
      (fun Z => ‖φ (Z + Y)‖ₑ * (‖kerC Z‖ₑ * ‖F Y‖ₑ)) Y
    simpa using h
  simp_rw [h1]
  have hm2 : AEMeasurable (fun q : ST × ST => ‖φ (q.2 + q.1)‖ₑ * (‖kerC q.2‖ₑ * ‖F q.1‖ₑ))
      (volume.prod volume) := by
    have : StronglyMeasurable (fun q : ST × ST => φ (q.2 + q.1) * (kerC q.2 * F q.1)) :=
      (hφm.comp_measurable (measurable_snd.add measurable_fst)).mul
        ((measurable_kerC.comp measurable_snd).stronglyMeasurable.mul
          (hFm.comp_measurable measurable_fst))
    simpa [enorm_mul] using hmeas _ this
  rw [lintegral_lintegral_swap hm2]
  have h2 : ∀ Z : ST, ∫⁻ Y, ‖φ (Z + Y)‖ₑ * (‖kerC Z‖ₑ * ‖F Y‖ₑ) ≤
      ‖kerC Z‖ₑ * (eLpNorm φ (conjExp p) volume * eLpNorm F p volume) := by
    intro Z
    have hrw : ∫⁻ Y, ‖φ (Z + Y)‖ₑ * (‖kerC Z‖ₑ * ‖F Y‖ₑ) =
        ‖kerC Z‖ₑ * ∫⁻ Y, ‖((fun Y => φ (Z + Y)) • F) Y‖ₑ := by
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      congr 1; funext Y
      show _ = ‖kerC Z‖ₑ * ‖φ (Z + Y) • F Y‖ₑ
      rw [smul_eq_mul, enorm_mul]; ring
    rw [hrw]
    gcongr
    have hH := eLpNorm_smul_le_mul_eLpNorm (p := conjExp p) (q := p) (r := 1) hF.1
      (φ := fun Y => φ (Z + Y))
      (hφm.comp_measurable (measurable_const_add Z)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm] at hH
    have htr : eLpNorm (fun Y => φ (Z + Y)) (conjExp p) volume =
        eLpNorm φ (conjExp p) volume :=
      eLpNorm_comp_measurePreserving hφ.1 (measurePreserving_add_left volume Z)
    rwa [htr] at hH
  calc _ ≤ ∫⁻ Z, ‖kerC Z‖ₑ * (eLpNorm φ (conjExp p) volume * eLpNorm F p volume) :=
        lintegral_mono h2
    _ = (∫⁻ Z, ‖kerC Z‖ₑ) * (eLpNorm φ (conjExp p) volume * eLpNorm F p volume) :=
        lintegral_mul_const _ measurable_kerC.enorm
    _ < ∞ := ENNReal.mul_lt_top integrable_kerC.2
        (ENNReal.mul_lt_top hφ.eLpNorm_lt_top hF.eLpNorm_lt_top)

theorem integrable_triple {p : ℝ≥0∞} [Fact (1 ≤ p)] {F φ : ST → ℂ}
    (hFm : StronglyMeasurable F) (hF : MemLp F p) (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ (conjExp p)) :
    Integrable (fun q : ST × ST => φ q.1 * (kerC (q.1 - q.2) * F q.2)) (volume.prod volume) :=
  ⟨(stronglyMeasurable_triple hFm hφm).aestronglyMeasurable,
    lintegral_triple_lt_top hFm hF hφm hφ⟩

/-- `K * F` is locally integrable for `F ∈ L^p`, `1 ≤ p ≤ ∞`. -/
theorem locallyIntegrable_kernelConv {p : ℝ≥0∞} [Fact (1 ≤ p)] {F : ST → ℂ}
    (hFm : StronglyMeasurable F) (hF : MemLp F p) : LocallyIntegrable (kernelConv F) := by
  rw [locallyIntegrable_iff]
  intro s hs
  have hsm : MeasurableSet s := hs.measurableSet
  have hφm : StronglyMeasurable (s.indicator fun _ : ST => (1 : ℂ)) :=
    stronglyMeasurable_const.indicator hsm
  have hφ : MemLp (s.indicator fun _ : ST => (1 : ℂ)) (conjExp p) :=
    memLp_indicator_const _ hsm 1 (Or.inr hs.measure_lt_top.ne)
  have hint := (integrable_triple hFm hF hφm hφ).integral_prod_left
  rw [← integrable_indicator_iff hsm]
  refine hint.congr (Filter.Eventually.of_forall fun X => ?_)
  simp only [kernelConv]
  rw [integral_const_mul]
  by_cases hX : X ∈ s <;> simp [hX, kernelConv]

/-- **The identity `H = K * F` (tex 7677–7679).** If `H, F ∈ L^p(ℝ × ℝ³)` (`1 ≤ p ≤ ∞`) and
`(∂_t − Δ_z + 1)H = F` in tempered distributions, then `H(X) = ∫ K(X − Y) F(Y) dY` for almost
every `X`. (The manuscript applies it to `H = χW`, `F ∈ L^q`, `q > 5/2`.) -/
theorem ae_eq_kernelConv {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {H F : Lp ℂ p (volume : Measure ST)}
    (hHF : resolventOp (H : 𝓢'(ST, ℂ)) = (F : 𝓢'(ST, ℂ))) :
    (H : ST → ℂ) =ᵐ[volume] kernelConv F := by
  have hFm := Lp.stronglyMeasurable F
  have hF := Lp.memLp F
  have hpair : ∀ φ : 𝓢(ST, ℂ), ∫ X, φ X * H X = ∫ X, φ X * kernelConv F X := by
    intro φ
    set ψ := resolventInvT φ
    have e1 : ∫ X, φ X * H X = ∫ Y, ψ Y * F Y := by
      have h1 := resolventOp_apply (H : 𝓢'(ST, ℂ)) ψ
      rw [resolventOpT_resolventInvT, hHF] at h1
      simp only [Lp.toTemperedDistribution_apply, smul_eq_mul] at h1
      exact h1.symm
    have e2 : ∫ X, φ X * kernelConv F X = ∫ Y, ψ Y * F Y := by
      have hint := integrable_triple hFm hF φ.continuous.stronglyMeasurable (φ.memLp _)
      have hX : ∀ X, φ X * kernelConv F X = ∫ Y, φ X * (kerC (X - Y) * F Y) := fun X => by
        rw [kernelConv, integral_const_mul]
      simp_rw [hX]
      rw [integral_integral_swap hint]
      congr 1; funext Y
      have hfs := integral_kerC_sub_mul_resolventOpT ψ Y
      rw [resolventOpT_resolventInvT] at hfs
      rw [← hfs, ← integral_mul_const]
      congr 1; funext X; ring
    rw [e1, e2]
  have hHloc : LocallyIntegrable (H : ST → ℂ) := (Lp.memLp H).locallyIntegrable hp.out
  refine ae_eq_of_integral_contDiff_smul_eq hHloc (locallyIntegrable_kernelConv hFm hF)
    fun g hg hgc => ?_
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
  have hg' : ContDiff ℝ _ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have := hpair (hgc'.toSchwartzMap hg')
  simp only [HasCompactSupport.toSchwartzMap_toFun] at this
  simpa [Complex.real_smul] using this

end UnforcedLeray.B0448
