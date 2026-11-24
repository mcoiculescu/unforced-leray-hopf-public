import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Analysis.LerayProjection.TranslationPairing

/-!
# The `L^p` Leray projection commutes with weak spatial derivatives (INF01 T16)

Blueprint: INF01 target T16 (`lerayLp_hasWeakSpatialDerivative`) of


Manuscript: unit B0201 (`paper/main.tex` lines 3051–3056: "`𝔓 = I + R⊗R` is bounded on
`W^{1,p}(R³)`, because `R_j` is bounded on `L^p` and commutes with `∂_j`"), unit B0691
(`background:eq:2.46`, lines 5764–5782: `∂_j𝔓 = 𝔓∂_j` on `Y_p`), unit B0693 (lines 5783–5810:
"spatial differentiation commutes with the bounded `L^p` Leray projection", so `f ∈ W^{k,Y_p}`
for every `k`).

Statement (`lerayLp_hasWeakSpatialDerivative`, **T16**): for `1 < p < ∞` and `F, G ∈ L^p(R³;R³)`
with `∂ᵢF = G` in the sense of `HasWeakSpatialDerivative` (`Statement.lean`), `∂ᵢ(𝔓F) = 𝔓G`.
Iterating gives the `W^{k,p}` statement.

Proof (the `L^p` version of the library's `L²` argument,
`lean/UnforcedLeray/Analysis/LerayProjection/TranslationGenerator.lean`): a weak derivative in
`L^p` is the strong derivative of the translation orbit `s ↦ F(· + s eᵢ)` in `L^p`
(`hasWeakSpatialDerivative_iff_hasDerivAt_shiftLp`; the orbit obeys
`F(· + t eᵢ) = F + ∫₀ᵗ G(· + s eᵢ) ds`, proved against compact tests, which separate `L^p`
classes); `𝔓` is bounded and commutes with translations (`lerayLp_translate`), so it maps the
orbit of `F` to the orbit of `𝔓F` and its derivative `G` to `𝔓G`.

The test-pairing derivative `hasDerivAt_integral_smul_shift` holds for every locally integrable
field (adapted from `Leray.hasDerivAt_translation_testPairing`,
`lean/UnforcedLeray/Analysis/LerayProjection/TranslationPairing.lean`, where it is stated on `L²`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace UnforcedLeray.RieszLp

/-! ### Translated test pairings of a locally integrable field -/

/-- `φ ∗ f` for a scalar test `φ` and a vector field `f`. -/
def testConvLoc (φ : Space → ℝ) (f : SpatialField) : SpatialField :=
  φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem testConvLoc_smooth {φ : Space → ℝ} (hφ : IsSpatialTest φ) {f : SpatialField}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (testConvLoc φ f) :=
  hφ.compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ.smooth hf

theorem testConvLoc_fderiv {φ : Space → ℝ} (hφ : IsSpatialTest φ) {f : SpatialField}
    (hf : LocallyIntegrable f volume) (i : Fin 3) (a : Space) :
    fderiv ℝ (testConvLoc φ f) a (coordinateVector i) =
      testConvLoc (spatialTestDerivative i φ) f a := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hd := hφ.compact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hf hφ1 a
  rw [testConvLoc, ← convolution_flip, hd.fderiv,
    convolution_precompR_apply _ hf (hφ.compact.fderiv ℝ) (hφ1.continuous_fderiv (by norm_num))]
  rw [testConvLoc, ← convolution_flip]
  rfl

/-- `∫ φ(x) f(x + a) dx = (φ(-·) ∗ f)(a)` (Lebesgue change of variables). -/
theorem integral_smul_shift_eq_testConvLoc (φ : Space → ℝ) (f : SpatialField) (a : Space) :
    (∫ x : Space, φ x • f (x + a)) = testConvLoc (Leray.reflectedTest φ) f a := by
  calc (∫ x : Space, φ x • f (x + a)) = ∫ x : Space, φ (x - a) • f x := by
        simpa only [add_sub_cancel_right] using
          (integral_add_right_eq_self (μ := (volume : Measure Space))
            (fun x : Space => φ (x - a) • f x) a)
    _ = testConvLoc (Leray.reflectedTest φ) f a := by
      rw [testConvLoc, convolution_eq_swap]
      change (∫ x : Space, φ (x - a) • f x) = ∫ x : Space, φ (-(a - x)) • f x
      simp only [neg_sub]

theorem reflected_testConvLoc_fderiv {φ : Space → ℝ} (hφ : IsSpatialTest φ) {f : SpatialField}
    (hf : LocallyIntegrable f volume) (i : Fin 3) (a : Space) :
    fderiv ℝ (testConvLoc (Leray.reflectedTest φ) f) a (coordinateVector i) =
      -(∫ x : Space, spatialTestDerivative i φ x • f (x + a)) := by
  rw [testConvLoc_fderiv (Leray.isSpatialTest_reflected hφ) hf,
    integral_smul_shift_eq_testConvLoc]
  change (∫ x : Space, spatialTestDerivative i (Leray.reflectedTest φ) x • f (a - x)) =
    -(∫ x : Space, spatialTestDerivative i φ (-x) • f (a - x))
  simp_rw [Leray.spatialTestDerivative_reflected φ hφ, neg_smul]
  exact integral_neg _

/-- For a locally integrable field `f` and a test `φ`, `s ↦ ∫ φ(x) f(x + s eᵢ) dx` is
differentiable with derivative `-∫ ∂ᵢφ(x) f(x + t eᵢ) dx` (no weak derivative of `f` is
assumed). -/
theorem hasDerivAt_integral_smul_shift {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {f : SpatialField} (hf : LocallyIntegrable f volume) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x : Space, φ x • f (x + s • coordinateVector i))
      (-(∫ x : Space, spatialTestDerivative i φ x • f (x + t • coordinateVector i))) t := by
  have hs := testConvLoc_smooth (Leray.isSpatialTest_reflected hφ) hf
  have hd := ((hs.differentiable (by simp))
    (t • coordinateVector i)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (coordinateVector i))
  have he : (fun s : ℝ => ∫ x : Space, φ x • f (x + s • coordinateVector i)) =
      (fun s : ℝ => testConvLoc (Leray.reflectedTest φ) f (s • coordinateVector i)) := by
    funext s
    exact integral_smul_shift_eq_testConvLoc φ f (s • coordinateVector i)
  rw [he]
  simpa only [Function.comp_def, id_eq, one_smul, reflected_testConvLoc_fderiv hφ hf i] using hd

/-! ### The translation orbit in `L^p` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The shift `H ↦ H(· + s eᵢ)` on `L^p(R³;R³)`. -/
abbrev shiftLp (i : Fin 3) (s : ℝ) (H : Lp Space p (volume : Measure Space)) :
    Lp Space p (volume : Measure Space) :=
  spaceTranslateLp p (-(s • coordinateVector i)) H

theorem coeFn_shiftLp (i : Fin 3) (s : ℝ) (H : Lp Space p (volume : Measure Space)) :
    (shiftLp p i s H : SpatialField) =ᵐ[volume] fun x => H (x + s • coordinateVector i) := by
  filter_upwards [coeFn_spaceTranslateLp (p := p) (-(s • coordinateVector i)) H] with x hx
  rw [hx, sub_neg_eq_add]

theorem shiftLp_zero (i : Fin 3) (H : Lp Space p (volume : Measure Space)) :
    shiftLp p i 0 H = H := by
  simp only [shiftLp, spaceTranslateLp, zero_smul, neg_zero]
  exact Heat.translateLp_zero _ _ H

theorem continuous_shiftLp_orbit (hp : p ≠ ⊤) (i : Fin 3)
    (H : Lp Space p (volume : Measure Space)) : Continuous fun s : ℝ => shiftLp p i s H :=
  (Heat.continuous_translateLp (AddMonoidHom.id Space) continuous_id hp H).comp
    ((continuous_id.smul continuous_const).neg)

/-! ### Test pairings on `L^p` -/

theorem memLp_testVec {φ : Space → ℝ} (hφ : IsSpatialTest φ) (v : Space) (r : ℝ≥0∞) :
    MemLp (fun x => φ x • v) r volume :=
  (hφ.smooth.continuous.smul continuous_const).memLp_of_hasCompactSupport
    (hφ.compact.smul_right (f' := fun _ => v))

theorem integrable_test_smul_Lp {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    (H : Lp Space p (volume : Measure Space)) : Integrable (fun x => φ x • H x) volume :=
  ((Lp.memLp H).locallyIntegrable Fact.out).integrable_smul_left_of_hasCompactSupport
    hφ.smooth.continuous hφ.compact

section Pairing

variable (q : ℝ≥0∞) [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- The test functional `H ↦ ⟨v, ∫ φ H⟩` on `L^p(R³;R³)`, a bounded operator (Hölder). -/
def pairLp (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) :
    Lp Space p (volume : Measure Space) →L[ℝ] ℝ :=
  (innerPairing p q).flip ((memLp_testVec hφ v q).toLp _)

theorem pairLp_apply (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space)
    (H : Lp Space p (volume : Measure Space)) :
    pairLp q φ hφ v H = inner ℝ v (∫ x, φ x • H x) := by
  rw [pairLp, ContinuousLinearMap.flip_apply, innerPairing_apply,
    ← integral_inner (integrable_test_smul_Lp hφ H) v]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_testVec hφ v q).coeFn_toLp] with x hx
  rw [hx, real_inner_smul_right, real_inner_smul_right, real_inner_comm]

/-- Compact tests separate `L^p` classes. -/
theorem eq_of_pairLp {A B : Lp Space p (volume : Measure Space)}
    (h : ∀ φ (hφ : IsSpatialTest φ) v, pairLp q φ hφ v A = pairLp q φ hφ v B) : A = B := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp A).locallyIntegrable Fact.out)
    ((Lp.memLp B).locallyIntegrable Fact.out)
  intro φ hs hc
  apply ext_inner_left ℝ
  intro v
  rw [← pairLp_apply q φ ⟨hs, hc⟩ v A, ← pairLp_apply q φ ⟨hs, hc⟩ v B]
  exact h φ ⟨hs, hc⟩ v

theorem pairLp_shiftLp (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space) (i : Fin 3) (s : ℝ)
    (H : Lp Space p (volume : Measure Space)) :
    pairLp q φ hφ v (shiftLp p i s H) =
      inner ℝ v (∫ x, φ x • H (x + s • coordinateVector i)) := by
  rw [pairLp_apply]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_shiftLp i s H] with x hx
  rw [hx]

theorem hasDerivAt_pairLp_shiftLp (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space)
    (i : Fin 3) (H : Lp Space p (volume : Measure Space)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pairLp q φ hφ v (shiftLp p i s H))
      (inner ℝ v (-(∫ x, spatialTestDerivative i φ x • H (x + t • coordinateVector i)))) t := by
  have hd := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_integral_smul_shift hφ ((Lp.memLp H).locallyIntegrable Fact.out) i t)
  have he : (fun s : ℝ => pairLp q φ hφ v (shiftLp p i s H)) =
      fun s : ℝ => inner ℝ v (∫ x, φ x • H (x + s • coordinateVector i)) :=
    funext fun s => pairLp_shiftLp q φ hφ v i s H
  rw [he]
  simpa only [Function.comp_def, innerSL_apply_apply] using hd

end Pairing

/-! ### Weak derivatives and the orbit -/

/-- **FTC along the orbit.** If `∂ᵢF = G` weakly with `F, G ∈ L^p`, `p < ∞`, then
`F(· + t eᵢ) = F + ∫₀ᵗ G(· + s eᵢ) ds` in `L^p`. -/
theorem shiftLp_eq_add_integral (hp : p ≠ ⊤) {i : Fin 3}
    {F G : Lp Space p (volume : Measure Space)}
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) (t : ℝ) :
    shiftLp p i t F = F + ∫ s in (0 : ℝ)..t, shiftLp p i s G := by
  have : Fact (1 ≤ p.conjExponent) := ⟨one_le_conjExponent p⟩
  have hc := continuous_shiftLp_orbit hp i G
  apply eq_of_pairLp p.conjExponent
  intro φ hφ v
  rw [map_add, ← (pairLp p.conjExponent φ hφ v).intervalIntegral_comp_comm
    (hc.intervalIntegrable 0 t)]
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s => pairLp p.conjExponent φ hφ v (shiftLp p i s F))
      (pairLp p.conjExponent φ hφ v (shiftLp p i s G)) s := by
    intro s
    have h1 := hasDerivAt_pairLp_shiftLp p.conjExponent φ hφ v i F s
    have hs := (Leray.weakDerivative_fieldTranslate (s • coordinateVector i) h).identity φ hφ
    have e : pairLp p.conjExponent φ hφ v (shiftLp p i s G) =
        inner ℝ v (-(∫ x, spatialTestDerivative i φ x • F (x + s • coordinateVector i))) := by
      rw [pairLp_shiftLp]
      change inner ℝ v (∫ x, φ x • Leray.fieldTranslate (s • coordinateVector i)
          (G : SpatialField) x) = inner ℝ v (-(∫ x, spatialTestDerivative i φ x •
            Leray.fieldTranslate (s • coordinateVector i) (F : SpatialField) x))
      rw [hs, neg_neg]
    rw [e]
    exact h1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (((pairLp p.conjExponent φ hφ v).continuous.comp hc).intervalIntegrable 0 t)
  rw [shiftLp_zero] at hFTC
  rw [hFTC]
  ring

/-- A weak derivative in `L^p`, `p < ∞`, is the strong derivative of the translation orbit. -/
theorem hasDerivAt_shiftLp (hp : p ≠ ⊤) {i : Fin 3} {F G : Lp Space p (volume : Measure Space)}
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasDerivAt (fun s : ℝ => shiftLp p i s F) G 0 := by
  have hc := continuous_shiftLp_orbit hp i G
  have he : (fun s : ℝ => shiftLp p i s F) =
      fun s => F + ∫ r in (0 : ℝ)..s, shiftLp p i r G :=
    funext (shiftLp_eq_add_integral hp h)
  rw [he]
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add F
  rwa [shiftLp_zero] at hd

/-- Conversely, a strong derivative of the translation orbit in `L^p` is a weak derivative. -/
theorem hasWeakSpatialDerivative_of_hasDerivAt_shiftLp {i : Fin 3}
    {H K : Lp Space p (volume : Measure Space)}
    (h : HasDerivAt (fun s : ℝ => shiftLp p i s H) K 0) :
    HasWeakSpatialDerivative i (H : SpatialField) (K : SpatialField) := by
  have : Fact (1 ≤ p.conjExponent) := ⟨one_le_conjExponent p⟩
  refine ⟨fun φ hφ => integrable_test_smul_Lp (hφ.derivative i) H,
    fun φ hφ => integrable_test_smul_Lp hφ K, ?_⟩
  intro φ hφ
  apply ext_inner_left ℝ
  intro v
  have h1 := (pairLp p.conjExponent φ hφ v).hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := hasDerivAt_pairLp_shiftLp p.conjExponent φ hφ v i H 0
  have he := h1.unique h2
  rw [pairLp_apply] at he
  simp only [zero_smul, add_zero] at he
  rw [inner_neg_right, he, inner_neg_right, neg_neg]

/-- Weak derivatives in `L^p`, `p < ∞`, are exactly the strong derivatives of the translation
orbit. -/
theorem hasWeakSpatialDerivative_iff_hasDerivAt_shiftLp (hp : p ≠ ⊤) (i : Fin 3)
    (F G : Lp Space p (volume : Measure Space)) :
    HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField) ↔
      HasDerivAt (fun s : ℝ => shiftLp p i s F) G 0 :=
  ⟨hasDerivAt_shiftLp hp, hasWeakSpatialDerivative_of_hasDerivAt_shiftLp⟩

/-! ### T16: `∂ᵢ 𝔓 = 𝔓 ∂ᵢ` -/

/-- **INF01 T16 (weak derivatives).** For `1 < p < ∞` and `F, G ∈ L^p(R³;R³)` with `∂ᵢF = G`
weakly, `∂ᵢ(𝔓F) = 𝔓G` weakly (B0201, `paper/main.tex` lines 3051–3056; B0691, lines 5764–5782;
B0693, lines 5783–5810). -/
theorem lerayLp_hasWeakSpatialDerivative (hp1 : 1 < p) (hp : p ≠ ⊤) {i : Fin 3}
    {F G : Lp Space p (volume : Measure Space)}
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i (lerayLp p hp1 hp F : SpatialField)
      (lerayLp p hp1 hp G : SpatialField) := by
  apply hasWeakSpatialDerivative_of_hasDerivAt_shiftLp
  have hd := (lerayLp p hp1 hp).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_shiftLp hp h)
  have he : (⇑(lerayLp p hp1 hp) ∘ fun s : ℝ => shiftLp p i s F) =
      fun s : ℝ => shiftLp p i s (lerayLp p hp1 hp F) := by
    funext s
    exact lerayLp_translate hp1 hp _ F
  rwa [he] at hd

/-- Function form of `lerayLp_hasWeakSpatialDerivative`: for `f, g ∈ L^p` with `∂ᵢf = g`
weakly, `∂ᵢ(𝔓f) = 𝔓g` weakly. -/
theorem lerayLp_toLp_hasWeakSpatialDerivative (hp1 : 1 < p) (hp : p ≠ ⊤) {i : Fin 3}
    {f g : SpatialField} (hf : MemLp f p volume) (hg : MemLp g p volume)
    (h : HasWeakSpatialDerivative i f g) :
    HasWeakSpatialDerivative i (lerayLp p hp1 hp (hf.toLp f) : SpatialField)
      (lerayLp p hp1 hp (hg.toLp g) : SpatialField) :=
  lerayLp_hasWeakSpatialDerivative hp1 hp (h.congr hf.coeFn_toLp.symm hg.coeFn_toLp.symm)

end UnforcedLeray.RieszLp
