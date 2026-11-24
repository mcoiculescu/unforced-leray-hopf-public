import UnforcedLeray.Loc.L14Realization.TestCalculus
import UnforcedLeray.Analysis.ViscosityTransport.Defs
import UnforcedLeray.Analysis.WeakL2R3
import UnforcedLeray.Analysis.EnergyInterpolation.Spacetime
import UnforcedLeray.Infra.JointMeasurableRep.Velocity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Real.ConjExponents

/-!
# Step L14, helpers: the weak form with initial datum from the strong equation

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 559–561: "this recovers the full pressure equation. Integrating it from a positive time
and using the strong trace gives `eq:initial-weak-form` with datum `u_{0,h}`"; blueprint unit
B1032, infrastructure "integrability of each pairing on the slab").

`solvesNavierStokesViscosity_of_strong` is package-free. Let `u` be a velocity, jointly
measurable on the slab, with `u(t) ∈ L²` continuous in `L²` on `[0,T]`, `u(0) = u₀` a.e.,
differentiable in `L²` on `(0,T)` with derivative `U'(t)`, and a pressure `p ∈ L^{5/3}` of the
slab with `p(t) ∈ L^{5/3}` for `t ∈ (0,T)`. If at every `t ∈ (0,T)` and every vector test `ψ`

  `⟨U'(t), ψ⟩ = ν ⟨u, Δψ⟩ + ∫ u·(Dψ u) + ∫ p div ψ`,

then `(u, p)` satisfies the full weak equation `SolvesNavierStokesViscosity ν T u₀ u p`: every
pairing is integrable on the slab, and the identity with the datum term holds for every
spacetime test `φ`. Proof: `t ↦ ⟨u(t), φ(t,·)⟩` is continuous on `[0,T]` and differentiable on
`(0,T)` (`hasDerivAt_toL2_slice`), its derivative is the spatial integral of the weak
integrand, which is integrable in time by Fubini, and the fundamental theorem of calculus
gives `0 - ⟨u₀, φ(0,·)⟩` because `φ(T,·) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Blueprint.L14

open ViscosityTransport

theorem integral_norm_sq_eq {f : SpatialField} (hf : MemLp f 2 volume) :
    ∫ x, ‖f x‖ ^ 2 = l2Norm f ^ 2 := by
  rw [← norm_toL2 hf, ← real_inner_self_eq_norm_sq, inner_toL2_eq_integral hf hf]
  exact integral_congr_ae (Eventually.of_forall fun x => (real_inner_self_eq_norm_sq _).symm)

/-- A jointly measurable velocity, uniformly bounded in `L²` on `(0,T)`, is in `L²` of the
slab. -/
theorem memLp_two_slab {T M : ℝ} {u : Velocity}
    (hmeas : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2) (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M) :
    MemLp (fun z : SpaceTime => u z.1 z.2) 2 (volume.restrict (slab T)) := by
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hm2 : AEStronglyMeasurable (fun z : SpaceTime => ‖u z.1 z.2‖ ^ 2)
      (volume.restrict (slab T)) := hmeas.norm.pow 2
  rw [EnergyInterpolation.slab_volume_eq] at hm2 ⊢
  refine (integrable_prod_iff hm2).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (memLp_two_iff_integrable_sq_norm (h2 t ht).1).mp (h2 t ht)
  · refine Integrable.mono' (g := fun _ => M ^ 2) (integrable_const _)
      hm2.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hI : ∫ x, ‖‖u t x‖ ^ 2‖ = l2Norm (u t) ^ 2 := by
      simp only [norm_pow, norm_norm]
      exact integral_norm_sq_eq (h2 t ht)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), hI]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hM t ht) 2

/-- `L² × L²` inner products are integrable. -/
theorem integrable_inner_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Space} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => inner ℝ (f z) (g z)) μ :=
  (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Eventually.of_forall fun z => by
      simpa only [Pi.mul_apply] using norm_inner_le_norm (𝕜 := ℝ) (f z) (g z))

theorem holderConjugate_fiveThirds : ENNReal.HolderConjugate (5 / 3 : ℝ≥0∞) (5 / 2) := by
  apply ENNReal.HolderConjugate.of_toReal
  rw [Real.holderConjugate_iff]
  norm_num [ENNReal.toReal_div]

/-- The spatial divergence of a test, as a smooth compactly supported field. -/
def Div (φ : SpaceTime → Space) (z : SpaceTime) : ℝ := ∑ i : Fin 3, Ds φ i z i

theorem contDiff_Div {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Div φ) := by
  unfold Div
  have h : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => Ds φ i z i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (contDiff_Ds hφ i)
  convert ContDiff.sum (s := Finset.univ) (fun i _ => h i) using 1

theorem hasCompactSupport_Div {φ : SpaceTime → Space} (hφ : HasCompactSupport φ) :
    HasCompactSupport (Div φ) := by
  unfold Div
  have h : ∀ i : Fin 3, HasCompactSupport (fun z => Ds φ i z i) := fun i =>
    (hasCompactSupport_Ds hφ i).comp_left (g := fun v : Space => v i) (by simp)
  have he : (fun z => ∑ i : Fin 3, Ds φ i z i) = ∑ i : Fin 3, fun z => Ds φ i z i := by
    funext z
    simp [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum fun i _ => h i

theorem spatialDivergence_eq_Div {φ : SpaceTime → Space} (hφ : ContDiff ℝ ∞ φ) (t : ℝ)
    (x : Space) : spatialDivergence φ t x = Div φ (t, x) := by
  unfold spatialDivergence Div
  exact Finset.sum_congr rfl fun i _ => by rw [spatialDerivative_coord_eq_Ds hφ]

/-- `toL2` of the zero field. -/
theorem toL2_eq_zero_of_eq_zero {f : SpatialField} (hf : ∀ x, f x = 0) : toL2 f = 0 := by
  have h0 : f = 0 := funext hf
  subst h0
  unfold toL2
  split_ifs with h
  · exact MemLp.toLp_zero h
  · rfl

section Weak

variable {ν T : ℝ} {u₀ : SpatialField} {u : Velocity} {p : Pressure} {U' : ℝ → L2Space}

/-- **The weak form with datum from the strong `L²` equation.** -/
theorem solvesNavierStokesViscosity_of_strong (hT : 0 < T)
    (hmeas : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2) (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 volume)
    (hcont : ContinuousOn (fun t => toL2 (u t)) (Icc (0 : ℝ) T))
    (h0 : u 0 =ᵐ[volume] u₀)
    (hp : MemLp (fun z : SpaceTime => p z.1 z.2) (5 / 3 : ℝ≥0∞) (volume.restrict (slab T)))
    (hpt : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (p t) (5 / 3 : ℝ≥0∞) volume)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => toL2 (u s)) (U' t) t)
    (hpair : ∀ t ∈ Ioo (0 : ℝ) T, ∀ ψ : Space → Space, IsVectorTest ψ →
      inner ℝ (U' t) (toL2 ψ) =
        ν * (∫ x, inner ℝ (u t x) (∑ i : Fin 3, testPartial (testPartial ψ i) i x)) +
        (∫ x, inner ℝ (u t x) (fderiv ℝ ψ x (u t x))) +
        ∫ x, p t x * ∑ i : Fin 3, testPartial ψ i x i) :
    SolvesNavierStokesViscosity ν T u₀ u p := by
  -- a uniform `L²` bound
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hMu : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M := fun t ht => by
    rw [← norm_toL2 (h2 t ⟨ht.1.le, ht.2.le⟩)]
    exact hM t ⟨ht.1.le, ht.2.le⟩
  have huL2 := memLp_two_slab hmeas (fun t ht => h2 t ⟨ht.1.le, ht.2.le⟩) hMu
  have hu₀ : MemLp u₀ 2 volume := (h2 0 ⟨le_rfl, hT.le⟩).ae_eq h0
  -- the pairings, for one test
  have hslab : ∀ {g : SpaceTime → Space}, Continuous g → HasCompactSupport g →
      MemLp g 2 (volume.restrict (slab T)) := fun hg hgc =>
    (hg.memLp_of_hasCompactSupport hgc).restrict _
  have htemp : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (temporalTerm u φ) (slab T) := by
    intro φ hφ
    have h := integrable_inner_of_memLp huL2
      (hslab (contDiff_Dt hφ.smooth).continuous (hasCompactSupport_Dt hφ.compact))
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [temporalTerm, timeDerivative_eq_Dt hφ.smooth]
  have hdiff : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (diffusionTerm u φ) (slab T) := by
    intro φ hφ
    have h := integrable_inner_of_memLp huL2
      (hslab (contDiff_Lap hφ.smooth).continuous (hasCompactSupport_Lap hφ.compact))
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [diffusionTerm, spatialLaplacian_eq_Lap hφ.smooth]
  have hpres : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (pressureTerm p φ) (slab T) := by
    intro φ hφ
    have := holderConjugate_fiveThirds
    have hD : MemLp (Div φ) (5 / 2 : ℝ≥0∞) (volume.restrict (slab T)) :=
      ((contDiff_Div hφ.smooth).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_Div hφ.compact)).restrict _
    have h := hp.integrable_mul hD
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [pressureTerm, spatialDivergence_eq_Div hφ.smooth, Pi.mul_apply]
  have hconv : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (convectionTerm u φ) (slab T) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := (hφ.smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hφ.compact.fderiv (𝕜 := ℝ))
    have hsq : Integrable (fun z : SpaceTime => ‖u z.1 z.2‖ ^ 2) (volume.restrict (slab T)) :=
      (memLp_two_iff_integrable_sq_norm huL2.1).mp huL2
    have hΦ : Continuous (fun w : SpaceTime × Space =>
        inner ℝ w.2 (fderiv ℝ φ w.1 ((0 : ℝ), w.2))) :=
      continuous_snd.inner (((hφ.smooth.continuous_fderiv (by simp)).comp continuous_fst).clm_apply
        (continuous_const.prodMk continuous_snd))
    have hmeasC : AEStronglyMeasurable (convectionTerm u φ) (volume.restrict (slab T)) := by
      have := hΦ.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hmeas)
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [id, convectionTerm, spatialDerivative_eq hφ.smooth]
    refine (hsq.const_mul B).mono' hmeasC (Eventually.of_forall fun z => ?_)
    simp only [convectionTerm, spatialDerivative_eq hφ.smooth]
    calc ‖inner ℝ (u z.1 z.2) (fderiv ℝ φ (z.1, z.2) ((0 : ℝ), u z.1 z.2))‖
        ≤ ‖u z.1 z.2‖ * ‖fderiv ℝ φ (z.1, z.2) ((0 : ℝ), u z.1 z.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u z.1 z.2‖ * (B * ‖u z.1 z.2‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          refine ((fderiv ℝ φ (z.1, z.2)).le_opNorm _).trans ?_
          have hn : ‖(((0 : ℝ), u z.1 z.2) : SpaceTime)‖ = ‖u z.1 z.2‖ := by
            simp [Prod.norm_def]
          rw [hn]
          exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      _ = B * ‖u z.1 z.2‖ ^ 2 := by ring
  have hdatum : ∀ φ, IsSpacetimeTest T φ →
      Integrable (fun x => inner ℝ (u₀ x) (φ (0, x))) := fun φ hφ =>
    integrable_inner_of_memLp hu₀ (memLp_slice hφ.smooth hφ.compact 0 2)
  refine ⟨htemp, hconv, hdiff, hpres, hdatum, fun φ hφ => ?_⟩
  -- the identity
  have hs := hφ.smooth
  have hc := hφ.compact
  set f : ℝ → ℝ := fun s => inner ℝ (toL2 (u s)) (toL2 (slice φ s)) with hfdef
  set f' : ℝ → ℝ := fun t => inner ℝ (toL2 (u t)) (toL2 (slice (Dt φ) t)) +
    inner ℝ (U' t) (toL2 (slice φ t)) with hf'def
  have hslcont : Continuous (fun s => toL2 (slice φ s)) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_toL2_slice hs hc s).continuousAt
  have hfcont : ContinuousOn f (Icc 0 T) := hcont.inner hslcont.continuousOn
  have hfderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt f (f' t) t := fun t ht =>
    HasDerivAt.inner ℝ (hderiv t ht) (hasDerivAt_toL2_slice hs hc t)
  -- integrability of the weak integrand
  have hI : IntegrableOn (viscosityWeakIntegrand ν u p φ) (slab T) :=
    (((htemp φ hφ).add (hconv φ hφ)).add ((hdiff φ hφ).const_mul ν)).add (hpres φ hφ)
  rw [IntegrableOn, EnergyInterpolation.slab_volume_eq] at hI
  have hItime := hI.integral_prod_left
  -- the derivative is the spatial integral of the weak integrand
  have key : ∀ t ∈ Ioo (0 : ℝ) T, f' t = ∫ x, viscosityWeakIntegrand ν u p φ (t, x) := by
    intro t ht
    have hut := h2 t ⟨ht.1.le, ht.2.le⟩
    have hψ := isVectorTest_slice hs hc t
    have hpp := hpair t ht (slice φ t) hψ
    have hA : Integrable (fun x => inner ℝ (u t x) (timeDerivative φ t x)) := by
      have := integrable_inner_of_memLp hut (memLp_slice (contDiff_Dt hs) (hasCompactSupport_Dt hc) t 2)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [slice, timeDerivative_eq_Dt hs]
    have hB : Integrable (fun x => inner ℝ (u t x) (spatialLaplacian φ t x)) := by
      have := integrable_inner_of_memLp hut (memLp_slice (contDiff_Lap hs) (hasCompactSupport_Lap hc) t 2)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [slice, spatialLaplacian_eq_Lap hs]
    have hC : Integrable (fun x => inner ℝ (u t x) (spatialDerivative φ t x (u t x))) := by
      obtain ⟨B, hB⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support
        (hc.fderiv (𝕜 := ℝ))
      have hsq : Integrable (fun x => ‖u t x‖ ^ 2) :=
        (memLp_two_iff_integrable_sq_norm hut.1).mp hut
      have hmC : AEStronglyMeasurable (fun x => inner ℝ (u t x) (spatialDerivative φ t x (u t x)))
          volume := by
        have hΦ : Continuous (fun w : Space × Space =>
            inner ℝ w.2 (fderiv ℝ φ (t, w.1) ((0 : ℝ), w.2))) :=
          continuous_snd.inner (((hs.continuous_fderiv (by simp)).comp
            (continuous_const.prodMk continuous_fst)).clm_apply
            (continuous_const.prodMk continuous_snd))
        have := hΦ.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hut.1)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [id, spatialDerivative_eq hs]
      refine (hsq.const_mul B).mono' hmC (Eventually.of_forall fun x => ?_)
      rw [spatialDerivative_eq hs]
      calc ‖inner ℝ (u t x) (fderiv ℝ φ (t, x) ((0 : ℝ), u t x))‖
          ≤ ‖u t x‖ * ‖fderiv ℝ φ (t, x) ((0 : ℝ), u t x)‖ := norm_inner_le_norm _ _
        _ ≤ ‖u t x‖ * (B * ‖u t x‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
            have hn : ‖(((0 : ℝ), u t x) : SpaceTime)‖ = ‖u t x‖ := by simp [Prod.norm_def]
            rw [hn]
            exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
        _ = B * ‖u t x‖ ^ 2 := by ring
    have hD : Integrable (fun x => p t x * spatialDivergence φ t x) := by
      have := holderConjugate_fiveThirds
      have hDv : MemLp (fun x => Div φ (t, x)) (5 / 2 : ℝ≥0∞) volume :=
        ((contDiff_Div hs).comp (contDiff_const.prodMk contDiff_id)).continuous.memLp_of_hasCompactSupport
          ((hasCompactSupport_Div hc).comp_isClosedEmbedding
            ⟨isEmbedding_prodMkRight t, (isClosedMap_prodMk_left t).isClosed_range⟩)
      have := (hpt t ht).integrable_mul hDv
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, spatialDivergence_eq_Div hs]
    have hsplit : ∫ x, viscosityWeakIntegrand ν u p φ (t, x) =
        (∫ x, inner ℝ (u t x) (timeDerivative φ t x)) +
        (∫ x, inner ℝ (u t x) (spatialDerivative φ t x (u t x))) +
        ν * (∫ x, inner ℝ (u t x) (spatialLaplacian φ t x)) +
        ∫ x, p t x * spatialDivergence φ t x := by
      have h1 : Integrable (fun x => inner ℝ (u t x) (timeDerivative φ t x) +
          inner ℝ (u t x) (spatialDerivative φ t x (u t x))) := hA.add hC
      have h2 : Integrable (fun x => ν * inner ℝ (u t x) (spatialLaplacian φ t x)) :=
        hB.const_mul ν
      have h3 : Integrable (fun x => inner ℝ (u t x) (timeDerivative φ t x) +
          inner ℝ (u t x) (spatialDerivative φ t x (u t x)) +
          ν * inner ℝ (u t x) (spatialLaplacian φ t x)) := h1.add h2
      calc ∫ x, viscosityWeakIntegrand ν u p φ (t, x)
          = ∫ x, (inner ℝ (u t x) (timeDerivative φ t x) +
              inner ℝ (u t x) (spatialDerivative φ t x (u t x)) +
              ν * inner ℝ (u t x) (spatialLaplacian φ t x)) +
              p t x * spatialDivergence φ t x := rfl
        _ = (∫ x, inner ℝ (u t x) (timeDerivative φ t x) +
              inner ℝ (u t x) (spatialDerivative φ t x (u t x)) +
              ν * inner ℝ (u t x) (spatialLaplacian φ t x)) +
              ∫ x, p t x * spatialDivergence φ t x := integral_add h3 hD
        _ = ((∫ x, inner ℝ (u t x) (timeDerivative φ t x) +
              inner ℝ (u t x) (spatialDerivative φ t x (u t x))) +
              ∫ x, ν * inner ℝ (u t x) (spatialLaplacian φ t x)) +
              ∫ x, p t x * spatialDivergence φ t x := by rw [integral_add h1 h2]
        _ = _ := by rw [integral_add hA hC, integral_const_mul]
    have hT1 : inner ℝ (toL2 (u t)) (toL2 (slice (Dt φ) t)) =
        ∫ x, inner ℝ (u t x) (timeDerivative φ t x) := by
      rw [inner_toL2_eq_integral hut (memLp_slice (contDiff_Dt hs) (hasCompactSupport_Dt hc) t 2)]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        simp only [slice, timeDerivative_eq_Dt hs])
    rw [hsplit, hf'def]
    simp only
    rw [hT1, hpp]
    have e1 : (∫ x, inner ℝ (u t x) (∑ i : Fin 3, testPartial (testPartial (slice φ t) i) i x)) =
        ∫ x, inner ℝ (u t x) (spatialLaplacian φ t x) := rfl
    have e2 : (∫ x, inner ℝ (u t x) (fderiv ℝ (slice φ t) x (u t x))) =
        ∫ x, inner ℝ (u t x) (spatialDerivative φ t x (u t x)) := rfl
    have e3 : (∫ x, p t x * ∑ i : Fin 3, testPartial (slice φ t) i x i) =
        ∫ x, p t x * spatialDivergence φ t x := rfl
    rw [e1, e2, e3]
    ring
  -- integrability of `f'`
  have hf'int : IntegrableOn f' (Ioo (0 : ℝ) T) := by
    refine hItime.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (key t ht).symm
  have hint : IntervalIntegrable f' volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hf'int
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hfcont hfderiv hint
  rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hcongr : ∫ t in Ioo (0 : ℝ) T, ∫ x, viscosityWeakIntegrand ν u p φ (t, x) =
      ∫ t in Ioo (0 : ℝ) T, f' t :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => (key t ht).symm
  -- the endpoint values
  have hfT : f T = 0 := by
    have hz : toL2 (slice φ T) = 0 := toL2_eq_zero_of_eq_zero fun x => by
      show φ (T, x) = 0
      exact image_eq_zero_of_notMem_tsupport fun hx => lt_irrefl T (hφ.timeSupport hx).1
    simp only [hfdef, hz, inner_zero_right]
  have hf0 : f 0 = ∫ x, inner ℝ (u₀ x) (φ (0, x)) := by
    simp only [hfdef]
    rw [Infra.JointMeasurableRep.toL2_congr_ae h0,
      inner_toL2_eq_integral hu₀ (memLp_slice hs hc 0 2)]
    rfl
  rw [hcongr, hFTC, hfT, hf0]
  ring

end Weak

end UnforcedLeray.Blueprint.L14
