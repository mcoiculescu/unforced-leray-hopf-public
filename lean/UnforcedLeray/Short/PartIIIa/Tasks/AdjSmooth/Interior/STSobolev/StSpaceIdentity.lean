import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.SliceIBP

/-!
# `PartIII-a:T21/2/7/2/1/1/7/7`: the spatial one-letter identity in space-time

Source: `the November 2 reference manuscript` lines 3060-3061.
For `Ψ ∈ C_c^∞((t,s) × ℝ²)` we need `∫ (∂_{x_i}Ψ) Gf = -∫ Ψ Gg` for jointly measurable
`L²_loc` versions `Gf, Gg` of the slices `f r, g r`, which are periodic weak `∂_i`-derivatives
in `X_{-m,c}` for every `r ∈ (t,s)`.

Route: Fubini on `ℝ × ℝ²` (`integral_prod`) for both sides.  For `r ∈ (t,s)` the inner
`x`-integrals agree with `SliceIBP` applied to `θ = Ψ(r, ·)` (chain rule
`fderiv Ψ (r,x) (0,dir i) = pd i θ x`, and `Gf(r,·) = f r`, `Gg(r,·) = g r` a.e.).  For
`r ∉ (t,s)` both inner integrals vanish identically, since `Ψ(r,·) = 0` and the derivative
vanishes there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem stSpaceIdentity : UnforcedLeray.Short.IIIa.STSpaceIdentity := by
  intro c m t s i f g Gf Gg hc hts hyp hGfm hGgm hGfL hGgL hGf hGg
  unfold STStepIdentity
  intro Ψ hΨ hΨc hΨU
  have hdir : stDir i.succ = (0, B0579.dir i) := by
    fin_cases i <;> simp [stDir, B0579.dir]
  rw [hdir]
  have hΨcont : Continuous Ψ := hΨ.continuous
  have hΨdiff : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hKc : IsCompact (tsupport Ψ) := hΨc.isCompact
  have hKU : tsupport Ψ ⊆ stSlab t s := hΨU
  -- integrability of `G` on the compact support
  have hGfI : IntegrableOn Gf (tsupport Ψ) := by
    haveI : IsFiniteMeasure (volume.restrict (tsupport Ψ)) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    exact (hGfL _ hKc hKU).integrable (by norm_num)
  have hGgI : IntegrableOn Gg (tsupport Ψ) := by
    haveI : IsFiniteMeasure (volume.restrict (tsupport Ψ)) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    exact (hGgL _ hKc hKU).integrable (by norm_num)
  -- a bounded multiplier vanishing off the support times an integrable-on-support function
  have hint : ∀ (φ : ℝ × (ℝ × ℝ) → ℝ) (G : ℝ × (ℝ × ℝ) → ℂ), Continuous φ →
      (∃ C : ℝ, ∀ p, ‖φ p‖ ≤ C) → (∀ p, p ∉ tsupport Ψ → φ p = 0) →
      IntegrableOn G (tsupport Ψ) → Integrable (fun p => φ p • G p) := by
    intro φ G hφc hφb hφ0 hG
    obtain ⟨C, hC⟩ := hφb
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := tsupport Ψ) (Integrable.bdd_smul hG C hφc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)) ?_
    intro p hp
    simp [hφ0 p hp]
  -- the directional derivative of `Ψ` in direction `(0, dir i)`
  have hφc : Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (0, B0579.dir i)) :=
    (hΨ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφcs : HasCompactSupport (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (0, B0579.dir i)) :=
    hΨc.fderiv_apply ℝ (0, B0579.dir i)
  obtain ⟨Cd, hCd⟩ := hφc.bounded_above_of_compact_support hφcs
  have hφ0 : ∀ p, p ∉ tsupport Ψ → fderiv ℝ Ψ p (0, B0579.dir i) = 0 := by
    intro p hp
    have h0 : fderiv ℝ Ψ p = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
    rw [h0]
    rfl
  obtain ⟨CΨ, hCΨ⟩ := hΨcont.bounded_above_of_compact_support hΨc
  -- the two integrability claims
  have hI1 : Integrable (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p (0, B0579.dir i) • Gf p) :=
    hint (fun p => fderiv ℝ Ψ p (0, B0579.dir i)) Gf hφc ⟨Cd, hCd⟩ hφ0 hGfI
  have hI2 : Integrable (fun p : ℝ × (ℝ × ℝ) => Ψ p • Gg p) :=
    hint Ψ Gg hΨcont ⟨CΨ, hCΨ⟩ (fun p hp => image_eq_zero_of_notMem_tsupport hp) hGgI
  refine ⟨hI1, hI2, ?_⟩
  -- Fubini on both sides
  have hfub1 : ∫ p : ℝ × (ℝ × ℝ), fderiv ℝ Ψ p (0, B0579.dir i) • Gf p =
      ∫ r : ℝ, ∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (0, B0579.dir i) • Gf (r, x) :=
    integral_prod _ hI1
  have hfub2 : ∫ p : ℝ × (ℝ × ℝ), Ψ p • Gg p = ∫ r : ℝ, ∫ x : ℝ × ℝ, Ψ (r, x) • Gg (r, x) :=
    integral_prod _ hI2
  -- the slice identity, for every `r`
  have hpt : ∀ r : ℝ, (∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (0, B0579.dir i) • Gf (r, x)) =
      -∫ x : ℝ × ℝ, Ψ (r, x) • Gg (r, x) := by
    intro r
    by_cases hr : r ∈ Ioo t s
    · obtain ⟨hpf, hf', hpg, hg', hW⟩ := hyp r hr
      have hθ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => Ψ (r, y)) :=
        hΨ.comp (contDiff_const.prodMk contDiff_id)
      have hθc : HasCompactSupport (fun y : ℝ × ℝ => Ψ (r, y)) :=
        HasCompactSupport.intro (hKc.image continuous_snd)
          (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(r, x), h, rfl⟩))
      -- chain rule: the directional derivative of `Ψ(r, ·)` is the slice derivative
      have hpd : ∀ x : ℝ × ℝ,
          fderiv ℝ Ψ (r, x) (0, B0579.dir i) = B0579.pd i (fun y => Ψ (r, y)) x := by
        intro x
        have hd : HasFDerivAt (fun y : ℝ × ℝ => Ψ (r, y))
            ((fderiv ℝ Ψ (r, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
          (hΨdiff (r, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right r x)
        unfold B0579.pd
        rw [hd.fderiv]
        simp
      have e1 : (∫ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (0, B0579.dir i) • Gf (r, x)) =
          ∫ x : ℝ × ℝ, f r x * ((B0579.pd i (fun y => Ψ (r, y)) x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hGf r hr] with x hx
        have hx' : Gf (r, x) = f r x := hx
        rw [hx', Complex.real_smul, hpd x, mul_comm]
      have e2 : (∫ x : ℝ × ℝ, f r x * ((B0579.pd i (fun y => Ψ (r, y)) x : ℝ) : ℂ)) =
          -∫ x : ℝ × ℝ, g r x * ((Ψ (r, x) : ℝ) : ℂ) :=
        (sliceIBP c m i (f r) (g r) hc hpf hpg hf' hg' hW (fun y => Ψ (r, y)) hθ hθc).2.2
      have e3 : (∫ x : ℝ × ℝ, g r x * ((Ψ (r, x) : ℝ) : ℂ)) =
          ∫ x : ℝ × ℝ, Ψ (r, x) • Gg (r, x) := by
        apply integral_congr_ae
        filter_upwards [hGg r hr] with x hx
        have hx' : Gg (r, x) = g r x := hx
        rw [hx', Complex.real_smul, mul_comm]
      rw [e1, e2, e3]
    · have hz : ∀ x : ℝ × ℝ, (r, x) ∉ tsupport Ψ := fun x h => hr (hΨU h).1
      have h1 : ∀ x : ℝ × ℝ, fderiv ℝ Ψ (r, x) (0, B0579.dir i) = 0 := fun x =>
        hφ0 (r, x) (hz x)
      have h2 : ∀ x : ℝ × ℝ, Ψ (r, x) = 0 := fun x => image_eq_zero_of_notMem_tsupport (hz x)
      simp [h1, h2]
  -- assemble
  rw [hfub1, hfub2, ← integral_neg]
  congr 1
  funext r
  exact hpt r

end UnforcedLeray.Short.IIIa
