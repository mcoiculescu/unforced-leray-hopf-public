import UnforcedLeray.Short.PartI.Sub.T02_3_8
import UnforcedLeray.Short.PartI.Sub.T02_2

/-!
# Part I, task `PartI:T02/3/8`: the mean part of the cylinder pressure (conditional)

Source of record: `the November 2 reference manuscript`, lines 276-288 and 447.

`cylPoisMeanPartBound_of` derives `CylPoisMeanPartBound` (`|\bar q| ≤ B²`) from the four leaves
`CylPoisHmeanC2`, `CylPoisHmeanLap`, `CylPoisMeanSource`, `CylPoisAffineZero`
(`Sub/T02_3_8.lean`).  The function `F = \bar q + \overline{u_η²}` has `F'' = \overline{Δq}
+ \overline{S} = 0`, tends to `0`, hence vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- A function of `η` alone tending to `0` along `|η| → ∞` (as a function on the plane) tends to `0`
at `cocompact ℝ`. -/
theorem cylpTendstoCocompact {g : ℝ → ℝ}
    (h : Tendsto (fun z : Plane => g z.2) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) :
    Tendsto g (cocompact ℝ) (𝓝 0) := by
  have h1 : Tendsto (fun η : ℝ => ((0 : ℝ), η)) (cocompact ℝ)
      (comap (fun z : Plane => |z.2|) atTop) := by
    rw [tendsto_comap_iff, cocompact_eq_atBot_atTop]
    exact tendsto_sup.2 ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
  exact h.comp h1

/-- The derivative of a `C²` function of one variable is differentiable. -/
theorem cylpDifferentiableDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (deriv f) := by
  exact hf.differentiable_deriv_two

/-- A bound on `|f|` gives the same bound on the horizontal average. -/
theorem cylpHmeanAbsLe {c K : ℝ} (hc : 0 < c) {f : Plane → ℝ} (hf : ∀ z, |f z| ≤ K) (η : ℝ) :
    |hmean c f η| ≤ K := by
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
    (f := fun q => f (q, η)) (C := K) (by simp) (fun q _ => by
      rw [Real.norm_eq_abs]
      exact hf (q, η))
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hint
  unfold hmean
  rw [← Real.norm_eq_abs, norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), f (q, η)‖ ≤ c⁻¹ * (K * c) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = K := by field_simp

/-- **The mean part from its four leaves.** -/
theorem cylPoisMeanPartBound_of (h1 : CylPoisHmeanC2) (h2 : CylPoisHmeanLap)
    (h3 : CylPoisMeanSource) (h4 : CylPoisAffineZero) : CylPoisMeanPartBound := by
  intro c B hc u q hu hq hup hqp hdiv hB hu0 hq0 hlap η
  -- the general step: for any `C²` function `g` whose average cancels the source average
  have key : ∀ g : Plane → ℝ, ContDiff ℝ 2 g →
      (∀ e, hmean c (poissonSource u) e = hmean c (Cyl.partialEta (Cyl.partialEta g)) e) →
      Tendsto (hmean c g) (cocompact ℝ) (𝓝 0) → ∀ e, hmean c q e + hmean c g e = 0 := by
    intro g hg2 hsrc hgd e
    obtain ⟨hqC, hq''⟩ := h1 c q hc hq
    obtain ⟨hgC, hg''⟩ := h1 c g hc hg2
    have hFC : ContDiff ℝ 2 (fun e => hmean c q e + hmean c g e) := hqC.add hgC
    have hlapfun : Train.lapS q = fun z => -poissonSource u z := funext hlap
    have hneg : ∀ e, hmean c (Train.lapS q) e = - hmean c (poissonSource u) e := by
      intro e
      rw [hlapfun]
      unfold hmean
      simp only [integral_neg, smul_neg]
    have hF2 : ∀ e, deriv (deriv (fun e => hmean c q e + hmean c g e)) e = 0 := by
      intro e
      have hd : deriv (fun e => hmean c q e + hmean c g e) =
          fun e => deriv (hmean c q) e + deriv (hmean c g) e := by
        funext e'
        exact deriv_add (hqC.differentiable (by norm_num) e') (hgC.differentiable (by norm_num) e')
      have hsum : deriv (fun e => deriv (hmean c q) e + deriv (hmean c g) e) e =
          deriv (deriv (hmean c q)) e + deriv (deriv (hmean c g)) e :=
        deriv_add (cylpDifferentiableDeriv hqC e) (cylpDifferentiableDeriv hgC e)
      rw [hd, hsum, hq'' e, hg'' e, ← h2 c q hc hq hqp e, hneg e, ← hsrc e]
      ring
    have hq_dec : Tendsto (hmean c q) (cocompact ℝ) (𝓝 0) :=
      cylpTendstoCocompact (gg_hmean_tendsto hc hq0)
    have hF_dec : Tendsto (fun e => hmean c q e + hmean c g e) (cocompact ℝ) (𝓝 0) := by
      simpa using hq_dec.add hgd
    exact h4 _ hFC hF2 hF_dec e
  -- apply it to `g = u_η²`
  have hproj : ContDiff ℝ ∞ (fun z : Plane => u z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hgs : ContDiff ℝ ∞ (fun z : Plane => u z 1 ^ 2) := hproj.pow 2
  have hg2 : ContDiff ℝ 2 (fun z : Plane => u z 1 ^ 2) := hgs.of_le (by simp)
  have hu1 : Tendsto (fun z : Plane => u z 1 ^ 2) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have h := ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.tendsto 0).comp hu0
    simpa using h.pow 2
  have hg_dec : Tendsto (hmean c (fun z : Plane => u z 1 ^ 2)) (cocompact ℝ) (𝓝 0) :=
    cylpTendstoCocompact (gg_hmean_tendsto hc hu1)
  have hsum := key (fun z : Plane => u z 1 ^ 2) hg2 (h3 c u hc hu hup hdiv) hg_dec η
  have hgb : ∀ z : Plane, |u z 1 ^ 2| ≤ B ^ 2 := fun z => by
    have h0 : ‖u z 1‖ ≤ ‖u z‖ := PiLp.norm_apply_le (u z) 1
    have h1' : ‖u z 1‖ ≤ B := h0.trans (hB z)
    rw [abs_pow, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) h1' 2
  have hmg := cylpHmeanAbsLe (c := c) (K := B ^ 2) hc hgb η
  have hq_eq : hmean c q η = - hmean c (fun z : Plane => u z 1 ^ 2) η := by linarith
  rw [hq_eq, abs_neg]
  exact hmg

end UnforcedLeray.Short.PartI
