import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.SliceCore

/-!
# `BgContRepWeakSlice`: the slices of the continuous representatives satisfy the weak derivative

Source of record: `the November 2 reference manuscript`, 1343-1349 (distributional
graph), 1515-1531 (continuous representatives), 2531-2537.

For a scalar test `φ`, a component `k` and a smooth `P`-periodic `χ`, the product
`χ(τ)φ(y)e_k` is a phase test; the real part of the identity `⟪-∂_jΦ, u⟫ = ⟪Φ, g⟫` read on the
continuous representatives (`re_phasePair_prod`) gives `∫₀ᴾ χ H_k = 0` with
`H_k(τ) = ∫ ∂_jφ F_k(τ,·) + φ G_k(τ,·)`; `H_k` is continuous and `P`-periodic, so it vanishes
(Fourier completeness, `periodic_eq_zero_of_trig`).  Integrability follows from continuity and
the compact support of `φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params contRep)

theorem bgContRepWeakSlice : BgContRepWeakSlice := by
  intro P _ hP1 ν hν u g j hop τ
  have hP : 0 < P := Fact.out
  obtain ⟨hFc, -⟩ := bgContRepGraph P hP1 ν hν u
  obtain ⟨hGc, -⟩ := bgContRepGraph P hP1 ν hν g
  set F : ℝ → Space → Space :=
    contRep (u : Yq P UnforcedLeray.B0412.q0E) with hFdef
  set G : ℝ → Space → Space :=
    contRep (g : Yq P UnforcedLeray.B0412.q0E) with hGdef
  have hFp : ∀ t, F (t + P) = F t :=
    fun t => UnforcedLeray.Cons.C03.Concrete.contRep_periodic _ t
  have hGp : ∀ t, G (t + P) = G t :=
    fun t => UnforcedLeray.Cons.C03.Concrete.contRep_periodic _ t
  -- the weak form on the representatives
  have hid : ∀ (φ : Space → ℝ), UnforcedLeray.IsSpatialTest φ → ∀ k : Fin 3, ∀ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ → (∀ t, χ (t + P) = χ t) →
      ∫ t in Ioc (0 : ℝ) P, ∫ y, χ t * (-(UnforcedLeray.spatialTestDerivative j φ y)) * F t y k =
        ∫ t in Ioc (0 : ℝ) P, ∫ y, χ t * φ y * G t y k := by
    intro φ hφ k χ hχ hχp
    have hΦ := prodTest_isPhaseTest (P := P) k hχ hχp hφ
    have h := hop (prodTestReal χ φ k) hΦ
    have hL : (fun Φ => -dy j Φ) (prodTestReal χ φ k) =
        prodTestReal χ (fun y => -(UnforcedLeray.spatialTestDerivative j φ y)) k := by
      show -(dy j (prodTestReal χ φ k)) = _
      rw [dy_prodTest k j hχ hφ]
      funext p
      simp [prodTestReal]
    rw [hL] at h
    have hΨ := prodTest_isPhaseTest (P := P) k hχ hχp
      (isSpatialTest_neg (isSpatialTest_derivative hφ j))
    have h1 := re_phasePair_prod (u : Yq P UnforcedLeray.B0412.q0E) hΨ χ
      (fun y => -(UnforcedLeray.spatialTestDerivative j φ y)) k (fun p => rfl)
    have h2 := re_phasePair_prod (g : Yq P UnforcedLeray.B0412.q0E) hΦ χ φ k (fun p => rfl)
    rw [h] at h1
    rw [h1] at h2
    exact mul_left_cancel₀ (inv_ne_zero hP.ne') h2
  have hFτ : Continuous (F τ) := hFc.comp (Continuous.prodMk_right τ)
  have hGτ : Continuous (G τ) := hGc.comp (Continuous.prodMk_right τ)
  have hint : ∀ ψ : Space → ℝ, UnforcedLeray.IsSpatialTest ψ → ∀ H : Space → Space,
      Continuous H → Integrable (fun x => ψ x • H x) := fun ψ hψ H hH =>
    (hψ.smooth.continuous.smul hH).integrable_of_hasCompactSupport (hψ.compact.smul_right (f' := H))
  refine ⟨fun φ hφ => hint _ (isSpatialTest_derivative hφ j) _ hFτ,
    fun φ hφ => hint _ hφ _ hGτ, fun φ hφ => ?_⟩
  have hA := hint _ (isSpatialTest_derivative hφ j) _ hFτ
  have hB := hint _ hφ _ hGτ
  ext k
  have hAk : (∫ x, UnforcedLeray.spatialTestDerivative j φ x • F τ x) k =
      ∫ x, UnforcedLeray.spatialTestDerivative j φ x * F τ x k := by
    have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hA
    simpa using this.symm
  have hBk : (∫ x, φ x • G τ x) k = ∫ x, φ x * G τ x k := by
    have := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hB
    simpa using this.symm
  have hFk : Continuous (fun y => F τ y k) := (EuclideanSpace.proj k).continuous.comp hFτ
  have hGk : Continuous (fun y => G τ y k) := (EuclideanSpace.proj k).continuous.comp hGτ
  have hdφ := isSpatialTest_derivative hφ j
  have hz := slice_core hP F G hFc hGc hFp hGp j φ hφ k
    (fun χ hχ hχp => hid φ hφ k χ hχ hχp) τ
  rw [integral_add (integrable_testMul _ hdφ.compact hdφ.smooth.continuous _ hFk)
    (integrable_testMul _ hφ.compact hφ.smooth.continuous _ hGk)] at hz
  rw [hAk, PiLp.neg_apply, hBk]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
