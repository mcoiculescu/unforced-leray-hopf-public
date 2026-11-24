import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4
import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub

/-!
# `RawDerivRes` from the weak identity and the `Y_{q₀}` derivative of the raw residual

Task `PartIII-b:C/ward/12/3/1/2/4/1`.  Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-- **Weak derivative of the raw residual lies in `Y_{q₀}`** (source 2542-2551 with the `U_raw`
derivative bounds 1206-1222: the unprojected derivatives of the train complete source are
`O(ϱ^{-3-k}(1+|y₃|/ϱ)^{-N})`, whose `q₀`-th integral over the period cell is finite).
For the BUC train, `c = ν⁻²`, `R ≥ 2`, `ν` small and period `≤ 1`, and each `j`, there is
`G ∈ Y_{q₀}` (`G = -∂_j F_R`) with `⟪∂_jΦ, F_R⟫ = ⟪Φ, G⟫` for every solenoidal phase test. -/
def RawResidualDerivY : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j : Fin 3,
      ∃ G : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
        pairF p.period (dy j Φ) (UnforcedLeray.Short.IIb.rawResidualC p) =
          phasePair p.period UnforcedLeray.B0412.q0E Φ G

theorem two_le_R_of_regime {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ dm) : 2 ≤ p.R := by
  have hν0 := p.ν_pos
  have hdm := hreg.dm_pos
  have hd : dm ≤ d := hreg.dm_le
  have h1 : 1 ≤ d / p.ν := by
    rw [le_div_iff₀ hν0]; linarith
  have h2 := Real.add_one_le_exp (d / p.ν)
  have h3 : p.R = Real.exp (d / p.ν) := by
    show p.ε⁻¹ = _
    rw [hreg.eps_eq, ← Real.exp_neg, neg_div, neg_neg]
  rw [h3]; linarith

theorem rawDerivRes_of (h₁ : UnforcedLeray.Short.IIb.RawResidualWeakIdentity)
    (h₂ : RawResidualDerivY) : RawDerivRes := by
  obtain ⟨ν₁, hν₁, H1⟩ := h₁
  obtain ⟨ν₂, hν₂, H2⟩ := h₂
  intro lam q _ dm dp hdm
  refine ⟨min (min (ν₁ / 2) (ν₂ / 2)) (min dm (dm ^ 3 / 12)), ?_, ?_⟩
  · have : 0 < dm ^ 3 / 12 := by positivity
    positivity
  intro p d hreg hν _ z g _ j
  have hνa : p.ν ≤ ν₁ / 2 := (hν.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb : p.ν ≤ ν₂ / 2 := (hν.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνc : p.ν ≤ dm := (hν.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hνd : p.ν ≤ dm ^ 3 / 12 := (hν.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hR := two_le_R_of_regime hreg hνc
  have hP := bgCorr_period_le_one hreg hνd
  obtain ⟨G, hG⟩ := H2 p hreg.train_buc (by linarith) hreg.c_eq hR hP j
  refine ⟨G, fun Φ hΦ => ?_⟩
  rw [H1 p hreg.train_buc (by linarith) hreg.c_eq hR (dy j Φ) (gEW_isSolTest_dy hΦ j)]
  exact hG Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
