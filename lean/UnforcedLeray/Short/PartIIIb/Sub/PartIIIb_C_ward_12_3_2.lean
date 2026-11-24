import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain

/-!
# `BgCorrHessGraph` from the Y_p Hessian and the twice differentiated equation (source 2542-2559)

Task `PartIII-b:C/ward/12/3/2`.  Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **`D²w ∈ Y_p`** (source 2552-2559: "if derivatives through order `k` are in the graph, all
factors through order `k` are bounded and derivatives through order `k+2` are in `Y_p`"; `g_j ∈ D_p`
gives `∇g_j ∈ Y_p` by `bg:common-body-graph`, 1351-1362): the distributional derivatives
`∂_lg_j = k_{jl}` exist in `Y_{q₀}`. -/
def BgCorrHessY : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
      ∀ g : Fin 3 → UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E,
        (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z)
          (g j : Yq p.period UnforcedLeray.B0412.q0E)) →
        ∃ k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
          ∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ)
            (g j : Yq p.period UnforcedLeray.B0412.q0E) (k j l)

/-- **The twice differentiated equation** `A₀∂_l g_j = ∂_lf_j + ∂_lg_j` with right side in `Y_p`
(source 2542-2559: one factor of each order-`(k+1)` derivative of `w·∇w` in `L^∞`
(`bg:supremum-embedding`, 1515-1531, applied to `w, Dw ∈ D_p`), the other in `Y_p`; complete
source in `W^{2,Y_p}`, 2542-2551): every distributional `∂_lg_j = k_{jl} ∈ Y_p` satisfies
`(0 + L₀ᵗ-transpose) k_{jl} = F` in distributions with `F ∈ Y_p`. -/
def BgCorrHessEq : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
      ∀ g : Fin 3 → UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E,
        (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z)
          (g j : Yq p.period UnforcedLeray.B0412.q0E)) →
        ∀ k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
          (∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ)
            (g j : Yq p.period UnforcedLeray.B0412.q0E) (k j l)) →
          ∀ j l : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
            HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T p.ν Φ) (k j l) F

theorem gammaR_q0E_pos2 : 0 < UnforcedLeray.Short.PartIIa.gammaR UnforcedLeray.B0412.q0E := by
  unfold UnforcedLeray.B0412.q0E
  have h0 : (0 : ℝ) ≤ UnforcedLeray.B0281.q0 := by rw [UnforcedLeray.B0281.q0_eq]; norm_num
  simp only [UnforcedLeray.Short.PartIIa.gammaR, ENNReal.toReal_ofReal h0]
  rw [UnforcedLeray.B0281.q0_eq]; norm_num

theorem q0E_gt_one2 : 1 < UnforcedLeray.B0412.q0E := by
  unfold UnforcedLeray.B0412.q0E
  rw [UnforcedLeray.B0281.q0_eq, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem q0E_lt_three2 : UnforcedLeray.B0412.q0E < 3 := by
  unfold UnforcedLeray.B0412.q0E
  rw [UnforcedLeray.B0281.q0_eq]
  have : (3 : ENNReal) = ENNReal.ofReal 3 := by simp
  rw [this]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-- `BgCorrHessGraph` from the two statements above and the maximal domain at shift zero. -/
theorem bgCorrHessGraph_of (h1 : BgCorrHessY) (h2 : BgCorrHessEq) : BgCorrHessGraph := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min (min ν₁ ν₂) (dm ^ 3 / 12), lt_min (lt_min hν₁ hν₂) (by positivity), ?_⟩
  intro p d hreg hν hmode z hPE g hg
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνd : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hνd
  obtain ⟨k, hk⟩ := H1 p d hreg hνa hmode z hPE g hg
  have hmem : ∀ j l, k j l ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E := by
    intro j l
    obtain ⟨F, hF⟩ := H2 p d hreg hνb hmode z hPE g hg k hk j l
    exact UnforcedLeray.Short.PartIIa.commonBodyMaximalDomain UnforcedLeray.B0412.q0E
      q0E_gt_one2 q0E_lt_three2 p.period hP1 p.ν p.ν_pos 0 (by simpa using gammaR_q0E_pos2)
      (k j l) F hF
  exact ⟨fun j l => ⟨k j l, hmem j l⟩, hk⟩

end UnforcedLeray.Short.PartIIIb.Concrete
