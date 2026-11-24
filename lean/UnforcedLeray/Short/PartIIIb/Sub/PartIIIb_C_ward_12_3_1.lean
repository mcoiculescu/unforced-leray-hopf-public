import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain

/-!
# `BgCorrGradGraph` from the Y_p gradient and the differentiated equation (source 2525-2541)

Task `PartIII-b:C/ward/12/3/1`.  Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **`Dw ∈ Y_p`** (source 2533, "Also `Dw ∈ Y_p` is already known"; `bg:common-body-graph`
gradient bound, 1351-1362): in the situation of `BgCorrGradGraph` the correction `w` has
distributional derivatives `∂_jw = g_j ∈ Y_{q₀}`. -/
def BgCorrGradY : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
        ∃ g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
          ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g j)

/-- **The differentiated equation** `A₀D_jw = f_j + ½D_jw` with right side in `Y_p`
(source 2525-2537: `A₀w = f - 𝐏(V·∇w + w·∇V + w·∇w)`, `∂_jA₀w = (A₀ - ½)∂_jw`,
`‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}`, the complete source `f ∈ W^{1,Y_p}`, 2542-2551; `w ∈ L^∞`
from `bg:supremum-embedding`, 1515-1531): for every distributional gradient `g` of `w` in `Y_p`,
each `g_j` satisfies `(0 + L₀ᵗ-transpose) g_j = F_j` in distributions with `F_j ∈ Y_p`. -/
def BgCorrGradEq : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
        ∀ g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
          (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g j)) →
          ∀ j : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
            HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T p.ν Φ) (g j) F

theorem gammaR_q0E_pos : 0 < UnforcedLeray.Short.PartIIa.gammaR UnforcedLeray.B0412.q0E := by
  unfold UnforcedLeray.B0412.q0E
  have h0 : (0 : ℝ) ≤ UnforcedLeray.B0281.q0 := by rw [UnforcedLeray.B0281.q0_eq]; norm_num
  simp only [UnforcedLeray.Short.PartIIa.gammaR, ENNReal.toReal_ofReal h0]
  rw [UnforcedLeray.B0281.q0_eq]; norm_num

theorem q0E_gt_one : 1 < UnforcedLeray.B0412.q0E := by
  unfold UnforcedLeray.B0412.q0E
  rw [UnforcedLeray.B0281.q0_eq, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem q0E_lt_three : UnforcedLeray.B0412.q0E < 3 := by
  unfold UnforcedLeray.B0412.q0E
  rw [UnforcedLeray.B0281.q0_eq]
  have : (3 : ENNReal) = ENNReal.ofReal 3 := by simp
  rw [this]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-- `BgCorrGradGraph` from the two statements above and the maximal domain at shift zero. -/
theorem bgCorrGradGraph_of (h1 : BgCorrGradY) (h2 : BgCorrGradEq) : BgCorrGradGraph := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min (min ν₁ ν₂) (dm ^ 3 / 12), lt_min (lt_min hν₁ hν₂) (by positivity), ?_⟩
  intro p d hreg hν hmode z hPE
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνd : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hνd
  obtain ⟨g, hg⟩ := H1 p d hreg hνa hmode z hPE
  have hmem : ∀ j, g j ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E := by
    intro j
    obtain ⟨F, hF⟩ := H2 p d hreg hνb hmode z hPE g hg j
    exact UnforcedLeray.Short.PartIIa.commonBodyMaximalDomain UnforcedLeray.B0412.q0E
      q0E_gt_one q0E_lt_three p.period hP1 p.ν p.ν_pos 0 (by simpa using gammaR_q0E_pos) (g j) F hF
  exact ⟨fun j => ⟨g j, hmem j⟩, hg⟩

end UnforcedLeray.Short.PartIIIb.Concrete
