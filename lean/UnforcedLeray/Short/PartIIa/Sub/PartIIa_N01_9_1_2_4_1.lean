import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `PartII-a:N01/9/1/2/4/1` (decomposition): `SlabDivZero`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  `g ∈ solenoidalHC 0 c` is orthogonal to
`cgrad 0 Φ` for every profile test (proved here: `orthWeakForm`); the weak equation for the smooth
representative `F` gives the classical divergence (`SlabWeakToClassical`, remaining).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest)

/-- **(W)** If the smooth force `F` satisfies the weak equation `∫ ⟪cgrad 0 Φ, F⟫ dμ_H = 0` for all
profile tests `Φ`, then every slice `F(σ,·)` is classically divergence free (weight `s^{-3/2}`
depends on `s` only; fundamental lemma on the open box `s>0, q∈(0,c)`, then continuity and
`q`-periodicity; `σ ≤ 0` trivial as `F = 0` there). -/
def SlabWeakToClassical : Prop :=
  ∀ c : ℝ, 0 < c → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    (∀ Φ : ProfileTest c,
      ∫ p, @inner ℂ _ _ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 p) (F p) ∂(measureH c) = 0) →
    ∀ σ y, slabDiv F σ y = 0

theorem orthWeakForm (c : ℝ) (g : HSpace c MeridC)
    (hg : g ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c) (F : Profile → MeridC)
    (hgF : (g : Profile → MeridC) =ᵐ[measureH c] F) (Φ : ProfileTest c) :
    ∫ p, @inner ℂ _ _ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 p) (F p) ∂(measureH c) = 0 := by
  have hm := UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0) Φ.2
  have horth := UnforcedLeray.Short.PartIIa.NearGradMemberAux.gen_mem_orth (ε := 0) Φ.2 hm
  have h0 : @inner ℂ _ _ (hm.toLp _) g = 0 := Submodule.inner_left_of_mem_orthogonal hg horth
  rw [MeasureTheory.L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp, hgF] with p h1 h2
  rw [h1, h2]

theorem slabDivZero_of (h : SlabWeakToClassical) : SlabDivZero := by
  intro c hc g hg F hF hgF σ y
  exact h c hc F hF (fun Φ => orthWeakForm c g hg F hgF Φ) σ y

end UnforcedLeray.Short.PartIIa.N01
