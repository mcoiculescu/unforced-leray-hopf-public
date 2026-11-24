import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIa.Tasks.F08Projected

/-!
# Decomposition of `GELift` (source 1358-1359, 1393-1400, 1409-1412)

Task `PartIII-b:C/ward/12/3/1/2/8`.  Source of record
`the November 2 reference manuscript`.

`gELift_of`: with `u ∈ D` the projected solution `L u = 𝐏F` (`commonBodyProjected`, `μ = 0`,
`γ_{q₀} > 0`), `v = D_jw - u` is solenoidal and kills `L₀ᵗΦ` for solenoidal `Φ`
(`𝐏` is the identity on solenoidal tests), so `v = 0` by uniqueness and `F' = L u`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (IsSolTest Params)

/-- **`D_jw` is solenoidal** (source 2525-2537: `w ∈ Y_σ` and `∂_j` commutes with the divergence,
`⟪∇φ, ∂_jw⟫ = ⟪∇∂_jφ, w⟫ = 0`). -/
def GEGradSol : Prop := ∀ (p : Params) (z : p.Z)
    (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E), GEData p z g →
  ∀ j, g j ∈ Ysigma p.period UnforcedLeray.B0412.q0E

/-- **Uniqueness on the solenoidal sector** (source 1393-1400 maximal domain with no hidden null
space, 1409-1412, adjoint solvability on solenoidal tests): a solenoidal `v ∈ Y_{q₀}` with
`⟪L₀ᵗΦ, v⟫ = 0` for every solenoidal test `Φ` is zero (`0 < P ≤ 1`, `ν > 0`). -/
def GEBodyUniqueSol : Prop :=
  ∀ (P ν : ℝ) [Fact (0 < P)], P ≤ 1 → 0 < ν → ∀ v : Yq P UnforcedLeray.B0412.q0E,
    v ∈ Ysigma P UnforcedLeray.B0412.q0E →
    (∀ Φ, IsSolTest P Φ → phasePair P UnforcedLeray.B0412.q0E (L0T ν Φ) v = 0) → v = 0

/-- **The Leray projection is invisible to solenoidal tests** (source 1358-1359): for a
solenoidal phase test `Φ`, `⟪Φ, 𝐏F⟫ = ⟪Φ, F⟫`. -/
def GELerayPairSol : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : Yq P UnforcedLeray.B0412.q0E) (Φ : ℝ × UnforcedLeray.Space →
      UnforcedLeray.PhaseSpace.CVec3), IsSolTest P Φ →
    phasePair P UnforcedLeray.B0412.q0E Φ
        (UnforcedLeray.RieszLp.lerayY P UnforcedLeray.B0412.q0E q0E_gt_one
          (ne_top_of_lt q0E_lt_three) F) =
      phasePair P UnforcedLeray.B0412.q0E Φ F

theorem gELift_of (h1 : GEGradSol) (h2 : GEBodyUniqueSol) (h3 : GELerayPairSol) : GELift := by
  intro lam q hq dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν hmode z g hd j F hF
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν
  have hgσ := h1 p z g hd j
  obtain ⟨u, huσ, hu⟩ := UnforcedLeray.Short.PartIIa.commonBodyProjected
    UnforcedLeray.B0412.q0E q0E_gt_one q0E_lt_three p.period hP1 p.ν p.ν_pos 0
    (by simpa using gammaR_q0E_pos) F
  have hL : L0D u = UnforcedLeray.RieszLp.lerayY p.period UnforcedLeray.B0412.q0E q0E_gt_one
      (ne_top_of_lt q0E_lt_three) F := by
    have := hu
    simpa [UnforcedLeray.Short.PartIIa.bodyOp, L0L_apply] using this
  have hv : g j - (u : Yq p.period UnforcedLeray.B0412.q0E) = 0 := by
    refine h2 p.period p.ν hP1 p.ν_pos _ (Submodule.sub_mem _ hgσ huσ) ?_
    intro Φ hΦ
    rw [map_sub, hF Φ hΦ, hasPhaseOp_L0D u Φ hΦ.1, hL, h3 _ F Φ hΦ, sub_self]
  have hgu : g j = (u : Yq p.period UnforcedLeray.B0412.q0E) := sub_eq_zero.1 hv
  refine ⟨L0D u, ?_⟩
  intro Φ hΦ
  simp only [zero_smul, zero_add]
  rw [hgu]
  exact hasPhaseOp_L0D u Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
