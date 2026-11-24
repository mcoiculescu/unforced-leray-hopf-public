import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarOf

/-!
# `PartIII-b:C/rep/4/2/org/1/1/2/2`: `SepInvYoung` by the far bridge (organizer `ORG:C-review/far-bridge`)

Source `the November 2 reference manuscript`
3593-3594, 3596-3621, 3902-3912, 4155-4171, 5303-5306, 5573-5576.

The thin twin of `sepYoungRepFar_of`: the value of the weak stress inverse `S` (equal to `Sop` by
free weak uniqueness) on the thin old source `oldThin T = χ_o(T₁, 0)` is the far response (the near
part vanishes on the young receiver, `sepFarNearVanish`), which is `-W_μ` by `SepFarAbs`/`SepFarId`
(stated for every stress `F`) once the thin source has a separated representative of finite
`L²_τL^{22/19}` norm (`SepThinSrcFinite`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **A finite separated representative of an old thin source** (3596-3626, 4155-4171, 5573-5584:
the thin old mass `N_0(1.2/ν) ≤ C ν^{1/2}‖T‖_{Z_1} < ∞` and the `Z_1` weights give the
`L²_τL^{22/19}` norm of the lift, the old disk `|z'| ≤ ε⁻¹√(5ν/6)` being the support of `χ_o`):
for every stress `T` and representatives `g₁ g₂` of `oldThin T` there is a separated
representative of `g₁ + g₂` in the sense of `SepRepOf`. -/
def SepThinSrcFinite (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ (T : LStr D.Pl D.K (D.level n)) (g₁ g₂ : Chart → Ten3),
      IsRep D.Pl D.K (D.level n) (oldThin D.Pl D.K (D.level n) T) g₁ g₂ →
      ∃ T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, SepRepOf (D.level n) (D.mu n z) (g₁ + g₂) T'

/-- **`SepInvYoung` by the far bridge.** -/
theorem sepInvYoungFar_of (dm dp : ℝ) (hD : FarBridge.FarOutTruncTendsto)
    (hFar : ∀ (Pl : PlanarData) (σ₀ mZ : ℝ), SopSubIsFarSeq Pl σ₀ mZ dm dp)
    (h2 : SepThinSrcFinite dm dp) (hA : SepFarAbs dm dp) (hI : SepFarId dm dp) :
    SepInvYoung dm dp := by
  intro D hst
  filter_upwards [hFar D.Pl D.σ₀ D.K.mZ D rfl rfl rfl hst, sepFarNearVanish dm dp D hst,
    h2 D hst, hA D hst, hI D hst, muWin_gt_quarter D hst, periodSmall D hst, hst.pins] with
    n a1 a2 a3 a4 a5 a6 a7 a8 z hz S hS T g₁ g₂ hg
  obtain ⟨Sf, hSf, hsplit⟩ := a1 z hz
  obtain ⟨T', hT'⟩ := a3 z hz T g₁ g₂ hg
  have hU := freeWeakUniquenessAll (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν (D.level n).ε
    (D.mu n z) (cOf_pos (D.level n).ν_pos) (D.level n).ν_pos
    (D.level n).ε_pos a7 (by linarith [a6 z hz])
  have hSs : IsWeakStressInverse (Sop D.Pl D.K (D.level n) (D.mu n z)) (D.level n).ε (D.mu n z) :=
    Classical.epsilon_spec (a8 z hz).stress
  have hEq : S (oldThin D.Pl D.K (D.level n) T) =
      Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T) :=
    hU _ _ _ (hS _) (hSs _)
  rw [hEq]
  exact youngFar_core hD (by linarith [a6 z hz]) hst.δ_pos
    (NearInst.ns_rhoB_pos ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 hst.C0_pos)
    hSf hsplit (oldThin D.Pl D.K (D.level n) T) (g₁ + g₂)
    (strSum (oldThin D.Pl D.K (D.level n) T)) (strSum_measurable_lin _) Filter.EventuallyEq.rfl
    (a2 z hz (thinPart T)) (a4 z hz _ g₁ g₂ T' hg hT') (a5 z hz _ g₁ g₂ T' hg hT')

end UnforcedLeray.Short.PartIIIb.Concrete
