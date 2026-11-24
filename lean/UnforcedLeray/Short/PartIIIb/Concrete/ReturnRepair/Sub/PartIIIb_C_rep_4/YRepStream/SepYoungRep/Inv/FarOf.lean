import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.Far
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarNear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Lin.Helpers

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv` by the far bridge (organizer `ORG:C-review/far-bridge`)

Source `the November 2 reference manuscript`
3593-3594, 3596-3626, 3902-3912, 4163-4174, 5303-5306.

`SepYoungRep` without the density route (`SepSmoothResponse`, `SepOldDensity`, `SepYoungCont`):
`S_μ F = S_N F + S_far F`; the near part of the old stress vanishes on the young receiver
(`sepFarNearVanish`, proved in `Inv/FarNear.lean`); the far part is the masked kernel response
(`FarBridge.farBridge_ae_of`, `Inv/Far.lean`) wherever the order-zero gap majorant is finite
(`SepFarAbs`), and there it is `-W_μ` (`SepFarId`).  The separated representative `T` is the one of
`SepOldSrcFinite` (`inv/2`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`S_Nχ_oT = 0` on the young receiver, along the sequence** (5303-5306): for large `n`,
`z ∈ [-1,1]`, every stress `T`, at a.e. output of age `ν s ≤ 1`. -/
theorem sepFarNearVanish (dm dp : ℝ) :
    ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ∀ᵐ p ∂(ageμ (cOf (D.level n).ν) (-3 / 2)), (D.level n).ν * p.1 ≤ 1 →
          (SNop D.Pl D.K (D.level n) (D.mu n z) (ftOld D.Pl D.K (D.level n) T) :
            Chart → Merid) p = 0 := by
  intro D hst
  obtain ⟨ν₂, hν₂, hrho⟩ :=
    NearInst.ns_rhoB_le D.K.m0 D.K.C0 dm dp D.K.k0 hst.C0_pos hst.m0_lt
  have hdm : 0 < dm := hst.dm_pos
  have hapos : 0 < D.K.b * dm := mul_pos hst.b_pos hdm
  have hlim : 0 < min ν₂ ((D.K.b * dm) ^ 2 / 2) := lt_min hν₂ (by positivity)
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₂ ((D.K.b * dm) ^ 2 / 2) :=
    Filter.Tendsto.eventually_le_const hlim (retNu_tendsto D.σ₀ hst.omega_ne)
  filter_upwards [hst.actual, hst.pins, muWin_gt_quarter D hst, hsmall] with n hact hpins hmu hs
  intro z hz T
  have hreg := hact.regime
  have hνn : (D.level n).ν ≤ ν₂ := hs.trans (min_le_left _ _)
  have hνa : (D.level n).ν ≤ (D.K.b * dm) ^ 2 / 2 := hs.trans (min_le_right _ _)
  have h1 := nyo_core_lt D.Pl D.K (D.level n) (D.mu n z) (by linarith [hmu z hz])
    (by linarith [hst.mZ_gt])
    (NearInst.ns_rhoB_pos ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 hst.C0_pos)
    (hrho _ _ hreg hνn) hst.δ_pos hst.δ_lt (scut_ge_inv D.Pl D.K (D.level n) hst.b_pos hreg hνa)
    (hpins z hz).near T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  filter_upwards [h1, ageμ_fst_eq_null (cOf (D.level n).ν) (-3 / 2) (1 / (D.level n).ν)]
    with p hp hne hle
  apply hp
  refine lt_of_le_of_ne ?_ hne
  rw [le_div_iff₀ hν]
  linarith

/-- **Absolute convergence of the masked `sep:resolvent` integral at a young receiver** (3604-3621
`sep:kernel`, 3905-3912, 4187-4194, 5169-5176): for a stress `F` with chart representatives
`g₁ g₂` and a separated representative `T` of `g₁ + g₂` (`SepRepOf`: old disk, `T = oldPhys`
a.e., finite `L²_τL^{22/19}` norm), the order-zero gap majorant of the lift of the measurable
representative `strSum F` is finite at a.e. young chart point at the gap
`(1 - e^{-δ/2})R/√s`.  (`cartLift (strSum F) = T` a.e. in `(τ, z)`: `ChartOfNullPullback`; `sepDom`
sees the a.e. class of the source; `IIIa.sepDomPointwise` for the fixed gap
`(1 - e^{-δ/2})R√ν ≤ (1 - e^{-δ/2})R/√s` with `p = 22/19`, `b = 22/3`, finite `L²_τ` norm gives
a.e. finite phase, periodicity, and `τ ↦ chartTau` preserves null sets; `sepDom` is antitone in
the gap.) -/
def SepFarAbs (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ (F : LStr D.Pl D.K (D.level n)) (g₁ g₂ : Chart → Ten3)
      (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
      IsRep D.Pl D.K (D.level n) F g₁ g₂ → SepRepOf (D.level n) (D.mu n z) (g₁ + g₂) T →
      ∀ᵐ x ∂(ageμ (cOf (D.level n).ν) (-3 / 2)), (D.level n).ν * x.1 ≤ 1 →
        UnforcedLeray.Short.IIIa.sepDom (2 * D.mu n z + 2) 0
            ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ / Real.sqrt x.1)
            (UnforcedLeray.Short.IIIa.srcNorm
              (NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F)))
            (NearInst.chartTau (D.level n).ε⁻¹ x) (NearInst.chartY (D.level n).ε⁻¹ x) < ⊤

/-- **The masked far output of an old source is `-W_μ` at a young receiver** (3611-3621, 3905-3912,
4163-4174): same data as `SepFarAbs`; at a.e. young chart point `νs ≤ 1` the output
`farOut` of the measurable representative `strSum F` equals `-coefOf (wardW …(g₁ + g₂))`.
(`e^δ < 12/11 < 6/5` and `νs ≤ 1 ≤ ν S` make the mask `e^δ s < R²/|z'|²` inactive on the old disk
`|z'|² ≤ R²·5ν/6` carrying `T`, and `T` vanishes outside it, so the masked lift of `strSum F` is
`T` a.e. in `(τ, z)` (`ChartOfNullPullback`); `SepWCongrAE` gives `sepWfar = sepW T`; with
`wardW = sepWre T` from `SepRepOf` and `merRe`/`coefOf` reading the components 0 and 2 the
identity is pointwise; the single age `s = S` is a null set.) -/
def SepFarId (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ (F : LStr D.Pl D.K (D.level n)) (g₁ g₂ : Chart → Ten3)
      (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
      IsRep D.Pl D.K (D.level n) F g₁ g₂ → SepRepOf (D.level n) (D.mu n z) (g₁ + g₂) T →
      ∀ᵐ x ∂(ageμ (cOf (D.level n).ν) (-3 / 2)), (D.level n).ν * x.1 ≤ 1 →
        NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) (strSum F) x =
          -coefOf (D.level n).ε⁻¹ (wardW (D.level n).ν (D.mu n z) (D.level n).ε⁻¹
            (cOf (D.level n).ν) (g₁ + g₂)) x

/-- **`SepYoungRep` by the far bridge**: `S_μ(χ_oM_{r_b}w)` is `-W_μ` on the young region, from
the far mask `Sop - SNop = S_far`, the vanishing of the near part, the bridge identity
(`FarOutTruncTendsto`), the separated representative of `inv/2` and the two leaves above. -/
theorem sepYoungRepFar_of (dm dp : ℝ) (hD : FarBridge.FarOutTruncTendsto)
    (hFar : ∀ (Pl : PlanarData) (σ₀ mZ : ℝ), SopSubIsFarSeq Pl σ₀ mZ dm dp)
    (h2 : SepOldSrcFinite dm dp) (hA : SepFarAbs dm dp) (hI : SepFarId dm dp) :
    SepYoungRep dm dp := by
  intro D hst
  filter_upwards [hFar D.Pl D.σ₀ D.K.mZ D rfl rfl rfl hst, sepFarNearVanish dm dp D hst,
    h2 D hst, hA D hst, hI D hst, muWin_gt_quarter D hst] with n a1 a2 a3 a4 a5 a6 z hz
  obtain ⟨Sf, hSf, hsplit⟩ := a1 z hz
  intro w g₁ g₂ hg
  obtain ⟨T, hT⟩ := a3 z hz w g₁ g₂ hg
  exact youngFar_core hD (by linarith [a6 z hz]) hst.δ_pos
    (NearInst.ns_rhoB_pos ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 hst.C0_pos)
    hSf hsplit (oldRep D.Pl D.K (D.level n) w) (g₁ + g₂) (strSum (oldRep D.Pl D.K (D.level n) w))
    (strSum_measurable_lin _) Filter.EventuallyEq.rfl
    (a2 z hz (repPart (multOp D.Pl D.K (D.level n) w)))
    (a4 z hz _ g₁ g₂ T hg hT) (a5 z hz _ g₁ g₂ T hg hT)

end UnforcedLeray.Short.PartIIIb.Concrete
