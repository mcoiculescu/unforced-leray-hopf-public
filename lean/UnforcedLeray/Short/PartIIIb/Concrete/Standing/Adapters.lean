import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Supply
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FlatPin

/-!
# Adapters from the standing hypotheses to the roots (`ORG:C/standing` (d))

Source of record: `the November 2 reference manuscript` (73 pages).

The roots applied by the final assembly (`PartIII-b:IIIb-D5`) take lists of hypotheses on the
sequence datum `D`; with `D.RepairStanding dm dp` (and, for the source pins, the flat pin
`SeqData.IsActualFlat`) they are read off as follows.

* `PartIII-b:C/ward` (`seqWardTriple_exists`: `IsGrowingEigenpair`, `IsYoungCutoff`,
  `2m₀ < 3d₋/11`, `hact`): `RepairStanding.wardTriple` (and the fields `planar.eigenpair`,
  `chiY.isYoungCutoff`, `m0_ball`, `actual`);
* `PartIII-b:C/asrc/ra` (`raBoundExists`: `hsplit`, `hax`, `hW1`): `RepairStanding.splitMult`,
  `RepairStanding.axi`, `RepairStanding.w1`, and `RepairStanding.raBoundExists`;
* `PartIII-b:C/asrc/pins` (`IsActualFlat κ m`, `IsBUCTrain`): the flat pin is an input of the
  adapter, `RepairStanding.bucTrain` gives the trains; `RepairStanding.sourcePinHyps` collects the
  numeric hypotheses;
* `PartIII-b:C/grad/6` (`hasym`, `hnear`, `hex`, `hact`): `RepairStanding.window` (with
  `isCompact_Icc` and `RepairStanding.window_sub`), the field `near`, and
  `RepairStanding.raBoundExists`;
* `PartIII-b:C/flatset/col` (`IsPlanarReference`, a compact window in `(0, 1/4)`): the field
  `planar` and `RepairStanding.window_sub`;
* `PartIII-b:C/rep/15` (`NearChoice`, `RepairStanding`, `NearBody`): `StandingChoices.near`
  (`Concrete/Standing/Choices.lean`); `NearBody` is not a standing hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace SeqData.RepairStanding

variable {D : SeqData} {dm dp : ℝ}

/-- `hsplit` of `PartIII-b:C/asrc/ra`: the split multiplier of the pins at `z = 0` (source 2706,
3877-3878). -/
theorem splitMult (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb := by
  filter_upwards [hst.pins] with n hn
  exact (hn 0 ⟨by norm_num, by norm_num⟩).split

/-- `hax` of `PartIII-b:C/asrc/ra`: `U` is axisymmetric without swirl at the actual levels (source
121-124, 2031, 2522-2523, 4144-4145), from `short-bg:strong` on the contraction ball. -/
theorem axi (hst : D.RepairStanding dm dp) (hSR : UnforcedLeray.Short.IIb.StrongRegularity) :
    ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ) :=
  seq_axi_act (bgAxiLevels_of hSR) D hst.dm_pos hst.m0_pos hst.m0_ball hst.C0_pos
    hst.planar.eigenpair hst.omega_ne hst.actual

/-- `hW1` of `PartIII-b:C/asrc/ra`: `U - U_raw` has a finite `W^{1,∞}` bound at the actual levels
(source 2538-2541, 5007-5008, 5094), from `short-bg:strong` on the contraction ball. -/
theorem w1 (hst : D.RepairStanding dm dp) (hSR : UnforcedLeray.Short.IIb.StrongRegularity) :
    ∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d :=
  seq_W1_act (bgW1Levels_of' hSR) D hst.dm_pos hst.m0_pos hst.m0_ball hst.C0_pos
    hst.planar.eigenpair hst.omega_ne hst.actual

/-- `RABoundExists D dm dp` (source 5001-5016) from the target of `PartIII-b:C/asrc/ra` with the
standing hypotheses and `short-bg:strong`. -/
theorem raBoundExists (hst : D.RepairStanding dm dp) (hRA : RABoundSupply)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity) : RABoundExists D dm dp :=
  hRA D dm dp hst.dm_pos hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt hst.chiF
    hst.C0_pos hst.as_pos.le hst.splitMult (hst.axi hSR) (hst.w1 hSR)

/-- The Ward triple along the sequence (source 4161-4303) from the target of `PartIII-b:C/ward`
with the standing hypotheses. -/
theorem wardTriple (hst : D.RepairStanding dm dp) (hW : SeqWardTripleSupply) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
          (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U
          (D.level n).pres :=
  regimePins_ward_of hW D hst.planar.eigenpair hst.omega_ne hst.sigma_pos hst.sigma_lt
    hst.m0_pos hst.m0_ball hst.C0_pos (by linarith [hst.mZ_gt]) hst.chiY hst.actual

/-- The window `[σ₀/2, (σ₀ + 1/4)/2]` is a compact subset of `(0, 1/4)` (source 5926-5927). -/
theorem window_sub (hst : D.RepairStanding dm dp) :
    Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) ⊆ Ioo 0 (1 / 4) :=
  fun x hx => ⟨by linarith [hx.1, hst.sigma_pos], by linarith [hx.2, hst.sigma_lt]⟩

/-- `hasym` of `PartIII-b:C/grad/6` (source 2031-2037, 5926-5950): for large `n`, `ν_n ≤ 1`,
`ε_n ≤ 1` and `μ_n(z) ∈ [σ₀/2, (σ₀ + 1/4)/2]` for `z ∈ [-1, 1]`. -/
theorem window (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 ∧ retEps D.Pl D.σ₀ n ≤ 1 ∧
      ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) := by
  filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
    D.coeff_ne, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n h1 h2
  exact ⟨h1.1, h1.2, h2⟩

/-- `hbuc` of `PartIII-b:C/asrc/pins`: the trains of the actual levels are the BUC trains of Part I
(source 261-288, 397). -/
theorem bucTrain (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, UnforcedLeray.Short.PartI.IsBUCTrain (D.train n) := by
  filter_upwards [hst.actual] with n hn
  exact hn.buc

/-- The numeric and cutoff hypotheses of `PartIII-b:C/asrc/pins`
(`SeqData.eventually_isSourceLPinned_of_data`). -/
theorem sourcePinHyps (hst : D.RepairStanding dm dp) :
    D.Pl.eigenvalue.im ≠ 0 ∧ 0 < D.Pl.eigenvalue.re ∧ 0 < D.σ₀ ∧ D.σ₀ < 1 / 4 ∧
      IsStreamCutoff D.K.χy ∧ IsSourceCutoffC D.K.χf ∧ 3 / 2 < D.K.mZ ∧ 0 < D.K.as :=
  ⟨hst.omega_ne, hst.gamma_pos, hst.sigma_pos, hst.sigma_lt, hst.chiY, hst.chiF, hst.mZ_gt,
    hst.as_pos⟩

end SeqData.RepairStanding

end UnforcedLeray.Short.PartIIIb.Concrete
