import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2

/-!
# `PartIII-b:C/asrc/kflat/1` : decomposition of `frakTOldFinite`

Source of record: `the November 2 reference manuscript`.

`FrakTOldFinite` (`OldThinFinite` of `𝔗A`) is the conjunction of
* `FrakTMeasProp` (defined in `PartIII-b_C_asrc_kflat_2`): a.e. strong measurability of `𝔗A` on the
  old region (joint measurability of `(u,x) ↦ symOuter (trainMer (u,x)) (kcMer (ξ_B(u)) x)`);
* `FrakTIntProp` : integrability of `u^{-3/2}|𝔗A|` on `u > 1.2/ν` (source 4637-4640, the `k = 0`
  case of `flat-return:all-moments`, proof 4677-4694), in the regime of `FrakTOldFinite`:
  `m > 8`, `ν ≤ ν₀`, BUC trains (the full forward estimate `prop:short-full-clock`, 2836-2860, and
  the later-age estimates 4432-4458 hold only for `ν` small and the actual train).

`FrakTIntProp` is decomposed in `PartIII-b_C_asrc_kflat_1_2.lean` (`frakTIntProp_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Integrability of `u^{-3/2}|𝔗A|` on the old region (source 4637-4640 with `k = 0`, 4677-4694),
for `m > 8` (2826), `ν ≤ ν₀` and BUC trains (270-288). -/
def FrakTIntProp (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ ε : ℝ)
    (χo : ℝ → ℝ) (hν : 0 < ν), ν ≤ ν₀ → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatInstData κ ν (cOf ν) m tr) (A : ℝ → Mat3), IsAffElem as A →
      Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
        frob (frakT (levelFlat hν FI χo ε) ν μ χf A p)) (oldMeasure (cOf ν) ν)

theorem frakTOldFinite_of (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)]
    (hM : FrakTMeasProp as χf m) (hI : FrakTIntProp as χf m) : FrakTOldFinite as χf m := by
  intro hχ hm
  obtain ⟨ν₀, hν₀, hI'⟩ := hI hχ hm
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro κ ν μ ε χo hν hνs hμ0 hμ1 tr htr FI A hA
  exact ⟨hM hχ κ ν μ ε χo hν (hνs.trans (min_le_right _ _)) hμ0 hμ1 tr FI A hA,
    hI' κ ν μ ε χo hν (hνs.trans (min_le_left _ _)) hμ0 hμ1 tr htr FI A hA⟩

end UnforcedLeray.Short.PartIIIb.Concrete
