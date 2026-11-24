import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.SliceTaylor.Bounds

/-!
# Part II-a, audit decomposition of `PartII-a:F09/1/3/1/1` (`sliceFwdSpatialTaylor`)

Source `the November 2 reference manuscript` lines 1403-1413 and 1426-1428.
The forward free action `S_ν(s) = freeEvolution ν s` has generator
`G u = νΔu + ½ y·∇u + ½ u = -(L₀ - ∂_τ) u` on a slice. The slice Taylor bound is the Re/Im
splitting (`FwdSliceDecomp`) of a real forward Taylor bound (`FwdSpatialTaylorReal`, the mirror of
`AdjointTaylor` for `freeEvolution`), with the uniform slice bounds of `SliceCalc.exists_uniform_bound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- The forward generator `G u = νΔu + ½ y·∇u + ½ u` on real spatial fields
(`= -(L₀ - ∂_τ)` on a slice, lines 1403-1413). -/
def fwdGen (ν : ℝ) (u : SpatialField) : SpatialField :=
  fun y => ν • B0418.vecLaplacian u y + (1 / 2 : ℝ) • fderiv ℝ u y y + (1 / 2 : ℝ) • u y

/-- The real forward remainder on a slice of a phase test, for a real component functional `K`. -/
def fwdXk (ν s : ℝ) (K : CVec3 →L[ℝ] Space) (t : ℝ) (Φ : ℝ × Space → CVec3) (y : Space) : Space :=
  AncientLocalization.freeEvolution ν s (fun z => K (Φ (t, z))) y - K (Φ (t, y)) -
    s • fwdGen ν (fun z => K (Φ (t, z))) y

/-- **Real forward second-order Taylor bound** (mirror of `AdjointTaylor`, lines 1403-1413,
1426-1428): for `ν > 0`, `R`, `1 ≤ p < ∞` there is `C` such that for every smooth real field `u`
supported in `‖y‖ ≤ R` with the six derivative quantities bounded by `M` and `0 < r ≤ 1`,
`‖S_ν(r)u - u - r G u‖_p ≤ C M r²`. -/
def FwdSpatialTaylorReal : Prop :=
  ∀ (ν R : ℝ) (p : ℝ≥0∞), 0 < ν → 1 ≤ p → p ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (u : SpatialField), ContDiff ℝ ∞ u → (∀ y, R < ‖y‖ → u y = 0) →
      (∀ y, ‖u y‖ ≤ M ∧ ‖fderiv ℝ u y‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M ∧
        ‖B0418.vecLaplacian u y‖ ≤ M ∧ ‖fderiv ℝ (B0418.vecLaplacian u) y‖ ≤ M ∧
        ‖B0418.vecLaplacian (B0418.vecLaplacian u) y‖ ≤ M) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        eLpNorm (fun y => AncientLocalization.freeEvolution ν r u y - u y - r • fwdGen ν u y) p
          volume ≤ ENNReal.ofReal (C * M * r ^ 2)

/-- **Measurability of the forward remainder** on a slice of a smooth `Φ`
(`freeEvolution` of a continuous field is measurable, `B0418.measurable_flow_uncurry`). -/
def FwdXkMeas : Prop :=
  ∀ (ν s : ℝ) (K : CVec3 →L[ℝ] Space) (t : ℝ) {Φ : ℝ × Space → CVec3}, ContDiff ℝ ∞ Φ →
    Measurable (fwdXk ν s K t Φ)

/-- **Re/Im splitting of the forward slice remainder** (`B0421.coeFn_freeC`, `L₀ - ∂_τ = -G`
slicewise): a.e. in `y`,
`(S_ν(s) Φ_t - Φ_t + s(L₀Φ_t - ∂_τΦ_t))(y) = ofReV (fwdXk reV) + ofImV (fwdXk imV)`. -/
def FwdSliceDecomp : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (P : ℝ) [Fact (0 < P)] (ν : ℝ)
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) (t s : ℝ),
    ⇑(B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t) - sliceMap (hΦ.isSliceTest p).2 t +
        (s : ℂ) • (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t -
          sliceMap (hΦ.dτ.isSliceTest p).2 t)) =ᵐ[volume]
      fun y => ofReV (fwdXk ν s reV t Φ y) + ofImV (fwdXk ν s imV t Φ y)

set_option maxHeartbeats 1600000 in
/-- **`sliceFwdSpatialTaylor` from the real forward Taylor bound, the measurability and the
Re/Im splitting.** -/
theorem sliceFwdSpatialTaylor_of (h1 : FwdSpatialTaylorReal) (h2 : FwdXkMeas)
    (h3 : FwdSliceDecomp) :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν →
    ∀ (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, 0 < s → s ≤ 1 →
      ‖B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t) - sliceMap (hΦ.isSliceTest p).2 t +
        (s : ℂ) • (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t -
          sliceMap (hΦ.dτ.isSliceTest p).2 t)‖ ≤ C * s ^ 2 := by
  intro p _ hp P _ ν hν Φ hΦ
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨C₀, hC₀, hT⟩ := h1 ν R p hν hp1 hp
  obtain ⟨M, hM0, hM⟩ := SliceCalc.exists_uniform_bound hΦ
  refine ⟨2 * C₀ * M, mul_nonneg (mul_nonneg (by norm_num) hC₀) hM0, fun t s hs0 hs1 => ?_⟩
  have hpart : ∀ K : CVec3 →L[ℝ] Space, ‖K‖ ≤ 1 →
      eLpNorm (fun y => fwdXk ν s K t Φ y) p volume ≤ ENNReal.ofReal (C₀ * M * s ^ 2) := by
    intro K hK
    have hu : ContDiff ℝ ∞ (fun z : Space => K (Φ (t, z))) :=
      K.contDiff.comp (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id))
    have hsupp : ∀ y : Space, R < ‖y‖ → (fun z : Space => K (Φ (t, z))) y = 0 :=
      fun y hy => by
        show K (Φ (t, y)) = 0
        rw [hR t y hy, map_zero]
    exact hT M _ hu hsupp (fun y => hM K hK t y) s hs0 hs1
  have hm1 : AEStronglyMeasurable (fun y => ofReV (fwdXk ν s reV t Φ y)) volume :=
    (ofReV.continuous.measurable.comp (h2 ν s reV t hΦ.smooth)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y => ofImV (fwdXk ν s imV t Φ y)) volume :=
    (ofImV.continuous.measurable.comp (h2 ν s imV t hΦ.smooth)).aestronglyMeasurable
  have hnn : 0 ≤ C₀ * M * s ^ 2 := mul_nonneg (mul_nonneg hC₀ hM0) (sq_nonneg s)
  have hbd : eLpNorm (fun y => ofReV (fwdXk ν s reV t Φ y) + ofImV (fwdXk ν s imV t Φ y))
        p volume ≤ ENNReal.ofReal (2 * C₀ * M * s ^ 2) := by
    calc eLpNorm (fun y => ofReV (fwdXk ν s reV t Φ y) + ofImV (fwdXk ν s imV t Φ y))
          p volume
        ≤ eLpNorm (fun y => ofReV (fwdXk ν s reV t Φ y)) p volume +
            eLpNorm (fun y => ofImV (fwdXk ν s imV t Φ y)) p volume :=
          eLpNorm_add_le hm1 hm2 hp1
      _ ≤ eLpNorm (fwdXk ν s reV t Φ) p volume + eLpNorm (fwdXk ν s imV t Φ) p volume :=
          add_le_add (SliceCalc.eLpNorm_clm_le ofReV norm_ofReV_le _ p)
            (SliceCalc.eLpNorm_clm_le ofImV norm_ofImV_le _ p)
      _ ≤ ENNReal.ofReal (C₀ * M * s ^ 2) + ENNReal.ofReal (C₀ * M * s ^ 2) :=
          add_le_add (hpart reV norm_reV_le) (hpart imV norm_imV_le)
      _ = ENNReal.ofReal (2 * C₀ * M * s ^ 2) := by
          rw [← ENNReal.ofReal_add hnn hnn]
          congr 1
          ring
  rw [Lp.norm_def, eLpNorm_congr_ae (h3 p hp P ν Φ hΦ t s)]
  have hnn2 : 0 ≤ 2 * C₀ * M * s ^ 2 := by positivity
  exact ENNReal.toReal_le_of_le_ofReal hnn2 hbd

end UnforcedLeray.Short.PartIIa
