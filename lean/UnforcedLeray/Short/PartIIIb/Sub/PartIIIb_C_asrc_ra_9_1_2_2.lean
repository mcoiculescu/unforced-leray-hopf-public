import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

/-!
# `PartIII-b:C/asrc/ra/9/1/2/2` : `ringLapRule` from the meridional second-order chain rule

Source: `the November 2 reference manuscript` lines 5034-5039 (`Δ(√s b)`), 4979-4980.

`Nv R b τ = liftMer (ρ,z) ↦ (R/ρ) • b (chartM R τ (ρ,z))` off the axis (`Nv_eq_liftMer`), so by
`vecLap_liftMer` the physical Laplacian is the lift of `vecLapMer` of that profile. The remaining
analytic content is `RingLapMerChain`, the second-order chain rule for the meridional profile.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The ring chart as a function of the meridional coordinates `(ρ, z)`. -/
def chartM (R τ : ℝ) (m : ℝ × ℝ) : Chart :=
  (R ^ 2 / m.1 ^ 2, (R * τ / 2 - (R / 2) * Real.log (R ^ 2 / m.1 ^ 2), R * m.2 / m.1))

theorem chart_eq_chartM (R τ : ℝ) (y : Space) : chart R τ y = chartM R τ (mer y) := rfl

/-- `Nv` is the meridional lift of `(ρ,z) ↦ (R/ρ) b(chartM)` off the axis. -/
theorem Nv_eq_liftMer {R : ℝ} (hR : 0 < R) (b : Chart → Merid) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) :
    Nv R b τ y = liftMer (fun m => (R / m.1) • b (chartM R τ m)) y := by
  rw [Nv, liftMer_eq_frameL, ← chart_eq_chartM, map_smul, sqrt_age hR hy]
  rfl

/-- The profile `(ρ,z) ↦ (R/ρ) b(chartM R τ (ρ,z))` is `C²` on `ρ > 0` when `b` is `C²` on `s > 0`. -/
theorem contDiffOn_ringProfile {R : ℝ} (hR : 0 < R) {b : Chart → Merid}
    (hb : ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ)) (τ : ℝ) :
    ContDiffOn ℝ 2 (fun m : ℝ × ℝ => (R / m.1) • b (chartM R τ m)) (Ioi 0 ×ˢ univ) := by
  have h1 : ∀ m ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), m.1 ≠ 0 := fun m hm => (ne_of_gt hm.1)
  have hs : ContDiffOn ℝ 2 (fun m : ℝ × ℝ => R ^ 2 / m.1 ^ 2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div (contDiff_fst.pow 2).contDiffOn fun m hm => pow_ne_zero 2 (h1 m hm)
  have hspos : ∀ m ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), R ^ 2 / m.1 ^ 2 ≠ 0 := fun m hm =>
    div_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (h1 m hm))
  have hch : ContDiffOn ℝ 2 (chartM R τ) (Ioi 0 ×ˢ univ) := by
    unfold chartM
    refine hs.prodMk (ContDiffOn.prodMk ?_ ?_)
    · exact contDiffOn_const.sub (contDiffOn_const.mul (hs.log hspos))
    · exact contDiffOn_const.mul contDiff_snd.contDiffOn |>.div contDiff_fst.contDiffOn h1
  have hmaps : MapsTo (chartM R τ) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun m hm =>
    ⟨div_pos (pow_pos hR 2) (pow_pos hm.1 2), trivial⟩
  exact (contDiffOn_const.div contDiff_fst.contDiffOn h1).smul (hb.comp hch hmaps)

/-- **Second-order meridional chain rule** (source 5034-5039): for `b` of class `C²` on `s > 0`,
`Δ_vec-mer[(R/ρ) b∘chartM] = (R/ρ)(R²/ρ²) {Δ_{q,η} b - 2ε(𝒦+1)∂_q b + ε²(𝒦+1)² b - ε² b_r e_r}∘chartM`,
`ε = R⁻¹` (`radial_chain`, `axial_chain` applied twice; `vecLapMer` includes the `-b_r/ρ²` term). -/
def RingLapMerChain : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (b : Chart → Merid), ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ) →
    ∀ (τ : ℝ) (m : ℝ × ℝ), 0 < m.1 →
      vecLapMer (fun m' => (R / m'.1) • b (chartM R τ m')) m =
        ((R / m.1) * (R ^ 2 / m.1 ^ 2)) •
          (lapQE b (chartM R τ m) - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) (chartM R τ m)
            + (R⁻¹) ^ 2 • K1 (K1 b) (chartM R τ m) - (R⁻¹) ^ 2 • erProj (b (chartM R τ m)))

theorem ringLapRule_of (h : RingLapMerChain) : RingLapRule := by
  intro R hR b hb τ y hy
  have hprof := contDiffOn_ringProfile hR hb τ
  have hev : Nv R b τ =ᶠ[nhds y] liftMer (fun m => (R / m.1) • b (chartM R τ m)) := by
    filter_upwards [(isClosed_axis.isOpen_compl).mem_nhds hy] with z hz
    exact Nv_eq_liftMer hR b τ hz
  have e1 : physLap (Nv R b τ) y = vecLap (liftMer (fun m => (R / m.1) • b (chartM R τ m))) y := by
    unfold physLap physPd2 physPd vecLap
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev' : (fun x => fderiv ℝ (Nv R b τ) x (coordinateVector i)) =ᶠ[nhds y]
        fun x => fderiv ℝ (liftMer (fun m => (R / m.1) • b (chartM R τ m))) x (coordinateVector i) := by
      filter_upwards [(isClosed_axis.isOpen_compl).eventually_mem hy] with z hz
      have : Nv R b τ =ᶠ[nhds z] liftMer (fun m => (R / m.1) • b (chartM R τ m)) := by
        filter_upwards [(isClosed_axis.isOpen_compl).mem_nhds hz] with w hw
        exact Nv_eq_liftMer hR b τ hw
      rw [this.fderiv_eq]
    rw [hev'.fderiv_eq]
  rw [e1, vecLap_liftMer hprof hy, Nv_eq_liftMer hR _ τ hy]
  have hm := h R hR b hb τ (mer y) (ϱ_pos hy)
  simp only [liftMer]
  rw [hm]
  simp only [chartM, smul_smul, mer]

end UnforcedLeray.Short.PartIIIb.Concrete
