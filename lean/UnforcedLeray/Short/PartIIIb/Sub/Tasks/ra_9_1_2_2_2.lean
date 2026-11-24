import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/2/2` : axial derivative of the weighted ring profile

Source: `the November 2 reference manuscript` lines 5034-5039 (`axial_chain`).
In `chartM R τ (ρ,z) = (R²/ρ², (Rτ/2 - (R/2) log(R²/ρ²), R z/ρ))` only the third component
depends on `z`, with `∂_z (R z/ρ) = R/ρ`; the weight `(R/ρ)^k` is `z`-independent.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The chart curve `z ↦ chartM R τ (ρ₀, z)` and its `z`-derivative `(0, (0, R/ρ₀))`. -/
theorem ra2222_chartCurve_z (R τ t : ℝ) (ht : t ≠ 0) (z0 : ℝ) :
    HasDerivAt (fun z' : ℝ => chartM R τ (t, z')) ((0 : ℝ), ((0 : ℝ), R / t)) z0 := by
  have h3 : HasDerivAt (fun z' : ℝ => R * z' / t) (R / t) z0 := by
    have h := ((hasDerivAt_id' z0).const_mul R).div_const t
    refine h.congr_deriv ?_
    ring
  exact (hasDerivAt_const z0 (R ^ 2 / t ^ 2)).prodMk
    ((hasDerivAt_const z0 (R * τ / 2 - (R / 2) * Real.log (R ^ 2 / t ^ 2))).prodMk h3)

/-- Axial chain rule for the weighted ring profile (source 5034-5039). -/
theorem ringWeightedDz {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ} (hR : 0 < R) (k : ℕ) {c : Chart → E} (hc : ContDiffOn ℝ 1 c (Set.Ioi 0 ×ˢ Set.univ)) (τ : ℝ) {m : ℝ × ℝ} (hm : 0 < m.1) : dz (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m = (R / m.1) ^ (k + 1) • UnforcedLeray.Axi.dEta c (chartM R τ m) := by
  have hRne : R ≠ 0 := hR.ne'
  have htne : m.1 ≠ 0 := hm.ne'
  have hmem : chartM R τ m ∈ (Ioi 0 ×ˢ univ : Set Chart) :=
    ⟨div_pos (pow_pos hR 2) (pow_pos hm 2), trivial⟩
  have hcd : DifferentiableAt ℝ c (chartM R τ m) :=
    (hc.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by norm_num)
  have h1 : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), m'.1 ≠ 0 := fun m' hm' => ne_of_gt hm'.1
  have hs : ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => R ^ 2 / m'.1 ^ 2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div (contDiff_fst.pow 2).contDiffOn fun m' hm' => pow_ne_zero 2 (h1 m' hm')
  have hspos : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), R ^ 2 / m'.1 ^ 2 ≠ 0 := fun m' hm' =>
    div_ne_zero (pow_ne_zero 2 hRne) (pow_ne_zero 2 (h1 m' hm'))
  have hch : ContDiffOn ℝ 1 (chartM R τ) (Ioi 0 ×ˢ univ) := by
    unfold chartM
    refine hs.prodMk (ContDiffOn.prodMk ?_ ?_)
    · exact contDiffOn_const.sub (contDiffOn_const.mul (hs.log hspos))
    · exact (contDiffOn_const.mul contDiff_snd.contDiffOn).div contDiff_fst.contDiffOn h1
  have hmaps : MapsTo (chartM R τ) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun m' hm' =>
    ⟨div_pos (pow_pos hR 2) (pow_pos hm'.1 2), trivial⟩
  have hF : ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m'))
      (Ioi 0 ×ˢ univ) :=
    ((contDiffOn_const.div contDiff_fst.contDiffOn h1).pow k).smul (hc.comp hch hmaps)
  have hmem' : m ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)) := ⟨hm, trivial⟩
  have hFd : DifferentiableAt ℝ (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m :=
    (hF.differentiableOn (by norm_num)).differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem')
  have hγ : HasDerivAt (fun z : ℝ => ((m.1, z) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) m.2 :=
    (hasDerivAt_const m.2 m.1).prodMk (hasDerivAt_id' m.2)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt m.2 hγ
  have hA : HasDerivAt (fun z : ℝ => (R / m.1) ^ k • c (chartM R τ (m.1, z)))
      ((R / m.1) ^ k • ((R / m.1) • UnforcedLeray.Axi.dEta c (chartM R τ m))) m.2 := by
    have hg : HasDerivAt (fun z : ℝ => c (chartM R τ (m.1, z)))
        (fderiv ℝ c (chartM R τ m) ((0 : ℝ), ((0 : ℝ), R / m.1))) m.2 :=
      hcd.hasFDerivAt.comp_hasDerivAt m.2 (ra2222_chartCurve_z R τ m.1 htne m.2)
    have h := (hasDerivAt_const m.2 ((R / m.1) ^ k)).smul hg
    refine h.congr_deriv ?_
    rw [clm_triple]
    unfold UnforcedLeray.Axi.dEta
    match_scalars <;> ring
  have hkey := hcomp.unique hA
  show fderiv ℝ (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m (0, 1) = _
  rw [hkey, smul_smul, ← pow_succ]

end UnforcedLeray.Short.PartIIIb.Concrete
