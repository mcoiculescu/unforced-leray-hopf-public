import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1
import UnforcedLeray.Short.PartIIb.Bridge.Dict

/-!
# Part II-b, task `PartII-b:T10/7/1/1/1` (`GLUniq`): uniqueness of weak derivatives

Source of record: `the November 2 reference manuscript` lines 1912-1921.

Target: `gl_uniq : UnforcedLeray.Short.IIb.GLUniq`.

Proof outline. The fields `f, f'` are in `Y_r` (`r > 1`, so `q := ofReal r ≥ 1`). Their Y_q
representatives `toYq` (Bridge/Dict.lean) have the same phase pairings against every phase test
(`phasePair_eq_pairF_of_hasRepY` turns the phase pairing into `pairF`), so they are equal in
`Y_q` by `eq_of_forall_phasePair`. Two jointly measurable representatives of one element of
`Y_q` agree a.e. (`ae_eq_of_hasRepY_pair`: slicewise a.e. equality, then Fubini on the
measurable representatives).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

/-- Two jointly measurable representatives of one element of `Y_q` agree a.e. -/
theorem ae_eq_of_hasRepY_pair {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {F : Yq P q} {W W' : ℝ × Space → CVec3} (hW : HasRepY F W) (hW' : HasRepY F W') :
    W =ᵐ[volume] W' := by
  have hslice : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W (τ, y) = W' (τ, y) := by
    filter_upwards [hW.slice, hW'.slice] with τ h1 h2
    filter_upwards [h1, h2] with y e1 e2
    exact e1.trans e2.symm
  have hsm : StronglyMeasurable (hW.meas.mk W) := hW.meas.stronglyMeasurable_mk
  have hsm' : StronglyMeasurable (hW'.meas.mk W') := hW'.meas.stronglyMeasurable_mk
  have e1 : W =ᵐ[volume] hW.meas.mk W := hW.meas.ae_eq_mk
  have e1' : W' =ᵐ[volume] hW'.meas.mk W' := hW'.meas.ae_eq_mk
  have e1p : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W (τ, y) = hW.meas.mk W (τ, y) := by
    refine Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W z = hW.meas.mk W z) ?_
    rw [← Measure.volume_eq_prod]
    exact e1
  have e1p' : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W' (τ, y) = hW'.meas.mk W' (τ, y) := by
    refine Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = hW'.meas.mk W' z) ?_
    rw [← Measure.volume_eq_prod]
    exact e1'
  have hA : ∀ᵐ τ : ℝ, ∀ᵐ y : Space,
      hW.meas.mk W (τ, y) = hW'.meas.mk W' (τ, y) := by
    filter_upwards [e1p, e1p', hslice] with τ a1 a2 a3
    filter_upwards [a1, a2, a3] with y b1 b2 b3
    rw [← b1, ← b2, b3]
  have hAll : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      hW.meas.mk W x = hW'.meas.mk W' x := by
    refine (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      ?_).2 hA
    exact measurableSet_eq_fun hsm.measurable hsm'.measurable
  filter_upwards [e1, e1', hAll] with x h1 h2 h3
  rw [h1, h2, h3]

theorem gl_uniq : UnforcedLeray.Short.IIb.GLUniq := by
  intro P r f f' hP hr1 hf hf' hpair
  have : Fact (0 < P) := ⟨hP⟩
  have hr : 0 < r := lt_trans zero_lt_one hr1
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.2 hr1.le⟩
  have hFG : toYq P r hr f hf = toYq P r hr f' hf' := by
    refine eq_of_forall_phasePair fun Φ hΦ => ?_
    rw [phasePair_eq_pairF_of_hasRepY _ f (toYq_hasRepY P r hr f hf) hΦ,
      phasePair_eq_pairF_of_hasRepY _ f' (toYq_hasRepY P r hr f' hf') hΦ]
    exact hpair Φ hΦ
  have h2 : HasRepY (toYq P r hr f hf) f' := by
    rw [hFG]
    exact toYq_hasRepY P r hr f' hf'
  exact ae_eq_of_hasRepY_pair (toYq_hasRepY P r hr f hf) h2

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_uniq
