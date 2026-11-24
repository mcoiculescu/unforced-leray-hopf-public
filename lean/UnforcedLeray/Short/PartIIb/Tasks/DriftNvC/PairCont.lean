import UnforcedLeray.Short.PartIIb.Sub.T08
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.Congr
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.HolderBound
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.NvCAlg

/-!
# Part II-b, task `PartII-b:T08/3`: continuity of the phase pairing in the `H_r` norm

Source of record: `the November 2 reference manuscript`, lines 1902-1906.
Proof: `N_v` is additive, `‖N_v b‖_{Y_r} = (πR²)^{1/r}‖b‖_{H_r}` (`phaseLpNorm_NvC`), and a Hölder
bound `|⟨Φ, u⟩| ≤ K‖u‖_{Y_r}` (`phase_holder_bound`), after replacing each profile by a measurable
everywhere-periodic representative (`periodicRepresentative`, `chartNullPullback`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The representative data for `b ∈ H_r`: measurable, everywhere periodic `b'`, a null set `M`,
with equal `H_r` norm and equal pairing of the lifts. -/
theorem pairCont_rep {c r ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (Φ : ℝ × Space → CVec3)
    (b : CProf) (hb : InHr c r b) :
    ∃ (b' : CProf) (M : Set Coord), Measurable b' ∧
      (∀ s ξ η, b' (s, (ξ + c, η)) = b' (s, (ξ, η))) ∧ MeasurableSet M ∧ volume M = 0 ∧
      (∀ x : Coord, 0 < x.1 → x ∉ M → b x = b' x) ∧ hNorm c r b' = hNorm c r b ∧
      pairF (2 * ε * c) Φ (NvC ε⁻¹ b) = pairF (2 * ε * c) Φ (NvC ε⁻¹ b') := by
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hbb'⟩ :=
    periodicRepresentative c r hc b hb.periodic hb.meas
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hnull := chartNullPullback ε⁻¹ c (2 * ε * c) hR hc hP M hMm hM0 hMper
  exact ⟨b', M, hb'm, hb'per, hMm, hM0, hbb', (hNorm_congr_of_null hc b b' M hMm hM0 hbb').symm,
    pairF_NvC_congr ε⁻¹ (2 * ε * c) hR Φ b b' M hbb' hnull⟩

theorem driftPairCont_proof : UnforcedLeray.Short.IIb.DriftPairCont := by
  intro c r ε Φ hc hε hr hΦ b bn hb hbn hlim
  have hr0 : 0 < r := by linarith
  have hP0 : 0 < 2 * ε * c := by positivity
  obtain ⟨K, hK⟩ := phase_holder_bound (2 * ε * c) r hP0 hr Φ hΦ
  set C0 : ℝ := (Real.pi * (ε⁻¹) ^ 2) ^ (1 / r) with hC0
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hbb', hNb', hpb⟩ := pairCont_rep hc hε Φ b hb
  choose bn' Mn hbn'm hbn'per hMnm hMn0 hbbn' hNbn' hpbn using
    fun n => pairCont_rep hc hε Φ (bn n) (hbn n)
  -- finiteness and measurability of the lifts
  have hfinNvC : ∀ g : CProf, Measurable g → (∀ s ξ η, g (s, (ξ + c, η)) = g (s, (ξ, η))) →
      hNorm c r g ≠ ⊤ → phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ g) ≠ ⊤ := by
    intro g hgm hgper hgfin
    rw [phaseLpNorm_NvC hc hr0 hε g (Filter.Eventually.of_forall fun x => hgper x.1 x.2.1 x.2.2)
      hgm.aestronglyMeasurable]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgfin
  have hbound : ∀ n, ‖pairF (2 * ε * c) Φ (NvC ε⁻¹ (bn n)) - pairF (2 * ε * c) Φ (NvC ε⁻¹ b)‖ ≤
      K * C0 * (hNorm c r (fun x => bn n x - b x)).toReal := by
    intro n
    set d' : CProf := fun x => bn' n x - b' x with hd'
    have hd'm : Measurable d' := (hbn'm n).sub hb'm
    have hd'per : ∀ s ξ η, d' (s, (ξ + c, η)) = d' (s, (ξ, η)) := by
      intro s ξ η; simp only [hd', hbn'per n, hb'per]
    have hfb' : hNorm c r b' ≠ ⊤ := by rw [hNb']; exact hb.finite.ne
    have hfbn' : hNorm c r (bn' n) ≠ ⊤ := by rw [hNbn' n]; exact (hbn n).finite.ne
    have hfd' : hNorm c r d' ≠ ⊤ := by
      have := eLpNorm_sub_le (μ := hMeas c r) (p := ENNReal.ofReal r)
        (hbn'm n).aestronglyMeasurable hb'm.aestronglyMeasurable
        (ENNReal.one_le_ofReal.2 hr.le)
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfbn', hfb'⟩) this
    have hu1 := hK _ (measurable_NvC ε⁻¹ (hbn'm n)) (hfinNvC _ (hbn'm n) (hbn'per n) hfbn')
    have hu2 := hK _ (measurable_NvC ε⁻¹ hb'm) (hfinNvC _ hb'm hb'per hfb')
    have hud := hK _ (measurable_NvC ε⁻¹ hd'm) (hfinNvC _ hd'm hd'per hfd')
    -- linearity of the pairing
    have hlin : pairF (2 * ε * c) Φ (NvC ε⁻¹ d') =
        pairF (2 * ε * c) Φ (NvC ε⁻¹ (bn' n)) - pairF (2 * ε * c) Φ (NvC ε⁻¹ b') := by
      rw [hd', NvC_sub]
      unfold pairF
      have hdiff : Integrable (fun z => dotL (Φ z) (NvC ε⁻¹ (bn' n) z - NvC ε⁻¹ b' z))
          (hSlab (2 * ε * c)) := by
        refine (hu1.1.sub hu2.1).congr (Filter.Eventually.of_forall fun z => ?_)
        simp [map_sub]
      rw [phaseInt_eq_slab hu1.1, phaseInt_eq_slab hu2.1, phaseInt_eq_slab hdiff]
      simp only [map_sub]
      rw [integral_sub hu1.1 hu2.1, smul_sub]
    have hnorms : hNorm c r d' = hNorm c r (fun x => bn n x - b x) := by
      symm
      refine hNorm_congr_of_null hc _ d' (Mn n ∪ M) (hMnm n |>.union hMm)
        (measure_union_null (hMn0 n) hM0) ?_
      intro x hx hxM
      simp only [hd']
      rw [← hbbn' n x hx (fun h => hxM (Or.inl h)), ← hbb' x hx (fun h => hxM (Or.inr h))]
    rw [hpbn n, hpb, ← hlin]
    refine hud.2.trans ?_
    rw [phaseLpNorm_NvC hc hr0 hε d' (Filter.Eventually.of_forall fun x => hd'per x.1 x.2.1 x.2.2)
      hd'm.aestronglyMeasurable, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      hnorms]
    exact le_of_eq (by ring)
  have ht : Tendsto (fun n => (hNorm c r (fun x => bn n x - b x)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hsq : Tendsto (fun n => pairF (2 * ε * c) Φ (NvC ε⁻¹ (bn n)) -
      pairF (2 * ε * c) Φ (NvC ε⁻¹ b)) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    simpa using ht.const_mul (K * C0)
  simpa using hsq.add_const (pairF (2 * ε * c) Φ (NvC ε⁻¹ b))

end UnforcedLeray.Short.IIb
