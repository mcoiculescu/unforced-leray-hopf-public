import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/8/6`: gluing local `C^∞` versions (`stGlueLocal`)

Each `p ∈ U` gets a ball `B p` and a `C^∞` version `G p` on it.  On an overlap of two balls the
two versions are continuous and a.e. equal to `F`, hence equal.  The glued function is
`q ↦ G q q`; a countable subcover (`countable_cover_nhdsWithin`) makes the a.e. identity hold
for all points of `U` at once.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Short.IIIa

theorem stGlueLocal : STGlueLocal := by
  intro U hU F hloc
  have hloc' : ∀ p : STSpace, ∃ r : ℝ, ∃ G : STSpace → ℂ, p ∈ U →
      (0 < r ∧ ball p r ⊆ U ∧ ContDiffOn ℝ ∞ G (ball p r) ∧
        ∀ᵐ q ∂(volume : Measure STSpace), q ∈ ball p r → G q = F q) := by
    intro p
    by_cases hp : p ∈ U
    · obtain ⟨r, hr, hrU, G, hG, hGae⟩ := hloc p hp
      exact ⟨r, G, fun _ => ⟨hr, hrU, hG, hGae⟩⟩
    · exact ⟨1, fun _ => 0, fun h => absurd h hp⟩
  choose R G hRG using hloc'
  have hover : ∀ p q, p ∈ U → q ∈ U → EqOn (G p) (G q) (ball p (R p) ∩ ball q (R q)) := by
    intro p q hp hq
    obtain ⟨-, -, hCp, hAp⟩ := hRG p hp
    obtain ⟨-, -, hCq, hAq⟩ := hRG q hq
    have hopen : IsOpen (ball p (R p) ∩ ball q (R q)) := isOpen_ball.inter isOpen_ball
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure STSpace)) ?_ hopen
      ((hCp.mono inter_subset_left).continuousOn) ((hCq.mono inter_subset_right).continuousOn)
    refine (ae_restrict_iff' hopen.measurableSet).mpr ?_
    filter_upwards [hAp, hAq] with x hxp hxq hx
    rw [hxp hx.1, hxq hx.2]
  have hF' : ContDiffOn ℝ ∞ (fun q => G q q) U := by
    refine contDiffOn_of_locally_contDiffOn fun p hp => ?_
    obtain ⟨hRpos, -, hCp, -⟩ := hRG p hp
    refine ⟨ball p (R p), isOpen_ball, mem_ball_self hRpos, ?_⟩
    refine (hCp.mono inter_subset_right).congr fun x hx => ?_
    exact (hover x p hx.1 hp) ⟨mem_ball_self (hRG x hx.1).1, hx.2⟩
  refine ⟨fun q => G q q, hF', ?_⟩
  obtain ⟨t, htU, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (R x)) (s := U)
    (fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hRG x hx).1))
  have hae : ∀ᵐ q ∂(volume : Measure STSpace), ∀ x (_hx : x ∈ t),
      q ∈ ball x (R x) → G x q = F q := by
    refine (ae_ball_iff htc).2 fun x hx => ?_
    exact (hRG x (htU hx)).2.2.2
  filter_upwards [hae] with q hq hqU
  obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp (hcov hqU)
  calc G q q = G x q := hover q x hqU (htU hx) ⟨mem_ball_self (hRG q hqU).1, hqx⟩
    _ = F q := hq x hx hqx

end UnforcedLeray.Short.IIIa
