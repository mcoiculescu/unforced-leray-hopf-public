import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.Dense.SmoothProf
import UnforcedLeray.Lib.PlanarSectorsB.SectorSum

/-!
# Part I, task `PartI:S11/1/2/2`: finite smooth sector sums are dense in `L²_M`

Source: `the November 2 reference manuscript`, lines 841-889.
Proof: for `g` and `e > 0`, the finite sector truncation `∑_{n∈F} secEmb n (secProf n g)` is
within `e/2` of `g` (`Planar.hasSum_secEmb_secProf`); each profile `secProf n g` is approximated
by a smooth compactly supported profile within `δ = e/(2(|F|+1))` (`smoothProfDense_proof`);
`secEmb n` is a linear isometry, so the finite sums are within `|F|·δ < e/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem smoothSectorSumsDenseL2_proof : UnforcedLeray.Short.PartI.SmoothSectorSumsDenseL2 := by
  intro M hM
  have hd : Dense {h : Planar.ProfL2 M | IsSmoothCptProfile M h} :=
    smoothProfDense_proof hM
  rw [Metric.dense_iff]
  intro g e he
  have hT : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, Planar.secEmb M n (Planar.secProf M n g))
      atTop (𝓝 g) := Planar.hasSum_secEmb_secProf g
  obtain ⟨F, hF⟩ := (Metric.tendsto_nhds.1 hT (e / 2) (half_pos he)).exists
  have hF' : dist (∑ n ∈ F, Planar.secEmb M n (Planar.secProf M n g)) g < e / 2 := hF
  set δ : ℝ := e / (2 * ((F.card : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδeq : δ * (2 * ((F.card : ℝ) + 1)) = e := by
    rw [hδdef]
    field_simp
  have happ : ∀ m : ℤ, ∃ y : Planar.ProfL2 M,
      IsSmoothCptProfile M y ∧ dist y (Planar.secProf M m g) < δ := by
    intro m
    obtain ⟨y, hyS, hy⟩ := hd.exists_dist_lt (Planar.secProf M m g) hδpos
    exact ⟨y, hyS, by rw [dist_comm]; exact hy⟩
  choose w hw hwd using happ
  refine ⟨∑ m ∈ F, Planar.secEmb M m (w m), ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball]
    have hclose : dist (∑ m ∈ F, Planar.secEmb M m (w m))
        (∑ m ∈ F, Planar.secEmb M m (Planar.secProf M m g)) ≤ ∑ _m ∈ F, δ := by
      apply dist_sum_sum_le_of_le
      intro m _
      rw [(Planar.secEmb M m).isometry.dist_eq]
      exact (hwd m).le
    rw [Finset.sum_const, nsmul_eq_mul] at hclose
    have hcard : (F.card : ℝ) * δ < e / 2 := by
      nlinarith [hδeq, hδpos]
    have htri := dist_triangle (∑ m ∈ F, Planar.secEmb M m (w m))
      (∑ m ∈ F, Planar.secEmb M m (Planar.secProf M m g)) g
    linarith
  · exact ⟨F, w, fun m _ => hw m, rfl⟩

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.smoothSectorSumsDenseL2_proof
