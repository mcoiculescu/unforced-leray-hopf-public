import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1_4
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4/4`: measurability of the stress integrand (Leaf B)

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

`stressF R c g Φ x = Σ_{ij} (strPhys R c g x)_{ij} ∂_jΦ_i(x)`.  The chart point `chartOf` is measurable
(floor), `cylFrame` has measurable entries, `nsSym` is continuous (linear), `dy j Φ` is continuous
(`IsPhaseTest.dy`), and finite sums and products of measurable functions are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray UnforcedLeray.Axi UnforcedLeray.PhaseSpace

instance hh2_matrix_secondCountable : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))

theorem hh2_hRad_measurable : Measurable fun z : Space => UnforcedLeray.Short.PartIIIb.NearInst.hRad z := by
  unfold UnforcedLeray.Short.PartIIIb.NearInst.hRad
  fun_prop

theorem hh2_nsSym_continuous :
    Continuous (fun T : UnforcedLeray.Short.PartIIIb.Concrete.Ten3 =>
      UnforcedLeray.Short.PartIIIb.NearInst.nsSym T) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  fin_cases a <;> fin_cases b <;>
    simp [UnforcedLeray.Short.PartIIIb.NearInst.nsSym, UnforcedLeray.Short.PartIIIb.NearInst.symRZ] <;>
    fun_prop

theorem hh2_cylFrame_measurable :
    Measurable UnforcedLeray.Short.PartIIIb.NearInst.cylFrame := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have hR' := hh2_hRad_measurable
  have hz0 : Measurable fun z : Space => z 0 := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable
  have hz1 : Measurable fun z : Space => z 1 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable
  fin_cases i <;> fin_cases j <;>
    simp [UnforcedLeray.Short.PartIIIb.NearInst.cylFrame] <;>
    fun_prop

theorem hh2_chartOf_measurable (R c : ℝ) :
    Measurable fun x : ℝ × Space => UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c x.2 x.1 := by
  unfold UnforcedLeray.Short.PartIIIb.NearInst.chartOf UnforcedLeray.Short.PartIIIb.NearInst.hRad
  have hz2 : Measurable fun z : Space => z 2 :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable
  fun_prop

set_option maxHeartbeats 1000000 in
theorem hh2_strPhys_matrix_measurable (R c : ℝ) (g : UnforcedLeray.Short.PartIIIb.Concrete.Chart →
      UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (hg : Measurable g) :
    Measurable (UnforcedLeray.Short.PartIIIb.Concrete.strPhys R c g) := by
  have hX : Measurable fun x : ℝ × Space =>
      (UnforcedLeray.Short.PartIIIb.NearInst.cylFrame x.2,
        (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c x.2 x.1).1,
        UnforcedLeray.Short.PartIIIb.NearInst.nsSym
          (g (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c x.2 x.1))) := by
    refine ((hh2_cylFrame_measurable).comp measurable_snd).prodMk
      ((measurable_fst.comp (hh2_chartOf_measurable R c)).prodMk ?_)
    exact (hh2_nsSym_continuous.measurable).comp (hg.comp (hh2_chartOf_measurable R c))
  have hQ : Continuous fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
      p.1 * (p.2.1 • p.2.2) * Matrix.transpose p.1 := by
    have h1 : Continuous fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ × Matrix (Fin 3) (Fin 3) ℝ => p.1 :=
      continuous_fst
    have h2 : Continuous fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
        p.2.1 • p.2.2 :=
      (continuous_fst.comp continuous_snd).smul (continuous_snd.comp continuous_snd)
    have h3 : Continuous fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
        Matrix.transpose p.1 :=
      h1.matrix_transpose
    exact (h1.matrix_mul h2).matrix_mul h3
  have key := hQ.measurable.comp hX
  exact key

theorem hh2_strPhys_entry_measurable (R c : ℝ) (g : UnforcedLeray.Short.PartIIIb.Concrete.Chart →
      UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (hg : Measurable g) (i j : Fin 3) :
    Measurable fun x : ℝ × Space =>
      UnforcedLeray.Short.PartIIIb.Concrete.strPhys R c g x i j := by
  have hS := hh2_strPhys_matrix_measurable R c g hg
  exact (Matrix.measurable_apply (i := i) (j := j)).comp hS

theorem stressMeasurable_proof : UnforcedLeray.Short.PartIIIb.Concrete.StressMeasurable := by
  intro R c P Φ hR hc hP hΦ g hg
  have hcont : ∀ j : Fin 3, Continuous (dy j Φ) := fun j =>
    (UnforcedLeray.PhaseSpace.IsPhaseTest.dy hΦ j).continuous
  have hm : ∀ i j : Fin 3, Measurable fun x : ℝ × Space =>
      ((UnforcedLeray.Short.PartIIIb.Concrete.strPhys R c g x i j : ℝ) : ℂ) * dy j Φ x i := by
    intro i j
    have hcoord : Measurable fun x : ℝ × Space => dy j Φ x i :=
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp (hcont j)).measurable
    exact (Complex.measurable_ofReal.comp (hh2_strPhys_entry_measurable R c g hg i j)).mul hcoord
  unfold UnforcedLeray.Short.PartIIIb.Concrete.stressF
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hm i j

end
