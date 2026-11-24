import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs
import UnforcedLeray.Units.B0592

/-!
# Part III-a, `PartIII-a:T21/2/1/2/3`: the weighted norm of an `L² + L^∞` field

Source of record: `the November 2 reference manuscript` lines 3053-3056.
Proof of `xNormSplitLe`: Minkowski in `L²(cellMeasure d (-m))`, comparison of the weighted
measure with the unweighted cell measure (the density `⟨y⟩^{-2m}` is at most `1`), and the
bounded part controlled by the total mass `∫⁻ ⟨y⟩^{-2m} = weightConst m ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem jb_one_le_xn (x : ℝ × ℝ) : 1 ≤ UnforcedLeray.B0579.jb x := by
  have h1 := sq_nonneg x.1
  have h2 := sq_nonneg x.2
  unfold UnforcedLeray.B0579.jb
  linarith

theorem density_neg_le_one_xn {m : ℝ} (hm : 0 ≤ m) (x : ℝ × ℝ) :
    (UnforcedLeray.B0579.density (-m) x : ℝ≥0∞) ≤ 1 := by
  have h : UnforcedLeray.B0579.density (-m) x ≤ 1 := by
    unfold UnforcedLeray.B0579.density
    exact Real.toNNReal_le_one.2
      (Real.rpow_le_one_of_one_le_of_nonpos (jb_one_le_xn x) (by linarith))
  exact_mod_cast h

/-- **The weighted norm of an `L² + L^∞` field** (`xNormSplitLe`, SP 3053-3056). -/
theorem xNormSplitLe (m : ℝ) : UnforcedLeray.Short.IIIa.XNormSplitLe m := by
  intro hm
  have hWfin : UnforcedLeray.B0592.weightConst m ≠ ⊤ :=
    (UnforcedLeray.B0592.weightConst_lt_top hm).ne
  refine ⟨(UnforcedLeray.B0592.weightConst m).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro d _hd f a b B hf ha hb hB
  rw [ENNReal.ofReal_toReal hWfin]
  have hle : UnforcedLeray.B0579.cellMeasure d (-m) ≤
      volume.restrict (UnforcedLeray.B0579.cell d) := by
    rw [Measure.le_iff]
    intro s hs
    rw [UnforcedLeray.B0579.cellMeasure, withDensity_apply _ hs]
    calc ∫⁻ x in s, (UnforcedLeray.B0579.density (-m) x : ℝ≥0∞)
          ∂(volume.restrict (UnforcedLeray.B0579.cell d))
        ≤ ∫⁻ x in s, 1 ∂(volume.restrict (UnforcedLeray.B0579.cell d)) :=
          setLIntegral_mono' hs (fun x _ => density_neg_le_one_xn (by linarith) x)
      _ = volume.restrict (UnforcedLeray.B0579.cell d) s := by simp
  have hmass : UnforcedLeray.B0579.cellMeasure d (-m) Set.univ ≤
      ∫⁻ x, ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (-m)) := by
    rw [UnforcedLeray.B0579.cellMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_restrict MeasurableSet.univ, Set.univ_inter]
    exact setLIntegral_le_lintegral _ _
  have huniv : UnforcedLeray.B0579.cellMeasure d (-m) Set.univ ^ (2⁻¹ : ℝ) ≤
      UnforcedLeray.B0592.weightConst m := by
    unfold UnforcedLeray.B0592.weightConst
    rw [one_div]
    exact ENNReal.rpow_le_rpow hmass (by norm_num)
  have hfμ : f =ᵐ[UnforcedLeray.B0579.cellMeasure d (-m)] a + b :=
    (UnforcedLeray.B0579.cellMeasure_ac d (-m)).ae_le hf
  show eLpNorm f 2 (UnforcedLeray.B0579.cellMeasure d (-m)) ≤ _
  calc eLpNorm f 2 (UnforcedLeray.B0579.cellMeasure d (-m))
      = eLpNorm (a + b) 2 (UnforcedLeray.B0579.cellMeasure d (-m)) := eLpNorm_congr_ae hfμ
    _ ≤ eLpNorm a 2 (UnforcedLeray.B0579.cellMeasure d (-m)) +
          eLpNorm b 2 (UnforcedLeray.B0579.cellMeasure d (-m)) :=
        eLpNorm_add_le (ha.mono_ac (UnforcedLeray.B0579.cellMeasure_ac d (-m)))
          (hb.mono_ac (UnforcedLeray.B0579.cellMeasure_ac d (-m))) (by norm_num)
    _ ≤ eLpNorm a 2 (volume.restrict (UnforcedLeray.B0579.cell d)) +
          UnforcedLeray.B0592.weightConst m * B :=
        add_le_add (eLpNorm_mono_measure a hle)
          ((eLpNorm_le_of_ae_enorm_bound (Eventually.of_forall hB)).trans (by
            rw [smul_eq_mul, ENNReal.toReal_ofNat, mul_comm]
            gcongr))

end UnforcedLeray.Short.IIIa
