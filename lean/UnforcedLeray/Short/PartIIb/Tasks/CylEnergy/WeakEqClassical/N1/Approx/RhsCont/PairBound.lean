import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3

/-!


Source: `the November 2 reference manuscript`
(SP 2074-2105). The bounded `g` is an element of `X_{-m}` with norm at most
`A * ‖jb^{-m/2}‖_{L²(cell)}`, and the duality `B0579.abs_integral_mul_le` gives the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem cylPair_integrable_jb_neg {m : ℝ} (hm : 1 < m) :
    Integrable (fun x : B0579.Plane => B0579.jb x ^ (-m)) volume := by
  have h1 : Integrable (fun t : ℝ => ((1 : ℝ) + ‖t‖ ^ 2) ^ (-m / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hm)
  have h2 : Integrable (fun z : ℝ × ℝ =>
      ((1 : ℝ) + ‖z.1‖ ^ 2) ^ (-m / 2) * ((1 : ℝ) + ‖z.2‖ ^ 2) ^ (-m / 2))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact h1.mul_prod h1
  refine Integrable.mono' h2 (B0579.continuous_jb_rpow _).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  simp only [Real.norm_eq_abs, sq_abs]
  have hsplit : B0579.jb x ^ (-m) = B0579.jb x ^ (-m / 2) * B0579.jb x ^ (-m / 2) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [hsplit]
  have ha : B0579.jb x ^ (-m / 2) ≤ ((1 : ℝ) + x.1 ^ 2) ^ (-m / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold B0579.jb; linarith [sq_nonneg x.2])
      (by linarith)
  have hb : B0579.jb x ^ (-m / 2) ≤ ((1 : ℝ) + x.2 ^ 2) ^ (-m / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold B0579.jb; linarith [sq_nonneg x.1])
      (by linarith)
  exact mul_le_mul ha hb (Real.rpow_nonneg (B0579.jb_pos x).le _) (Real.rpow_nonneg (by positivity) _)

theorem cylPair_memLp_jb {m : ℝ} (hm : 1 < m) (c : ℝ) :
    MemLp (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2 (volume.restrict (B0579.cell c)) := by
  have hae : AEStronglyMeasurable (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2))
      (volume.restrict (B0579.cell c)) :=
    (B0579.continuous_jb_rpow _).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  refine (cylPair_integrable_jb_neg hm).restrict.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  congr 1
  push_cast
  ring

/-- The constant `K = ‖⟨x⟩^{-m}‖_{L²(cell)}` of the pairing bound. -/
def cylPairK (c m : ℝ) : ℝ :=
  (eLpNorm (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2 (volume.restrict (B0579.cell c))).toReal

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb in
theorem cylPairBound : UnforcedLeray.Short.IIb.CylPairBound := by
  intro m hm c hc
  have hm1 : 1 < m := by linarith
  refine ⟨cylPairK c m, ENNReal.toReal_nonneg, ?_⟩
  intro ω g A hω hg hgA
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, trivial⟩
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (hgA _ hx0)
  have hB := cylPair_memLp_jb hm1 c
  have hbound : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖B0579.jb x ^ ((-m) / 2) * g x‖ ≤ A * B0579.jb x ^ ((-m) / 2) := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), mul_comm A]
    exact mul_le_mul_of_nonneg_left (hgA x hx) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  have hH : MemLp (fun x => B0579.jb x ^ ((-m) / 2) * g x) 2 (volume.restrict (B0579.cell c)) :=
    MemLp.of_le (hB.const_mul A)
      ((B0579.continuous_jb_rpow _).aestronglyMeasurable.mul hg)
      (hbound.mono fun x hx => hx.trans (le_of_eq (Real.norm_of_nonneg
        (mul_nonneg hA (Real.rpow_nonneg (B0579.jb_pos x).le _))).symm))
  have hG : MemLp g 2 (B0579.cellMeasure c (-m)) := by
    refine ⟨hg.mono_ac (B0579.cellMeasure_ac c (-m)), ?_⟩
    rw [B0579.eLpNorm_cellMeasure]
    exact hH.2
  have hle : eLpNorm (fun x => B0579.jb x ^ ((-m) / 2) * g x) 2 (volume.restrict (B0579.cell c))
      ≤ ENNReal.ofReal A * eLpNorm (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2
          (volume.restrict (B0579.cell c)) := by
    calc _ ≤ eLpNorm (fun x => A * B0579.jb x ^ ((-m) / 2)) 2 (volume.restrict (B0579.cell c)) :=
          eLpNorm_mono_ae_real hbound
      _ = ‖A‖ₑ * eLpNorm (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2
          (volume.restrict (B0579.cell c)) := eLpNorm_const_smul A _ 2 _
      _ = ENNReal.ofReal A * eLpNorm (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2
          (volume.restrict (B0579.cell c)) := by rw [Real.enorm_eq_ofReal hA]
  have hgX : ‖hG.toLp g‖ ≤ cylPairK c m * A := by
    calc ‖hG.toLp g‖
        = (eLpNorm (fun x => B0579.jb x ^ ((-m) / 2) * g x) 2
            (volume.restrict (B0579.cell c))).toReal := by
          rw [Lp.norm_toLp g hG, B0579.eLpNorm_cellMeasure]
      _ ≤ (ENNReal.ofReal A * eLpNorm (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2
            (volume.restrict (B0579.cell c))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.2.ne) hle
      _ = A * cylPairK c m := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
          rfl
      _ = cylPairK c m * A := mul_comm _ _
  have hint : ∫ x in B0579.cell c, ω x * g x
      = ∫ x in B0579.cell c, (hω.toLp ω : B0579.Plane → ℝ) x * (hG.toLp g : B0579.Plane → ℝ) x := by
    refine integral_congr_ae ?_
    have h1 := (B0579.ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hω).symm
    have h2 := (B0579.ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp hG).symm
    filter_upwards [h1, h2] with x h1 h2
    rw [h1, h2]
  have hlin := B0579.abs_integral_mul_le c m (hω.toLp ω) (hG.toLp g)
  have hfin : ‖hω.toLp ω‖ = (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal := Lp.norm_toLp ω hω
  calc |∫ x in B0579.cell c, ω x * g x|
      = |∫ x in B0579.cell c, (hω.toLp ω : B0579.Plane → ℝ) x * (hG.toLp g : B0579.Plane → ℝ) x| := by
        rw [hint]
    _ ≤ ‖hω.toLp ω‖ * ‖hG.toLp g‖ := hlin
    _ ≤ ‖hω.toLp ω‖ * (cylPairK c m * A) := mul_le_mul_of_nonneg_left hgX (norm_nonneg _)
    _ = cylPairK c m * A * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal := by
        rw [hfin]
        ring
