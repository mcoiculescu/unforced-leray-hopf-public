import UnforcedLeray.Short.PartIIIa.Sub.T21_3_TrainBounds
import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.FluxContinuity.JointEc
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.TrainBoundsSmall.Sup

/-!
# Part III-a, `PartIII-a:T21/3/1/2`: finite-horizon train bounds from the uniform transverse tails

Source of record: `the November 2 reference manuscript`: SP 270-288 (BUC train:
bounded velocity and derivatives on every `[0, S]`), SP 460-467 (`sct:transverse`: tails
`P_{S_*}{e^{-bl/c} + e^{-bl²/(C₀+νS_*)}}` for `|η| ≥ C/ν + 2 + l`, `0 < s ≤ S_*`), SP 255-258
(`P_S`).  The velocity half is `velocityBoundOn_of_isBUCTrain`.  For the curl on the cell
`|q| ≤ c/2`: in the band `|η| ≤ C'/ν + 2` the BUC bound of `Dv` (`PartI.crBounded`) and the bound
`⟨x⟩ ≤ 1 + c/2 + C'/ν + 2`; in the tail the transverse tail with `S_* = T + 1` and the suprema
`exists_poly_exp_sup`, `exists_poly_gauss_sup`; at `s = 0` (where the tails are not stated) the
bound passes to the limit `s → 0⁺` by the joint continuity `jointContinuousOn_Ec`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.B0579 hiding Plane

/-- On the cell, `⟨x⟩ ≤ 1 + c/2 + |η|`. -/
theorem bracket_le_of_mem_cell {c : ℝ} {x : UnforcedLeray.Cyl.Plane}
    (hx : x ∈ UnforcedLeray.B0579.cell c) : bracket x ≤ 1 + c / 2 + |x.2| := by
  have hq : |x.1| ≤ c / 2 := abs_le.2 ⟨by linarith [hx.1.1], hx.1.2.le⟩
  have h0 : 0 ≤ 1 + c / 2 + |x.2| := by
    have := (abs_nonneg x.1).trans hq
    positivity
  unfold bracket
  rw [Real.sqrt_le_iff]
  refine ⟨h0, ?_⟩
  unfold jb
  nlinarith [abs_nonneg x.1, abs_nonneg x.2, sq_abs x.1, sq_abs x.2, hq]

theorem one_le_bracket (x : UnforcedLeray.Cyl.Plane) : 1 ≤ bracket x := by
  unfold bracket
  rw [Real.one_le_sqrt]
  unfold jb
  nlinarith [sq_nonneg x.1, sq_nonneg x.2]

theorem trainBoundsSmall_of (hT : UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform) :
    UnforcedLeray.Short.IIIa.Exist.TrainBoundsSmall := by
  intro m hm8
  obtain ⟨b, C₀, C', C, N, ν₀, hb, hC₀, hC', hC, hν₀, hT'⟩ := hT 2 (by norm_num) 0 0
  refine ⟨ν₀, hν₀, fun ν hν hνle tr htr T hT0 => ?_⟩
  have hm0 : 0 ≤ m := by linarith
  generalize hc : ν ^ (-2 : ℝ) = c at tr htr
  obtain ⟨Cv, hCv0, hCv⟩ := velocityBoundOn_of_isBUCTrain htr hT0
  -- band: global bound of the vorticity on `[0, T]`
  obtain ⟨M2, hM2⟩ := UnforcedLeray.Short.PartI.crBounded
    (v := tr.v) (T := T)
    (tr.isTrain.smooth_v.mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)) (htr T hT0)
  have hM2' : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, |UnforcedLeray.B0238.Ec tr s z| ≤ max M2 0 :=
    fun s hs z => (hM2 s hs z).trans (le_max_left _ _)
  have hcpos : 0 < c := hc ▸ Real.rpow_pos_of_pos hν _
  set A : ℝ := C' / ν + 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set S_ : ℝ := T + 1 with hS
  have hS1 : 1 ≤ S_ := by linarith
  set P : ℝ := UnforcedLeray.Short.PartI.polyPS C N ν c S_ with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    unfold UnforcedLeray.Short.PartI.polyPS
    have : 0 ≤ (1 + c + ν⁻¹) * (1 + S_) := by positivity
    positivity
  set B0 : ℝ := 1 + c / 2 + A with hB0
  have hB0pos : 1 ≤ B0 := by rw [hB0]; linarith [half_pos hcpos]
  set k : ℕ := ⌈m⌉₊ with hk
  obtain ⟨Mβ, hMβ0, hMβ⟩ := exists_poly_exp_sup k hb hcpos (by linarith : 0 ≤ B0)
  obtain ⟨Mγ, hMγ0, hMγ⟩ := exists_poly_gauss_sup k (D := C₀ + ν * S_) hb (by positivity)
    (by linarith : 0 ≤ B0)
  -- the tail bound for positive ages
  have hTail : ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ x ∈ UnforcedLeray.B0579.cell c, A < |x.2| →
      |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ P * (Mβ + Mγ) := by
    intro s hs hsS x hx hAx
    set l : ℝ := |x.2| - A with hl
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hK := hT' ν hν hνle c (by rw [← hc]; rfl) tr htr S_ (by linarith) l hl0 s hs hsS x (by rw [hl, hA]; linarith)
    obtain ⟨-, -, hcurl, -⟩ := hK
    rw [UnforcedLeray.Short.IIIa.T23Tail.norm_ageJet_zero_zero, Real.norm_eq_abs] at hcurl
    have hbr : bracket x ≤ B0 + l := by
      have := bracket_le_of_mem_cell hx
      rw [hB0, hl, hA]; linarith
    have hbr1 : 1 ≤ B0 + l := by linarith
    have hbm : bracket x ^ m ≤ (B0 + l) ^ k := by
      calc bracket x ^ m ≤ (B0 + l) ^ m :=
            Real.rpow_le_rpow (by linarith [one_le_bracket x]) hbr hm0
        _ ≤ (B0 + l) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hbr1 (Nat.le_ceil m)
        _ = (B0 + l) ^ k := Real.rpow_natCast _ _
    have hE : |UnforcedLeray.B0238.Ec tr s x| ≤ P * (Real.exp (-(b * l / c)) +
        Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))) := hcurl
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith [one_le_bracket x]) m)]
    calc bracket x ^ m * |UnforcedLeray.B0238.Ec tr s x|
        ≤ (B0 + l) ^ k * (P * (Real.exp (-(b * l / c)) +
            Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))) :=
          mul_le_mul hbm hE (abs_nonneg _) (by positivity)
      _ = P * ((B0 + l) ^ k * Real.exp (-(b * l / c)) +
            (B0 + l) ^ k * Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))) := by ring
      _ ≤ P * (Mβ + Mγ) := mul_le_mul_of_nonneg_left (add_le_add (hMβ l hl0) (hMγ l hl0)) hP0
  -- the tail bound at age zero, by continuity
  have hTail0 : ∀ x ∈ UnforcedLeray.B0579.cell c, A < |x.2| →
      |bracket x ^ m * UnforcedLeray.B0238.Ec tr 0 x| ≤ P * (Mβ + Mγ) := by
    intro x hx hAx
    have hcont : ContinuousWithinAt (fun s : ℝ => bracket x ^ m * UnforcedLeray.B0238.Ec tr s x)
        (Ioi 0) 0 := by
      have h1 : ContinuousOn (fun s : ℝ => UnforcedLeray.B0238.Ec tr s x) (Ici 0) :=
        (jointContinuousOn_Ec tr).comp (by fun_prop : Continuous fun s : ℝ => (s, x)).continuousOn
          (fun s hs => ⟨hs, mem_univ _⟩)
      exact (continuousWithinAt_const.mul
        ((h1 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self))
    have hlim := (continuous_abs.tendsto _).comp hcont.tendsto
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    exact hTail s hs.1 (by linarith [hs.2]) x hx hAx
  refine ⟨Cv, B0 ^ m * max M2 0 + P * (Mβ + Mγ), hCv0, by positivity, hCv, ?_⟩
  intro s x hx
  by_cases hband : |x.2| ≤ A
  · have hbr : bracket x ≤ B0 := by
      have := bracket_le_of_mem_cell hx
      rw [hB0]; linarith
    have hbm : bracket x ^ m ≤ B0 ^ m :=
      Real.rpow_le_rpow (by linarith [one_le_bracket x]) hbr hm0
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith [one_le_bracket x]) m)]
    have : bracket x ^ m * |UnforcedLeray.B0238.Ec tr s.1 x| ≤ B0 ^ m * max M2 0 :=
      mul_le_mul hbm (hM2' s s.2 x) (abs_nonneg _) (by positivity)
    have h2 : 0 ≤ P * (Mβ + Mγ) := by positivity
    linarith
  · have hAx : A < |x.2| := not_le.1 hband
    have h1 : |bracket x ^ m * UnforcedLeray.B0238.Ec tr s.1 x| ≤ P * (Mβ + Mγ) := by
      rcases eq_or_lt_of_le s.2.1 with h0 | hpos
      · rw [← h0]; exact hTail0 x hx hAx
      · exact hTail s.1 hpos (by linarith [s.2.2]) x hx hAx
    have h2 : 0 ≤ B0 ^ m * max M2 0 := by positivity
    linarith

end UnforcedLeray.Short.IIIa.Exist
