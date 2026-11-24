import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The squared (`ℝ≥0∞`-valued) pointwise norm of `g`, as in `eLpNorm _ 2`. -/
def pbF (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ (2 : ℝ)

lemma pb_eLpNorm_two (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, pbF f x ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp [pbF]

/-- A real `x₁` is `k c` plus a point of the centred interval, with `|k|` bounded in terms of
`|R| ≥ |x₁|`. -/
lemma pb_cell_shift {c R x₁ : ℝ} (hc : 0 < c) (hx₁ : |x₁| ≤ |R|) :
    ∃ k : ℤ, -(⌈|R| / c⌉ + 1) ≤ k ∧ k ≤ ⌈|R| / c⌉ + 1 ∧
      x₁ - (k : ℝ) * c ∈ Ico (-(c / 2)) (c / 2) := by
  have hKc : |R| + c ≤ ((⌈|R| / c⌉ + 1 : ℤ) : ℝ) * c := by
    have h1 : |R| / c ≤ (⌈|R| / c⌉ : ℝ) := Int.le_ceil _
    have h2 : |R| ≤ (⌈|R| / c⌉ : ℝ) * c := (div_le_iff₀ hc).1 h1
    push_cast
    nlinarith
  have h1 : ((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) * c ≤ x₁ + c / 2 :=
    (le_div_iff₀ hc).1 (Int.floor_le _)
  have h2 : x₁ + c / 2 < (((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) + 1) * c :=
    (div_lt_iff₀ hc).1 (Int.lt_floor_add_one _)
  have hl : -|R| ≤ x₁ := (abs_le.1 hx₁).1
  have hu : x₁ ≤ |R| := (abs_le.1 hx₁).2
  refine ⟨⌊(x₁ + c / 2) / c⌋, ?_, ?_, ?_⟩
  · have h3 : -(((⌈|R| / c⌉ + 1 : ℤ) : ℝ)) * c < ((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) * c := by
      nlinarith
    have h4 : -(((⌈|R| / c⌉ + 1 : ℤ) : ℝ)) < ((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) :=
      lt_of_mul_lt_mul_right h3 hc.le
    have h5 : -(⌈|R| / c⌉ + 1) < ⌊(x₁ + c / 2) / c⌋ := by exact_mod_cast h4
    omega
  · have h3 : ((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) * c < ((⌈|R| / c⌉ + 1 : ℤ) : ℝ) * c := by
      nlinarith
    have h4 : ((⌊(x₁ + c / 2) / c⌋ : ℤ) : ℝ) < ((⌈|R| / c⌉ + 1 : ℤ) : ℝ) :=
      lt_of_mul_lt_mul_right h3 hc.le
    have h5 : ⌊(x₁ + c / 2) / c⌋ < ⌈|R| / c⌉ + 1 := by exact_mod_cast h4
    omega
  · rw [Set.mem_Ico]
    constructor <;> nlinarith

lemma pb_shift_eq {c : ℝ} {g : ℝ × ℝ → ℂ} (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (k : ℤ) (x : ℝ × ℝ) : g (x - ((k : ℝ) * c, (0 : ℝ))) = g x := by
  have hk : ∀ j : ℤ, ∀ y : ℝ × ℝ, g (y.1 + (j : ℝ) * c, y.2) = g y := by
    intro j
    refine Int.induction_on j ?_ ?_ ?_
    · intro y
      simp
    · intro i ih y
      have h1 := ih (y.1 + c, y.2)
      dsimp only at h1
      rw [show y.1 + c + ((i : ℤ) : ℝ) * c = y.1 + (((i : ℤ) + 1 : ℤ) : ℝ) * c by
        push_cast; ring] at h1
      rw [h1]
      exact hg y
    · intro i ih y
      have h1 := hg (y.1 + (((-(i : ℤ)) - 1 : ℤ) : ℝ) * c, y.2)
      dsimp only at h1
      rw [show y.1 + (((-(i : ℤ)) - 1 : ℤ) : ℝ) * c + c
          = y.1 + ((-(i : ℤ) : ℤ) : ℝ) * c by push_cast; ring] at h1
      rw [← h1]
      exact ih y
  have e : x - ((k : ℝ) * c, (0 : ℝ)) = (x.1 + ((-k : ℤ) : ℝ) * c, x.2) := by
    ext <;> simp <;> ring
  rw [e]
  exact hk (-k) x

lemma pb_aesm_plane {c n : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (hm : AEStronglyMeasurable g (B0579.cellMeasure c n)) :
    AEStronglyMeasurable g volume := by
  have hm0 : AEStronglyMeasurable g (volume.restrict (B0579.cell c)) :=
    hm.mono_ac (B0579.ac_cellMeasure c n)
  have hcover : (⋃ k : ℤ, (fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ))) ⁻¹' B0579.cell c) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨k, -, -, hk⟩ := pb_cell_shift (R := x.1) (x₁ := x.1) hc le_rfl
    exact ⟨k, ⟨by simpa using hk, mem_univ _⟩⟩
  rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ × ℝ))), ← hcover,
    aestronglyMeasurable_iUnion_iff]
  intro k
  have hmp : MeasurePreserving (fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ)))
      (volume.restrict ((fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ))) ⁻¹' B0579.cell c))
      (volume.restrict (B0579.cell c)) :=
    (measurePreserving_sub_right volume _).restrict_preimage (B0579.measurableSet_cell c)
  exact (hm0.comp_measurePreserving hmp).congr (Eventually.of_forall fun x => pb_shift_eq hg k x)

theorem periodicBoxBound : UnforcedLeray.Short.IIIa.PeriodicBoxBound := by
  intro c m R hc
  set n : ℝ := -m with hn
  set K : ℤ := ⌈|R| / c⌉ + 1 with hK
  set J : ℝ := 1 + c ^ 2 / 4 + R ^ 2 with hJ
  have hJpos : 0 < J := by rw [hJ]; positivity
  set q : ℝ := max 1 (J ^ (-n)) with hq
  have hq1 : 1 ≤ q := le_max_left _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  set N : ℕ := (Finset.Icc (-K) K).card with hN
  refine ⟨((N : ℝ≥0∞) * ENNReal.ofReal q) ^ (1 / 2 : ℝ),
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top), ?_⟩
  intro g hg hgm
  have hgm' : AEStronglyMeasurable g (B0579.cellMeasure c n) := hgm
  have hP : AEStronglyMeasurable g volume := pb_aesm_plane hc hg hgm'
  have hFm : AEMeasurable (pbF g) volume := hP.aemeasurable.enorm.pow_const (2 : ℝ)
  -- density lower bound on the centred strip
  have hdens : ∀ y ∈ Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R,
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal q * (B0579.density n y : ℝ≥0∞) := by
    rintro y ⟨hy1, hy2⟩
    have hy1' : y.1 ^ 2 ≤ (c / 2) ^ 2 := by nlinarith [hy1.1, hy1.2]
    have hy2' : y.2 ^ 2 ≤ R ^ 2 := by nlinarith [hy2.1, hy2.2]
    have hjy1 : 1 ≤ B0579.jb y := by
      unfold B0579.jb; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hjyJ : B0579.jb y ≤ J := by
      unfold B0579.jb; rw [hJ]; nlinarith
    have hkey : 1 ≤ q * B0579.jb y ^ n := by
      rcases le_total 0 n with hn0 | hn0
      · have h1 : 1 ≤ B0579.jb y ^ n := Real.one_le_rpow hjy1 hn0
        nlinarith
      · have h1 : J ^ n ≤ B0579.jb y ^ n :=
          Real.rpow_le_rpow_of_nonpos (B0579.jb_pos y) hjyJ hn0
        have h2 : J ^ (-n) ≤ q := le_max_right _ _
        have h3 : J ^ (-n) * J ^ n = 1 := by
          rw [← Real.rpow_add hJpos]; simp
        have h4 : 0 ≤ B0579.jb y ^ n := Real.rpow_nonneg (B0579.jb_pos y).le _
        calc (1 : ℝ) = J ^ (-n) * J ^ n := h3.symm
          _ ≤ J ^ (-n) * B0579.jb y ^ n :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hJpos.le _)
          _ ≤ q * B0579.jb y ^ n := mul_le_mul_of_nonneg_right h2 h4
    rw [show (B0579.density n y : ℝ≥0∞) = ENNReal.ofReal (B0579.jb y ^ n) from rfl,
      ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hkey
  have hCr_meas : MeasurableSet (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hbox_meas : MeasurableSet (sliceBox R) := measurableSet_Icc.prod measurableSet_Icc
  -- pointwise covering of the box by finitely many translates of the strip
  have hcover : ∀ x : ℝ × ℝ,
      (sliceBox R).indicator (pbF g) x ≤
        ∑ k ∈ Finset.Icc (-K) K,
          (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g)
            (x - ((k : ℝ) * c, (0 : ℝ))) := by
    intro x
    by_cases hx : x ∈ sliceBox R
    · have hx' : x.1 ∈ Icc (-R) R ∧ x.2 ∈ Icc (-R) R := hx
      have hx1 : |x.1| ≤ |R| :=
        abs_le.2 ⟨by linarith [le_abs_self R, hx'.1.1], by linarith [le_abs_self R, hx'.1.2]⟩
      obtain ⟨k, hk1, hk2, hk3⟩ := pb_cell_shift (R := R) (x₁ := x.1) hc hx1
      have hkmem : k ∈ Finset.Icc (-K) K := Finset.mem_Icc.2 ⟨hk1, hk2⟩
      have hmem : x - ((k : ℝ) * c, (0 : ℝ)) ∈ Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R :=
        ⟨by simpa using hk3, by simpa using hx'.2⟩
      have hterm : (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g)
          (x - ((k : ℝ) * c, (0 : ℝ))) = pbF g x := by
        rw [Set.indicator_of_mem hmem]
        unfold pbF
        rw [pb_shift_eq hg k x]
      rw [Set.indicator_of_mem hx, ← hterm]
      exact Finset.single_le_sum
        (f := fun k : ℤ => (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g)
          (x - ((k : ℝ) * c, (0 : ℝ))))
        (fun _ _ => zero_le) hkmem
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  -- integrate the covering bound
  have hbox_int : ∫⁻ x in sliceBox R, pbF g x ≤
      (N : ℝ≥0∞) * ∫⁻ y, (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y := by
    rw [← lintegral_indicator hbox_meas]
    calc ∫⁻ x, (sliceBox R).indicator (pbF g) x
        ≤ ∫⁻ x, ∑ k ∈ Finset.Icc (-K) K,
            (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g)
              (x - ((k : ℝ) * c, (0 : ℝ))) := lintegral_mono hcover
      _ = ∑ k ∈ Finset.Icc (-K) K, ∫⁻ x,
            (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g)
              (x - ((k : ℝ) * c, (0 : ℝ))) := by
          rw [lintegral_finsetSum']
          intro k _
          exact (hFm.indicator hCr_meas).comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume ((k : ℝ) * c, (0 : ℝ))).quasiMeasurePreserving
      _ = ∑ k ∈ Finset.Icc (-K) K, ∫⁻ y,
            (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact lintegral_sub_right_eq_self _ _
      _ = (N : ℝ≥0∞) * ∫⁻ y,
            (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the strip integral against the cell integral
  have hCr_le : ∫⁻ y, (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y ≤
      ENNReal.ofReal q * ∫⁻ y in B0579.cell c, (B0579.density n y : ℝ≥0∞) * pbF g y := by
    have hpt : ∀ y, (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y ≤
        ENNReal.ofReal q * (B0579.cell c).indicator
          (fun y => (B0579.density n y : ℝ≥0∞) * pbF g y) y := by
      intro y
      by_cases hy : y ∈ Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
      · have hyc : y ∈ B0579.cell c := ⟨hy.1, mem_univ _⟩
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyc]
        calc pbF g y = 1 * pbF g y := (one_mul _).symm
          _ ≤ (ENNReal.ofReal q * (B0579.density n y : ℝ≥0∞)) * pbF g y := by
              gcongr
              exact hdens y hy
          _ = ENNReal.ofReal q * ((B0579.density n y : ℝ≥0∞) * pbF g y) := by ring
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    calc ∫⁻ y, (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (pbF g) y
        ≤ ∫⁻ y, ENNReal.ofReal q * (B0579.cell c).indicator
            (fun y => (B0579.density n y : ℝ≥0∞) * pbF g y) y := lintegral_mono hpt
      _ = ENNReal.ofReal q * ∫⁻ y, (B0579.cell c).indicator
            (fun y => (B0579.density n y : ℝ≥0∞) * pbF g y) y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal q * ∫⁻ y in B0579.cell c,
            (B0579.density n y : ℝ≥0∞) * pbF g y := by
          rw [lintegral_indicator (B0579.measurableSet_cell c)]
  -- the weighted norm
  have hX : xNorm c n g = (∫⁻ y in B0579.cell c,
      (B0579.density n y : ℝ≥0∞) * pbF g y) ^ (1 / 2 : ℝ) := by
    unfold xNorm
    rw [pb_eLpNorm_two, B0579.cellMeasure,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (B0579.measurable_density n).coe_nnreal_ennreal
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    rfl
  have hbox_eq : eLpNorm g 2 (volume.restrict (sliceBox R)) =
      (∫⁻ x in sliceBox R, pbF g x) ^ (1 / 2 : ℝ) :=
    pb_eLpNorm_two g _
  refine ⟨hP.restrict, ?_⟩
  rw [hbox_eq, hX]
  calc (∫⁻ x in sliceBox R, pbF g x) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * (ENNReal.ofReal q * ∫⁻ y in B0579.cell c,
          (B0579.density n y : ℝ≥0∞) * pbF g y)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hbox_int.trans (mul_le_mul_of_nonneg_left hCr_le (by positivity)))
          (by norm_num)
    _ = ((N : ℝ≥0∞) * ENNReal.ofReal q) ^ (1 / 2 : ℝ) *
          (∫⁻ y in B0579.cell c, (B0579.density n y : ℝ≥0∞) * pbF g y) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end UnforcedLeray.Short.IIIa
