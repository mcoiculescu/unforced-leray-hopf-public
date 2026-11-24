import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- On the cell, `1 + x₂² ≤ ⟨x⟩² ≤ (1 + c²/4)(1 + x₂²)`. -/
theorem wm_jb_bounds {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ UnforcedLeray.B0579.cell c) :
    1 + x.2 ^ 2 ≤ UnforcedLeray.B0579.jb x ∧
      UnforcedLeray.B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  obtain ⟨hq, -⟩ := hx
  obtain ⟨h1, h2⟩ := hq
  unfold UnforcedLeray.B0579.jb
  have hsq : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ c / 2 - x.1 by linarith)
      (show (0:ℝ) ≤ c / 2 + x.1 by linarith)]
  have hx1 : 0 ≤ x.1 ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]

theorem wm_rpow_ratio {r ρ : ℝ} (e : ℝ) (h1 : 1 ≤ r) (h2 : r ≤ ρ) : r ^ e ≤ max 1 (ρ ^ e) := by
  rcases le_total 0 e with he | he
  · exact (Real.rpow_le_rpow (by linarith) h2 he).trans (le_max_right _ _)
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 he).trans (le_max_left _ _)

theorem wm_jb_rpow_le {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ UnforcedLeray.B0579.cell c) (e : ℝ) :
    UnforcedLeray.B0579.jb x ^ e ≤ max 1 ((1 + c ^ 2 / 4) ^ e) * (1 + x.2 ^ 2) ^ e := by
  obtain ⟨hb1, hb2⟩ := wm_jb_bounds hx
  have ht : 0 < 1 + x.2 ^ 2 := by positivity
  have hne : (1 + x.2 ^ 2) ≠ 0 := ht.ne'
  have hjb : UnforcedLeray.B0579.jb x =
      (1 + x.2 ^ 2) * (UnforcedLeray.B0579.jb x / (1 + x.2 ^ 2)) := by
    field_simp
  have hr1 : 1 ≤ UnforcedLeray.B0579.jb x / (1 + x.2 ^ 2) := (one_le_div ht).2 hb1
  have hr2 : UnforcedLeray.B0579.jb x / (1 + x.2 ^ 2) ≤ 1 + c ^ 2 / 4 :=
    (div_le_iff₀ ht).2 (by linarith [hb2])
  have key := wm_rpow_ratio e hr1 hr2
  calc UnforcedLeray.B0579.jb x ^ e
      = (1 + x.2 ^ 2) ^ e * (UnforcedLeray.B0579.jb x / (1 + x.2 ^ 2)) ^ e := by
        conv_lhs => rw [hjb]
        exact Real.mul_rpow ht.le (div_nonneg (UnforcedLeray.B0579.jb_pos x).le ht.le)
    _ ≤ (1 + x.2 ^ 2) ^ e * max 1 ((1 + c ^ 2 / 4) ^ e) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg ht.le e)
    _ = max 1 ((1 + c ^ 2 / 4) ^ e) * (1 + x.2 ^ 2) ^ e := mul_comm _ _

/-- The pointwise bound `|A| ⟨x⟩^m ≤ B K H` on the cell, with `H = (1+x₂²)^{-1/2}`. -/
theorem wm_G_bound {c m A B : ℝ} {x : ℝ × ℝ} (hx : x ∈ UnforcedLeray.B0579.cell c)
    (hB0 : 0 ≤ B) (hw : (1 + x.2 ^ 2) ^ ((m + 1) / 2) * |A| ≤ B) :
    |A| * UnforcedLeray.B0579.jb x ^ (m / 2) ≤
      B * (max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) := by
  have ht : 0 < 1 + x.2 ^ 2 := by positivity
  have hw0 : 0 < (1 + x.2 ^ 2) ^ ((m + 1) / 2) := Real.rpow_pos_of_pos ht _
  have hwne : (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≠ 0 := hw0.ne'
  have hq : UnforcedLeray.B0579.jb x ^ (m / 2) / (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≤
      max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [div_le_iff₀ hw0]
    have h1 := wm_jb_rpow_le hx (m / 2)
    have h2 : (1 + x.2 ^ 2) ^ (m / 2) =
        (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)) * (1 + x.2 ^ 2) ^ ((m + 1) / 2) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc UnforcedLeray.B0579.jb x ^ (m / 2)
        ≤ max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) * (1 + x.2 ^ 2) ^ (m / 2) := h1
      _ = max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)) *
            (1 + x.2 ^ 2) ^ ((m + 1) / 2) := by rw [h2]; ring
  have hsplit : |A| * UnforcedLeray.B0579.jb x ^ (m / 2) =
      ((1 + x.2 ^ 2) ^ ((m + 1) / 2) * |A|) *
        (UnforcedLeray.B0579.jb x ^ (m / 2) / (1 + x.2 ^ 2) ^ ((m + 1) / 2)) := by
    field_simp
  rw [hsplit]
  have hq0 : 0 ≤ UnforcedLeray.B0579.jb x ^ (m / 2) / (1 + x.2 ^ 2) ^ ((m + 1) / 2) :=
    div_nonneg (Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _) hw0.le
  calc ((1 + x.2 ^ 2) ^ ((m + 1) / 2) * |A|) *
        (UnforcedLeray.B0579.jb x ^ (m / 2) / (1 + x.2 ^ 2) ^ ((m + 1) / 2))
      ≤ B * (UnforcedLeray.B0579.jb x ^ (m / 2) / (1 + x.2 ^ 2) ^ ((m + 1) / 2)) :=
        mul_le_mul_of_nonneg_right hw hq0
    _ ≤ B * (max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hq hB0

/-- `H = (1+x₂²)^{-1/2}` is square integrable on the cell (Fubini on `Ico × ℝ`). -/
theorem wm_H_memLp {c : ℝ} :
    MemLp (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  have hcont : Continuous (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) :=
    (continuous_const.add (continuous_snd.pow 2)).rpow_const
      (fun x => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg x.2))))
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  have hp : (volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.B0579.cell c) =
      (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume.restrict (univ : Set ℝ)) := by
    rw [UnforcedLeray.B0579.cell, Measure.volume_eq_prod, Measure.prod_restrict]
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (-(c / 2)) (c / 2))) :=
    integrableOn_const (by simp)
  have h2 : Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹) (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.restrict_univ]
    exact integrable_inv_one_add_sq
  have h3 := h1.mul_prod h2
  rw [hp]
  have key : ∀ t : ℝ, 0 < t → (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
    intro t ht
    rw [sq, ← Real.rpow_add ht]
    norm_num [Real.rpow_neg_one]
  refine h3.congr (Eventually.of_forall fun z => ?_)
  have ht : 0 < 1 + z.2 ^ 2 := by positivity
  show (1 : ℝ) * (1 + z.2 ^ 2)⁻¹ = ((1 + z.2 ^ 2) ^ (-(1 / 2 : ℝ))) ^ 2
  rw [key _ ht, one_mul]


theorem wm_enorm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  simp only [enorm_eq_nnnorm, Complex.nnnorm_real]

/-- The weighted function `⟨x⟩^{-m} f` whose `L²(cell)` norm is `‖f‖_{X_{-m,c}}`. -/
def wmF (m : ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  (((UnforcedLeray.B0579.jb x ^ (-m / 2)) : ℝ) : ℂ) * f x

/-- The complex weighted norm as an `L²(cell)` norm (the complex version of
`B0579.eLpNorm_cellMeasure`). -/
theorem wm_xNorm_eq {c m : ℝ} (f : ℝ × ℝ → ℂ) :
    UnforcedLeray.Short.IIIa.xNorm c m f =
      eLpNorm (fun x => (((UnforcedLeray.B0579.jb x ^ (m / 2)) : ℝ) : ℂ) * f x) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  unfold UnforcedLeray.Short.IIIa.xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    UnforcedLeray.B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (UnforcedLeray.B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, wm_enorm_ofReal_complex, ENNReal.toReal_ofNat,
    ENNReal.rpow_two]
  have h0 : 0 ≤ UnforcedLeray.B0579.jb x ^ (m / 2) :=
    Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
  rw [mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
    ← Real.rpow_mul (UnforcedLeray.B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

theorem wm_H_le_one (x : ℝ × ℝ) : (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)

theorem wm_H_nonneg (x : ℝ × ℝ) : 0 ≤ (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg (by positivity) _

theorem weightedMulL12 : WeightedMulL12 := by
  intro c m hc
  set Ka : ℝ := max 1 ((1 + c ^ 2 / 4) ^ (m / 2)) with hKa_def
  have hKa0 : 0 ≤ Ka := le_trans zero_le_one (le_max_left _ _)
  have hHmem : MemLp (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := wm_H_memLp
  have hMfin := hHmem.eLpNorm_lt_top
  set M : ℝ := (eLpNorm (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
      (volume.restrict (UnforcedLeray.B0579.cell c))).toReal with hM_def
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hMofReal : ENNReal.ofReal M = eLpNorm (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := ENNReal.ofReal_toReal hMfin.ne
  refine ⟨Ka * (M + 1), mul_nonneg hKa0 (by linarith), fun A f B hA hf hB => ?_⟩
  have h00 : (0 : ℝ × ℝ) ∈ UnforcedLeray.B0579.cell c :=
    ⟨⟨by show -(c / 2) ≤ (0 : ℝ); linarith, by show (0 : ℝ) < c / 2; linarith⟩,
      Set.mem_univ _⟩
  have hw00 : UnforcedLeray.Short.IIIa.ejWeight m 0 * |A 0| ≤ B := hB _ h00
  have hej0 : 0 ≤ UnforcedLeray.Short.IIIa.ejWeight m (0 : ℝ × ℝ) := by
    unfold UnforcedLeray.Short.IIIa.ejWeight
    positivity
  have hB0 : 0 ≤ B := le_trans (mul_nonneg hej0 (abs_nonneg _)) hw00
  have hw : ∀ x ∈ UnforcedLeray.B0579.cell c,
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) * |A x| ≤ B := fun x hx => hB x hx
  have hprod : ∀ x : ℝ × ℝ,
      UnforcedLeray.B0579.jb x ^ (m / 2) * UnforcedLeray.B0579.jb x ^ (-m / 2) = 1 := by
    intro x
    rw [← Real.rpow_add (UnforcedLeray.B0579.jb_pos x), show m / 2 + -m / 2 = 0 by ring,
      Real.rpow_zero]
  have hpt : ∀ x : ℝ × ℝ, ‖(A x : ℂ) * f x‖ =
      |A x * UnforcedLeray.B0579.jb x ^ (m / 2)| * ‖wmF m f x‖ := by
    intro x
    unfold wmF
    have hr0 : 0 ≤ UnforcedLeray.B0579.jb x ^ (-m / 2) :=
      Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
    have hm0 : 0 ≤ UnforcedLeray.B0579.jb x ^ (m / 2) :=
      Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hm0]
    linear_combination (-(|A x| * ‖f x‖)) * hprod x
  have hGb : ∀ x ∈ UnforcedLeray.B0579.cell c,
      |A x * UnforcedLeray.B0579.jb x ^ (m / 2)| ≤
        B * (Ka * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _)]
    exact wm_G_bound hx hB0 (hw x hx)
  have hae2 : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      ‖(A x : ℂ) * f x‖ ≤ (B * Ka) * ‖wmF m f x‖ := by
    refine (ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)).mono fun x hx => ?_
    rw [hpt x]
    have hF0 : 0 ≤ ‖wmF m f x‖ := norm_nonneg _
    calc |A x * UnforcedLeray.B0579.jb x ^ (m / 2)| * ‖wmF m f x‖
        ≤ (B * (Ka * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)))) * ‖wmF m f x‖ :=
          mul_le_mul_of_nonneg_right (hGb x hx) hF0
      _ ≤ (B * Ka) * ‖wmF m f x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hKa0 (wm_H_le_one x)) hB0) hF0
  have hBK0 : 0 ≤ B * Ka := mul_nonneg hB0 hKa0
  have hae1 : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      ‖(A x : ℂ) * f x‖ ≤ ‖((B * Ka) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) * ‖wmF m f x‖‖ := by
    refine (ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)).mono fun x hx => ?_
    rw [hpt x, Real.norm_of_nonneg (mul_nonneg (mul_nonneg hBK0 (wm_H_nonneg x))
      (norm_nonneg _))]
    calc |A x * UnforcedLeray.B0579.jb x ^ (m / 2)| * ‖wmF m f x‖
        ≤ (B * (Ka * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)))) * ‖wmF m f x‖ :=
          mul_le_mul_of_nonneg_right (hGb x hx) (norm_nonneg _)
      _ = ((B * Ka) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) * ‖wmF m f x‖ := by ring
  have hfR : AEStronglyMeasurable f (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hf.aestronglyMeasurable.mono_ac (UnforcedLeray.B0579.ac_cellMeasure c (-m))
  have hrC : Continuous (fun x : ℝ × ℝ => (((UnforcedLeray.B0579.jb x ^ (-m / 2)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (UnforcedLeray.B0579.continuous_jb_rpow _)
  have hFm : AEStronglyMeasurable (wmF m f) (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    hrC.aestronglyMeasurable.mul hfR
  have hsA : AEStronglyMeasurable (fun x => (A x : ℂ) * f x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hA).mul hfR
  have hfm : AEStronglyMeasurable (fun x : ℝ × ℝ => (B * Ka) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ)))
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    (wm_H_memLp (c := c)).aestronglyMeasurable.const_mul (B * Ka)
  have hgm : AEStronglyMeasurable (fun x => ‖wmF m f x‖)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := hFm.norm
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hHold := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume.restrict (UnforcedLeray.B0579.cell c))
    (p := 2) (q := 2) (r := 1) hfm hgm (fun a b : ℝ => a * b) 1
    (Eventually.of_forall fun x => by simp [nnnorm_mul])
  rw [eLpNorm_norm (wmF m f)] at hHold
  have hfH : eLpNorm (fun x : ℝ × ℝ => (B * Ka) * (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
        ENNReal.ofReal (B * Ka) * eLpNorm (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
          (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (Eventually.of_forall fun x => le_of_eq (by
        rw [norm_mul, Real.norm_of_nonneg hBK0, Real.norm_of_nonneg (wm_H_nonneg x)])) 2
  have hL1a := eLpNorm_mono_ae (p := 1) hae1
  have hL1 : eLpNorm (fun x => (A x : ℂ) * f x) 1 (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
      ENNReal.ofReal (B * Ka) * eLpNorm (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) *
        eLpNorm (wmF m f) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    refine hL1a.trans (hHold.trans ?_)
    rw [ENNReal.coe_one, one_mul]
    exact mul_le_mul' hfH le_rfl
  have hL2 : eLpNorm (fun x => (A x : ℂ) * f x) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
        ENNReal.ofReal (B * Ka) * eLpNorm (wmF m f) 2
          (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hae2 2
  have hX : UnforcedLeray.Short.IIIa.xNorm c (-m) f =
      eLpNorm (wmF m f) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    wm_xNorm_eq f
  have hXfin : eLpNorm (wmF m f) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) < ⊤ := by
    rw [← hX]
    exact hf.eLpNorm_lt_top
  have hL1fin : eLpNorm (fun x => (A x : ℂ) * f x) 1
      (volume.restrict (UnforcedLeray.B0579.cell c)) < ⊤ :=
    lt_of_le_of_lt hL1 (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMfin) hXfin)
  have hmem1 : MemLp (fun x => (A x : ℂ) * f x) 1
      (volume.restrict (UnforcedLeray.B0579.cell c)) := ⟨hsA, hL1fin⟩
  have hmem2 : MemLp (fun x => (A x : ℂ) * f x) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    ⟨hsA, lt_of_le_of_lt hL2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hXfin)⟩
  have hKB : ENNReal.ofReal (Ka * (M + 1) * B) =
      ENNReal.ofReal (B * Ka) * ENNReal.ofReal M + ENNReal.ofReal (B * Ka) := by
    have e1 : Ka * (M + 1) * B = (B * Ka) * M + B * Ka := by ring
    rw [e1, ENNReal.ofReal_add (mul_nonneg hBK0 hM0) hBK0, ENNReal.ofReal_mul hBK0]
  refine ⟨memLp_one_iff_integrable.1 hmem1, hmem2, ?_⟩
  calc eLpNorm (fun x => (A x : ℂ) * f x) 1 (volume.restrict (UnforcedLeray.B0579.cell c)) +
        eLpNorm (fun x => (A x : ℂ) * f x) 2 (volume.restrict (UnforcedLeray.B0579.cell c))
      ≤ (ENNReal.ofReal (B * Ka) * eLpNorm (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(1 / 2 : ℝ))) 2
          (volume.restrict (UnforcedLeray.B0579.cell c))) * eLpNorm (wmF m f) 2
            (volume.restrict (UnforcedLeray.B0579.cell c)) +
          ENNReal.ofReal (B * Ka) * eLpNorm (wmF m f) 2
            (volume.restrict (UnforcedLeray.B0579.cell c)) := add_le_add hL1 hL2
    _ = (ENNReal.ofReal (B * Ka) * ENNReal.ofReal M + ENNReal.ofReal (B * Ka)) *
          eLpNorm (wmF m f) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
        rw [hMofReal]
        ring
    _ = ENNReal.ofReal (Ka * (M + 1) * B) *
          UnforcedLeray.Short.IIIa.xNorm c (-m) f := by
        rw [hKB, hX]
end UnforcedLeray.Short.IIIa
