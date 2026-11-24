import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.CellYoung

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/1/2`: the weighted periodic Young inequality on `X_{-m,c}`

Proves `AdjKerYoungMoment` (SP 2819-2836, 3044-3050) from `adjCellYoung` (`H1/CellYoung.lean`).

Route: for `w ∈ X_{-m,c}` with periodic lift `f̃ = perRep c w`, the weight `jb^{-m/2}` of the
`B0579` cell measure is compared with the axial weight by a Peetre inequality
`jb x^{-m/2} ≤ 2^{m/2} (1+(x₂-y₂)²)^{m/2} (1+y₂²)^{-m/2}`; the integral is then translated to the
kernel variable `z = x - y`, Minkowski's inequality on the cell (`adjCellYoung`) is applied to the
periodic function `g y = (1+y₂²)^{-m/2} |f̃ y|`, and `g` is compared with `w` on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Reciprocal monotonicity: `J⁻¹ ≤ R Y⁻¹` whenever `Y ≤ R J`. -/
theorem kerY_inv_le_mul {J Y R : ℝ} (hJ : 0 < J) (hY : 0 < Y) (h : Y ≤ R * J) :
    J⁻¹ ≤ R * Y⁻¹ := by
  calc J⁻¹ = (J⁻¹ * Y) * Y⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hY.ne', mul_one]
    _ ≤ (J⁻¹ * (R * J)) * Y⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (inv_nonneg.2 hJ.le))
          (inv_nonneg.2 hY.le)
    _ = R * Y⁻¹ := by
        rw [show J⁻¹ * (R * J) = R * (J⁻¹ * J) by ring, inv_mul_cancel₀ hJ.ne', mul_one]

/-- The Peetre-type weight bound: `jb x^{-m/2} ≤ 2^{m/2} (1+(x₂-y₂)²)^{m/2} (1+y₂²)^{-m/2}`
for all `x, y`. -/
theorem kerY_jb_neg_le_peetre {m : ℝ} (hm : 0 ≤ m) (x y : ℝ × ℝ) :
    UnforcedLeray.B0579.jb x ^ ((-m) / 2) ≤
      (2 : ℝ) ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) * (1 + y.2 ^ 2) ^ (-(m / 2)) := by
  have hm2 : 0 ≤ m / 2 := div_nonneg hm (by norm_num)
  have hJ : 0 < UnforcedLeray.B0579.jb x ^ (m / 2) :=
    Real.rpow_pos_of_pos (UnforcedLeray.B0579.jb_pos x) _
  have hYpos : 0 < (1 + y.2 ^ 2) ^ (m / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hP2 : 1 + y.2 ^ 2 ≤ 2 * (1 + (x.2 - y.2) ^ 2) * (1 + x.2 ^ 2) := by
    nlinarith [sq_nonneg (x.2 + (x.2 - y.2)), sq_nonneg (x.2 * (x.2 - y.2))]
  have hjb : 1 + x.2 ^ 2 ≤ UnforcedLeray.B0579.jb x := by
    unfold UnforcedLeray.B0579.jb
    nlinarith [sq_nonneg x.1]
  have hY : (1 + y.2 ^ 2) ^ (m / 2) ≤
      (2 : ℝ) ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) *
        UnforcedLeray.B0579.jb x ^ (m / 2) := by
    calc (1 + y.2 ^ 2) ^ (m / 2)
        ≤ (2 * (1 + (x.2 - y.2) ^ 2) * (1 + x.2 ^ 2)) ^ (m / 2) :=
          Real.rpow_le_rpow (by positivity) hP2 hm2
      _ = (2 : ℝ) ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) * (1 + x.2 ^ 2) ^ (m / 2) := by
          rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * (1 + (x.2 - y.2) ^ 2))
              (by positivity : (0 : ℝ) ≤ 1 + x.2 ^ 2),
            Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 + (x.2 - y.2) ^ 2)]
      _ ≤ (2 : ℝ) ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) *
            UnforcedLeray.B0579.jb x ^ (m / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hjb hm2) (by positivity)
  rw [show (-m) / 2 = -(m / 2) by ring,
    Real.rpow_neg (UnforcedLeray.B0579.jb_pos x).le,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + y.2 ^ 2)]
  exact kerY_inv_le_mul hJ hYpos hY

/-- On the centred cell, the axial weight `(1 + x₂²)^{-m/2}` is dominated by the `B0579` weight
`jb^{-m/2}` with the constant `(1 + c²/4)^{m/2}`. -/
theorem kerY_cell_weight_le {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) {x : ℝ × ℝ}
    (hx : x ∈ UnforcedLeray.B0579.cell c) :
    (1 + x.2 ^ 2) ^ (-(m / 2)) ≤
      (1 + c ^ 2 / 4) ^ (m / 2) * UnforcedLeray.B0579.jb x ^ ((-m) / 2) := by
  have hm2 : 0 ≤ m / 2 := div_nonneg hm (by norm_num)
  have hq : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    have h1 : 0 ≤ c / 2 - x.1 := by linarith [hx.1.2]
    have h2 : 0 ≤ x.1 + c / 2 := by linarith [hx.1.1]
    nlinarith [mul_nonneg h1 h2]
  have hjb : UnforcedLeray.B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
    unfold UnforcedLeray.B0579.jb
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]
  have hJ : 0 < (1 + x.2 ^ 2) ^ (m / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hY : UnforcedLeray.B0579.jb x ^ (m / 2) ≤
      (1 + c ^ 2 / 4) ^ (m / 2) * (1 + x.2 ^ 2) ^ (m / 2) := by
    calc UnforcedLeray.B0579.jb x ^ (m / 2)
        ≤ ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ (m / 2) :=
          Real.rpow_le_rpow (UnforcedLeray.B0579.jb_pos x).le hjb hm2
      _ = (1 + c ^ 2 / 4) ^ (m / 2) * (1 + x.2 ^ 2) ^ (m / 2) :=
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + c ^ 2 / 4)
            (by positivity : (0 : ℝ) ≤ 1 + x.2 ^ 2)
  rw [show (-m) / 2 = -(m / 2) by ring,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + x.2 ^ 2),
    Real.rpow_neg (UnforcedLeray.B0579.jb_pos x).le]
  exact kerY_inv_le_mul hJ (Real.rpow_pos_of_pos (UnforcedLeray.B0579.jb_pos x) _) hY

/-- The cell `L²` norm with the `B0579` density, for an arbitrary `ENorm`-valued function:
the density `⟨x⟩^{2m} = jb^m` becomes the weight `jb^{m/2}` on the unweighted cell. -/
theorem kerY_eLpNorm_cellMeasure {E : Type*} [ENorm E] (c m : ℝ) (f : ℝ × ℝ → E) :
    eLpNorm f 2 (UnforcedLeray.B0579.cellMeasure c m) =
      eLpNorm (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (m / 2)) * ‖f x‖ₑ) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    UnforcedLeray.B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (UnforcedLeray.B0579.measurable_density m).coe_nnreal_ennreal
      (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two, Pi.mul_apply]
  have h0 : 0 ≤ UnforcedLeray.B0579.jb x ^ (m / 2) :=
    Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _
  have hd : ((UnforcedLeray.B0579.density m x : NNReal) : ENNReal) =
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ m) := rfl
  have hsq : ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ (m / 2)) ^ 2 =
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ m) := by
    rw [← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
      ← Real.rpow_mul (UnforcedLeray.B0579.jb_pos x).le,
      show m / 2 * ((2 : ℕ) : ℝ) = m by push_cast; ring]
  rw [hd, mul_pow, hsq]

/-- **(H1.1) The weighted periodic Young inequality on `X_{-m,c}`** (SP 2819-2836, 3044-3050).
The Peetre bound, the translation `z = x - y`, Minkowski on the cell (`adjCellYoung`) and the
comparison of `g` with `w` on the cell give the constant `(2(1+c²/4))^{m/2} A`. -/
theorem adjKerYoungMoment : AdjKerYoungMoment := by
  unfold AdjKerYoungMoment
  intro c m hc hm k hk A hA hmom
  unfold KerYoung
  intro w
  have hm2 : 0 ≤ m / 2 := div_nonneg hm (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ × ℝ → ENNReal,
      K = fun z => ‖k z‖ₑ * ENNReal.ofReal ((1 + z.2 ^ 2) ^ (m / 2)) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ × ℝ → ℝ,
      g = fun y => (1 + y.2 ^ 2) ^ (-(m / 2)) * ‖perRep c (⇑w) y‖ := ⟨_, rfl⟩
  have hK : ∀ z, K z = ‖k z‖ₑ * ENNReal.ofReal ((1 + z.2 ^ 2) ^ (m / 2)) :=
    fun z => by rw [hKdef]
  have hg : ∀ y, g y = (1 + y.2 ^ 2) ^ (-(m / 2)) * ‖perRep c (⇑w) y‖ :=
    fun y => by rw [hgdef]
  have hKm : Measurable K := by
    rw [show K = fun z => ‖k z‖ₑ * ENNReal.ofReal ((1 + z.2 ^ 2) ^ (m / 2)) from funext hK]
    exact hk.measurable.enorm.mul (ENNReal.measurable_ofReal.comp
      (Measurable.pow_const (measurable_const.add (measurable_snd.pow_const 2)) _))
  have hKfin : ∀ z, K z ≠ ⊤ := fun z => by
    rw [hK]
    exact ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top
  have hgm : AEStronglyMeasurable g volume := by
    have hcont : Continuous (fun y : ℝ × ℝ => (1 + y.2 ^ 2) ^ (-(m / 2))) :=
      (by fun_prop : Continuous fun y : ℝ × ℝ => 1 + y.2 ^ 2).rpow_const
        (fun y => Or.inl (by positivity))
    have hpm : StronglyMeasurable (fun y => perRep c (⇑w) y) :=
      stronglyMeasurable_perRep hc (Lp.stronglyMeasurable w)
    rw [hgdef]
    exact hcont.aestronglyMeasurable.mul hpm.norm.aestronglyMeasurable
  have hper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x := by
    intro x
    rw [hg, hg]
    simp only [perRep_periodic hc]
  -- pointwise Peetre bound on the integrand
  have hpt : ∀ x y : ℝ × ℝ,
      ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
          (‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * (K (x - y) * ‖g y‖ₑ) := by
    intro x y
    have hgE : ‖g y‖ₑ =
        ENNReal.ofReal ((1 + y.2 ^ 2) ^ (-(m / 2))) * ‖perRep c (⇑w) y‖ₑ := by
      rw [hg, Real.enorm_eq_ofReal (mul_nonneg
          (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + y.2 ^ 2) _)
          (norm_nonneg (perRep c (⇑w) y))),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + y.2 ^ 2) _),
        ofReal_norm]
    have hKE : K (x - y) =
        ‖k (x - y)‖ₑ * ENNReal.ofReal ((1 + (x.2 - y.2) ^ 2) ^ (m / 2)) := by
      rw [hK, Prod.snd_sub]
    have e : ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ENNReal.ofReal ((1 + (x.2 - y.2) ^ 2) ^ (m / 2)) *
        ENNReal.ofReal ((1 + y.2 ^ 2) ^ (-(m / 2))) =
        ENNReal.ofReal ((2 : ℝ) ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) *
          (1 + y.2 ^ 2) ^ (-(m / 2))) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m / 2) *
            (1 + (x.2 - y.2) ^ 2) ^ (m / 2)),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m / 2))]
    have hle : ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          ENNReal.ofReal ((1 + (x.2 - y.2) ^ 2) ^ (m / 2)) *
          ENNReal.ofReal ((1 + y.2 ^ 2) ^ (-(m / 2))) := by
      rw [e]
      exact ENNReal.ofReal_le_ofReal (kerY_jb_neg_le_peetre hm x y)
    rw [hgE, hKE]
    exact (mul_le_mul_of_nonneg_right hle zero_le).trans (le_of_eq (by ring))
  -- the cell weight comparison for `g` against `w`
  have hgw : eLpNorm g 2 (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
      ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        eLpNorm (⇑w) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) := by
    rw [kerY_eLpNorm_cellMeasure c (-m) (⇑w)]
    have hC : (0 : ℝ) ≤ (1 + c ^ 2 / 4) ^ (m / 2) := by positivity
    calc eLpNorm g 2 (volume.restrict (UnforcedLeray.B0579.cell c))
        ≤ eLpNorm (fun x => ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
            (ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) * ‖(⇑w) x‖ₑ)) 2
            (volume.restrict (UnforcedLeray.B0579.cell c)) := by
          refine eLpNorm_mono_enorm_ae ?_
          filter_upwards [ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)] with x hx
          have hgx : ‖g x‖ₑ = ENNReal.ofReal ((1 + x.2 ^ 2) ^ (-(m / 2))) * ‖(⇑w) x‖ₑ := by
            rw [hg, Real.enorm_eq_ofReal (mul_nonneg
                (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + x.2 ^ 2) _)
                (norm_nonneg (perRep c (⇑w) x))),
              ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + x.2 ^ 2) _),
              perRep_of_mem_cell hc (⇑w) hx, ofReal_norm]
          have hWle : ENNReal.ofReal ((1 + x.2 ^ 2) ^ (-(m / 2))) ≤
              ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
                ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) := by
            rw [← ENNReal.ofReal_mul hC]
            exact ENNReal.ofReal_le_ofReal (kerY_cell_weight_le hc hm hx)
          rw [hgx, enorm_eq_self]
          exact (mul_le_mul_of_nonneg_right hWle zero_le).trans (le_of_eq (by ring))
      _ = ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
            eLpNorm (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
              ‖(⇑w) x‖ₑ) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
          UnforcedLeray.B0284.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top
            (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) * ‖(⇑w) x‖ₑ)
            two_ne_zero two_ne_top_ennreal
  -- the integral identity: the kernel integral, with `∫⁻ K = kerAxialMoment m k`
  have hKint : ∫⁻ z, K z = kerAxialMoment m k := lintegral_congr hK
  have hKA : ∫⁻ z, K z ≤ ENNReal.ofReal A := hKint.le.trans hmom
  have hid : eLpNorm (fun x => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
      (UnforcedLeray.B0579.cellMeasure c (-m)) =
      eLpNorm (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
        ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    rw [kerY_eLpNorm_cellMeasure]
    simp only [enorm_eq_self]
  have hstep1 : eLpNorm (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
        ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
      eLpNorm (fun x => ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    apply eLpNorm_mono_enorm
    intro x
    simp only [enorm_eq_self]
    have hsub : ∫⁻ y, K (x - y) * ‖g y‖ₑ = ∫⁻ z, K z * ‖g (x - z)‖ₑ := by
      have h := lintegral_sub_left_eq_self (μ := (volume : Measure (ℝ × ℝ)))
        (fun z => K z * ‖g (x - z)‖ₑ) x
      simpa only [sub_sub_cancel] using h
    calc ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
          ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ
        = ∫⁻ y, ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
            (‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * (K (x - y) * ‖g y‖ₑ) :=
          lintegral_mono fun y => hpt x y
      _ = ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * ∫⁻ y, K (x - y) * ‖g y‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * ∫⁻ z, K z * ‖g (x - z)‖ₑ := by
          rw [hsub]
  have hstep2 : eLpNorm (fun x => ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) =
      ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        eLpNorm (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2
          (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    UnforcedLeray.B0284.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top
      (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) two_ne_zero two_ne_top_ennreal
  have hstep3 : eLpNorm (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) ≤
      (∫⁻ z, K z) * eLpNorm g 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    adjCellYoung c hc K hKm hKfin g hper hgm
  rw [hid]
  have hPe : ENNReal.ofReal ((2 * (1 + c ^ 2 / 4)) ^ (m / 2) * A) =
      ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal A := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 + c ^ 2 / 4),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m / 2) *
        (1 + c ^ 2 / 4) ^ (m / 2)),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m / 2))]
  calc eLpNorm (fun x => ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ ((-m) / 2)) *
        ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
        (volume.restrict (UnforcedLeray.B0579.cell c))
      ≤ eLpNorm (fun x => ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := hstep1
    _ = ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          eLpNorm (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2
            (volume.restrict (UnforcedLeray.B0579.cell c)) := hstep2
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          ((∫⁻ z, K z) * eLpNorm g 2 (volume.restrict (UnforcedLeray.B0579.cell c))) := by
        gcongr
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          (ENNReal.ofReal A * (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
            eLpNorm (⇑w) 2 (UnforcedLeray.B0579.cellMeasure c (-m)))) := by
        gcongr
    _ = ENNReal.ofReal ((2 * (1 + c ^ 2 / 4)) ^ (m / 2) * A) *
          eLpNorm (⇑w) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) := by
        rw [hPe]
        ring

end UnforcedLeray.Short.IIIa
