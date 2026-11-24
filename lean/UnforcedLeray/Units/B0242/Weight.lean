import UnforcedLeray.Units.B0242.Profile
import UnforcedLeray.Units.B0656.Spaces

/-!
# B0242, part 2: the periodic cell weight, the space `X_c`, and the seam

Blueprint unit **B0242** (`unlabeled:4173`), `paper/main.tex` lines 4171–4184:

> Fix `m` sufficiently large, for example `m > 8`, and use
> `X_c = L²(C_c, (1+q²+η²)^m dq dη)`. The weight is defined on the centered cell and
> periodically continued. It is continuous across the seam. Its normal derivative has a
> negative jump there, …  All Sobolev norms below can equivalently use a smooth uniformly
> comparable periodic weight.

The cylinder `C_c = (ℝ/cℤ) × ℝ` (line 4127, `q ∈ [-c/2, c/2)`) is represented as in B0656:
lifted coordinates `(q, η) ∈ ℝ × ℝ`, and the measure `dq dη` on the cylinder is Lebesgue
measure on the open centered cell `B0656.cell c = (-c/2, c/2) × ℝ` (the seam is null), i.e.
`B0656.cellMeasure c`.

The centered-cell weight `(1+q²+η²)^m`, continued periodically, is
`(1 + d(q)² + η²)^m`, where `d(q) = ‖(q : ℝ/cℤ)‖` is the distance from `q` to `cℤ`; on the
closed centered cell `d(q) = |q|` (`cellWeight_eq_polyWeight`). The smooth comparable weight
is B0656's `ρ_c` (line 13872); `rho_rpow_comparable` gives the comparison with constants
depending only on `m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace UnforcedLeray.B0242

open UnforcedLeray.B0656 (cell cellMeasure rho measurableSet_cell)

/-- The distance from `q` to the seam lattice `cℤ`, i.e. the norm of `q` in `ℝ/cℤ`. -/
def latticeDist (c q : ℝ) : ℝ := ‖(q : AddCircle c)‖

theorem latticeDist_of_abs_le {c q : ℝ} (hc : 0 < c) (hq : |q| ≤ c / 2) :
    latticeDist c q = |q| :=
  (AddCircle.norm_coe_eq_abs_iff (p := c) hc.ne').2 (by rwa [abs_of_pos hc])

theorem latticeDist_add_period (c q : ℝ) : latticeDist c (q + c) = latticeDist c q := by
  simp only [latticeDist, AddCircle.coe_add_period]

theorem continuous_latticeDist (c : ℝ) : Continuous (latticeDist c) :=
  continuous_norm.comp (AddCircle.continuous_mk' c)

/-- The weight `(1+q²+η²)^m` of `X_c`, defined on the centered cell and periodically
continued: `(1 + d(q)² + η²)^m` with `d(q)` the distance from `q` to `cℤ`. -/
def cellWeight (m c : ℝ) (z : ℝ × ℝ) : ℝ := (1 + latticeDist c z.1 ^ 2 + z.2 ^ 2) ^ m

/-- The centered-cell formula `(1+q²+η²)^m`. -/
def polyWeight (m : ℝ) (z : ℝ × ℝ) : ℝ := (1 + z.1 ^ 2 + z.2 ^ 2) ^ m

theorem polyWeight_eq_profile_fst (m q η : ℝ) :
    polyWeight m (q, η) = profile m (1 + η ^ 2) q := by
  simp only [polyWeight, profile]
  rw [show 1 + q ^ 2 + η ^ 2 = 1 + η ^ 2 + q ^ 2 by ring]

theorem polyWeight_eq_profile_snd (m q η : ℝ) :
    polyWeight m (q, η) = profile m (1 + q ^ 2) η := rfl

theorem polyWeight_pos (m : ℝ) (z : ℝ × ℝ) : 0 < polyWeight m z :=
  Real.rpow_pos_of_pos (by positivity) m

theorem continuous_polyWeight (m : ℝ) : Continuous (polyWeight m) := by
  have hb : Continuous fun z : ℝ × ℝ => 1 + z.1 ^ 2 + z.2 ^ 2 := by fun_prop
  exact hb.rpow_const fun z => Or.inl (by positivity)

/-- On the closed centered cell the weight is `(1+q²+η²)^m`. -/
theorem cellWeight_eq_polyWeight {m c : ℝ} (hc : 0 < c) {z : ℝ × ℝ} (hz : |z.1| ≤ c / 2) :
    cellWeight m c z = polyWeight m z := by
  simp only [cellWeight, polyWeight, latticeDist_of_abs_le hc hz, sq_abs]

/-- The weight is `c`-periodic in `q`. -/
theorem cellWeight_add_period (m c q η : ℝ) :
    cellWeight m c (q + c, η) = cellWeight m c (q, η) := by
  simp only [cellWeight, latticeDist_add_period]

/-- **Continuity across the seam**: the periodically continued weight is continuous on the
whole cylinder (in particular across `q = ±c/2`). -/
theorem continuous_cellWeight (m c : ℝ) : Continuous (cellWeight m c) := by
  have hd := (continuous_latticeDist c).comp (continuous_fst (X := ℝ) (Y := ℝ))
  have hb : Continuous fun z : ℝ × ℝ => 1 + latticeDist c z.1 ^ 2 + z.2 ^ 2 :=
    (continuous_const.add (hd.pow 2)).add (continuous_snd.pow 2)
  exact hb.rpow_const fun z => Or.inl (by positivity)

theorem cellWeight_pos (m c : ℝ) (z : ℝ × ℝ) : 0 < cellWeight m c z :=
  Real.rpow_pos_of_pos (by positivity) m

/-- On the open cell the weight agrees with `(1+q²+η²)^m`. -/
theorem cellWeight_eq_polyWeight_of_mem {m c : ℝ} (hc : 0 < c) {z : ℝ × ℝ} (hz : z ∈ cell c) :
    cellWeight m c z = polyWeight m z :=
  cellWeight_eq_polyWeight hc (abs_le.2 ⟨hz.1.1.le, hz.1.2.le⟩)

/-! ### The seam: one-sided normal derivatives -/

/-- The normal derivative at the seam `q = c/2` from inside the centered cell. -/
theorem hasDerivWithinAt_cellWeight_seam_left {m c : ℝ} (hc : 0 < c) (η : ℝ) :
    HasDerivWithinAt (fun q => cellWeight m c (q, η)) (profileD m (1 + η ^ 2) (c / 2))
      (Iic (c / 2)) (c / 2) := by
  have ha : (0 : ℝ) < 1 + η ^ 2 := by positivity
  have h := (hasDerivAt_profile m ha (c / 2)).hasDerivWithinAt (s := Iic (c / 2))
  refine h.congr_of_eventuallyEq ?_ ?_
  · have hI : Icc (-(c / 2)) (c / 2) ∈ 𝓝[≤] (c / 2) := Icc_mem_nhdsLE (by linarith)
    filter_upwards [hI] with q hq
    rw [cellWeight_eq_polyWeight hc (z := (q, η)) (abs_le.2 hq), polyWeight_eq_profile_fst]
  · rw [cellWeight_eq_polyWeight hc (z := (c / 2, η)) (by rw [abs_of_pos (by linarith)]),
      polyWeight_eq_profile_fst]

/-- The normal derivative at the seam `q = c/2` from the next cell. -/
theorem hasDerivWithinAt_cellWeight_seam_right {m c : ℝ} (hc : 0 < c) (η : ℝ) :
    HasDerivWithinAt (fun q => cellWeight m c (q, η)) (profileD m (1 + η ^ 2) (-(c / 2)))
      (Ici (c / 2)) (c / 2) := by
  have ha : (0 : ℝ) < 1 + η ^ 2 := by positivity
  have h0 := hasDerivAt_profile m ha (c / 2 - c)
  have h := (h0.comp_sub_const (c / 2) c).hasDerivWithinAt (s := Ici (c / 2))
  rw [show c / 2 - c = -(c / 2) by ring] at h
  have key : ∀ q ∈ Icc (c / 2) (c / 2 + c),
      cellWeight m c (q, η) = profile m (1 + η ^ 2) (q - c) := by
    intro q hq
    have e : cellWeight m c (q, η) = cellWeight m c (q - c, η) := by
      rw [← cellWeight_add_period m c (q - c) η, sub_add_cancel]
    rw [e, cellWeight_eq_polyWeight hc (abs_le.2 ⟨by linarith [hq.1], by linarith [hq.2]⟩),
      polyWeight_eq_profile_fst]
  refine h.congr_of_eventuallyEq ?_ ?_
  · have hI : Icc (c / 2) (c / 2 + c) ∈ 𝓝[≥] (c / 2) := Icc_mem_nhdsGE (by linarith)
    filter_upwards [hI] with q hq
    exact key q hq
  · exact key (c / 2) ⟨le_rfl, by linarith⟩

/-- The jump of the normal derivative across the seam, right minus left. -/
theorem seam_jump_eq (m c η : ℝ) :
    profileD m (1 + η ^ 2) (-(c / 2)) - profileD m (1 + η ^ 2) (c / 2) =
      -(2 * m * c * (1 + η ^ 2 + (c / 2) ^ 2) ^ (m - 1)) := by
  simp only [profileD, neg_sq]
  ring

/-- **The normal derivative has a negative jump at the seam** (line 4179), for `m > 0`. -/
theorem seam_jump_neg {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (η : ℝ) :
    profileD m (1 + η ^ 2) (-(c / 2)) - profileD m (1 + η ^ 2) (c / 2) < 0 := by
  rw [seam_jump_eq]
  have : 0 < (1 + η ^ 2 + (c / 2) ^ 2) ^ (m - 1) := Real.rpow_pos_of_pos (by positivity) _
  have : 0 < 2 * m * c * (1 + η ^ 2 + (c / 2) ^ 2) ^ (m - 1) := by positivity
  linarith

/-! ### The space `X_c` -/

/-- The density `(1+q²+η²)^m`, periodically continued. -/
def weightDensity (m c : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (cellWeight m c z)

/-- The measure `(1+q²+η²)^m dq dη` on the cylinder `C_c`, realized on the centered cell. -/
def weightMeasure (m c : ℝ) : Measure (ℝ × ℝ) := (cellMeasure c).withDensity (weightDensity m c)

/-- `X_c = L²(C_c, (1+q²+η²)^m dq dη)` (line 4175), real valued. -/
abbrev Xc (m c : ℝ) := Lp ℝ 2 (weightMeasure m c)

theorem measurable_weightNN (m c : ℝ) :
    Measurable fun z : ℝ × ℝ => (cellWeight m c z).toNNReal :=
  (continuous_cellWeight m c).measurable.real_toNNReal

theorem weightMeasure_eq (m c : ℝ) :
    weightMeasure m c = (cellMeasure c).withDensity
      (fun z => ((cellWeight m c z).toNNReal : ℝ≥0∞)) := rfl

theorem ae_cell_polyWeight {m c : ℝ} (hc : 0 < c) :
    ∀ᵐ z ∂cellMeasure c, ((cellWeight m c z).toNNReal : ℝ) = polyWeight m z :=
  ae_restrict_of_forall_mem (measurableSet_cell c) fun z hz => by
    rw [Real.coe_toNNReal _ (cellWeight_pos m c z).le, cellWeight_eq_polyWeight_of_mem hc hz]

/-- Integrals against the `X_c` measure are cell integrals with the weight `(1+q²+η²)^m`. -/
theorem integral_weightMeasure {m c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ) :
    ∫ z, g z ∂weightMeasure m c = ∫ z, polyWeight m z * g z ∂cellMeasure c := by
  rw [weightMeasure_eq, integral_withDensity_eq_integral_smul (measurable_weightNN m c)]
  refine integral_congr_ae ?_
  filter_upwards [ae_cell_polyWeight (m := m) hc] with z hz
  rw [NNReal.smul_def, smul_eq_mul, hz]

theorem integrable_weightMeasure_iff {m c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ} :
    Integrable g (weightMeasure m c) ↔
      Integrable (fun z => polyWeight m z * g z) (cellMeasure c) := by
  rw [weightMeasure_eq, integrable_withDensity_iff_integrable_smul (measurable_weightNN m c)]
  refine integrable_congr ?_
  filter_upwards [ae_cell_polyWeight (m := m) hc] with z hz
  rw [NNReal.smul_def, smul_eq_mul, hz]

/-! ### The smooth comparable periodic weight -/

/-- **Uniform comparability with the smooth periodic weight** `ρ_c` of B0656 (line 13872):
for `m ≥ 0` and every `c > 0`, `(4/π²)^m W ≤ ρ_c^m ≤ W` everywhere on the cylinder, where `W`
is the periodically continued weight `(1+q²+η²)^m`. The constants depend only on `m`. -/
theorem rho_rpow_comparable {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (z : ℝ × ℝ) :
    (4 / Real.pi ^ 2) ^ m * cellWeight m c z ≤ rho c z ^ m ∧ rho c z ^ m ≤ cellWeight m c z := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (c⁻¹ * z.1) := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = z.1 - k * c := ⟨_, rfl⟩
  have hd : latticeDist c z.1 = |r| := by
    rw [hr_def, hk]; exact AddCircle.norm_eq c
  have hr : |r| ≤ c / 2 := by
    rw [← hd]
    have := AddCircle.norm_le_half_period (p := c) (x := (z.1 : AddCircle c)) hc.ne'
    rwa [abs_of_pos hc] at this
  have hper : Function.Periodic (fun q => rho c (q, z.2)) c :=
    fun q => B0656.rho_periodic hc.ne' q z.2
  have hρ : rho c z = rho c (r, z.2) := by
    have := (hper.int_mul k) r
    rw [hr_def, sub_add_cancel] at this
    rw [hr_def]
    exact this
  have hW : cellWeight m c z = polyWeight m (r, z.2) := by
    simp only [cellWeight, polyWeight, hd, sq_abs]
  obtain ⟨h1, h2⟩ := B0656.rho_comparable hc (r, z.2) hr
  have hb : (0 : ℝ) ≤ 1 + r ^ 2 + z.2 ^ 2 := by positivity
  have hpi : (0 : ℝ) ≤ 4 / Real.pi ^ 2 := by positivity
  rw [hρ, hW, polyWeight]
  refine ⟨?_, Real.rpow_le_rpow (B0656.rho_pos c _).le h2 hm⟩
  rw [← Real.mul_rpow hpi hb]
  exact Real.rpow_le_rpow (mul_nonneg hpi hb) h1 hm

theorem rho_measure_le {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) :
    B0656.weightMeasure c m ≤ weightMeasure m c := by
  refine withDensity_mono (ae_of_all _ fun z => ?_)
  exact ENNReal.ofReal_le_ofReal (rho_rpow_comparable hm hc z).2

theorem measure_le_rho {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) :
    weightMeasure m c ≤ ENNReal.ofReal ((Real.pi ^ 2 / 4) ^ m) • B0656.weightMeasure c m := by
  rw [B0656.weightMeasure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (ae_of_all _ fun z => ?_)
  have hC : (0 : ℝ) < (Real.pi ^ 2 / 4) ^ m := Real.rpow_pos_of_pos (by positivity) m
  have hc' : (Real.pi ^ 2 / 4) ^ m * (4 / Real.pi ^ 2) ^ m = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show Real.pi ^ 2 / 4 * (4 / Real.pi ^ 2) = 1 by field_simp, Real.one_rpow]
  have h1 := (rho_rpow_comparable hm hc z).1
  have : cellWeight m c z ≤ (Real.pi ^ 2 / 4) ^ m * rho c z ^ m := by
    have := mul_le_mul_of_nonneg_left h1 hC.le
    rwa [← mul_assoc, hc', one_mul] at this
  simp only [Pi.smul_apply, smul_eq_mul, weightDensity, B0656.weightDensity]
  rw [← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal this

/-- **Equivalent norms** (line 4183): `X_c` and the space `X_m` of B0656 built on the smooth
weight `ρ_c^m` have the same elements, with `‖f‖_{X_m} ≤ ‖f‖_{X_c}` and
`‖f‖_{X_c} ≤ ((π²/4)^m)^{1/2} ‖f‖_{X_m}`; the constants depend only on `m`. -/
theorem eLpNorm_rho_le {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (f : ℝ × ℝ → ℝ) :
    eLpNorm f 2 (B0656.weightMeasure c m) ≤ eLpNorm f 2 (weightMeasure m c) :=
  eLpNorm_mono_measure f (rho_measure_le hm hc)

theorem eLpNorm_le_rho {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (f : ℝ × ℝ → ℝ) :
    eLpNorm f 2 (weightMeasure m c) ≤
      ENNReal.ofReal ((Real.pi ^ 2 / 4) ^ m) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (B0656.weightMeasure c m) := by
  have := eLpNorm_mono_measure f (measure_le_rho hm hc) (p := 2)
  rw [eLpNorm_smul_measure_of_ne_top (by simp)] at this
  simpa using this

theorem memLp_iff_rho {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) {f : ℝ × ℝ → ℝ} :
    MemLp f 2 (weightMeasure m c) ↔ MemLp f 2 (B0656.weightMeasure c m) := by
  constructor
  · exact fun h => h.mono_measure (rho_measure_le hm hc)
  · intro h
    exact (h.smul_measure ENNReal.ofReal_ne_top).mono_measure (measure_le_rho hm hc)

end UnforcedLeray.B0242
