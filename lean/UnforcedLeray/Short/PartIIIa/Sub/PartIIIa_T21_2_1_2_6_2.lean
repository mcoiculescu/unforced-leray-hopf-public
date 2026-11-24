import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# `KerApproxId`: decomposition into analytic leaves (SP 2081-2084, 3121)

`the November 2 reference manuscript` lines
2081-2084 and 3121 (`ΔG_d = Σ_n δ_{(nd,0)}`).  Write
`L_ε(z) = (π ε/d²)(cosh(2πη/d) + cos(2πq/d)) / (den z + ε)²` for the Laplacian of
`G_{d,ε} = (4π)⁻¹ log (den + ε)`.  Leaves: the explicit formula, integrability, unit mass on the
cell, and the far tail `≤ C ε`.  The periodic shift, nonnegativity and the `ε → 0` assembly are
proved here (`kerApproxId_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The Laplacian of the regularised stream function (SP 2081-2084). -/
def lapForm (d ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.pi * ε / d ^ 2 * (Real.cosh (2 * Real.pi * z.2 / d) + Real.cos (2 * Real.pi * z.1 / d)) /
    (UnforcedLeray.B0592.den d z + ε) ^ 2

/-- **Leaf (a)**: `ΔG_{d,ε} = lapForm d ε`.  Proof sketch: `∂_q G = (2π/d) sin(2πq/d)/(4π(den+ε))`,
`∂_η G = (2π/d) sinh(2πη/d)/(4π(den+ε))`; `den_q = (2π/d) sin`, `den_η = (2π/d) sinh`,
`den_qq + den_ηη = (2π/d)²(cos+cosh)`, `|∇den|² = (2π/d)²(sin²+sinh²) = (2π/d)² den (cosh+cos)`
(since `sin² + sinh² = cosh² - cos² = den·(cosh+cos)`), so
`ΔG = (4π)⁻¹ [Δden/(den+ε) - |∇den|²/(den+ε)²]
    = (4π)⁻¹ (2π/d)² (cosh+cos) [(den+ε) - den]/(den+ε)²`. -/
def KerLapFormula : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → ∀ z : ℝ × ℝ,
    B0579.pd 0 (B0579.pd 0 (kerReg d ε)) z + B0579.pd 1 (B0579.pd 1 (kerReg d ε)) z =
      lapForm d ε z

/-- **Leaf (b)**: `lapForm d ε` is integrable on the cell (continuous, and
`≤ C e^{-2π|η|/d}` since `den + ε ≥ cosh - 1 + ε`, `cosh + cos ≤ 2 cosh`). -/
def KerLapInt : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → IntegrableOn (lapForm d ε) (B0579.cell d)

/-- **Leaf (c)**: unit mass, `∫_{C_d} ΔG_{d,ε} = 1`.  Sketch: `lapForm = ∂_q(∂_q G) + ∂_η(∂_η G)`;
the `q`-part integrates to `0` by `d`-periodicity, the `η`-part gives
`∫_q [∂_ηG]_{η=-∞}^{+∞} dq` with `∂_ηG → ±1/(2d)` as `η → ±∞`, total `d · (1/(2d)) · 2 = 1`. -/
def KerLapMass : Prop :=
  ∀ d ε : ℝ, 0 < d → 0 < ε → ∫ x in B0579.cell d, lapForm d ε x = 1

/-- **Leaf (d)**: far tail, `∫_{C_d ∩ {‖z‖ ≥ δ}} ΔG_{d,ε} ≤ C_{d,δ} ε` for `0 < ε ≤ 1`
(on `‖z‖ ≥ δ` in the cell, `den ≥ c_{d,δ} > 0` and `den ≳ cosh` for large `|η|`, so
`lapForm ≤ ε · C (cosh+1)/(den+ε)² ≤ ε C' / cosh`, integrable in `η`). -/
def KerLapFar : Prop :=
  ∀ d δ : ℝ, 0 < d → 0 < δ → ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∫ x in B0579.cell d ∩ {x : ℝ × ℝ | δ ≤ ‖x‖}, lapForm d ε x ≤ C * ε


lemma lapForm_nonneg (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (z : ℝ × ℝ) : 0 ≤ lapForm d ε z := by
  unfold lapForm
  have h1 : 1 ≤ Real.cosh (2 * Real.pi * z.2 / d) := Real.one_le_cosh _
  have h2 := Real.neg_one_le_cos (2 * Real.pi * z.1 / d)
  exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)

lemma lapForm_periodic (d ε : ℝ) (hd : 0 < d) (z : ℝ × ℝ) :
    lapForm d ε (z.1 + d, z.2) = lapForm d ε z := by
  have h : 2 * Real.pi * (z.1 + d) / d = 2 * Real.pi * z.1 / d + 2 * Real.pi := by
    field_simp
  simp only [lapForm, UnforcedLeray.B0592.den, h, Real.cos_add_two_pi]

lemma cell_eq_cyl (d : ℝ) : B0579.cell d = UnforcedLeray.Cyl.cell d := by
  simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

/-- Periodic shift: `∫_{cell} H(x + v) dx = ∫_{cell} H`. -/
lemma shift_cell (d : ℝ) (hd : 0 < d) (H : ℝ × ℝ → ℝ) (hH : ∀ z : ℝ × ℝ, H (z.1 + d, z.2) = H z)
    (v : ℝ × ℝ) : ∫ x in B0579.cell d, H (x + v) = ∫ x in B0579.cell d, H x := by
  have hset : B0579.cell d = (fun x : ℝ × ℝ => x + v) ⁻¹'
      (Ico (-d / 2 + v.1) (-d / 2 + v.1 + d) ×ˢ (univ : Set ℝ)) := by
    rw [cell_eq_cyl]
    have := UnforcedLeray.Cyl.preimage_add_strip d (-d / 2) v
    rw [this]
    ext z; simp only [UnforcedLeray.Cyl.cell, mem_prod, mem_Ico, mem_univ, and_true]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  conv_lhs => rw [hset]
  rw [(measurePreserving_add_right volume v).setIntegral_preimage_emb
    (MeasurableEquiv.addRight v).measurableEmbedding H]
  rw [UnforcedLeray.Cyl.integral_strip_eq_cell hd hH, cell_eq_cyl]


/-- The pairing in `KerApproxId` equals `∫_cell L_ε(z) φ(z + y) dz` (periodic shift). -/
lemma pairing_eq (hF : KerLapFormula) (d : ℝ) (hd : 0 < d) (φ : ℝ × ℝ → ℝ)
    (hφ : B0579.IsCylTest d φ) (y : ℝ × ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x =
    ∫ z in B0579.cell d, lapForm d ε z * φ (z + y) := by
  have h1 : ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x =
      ∫ x in B0579.cell d, (fun z : ℝ × ℝ => lapForm d ε z * φ (z + y)) (x + -y) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e0 : B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y)) =
        fun x => B0579.pd 0 (kerReg d ε) (x - y) := funext fun x => pd_shift _ y x 0
    have e1 : B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y)) =
        fun x => B0579.pd 1 (kerReg d ε) (x - y) := funext fun x => pd_shift _ y x 1
    simp only [e0, e1]
    rw [pd_shift (B0579.pd 0 (kerReg d ε)) y x 0, pd_shift (B0579.pd 1 (kerReg d ε)) y x 1,
      hF d ε hd hε (x - y)]
    simp [sub_eq_add_neg]
  rw [h1]
  refine shift_cell d hd (fun z => lapForm d ε z * φ (z + y)) (fun z => ?_) (-y)
  simp only [lapForm_periodic d ε hd z]
  have h2 : ((z.1 + d, z.2) + y : ℝ × ℝ) = ((z + y).1 + d, (z + y).2) := by
    ext <;> simp <;> ring
  rw [h2, hφ.periodic (z + y)]

theorem kerApproxId_of (hF : KerLapFormula) (hI : KerLapInt) (hM : KerLapMass)
    (hFar : KerLapFar) : KerApproxId := by
  intro d hd φ hφ y
  have hd0 : 0 < d := by linarith
  obtain ⟨M, hM0, hMb⟩ := UnforcedLeray.Short.IIIa.Exist.cylTest_exists_bound hd0 hφ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  -- continuity at y
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 (hφ.continuous.continuousAt (x := y))
    (e / 2) (by linarith)
  obtain ⟨C, hC⟩ := hFar d δ hd0 hδ
  set K : ℝ := 2 * M * |C| + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min 1 (e / (2 * K)), lt_min one_pos (by positivity), fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := hε
  have hh : |ε| < 1 ∧ |ε| < e / (2 * K) := by simpa [Real.dist_eq, lt_min_iff] using hεd
  have hε1 : ε < 1 := lt_of_le_of_lt (le_abs_self ε) hh.1
  have hε2 : ε < e / (2 * K) := lt_of_le_of_lt (le_abs_self ε) hh.2
  rw [pairing_eq hF d hd0 φ hφ y ε hε0]
  have hLi := hI d ε hd0 hε0
  have hLnn := lapForm_nonneg d ε hd0 hε0
  have hmass := hM d ε hd0 hε0
  set far : Set (ℝ × ℝ) := {x | δ ≤ ‖x‖} with hfar
  have hfarm : MeasurableSet far := (isClosed_le continuous_const continuous_norm).measurableSet
  have hφc : Continuous fun z : ℝ × ℝ => φ (z + y) :=
    hφ.continuous.comp (continuous_id.add continuous_const)
  have hFi : IntegrableOn (fun z : ℝ × ℝ => lapForm d ε z * φ (z + y)) (B0579.cell d) :=
    hLi.mul_bdd hφc.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hMb (z + y))
  have hGi : IntegrableOn (fun z : ℝ × ℝ => lapForm d ε z * φ y) (B0579.cell d) := hLi.mul_const _
  have hdiff : (∫ z in B0579.cell d, lapForm d ε z * φ (z + y)) - φ y =
      ∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y) := by
    have : ∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y) =
        (∫ z in B0579.cell d, lapForm d ε z * φ (z + y)) -
          ∫ z in B0579.cell d, lapForm d ε z * φ y := by
      rw [← integral_sub hFi hGi]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [mul_sub]
    rw [this, integral_mul_const, hmass, one_mul]
  have hfari : IntegrableOn (lapForm d ε) (B0579.cell d ∩ far) := hLi.mono_set inter_subset_left
  have hLr : Integrable (lapForm d ε) ((volume.restrict (B0579.cell d)).restrict far) :=
    Integrable.restrict (show Integrable (lapForm d ε) (volume.restrict (B0579.cell d)) from hLi)
  have hg_int : Integrable (fun z : ℝ × ℝ => lapForm d ε z * (e / 2) +
      far.indicator (fun z => 2 * M * lapForm d ε z) z) (volume.restrict (B0579.cell d)) := by
    refine (hLi.mul_const _).add ?_
    refine (integrable_indicator_iff hfarm).2 ?_
    exact hLr.const_mul (2 * M)
  have hbound : ‖∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)‖ ≤
      ∫ z in B0579.cell d, (lapForm d ε z * (e / 2) +
        far.indicator (fun z => 2 * M * lapForm d ε z) z) := by
    refine norm_integral_le_of_norm_le hg_int (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hLnn z)]
    by_cases hz : z ∈ far
    · have h2 : ‖φ (z + y) - φ y‖ ≤ 2 * M := by
        rw [Real.norm_eq_abs]
        calc |φ (z + y) - φ y| ≤ |φ (z + y)| + |φ y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hMb _) (hMb _)
          _ = 2 * M := by ring
      rw [Set.indicator_of_mem hz]
      have : 0 ≤ lapForm d ε z * (e / 2) := mul_nonneg (hLnn z) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h2 (hLnn z)]
    · have hz' : ‖z‖ < δ := by simpa [hfar] using hz
      have h2 : dist (φ (z + y)) (φ y) < e / 2 := hcont (by
        rw [dist_eq_norm]; simpa using hz')
      rw [Set.indicator_of_notMem hz, add_zero]
      exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs, ← Real.dist_eq]; exact h2.le)
        (hLnn z)
  have hint : ∫ z in B0579.cell d, (lapForm d ε z * (e / 2) +
      far.indicator (fun z => 2 * M * lapForm d ε z) z) =
      e / 2 + 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z := by
    rw [integral_add (hLi.mul_const _) ((integrable_indicator_iff hfarm).2
      (hLr.const_mul (2 * M))),
      integral_mul_const, hmass, one_mul, setIntegral_indicator hfarm, integral_const_mul]
  have hfarb : ∫ z in B0579.cell d ∩ far, lapForm d ε z ≤ C * ε := hC ε hε0 hε1.le
  have hfin : 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z < e / 2 := by
    have h1 : 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z ≤ 2 * M * (C * ε) :=
      mul_le_mul_of_nonneg_left hfarb (by linarith)
    have h2 : 2 * M * (C * ε) ≤ 2 * M * |C| * ε := by
      have := le_abs_self C
      nlinarith [mul_nonneg hM0 hε0.le, mul_le_mul_of_nonneg_left this (mul_nonneg hM0 hε0.le)]
    have h3 : 2 * M * |C| * ε < K * ε := by
      rw [hK]; nlinarith
    have h4 : K * ε < e / 2 := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * K)).1 hε2
      linarith
    linarith
  rw [Real.dist_eq, hdiff]
  calc |∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)|
      = ‖∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := hbound
    _ = _ := hint
    _ < e := by linarith

end UnforcedLeray.Short.IIIa
