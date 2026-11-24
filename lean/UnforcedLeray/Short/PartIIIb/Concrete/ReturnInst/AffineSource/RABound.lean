import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.ChartConv
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.Envelope

/-!
# The bound of `𝔯_A` and `RABoundExists` (source 5009-5016, proof 5022-5079)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (a) of `ORG:return-concrete/instance-3/affine-source`, the estimate half, and the reduction
of `RABoundExists D dm dp` (`Concrete/ReturnInst.lean`) to the leaves of `RADefs.lean`.

* `chartL2_cell52`, `chartL2_cellGeo` : the body conversion (source 5055-5060, `ChartL2Conv`,
  accepted `PartIII-b:C/inst/9/5`) of the cell bounds `C δ_base M s^{5/2}` of `r_per`
  (coefficient `s·r_per`) and `P_ν εM(s^{5/2}+s^{7/2})` of the geometric remainder: the age
  powers `s^{11/2}, s^{7/2}` are integrable at zero and the upper end `T = 1.1/ν` costs `P_ν`;
* `rAcoef_bound_of` : at one level, `rAcoef = s·r_per + geoCoef + convCoef` (`rAcoef_decomp`) is in
  `L²(π s^{-3/2} dς)` with `R⁻¹‖𝔯_A‖_{Y_2} ≤ P_ν(ε + δ_base + δ_U)M(A)`;
* `raBoundExists_of` : **`RABoundExists D dm dp`** from the leaves, the accepted first-line
  leaves of `ReturnInst/AffineFields.lean`, the envelope (`affMEnvelope`), the transport pin
  `NearInst.MultPinOfLink` (`PartIII-b:C/near/link/2`) and three per-level background facts:
  the split multiplier exists (`IsSplitMult`, the near layer `NearInst.NearOpsExistC`,
  `PartIII-b:C/near/5`), `U = V + r_b` is axisymmetric without swirl (source 2031, 2522-2523,
  4144-4145), and `U - U_raw` has a finite `W^{1,∞}` bound (source 5094: "`δ_U ≤ P_νρ` from the
  background bounds").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Real-power algebra -/

theorem ra_rpow52_sq {s : ℝ} (hs : 0 ≤ s) : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
  rw [← Real.rpow_mul_natCast hs, ← Real.rpow_natCast s 5]
  norm_num

theorem ra_rpow72 {s : ℝ} (hs : 0 < s) : s ^ (7 / 2 : ℝ) = s * s ^ (5 / 2 : ℝ) := by
  rw [show (7 / 2 : ℝ) = 1 + 5 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]

theorem toMer_zero : toMer (0 : ℝ × ℝ) = 0 := by
  ext i
  fin_cases i <;> rfl

/-! ## 2. The body conversion (source 5055-5060) -/

/-- The cell bound `|r_per(s)| ≤ K s^{5/2}` on `(0, T]` gives `‖s·r_per‖_{L²(π s^{-3/2}dς)} ≤ |K|T⁴`. -/
theorem chartL2_cell52 (hconv : ChartL2Conv) {c T K : ℝ} {r : ℝ → ℝ × ℝ → ℝ × ℝ}
    (hc : 0 < c) (hT : 1 ≤ T)
    (hm : AEStronglyMeasurable (fun p : Chart => p.1 • toMer (r p.1 p.2)) (srcMeasure c))
    (hsupp : ∀ s : ℝ, T < s → ∀ x : ℝ × ℝ, r s x = 0)
    (hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖toMer (r s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal ((K * s ^ (5 / 2 : ℝ)) ^ 2)) :
    MemLp (fun p : Chart => p.1 • toMer (r p.1 p.2)) 2 (srcMeasure c) ∧
      eLpNorm (fun p : Chart => p.1 • toMer (r p.1 p.2)) 2 (srcMeasure c) ≤
        ENNReal.ofReal (|K| * T * T ^ 3) := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  refine hconv c T (|K| * T) _ hc hT (mul_nonneg (abs_nonneg K) hT0.le) hm ?_ ?_
  · intro s hs x
    simp only [hsupp s hs x, toMer_zero, smul_zero]
  · intro s hs hsT
    have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖(s, x).1 • toMer (r (s, x).1 (s, x).2)‖ ^ 2) =
        ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (‖toMer (r s x)‖ ^ 2) := by
      intro x
      rw [← ENNReal.ofReal_mul (sq_nonneg s), norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_of_nonneg_left (hcell s hs hsT) bot_le).trans ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg s)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h5 := ra_rpow52_sq hs.le
    have hsT2 : s ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hs.le hsT 2
    have e1 : s ^ 2 * (K * s ^ (5 / 2 : ℝ)) ^ 2 = K ^ 2 * s ^ 5 * s ^ 2 := by
      rw [mul_pow, h5]; ring
    have e2 : (|K| * T) ^ 2 * s ^ 5 = K ^ 2 * s ^ 5 * T ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hsT2 (mul_nonneg (sq_nonneg K) (pow_nonneg hs.le 5))

/-- The cell bound `|g(s)| ≤ K(s^{5/2} + s^{7/2})` on `(0, T]` gives
`‖g‖_{L²(π s^{-3/2}dς)} ≤ |K|(1+T)T³`. -/
theorem chartL2_cellGeo (hconv : ChartL2Conv) {c T K : ℝ} {F : Chart → Merid}
    (hc : 0 < c) (hT : 1 ≤ T) (hm : AEStronglyMeasurable F (srcMeasure c))
    (hsupp : ∀ s : ℝ, T < s → ∀ x : ℝ × ℝ, F (s, x) = 0)
    (hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal ((K * (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2)) :
    MemLp F 2 (srcMeasure c) ∧
      eLpNorm F 2 (srcMeasure c) ≤ ENNReal.ofReal (|K| * (1 + T) * T ^ 3) := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  refine hconv c T (|K| * (1 + T)) F hc hT (mul_nonneg (abs_nonneg K) (by linarith)) hm hsupp ?_
  intro s hs hsT
  refine (hcell s hs hsT).trans (ENNReal.ofReal_le_ofReal ?_)
  have h5 := ra_rpow52_sq hs.le
  have hq : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have e1 : (K * (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2 =
      (|K| * s ^ (5 / 2 : ℝ) * (1 + s)) ^ 2 := by
    rw [ra_rpow72 hs, mul_pow, mul_pow, mul_pow, sq_abs]; ring
  have e2 : (|K| * (1 + T)) ^ 2 * s ^ 5 = (|K| * s ^ (5 / 2 : ℝ) * (1 + T)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, h5]; ring
  rw [e1, e2]
  have h0 : 0 ≤ |K| * s ^ (5 / 2 : ℝ) * (1 + s) :=
    mul_nonneg (mul_nonneg (abs_nonneg K) hq) (by linarith)
  exact pow_le_pow_left₀ h0
    (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg K) hq)) 2

/-! ## 3. The bound at one level -/

/-- **`R⁻¹‖𝔯_A‖_{Y_2} ≤ P_ν(ε + δ_base + δ_U)M(A)` at one level** (source 5014-5016, 5022-5079), from
the three part estimates and the body conversion, for `0 < ν ≤ 1`, `c = ν⁻²`. -/
theorem rAcoef_bound_of (hconv : ChartL2Conv) {p : Params} {μ : ℝ} {χf : ℝ → ℝ}
    {U : ℝ → SpatialField} {A : ℝ → Mat3} (hν1 : p.ν ≤ 1) {δ M δU C₁ C₂ C₃ : ℝ}
    {k₁ k₂ k₃ : ℕ}
    (h1 : AEStronglyMeasurable (rPerCoef μ χf p.train A) (srcMeasure p.c) ∧
      (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, rPer μ χf p.train A s x = 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        ∫⁻ x, ENNReal.ofReal (‖toMer (rPer μ χf p.train A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
          ≤ ENNReal.ofReal ((C₁ * p.ν⁻¹ ^ k₁ * δ * M * s ^ (5 / 2 : ℝ)) ^ 2))
    (h2 : AEStronglyMeasurable (geoCoef p μ χf A) (srcMeasure p.c) ∧
      (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, geoCoef p μ χf A (s, x) = 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        ∫⁻ x, ENNReal.ofReal (‖geoCoef p μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
          ≤ ENNReal.ofReal ((C₂ * p.ν⁻¹ ^ k₂ * p.ε * M * (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2))
    (h3 : MemLp (convCoef p μ χf U A) 2 (srcMeasure p.c) ∧
      eLpNorm (convCoef p μ χf U A) 2 (srcMeasure p.c) ≤
        ENNReal.ofReal (C₃ * p.ν⁻¹ ^ k₃ * δU * M))
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hδU : 0 ≤ δU) :
    MemLp (rAcoef p.ν μ p.ε p.c χf U A) 2 (srcMeasure p.c) ∧
      eLpNorm (rAcoef p.ν μ p.ε p.c χf U A) 2 (srcMeasure p.c) ≤
        ENNReal.ofReal ((16 * |C₁| + 24 * |C₂| + |C₃|) * p.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
          (p.ε + δ + δU) * M) := by
  set T := (11 / 10) / p.ν with hTdef
  set a := p.ν⁻¹ with ha
  have hν := p.ν_pos
  have ha1 : 1 ≤ a := (one_le_inv₀ hν).2 hν1
  have ha0 : 0 ≤ a := le_trans zero_le_one ha1
  have hT : 1 ≤ T := by
    rw [hTdef, le_div_iff₀ hν]
    linarith
  have hTa : T ≤ 2 * a := by
    rw [hTdef, ha, div_eq_mul_inv]
    have := inv_pos.2 hν
    nlinarith
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hε := p.ε_pos
  have c1 := chartL2_cell52 hconv p.c_pos hT h1.1 h1.2.1 h1.2.2
  have c2 := chartL2_cellGeo hconv p.c_pos hT h2.1 h2.2.1 h2.2.2
  have hdec := rAcoef_decomp p μ χf U A
  have hmem : MemLp (rAcoef p.ν μ p.ε p.c χf U A) 2 (srcMeasure p.c) := by
    rw [hdec]
    exact (c1.1.add c2.1).add h3.1
  refine ⟨hmem, ?_⟩
  have hsum : eLpNorm (rAcoef p.ν μ p.ε p.c χf U A) 2 (srcMeasure p.c) ≤
      ENNReal.ofReal (|C₁ * a ^ k₁ * δ * M| * T * T ^ 3) +
        ENNReal.ofReal (|C₂ * a ^ k₂ * p.ε * M| * (1 + T) * T ^ 3) +
        ENNReal.ofReal (C₃ * a ^ k₃ * δU * M) := by
    rw [hdec]
    refine (eLpNorm_add_le (c1.1.add c2.1).1 h3.1.1 (by norm_num)).trans ?_
    refine add_le_add ((eLpNorm_add_le c1.1.1 c2.1.1 (by norm_num)).trans ?_) h3.2
    exact add_le_add c1.2 c2.2
  refine hsum.trans ?_
  have hA1 : |C₁ * a ^ k₁ * δ * M| = |C₁| * a ^ k₁ * δ * M := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ha0 _), abs_of_nonneg hδ,
      abs_of_nonneg hM]
  have hA2 : |C₂ * a ^ k₂ * p.ε * M| = |C₂| * a ^ k₂ * p.ε * M := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ha0 _), abs_of_nonneg hε.le,
      abs_of_nonneg hM]
  rw [hA1, hA2]
  have n1 : 0 ≤ |C₁| * a ^ k₁ * δ * M * T * T ^ 3 := by positivity
  have n2 : 0 ≤ |C₂| * a ^ k₂ * p.ε * M * (1 + T) * T ^ 3 := by positivity
  rw [← ENNReal.ofReal_add n1 n2]
  refine (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
    (show C₃ * a ^ k₃ * δU * M ≤ |C₃| * a ^ k₃ * δU * M from
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₃) (pow_nonneg ha0 _)) hδU) hM))).trans ?_
  have n3 : 0 ≤ |C₃| * a ^ k₃ * δU * M := by positivity
  rw [← ENNReal.ofReal_add (add_nonneg n1 n2) n3]
  refine ENNReal.ofReal_le_ofReal ?_
  set k := k₁ + k₂ + k₃ + 4 with hk
  have hp1 : a ^ (k₁ + 4) ≤ a ^ k := pow_le_pow_right₀ ha1 (by omega)
  have hp2 : a ^ (k₂ + 4) ≤ a ^ k := pow_le_pow_right₀ ha1 (by omega)
  have hp3 : a ^ k₃ ≤ a ^ k := pow_le_pow_right₀ ha1 (by omega)
  have hT4 : T * T ^ 3 ≤ 16 * a ^ 4 := by
    have h4 : T ^ 4 ≤ (2 * a) ^ 4 := pow_le_pow_left₀ hT0 hTa 4
    calc T * T ^ 3 = T ^ 4 := by ring
      _ ≤ (2 * a) ^ 4 := h4
      _ = 16 * a ^ 4 := by ring
  have hT13 : (1 + T) * T ^ 3 ≤ 24 * a ^ 4 := by
    have h1T : 1 + T ≤ 3 * a := by linarith
    have h3' : T ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ hT0 hTa 3
    calc (1 + T) * T ^ 3 ≤ (3 * a) * (2 * a) ^ 3 :=
          mul_le_mul h1T h3' (pow_nonneg hT0 3) (by positivity)
      _ = 24 * a ^ 4 := by ring
  have t1 : |C₁| * a ^ k₁ * δ * M * T * T ^ 3 ≤ 16 * |C₁| * a ^ k * δ * M := by
    have : |C₁| * a ^ k₁ * δ * M * T * T ^ 3 = (|C₁| * δ * M) * (a ^ k₁ * (T * T ^ 3)) := by ring
    rw [this]
    have hb : a ^ k₁ * (T * T ^ 3) ≤ 16 * a ^ k := by
      calc a ^ k₁ * (T * T ^ 3) ≤ a ^ k₁ * (16 * a ^ 4) :=
            mul_le_mul_of_nonneg_left hT4 (pow_nonneg ha0 _)
        _ = 16 * a ^ (k₁ + 4) := by ring
        _ ≤ 16 * a ^ k := by linarith
    calc (|C₁| * δ * M) * (a ^ k₁ * (T * T ^ 3)) ≤ (|C₁| * δ * M) * (16 * a ^ k) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 16 * |C₁| * a ^ k * δ * M := by ring
  have t2 : |C₂| * a ^ k₂ * p.ε * M * (1 + T) * T ^ 3 ≤ 24 * |C₂| * a ^ k * p.ε * M := by
    have : |C₂| * a ^ k₂ * p.ε * M * (1 + T) * T ^ 3 =
        (|C₂| * p.ε * M) * (a ^ k₂ * ((1 + T) * T ^ 3)) := by ring
    rw [this]
    have hb : a ^ k₂ * ((1 + T) * T ^ 3) ≤ 24 * a ^ k := by
      calc a ^ k₂ * ((1 + T) * T ^ 3) ≤ a ^ k₂ * (24 * a ^ 4) :=
            mul_le_mul_of_nonneg_left hT13 (pow_nonneg ha0 _)
        _ = 24 * a ^ (k₂ + 4) := by ring
        _ ≤ 24 * a ^ k := by linarith
    calc (|C₂| * p.ε * M) * (a ^ k₂ * ((1 + T) * T ^ 3)) ≤ (|C₂| * p.ε * M) * (24 * a ^ k) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 24 * |C₂| * a ^ k * p.ε * M := by ring
  have t3 : |C₃| * a ^ k₃ * δU * M ≤ |C₃| * a ^ k * δU * M := by
    have : |C₃| * a ^ k₃ * δU * M = (|C₃| * δU * M) * a ^ k₃ := by ring
    rw [this]
    calc (|C₃| * δU * M) * a ^ k₃ ≤ (|C₃| * δU * M) * a ^ k :=
          mul_le_mul_of_nonneg_left hp3 (by positivity)
      _ = |C₃| * a ^ k * δU * M := by ring
  have hrest : 0 ≤ a ^ k * M * (16 * |C₁| * (p.ε + δU) + 24 * |C₂| * (δ + δU) +
      |C₃| * (p.ε + δ)) := by positivity
  have e : (16 * |C₁| + 24 * |C₂| + |C₃|) * a ^ k * (p.ε + δ + δU) * M =
      16 * |C₁| * a ^ k * δ * M + 24 * |C₂| * a ^ k * p.ε * M + |C₃| * a ^ k * δU * M +
        a ^ k * M * (16 * |C₁| * (p.ε + δU) + 24 * |C₂| * (δ + δU) + |C₃| * (p.ε + δ)) := by ring
  rw [e]
  linarith

/-! ## 4. `RABoundExists` -/

/-- A finite `W^{1,∞}` bound `d` of `U - U_raw` at level `n` (source 5007-5008, 5094). -/
def SeqData.W1InfAt (D : SeqData) (n : ℕ) (d : ℝ) : Prop :=
  ∀ (τ : ℝ) (y : Space),
    ‖(D.level n).U τ y - ((D.level n).params D.Pl).raw τ y‖ ≤ d ∧
      ‖fderiv ℝ (fun y' => (D.level n).U τ y' - ((D.level n).params D.Pl).raw τ y') y‖ ≤ d

/-- **Lemma `ret:physical-affine` with the second line of `ret:general-affine-bounds` along the
sequence** (source 5001-5016, proof 5022-5079): `RABoundExists D dm dp` from

* the data of `D`: `Im λ ≠ 0`, `Re λ > 0`, `σ₀ ∈ (0, 1/4)`, the source cutoff `χ̂_f`, `C₀ > 0`,
  `a_s ≥ 0`, `d₋ > 0`;
* three per-level background facts for large `n`: the split multiplier `M_U` exists (near layer,
  `PartIII-b:C/near/5`), `U = V + r_b` is axisymmetric without swirl (source 2031, 2522-2523,
  4144-4145), `U - U_raw` has a finite `W^{1,∞}` bound (source 5094);
* accepted or queued facts: `MultPinOfLink` (`PartIII-b:C/near/link/2`), `ChartL2Conv`
  (`PartIII-b:C/inst/9/5`), the first-line leaves `HhatCoefLinear`, `FACoefLinear`,
  `EACoefLinear` (`PartIII-b:C/ret/7..9` chain), `HhatCoefBound`, `FACoefBound`, `EACoefBound`
  (`PartIII-b:C/inst/11`, `/9`, `/10`);
* the leaves of `RADefs.lean`. -/
theorem raBoundExists_of (D : SeqData) (dm dp : ℝ) (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (hC0 : 0 < D.K.C0) (has : 0 ≤ D.K.as)
    (hsplit : ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb)
    (hax : ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ))
    (hW1 : ∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d)
    (hpin : NearInst.MultPinOfLink)
    (lh : HhatCoefLinear D.K.as D.K.χf) (lF : FACoefLinear D.K.as D.K.χf)
    (lE : EACoefLinear D.K.as D.K.χf) (bh : HhatCoefBound D.K.as D.K.χf)
    (bF : FACoefBound D.K.as D.K.χf) (bE : EACoefBound D.K.as D.K.χf)
    (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1) (hCont : IBPContC)
    (hreg : AffineLiftReg D.K.as D.K.χf) (haxi : RAPhysAxi D.K.as D.K.χf)
    (hlin : RALinear D.K.as D.K.χf) (hper : RPerBound D.K.as D.K.χf)
    (hgeo : RAGeoBound D.K.as D.K.χf) (hcv : RAConvBound D.K.as D.K.χf) :
    RABoundExists D dm dp := by
  intro hact
  set Kset : Set ℝ := Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) with hKdef
  have hKc : IsCompact Kset := isCompact_Icc
  have hKs : Kset ⊆ Ioo 0 (1 / 4) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨Csig, bsig, C₁, k₁, ν₁, hb, hν₁, h1⟩ := hper hχf Kset hKc hKs dm dp hdm
  obtain ⟨C₂, k₂, ν₂, hν₂, h2⟩ := hgeo hχf Kset hKc hKs dm dp hdm
  obtain ⟨C₃, k₃, ν₃, hν₃, h3⟩ := hcv hχf Kset hKc hKs dm dp hdm
  obtain ⟨Cenv, hCenv0, hCenv⟩ := affM_le_norm_of (affMEnvelope D.K.χf hχf)
  have hν0 : 0 < min (min ν₁ ν₂) ν₃ := lt_min (lt_min hν₁ hν₂) hν₃
  have hev := ((((((hact.and ((retNu_tendsto D.σ₀ hω).eventually_le_const hν0)).and
    (retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hω hγ D.coeff_ne)).and
    (mu_eventually_mem D hω hσ0 hσ1)).and hsplit).and hax).and hW1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨Csig, bsig, 16 * |C₁| + 24 * |C₂| + |C₃|, k₁ + k₂ + k₃ + 4, N, hb, ?_⟩
  intro n hn z hz
  obtain ⟨⟨⟨⟨⟨⟨hactn, hνn⟩, hνε⟩, hμn⟩, hsn⟩, haxn⟩, ⟨d, hd⟩⟩ := hN n hn
  have hμK : D.mu n z ∈ Kset := hμn z hz
  have hνp1 : retNu D.Pl D.σ₀ n ≤ ν₁ := le_trans hνn (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνp2 : retNu D.Pl D.σ₀ n ≤ ν₂ := le_trans hνn (le_trans (min_le_left _ _) (min_le_right _ _))
  have hνp3 : retNu D.Pl D.σ₀ n ≤ ν₃ := le_trans hνn (min_le_right _ _)
  set L := D.level n with hL
  set p := L.params D.Pl with hp
  set μ := D.mu n z with hμ
  have hν : 0 < L.ν := L.ν_pos
  have hLν : L.ν = retNu D.Pl D.σ₀ n := rfl
  -- the affine field data and the envelope at the level
  have henv : ∀ A : AffSp D.K.as,
      affM L.ν D.K.χf (affIota D.K.as A) ≤ Cenv * Real.exp (1.1 * D.K.as / L.ν) * ‖A‖ :=
    fun A => hCenv D.K.as L.ν (fun A => affIota D.K.as A) has hν (affIota_mem D.K.as)
      (fun A => (affNorm_affIota D.K.as A).le) A
  have hdat : AffineFieldData D.K.as L.ν μ L.ε (gRate D.Pl) D.K.χf (affIota D.K.as) :=
    affineFieldData_of (affIota_mem D.K.as) hν hνε.1 L.ε_pos hνε.2 hγ.le hKc hKs hμK _ henv
      lh lF lE bh bF bE
  -- the bound at the level, for every `W^{1,∞}` bound
  have key : ∀ δU : ℝ, (∀ (τ : ℝ) (y : Space), ‖L.U τ y - p.raw τ y‖ ≤ δU ∧
        ‖fderiv ℝ (fun y' => L.U τ y' - p.raw τ y') y‖ ≤ δU) →
      ∀ A : ℝ → Mat3, IsAffElem D.K.as A →
        MemLp (rAcoef L.ν μ L.ε (cOf L.ν) D.K.χf L.U A) 2 (srcMeasure (cOf L.ν)) ∧
        eLpNorm (rAcoef L.ν μ L.ε (cOf L.ν) D.K.χf L.U A) 2 (srcMeasure (cOf L.ν)) ≤
          ENNReal.ofReal ((16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
            (L.ε + deltaBase Csig bsig L.ν + δU) * affM L.ν D.K.χf A) := by
    intro δU hδU A hA
    have hδU0 : 0 ≤ δU := le_trans (norm_nonneg _) (hδU 0 0).1
    exact rAcoef_bound_of (p := p) chartL2Conv hνε.1
      (h1 p _ hactn.regime hνp1 μ hμK A hA) (h2 p _ hactn.regime hνp2 μ hμK A hA)
      (h3 p _ hactn.regime hνp3 μ hμK L.U (D.pres n) hactn.profile δU hδU A hA)
      (Real.exp_pos _).le (affM_nonneg _ _ _) hδU0
  have hU1 : ContDiff ℝ 1 (fun x : ℝ × Space => L.U x.1 x.2) :=
    hactn.profile.smoothU.of_le (by exact_mod_cast le_top)
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) (hd 0 0).1
  have hδb : 0 < deltaBase Csig bsig L.ν := Real.exp_pos _
  have hpre : ∀ δU : ℝ, 0 ≤ δU → 0 ≤ (16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
      (L.ε + deltaBase Csig bsig L.ν + δU) := fun δU h0 =>
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 hν.le) _))
      (by linarith [L.ε_pos])
  have hfam : IsL2Family (srcMeasure (cOf L.ν))
      (fun A : AffSp D.K.as => rAcoef L.ν μ L.ε (cOf L.ν) D.K.χf L.U (affIota D.K.as A)) :=
    { memLp := fun A => (key d hd (affIota D.K.as A) (affIota_mem D.K.as A)).1
      add := fun A A' => by
        filter_upwards [ae_srcMeasure_fst_pos (cOf L.ν)] with q hq
        simp only [map_add, Pi.add_apply]
        exact (hlin hχf L.ν μ L.ε hν L.ε_pos L.U hU1 _ _ 1 (affIota_mem D.K.as A)
          (affIota_mem D.K.as A') q hq).1
      smul := fun r A => by
        filter_upwards [ae_srcMeasure_fst_pos (cOf L.ν)] with q hq
        simp only [map_smul, Pi.smul_apply]
        exact (hlin hχf L.ν μ L.ε hν L.ε_pos L.U hU1 _ _ r (affIota_mem D.K.as A)
          (affIota_mem D.K.as A) q hq).2
      bound := ⟨(16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
          (L.ε + deltaBase Csig bsig L.ν + d) * (Cenv * Real.exp (1.1 * D.K.as / L.ν)), fun A => by
        refine (key d hd (affIota D.K.as A) (affIota_mem D.K.as A)).2.trans
          (ENNReal.ofReal_le_ofReal ?_)
        calc (16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
              (L.ε + deltaBase Csig bsig L.ν + d) * affM L.ν D.K.χf (affIota D.K.as A)
            ≤ (16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
              (L.ε + deltaBase Csig bsig L.ν + d) *
                (Cenv * Real.exp (1.1 * D.K.as / L.ν) * ‖A‖) :=
              mul_le_mul_of_nonneg_left (henv A) (hpre d hd0)
          _ = (16 * |C₁| + 24 * |C₂| + |C₃|) * L.ν⁻¹ ^ (k₁ + k₂ + k₃ + 4) *
              (L.ε + deltaBase Csig bsig L.ν + d) * (Cenv * Real.exp (1.1 * D.K.as / L.ν)) *
                ‖A‖ := by ring⟩ }
  refine ⟨hfam.toCLM, isRAOp_of hAdj hDiv hGrad hCont hreg haxi hχf hpin hsn hC0 haxn
    hactn.profile hdat hfam.toCLM hfam.toCLM_ae, ?_⟩
  intro e he A
  rw [IsL2Family.norm_toCLM]
  have hen : ∀ (τ : ℝ) (y : Space), ‖L.U τ y - p.raw τ y‖ ≤ e ∧
      ‖fderiv ℝ (fun y' => L.U τ y' - p.raw τ y') y‖ ≤ e := fun τ y => he τ y
  have he0 : 0 ≤ e := le_trans (norm_nonneg _) (hen 0 0).1
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (hpre e he0) (affM_nonneg _ _ _))
    (key e hen (affIota D.K.as A) (affIota_mem D.K.as A)).2

end UnforcedLeray.Short.PartIIIb.Concrete
