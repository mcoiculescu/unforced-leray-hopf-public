import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# `PartIII-b:C/inst/9`: `FACoefBound` from five source leaves

Source `the November 2 reference manuscript`:
`ret:general-affine-bounds` first line 5009-5016, proof 5063-5079 (Gaussian cell norms bounded by
`C M(A) s^{3/2}` for `f_A`), cutoff 4953-4963.

`FAcoef = merOf (s^{-1/2} • s^{3/2} • f_A) = s · merOf f_A`.  Leaves:

* `FAcSupport` : `F_A = 0` for `s > 1.1/ν` (`χ_f = 0` on `t ≥ 1.1`);
* `BmatBound`  : `|B(s)| ≤ (1+μ) s^{3/2} M(A)` for `0 < s ≤ 1.1/ν` (conormal size, `|A^y|, |s A^y'| ≤ s^{5/2} M(A)`);
* `FAcCellBound` : the normalized `L²` cell norm of `merOf (f_A)` for constant matrix `B` is `≤ K |B|`
  uniformly for `ν ≤ 1`, `s ≤ 1.1/ν` (Gaussian lattice sum, Cauchy-Schwarz);
* `FAcMeas` : `FAcoef` is a.e. strongly measurable (continuity on `s > 0`);
* `ChartL2Conv` : generic conversion of a cell bound `D² s^5` on `0 < s ≤ T` (zero beyond) into the
  `L²(π s^{-3/2} dς)` norm: `π ∫_0^T s^{-3/2} D² s^5 ds = π D² T^{9/2}/(9/2)`, so the norm is `≤ D T^3`.

Proved here: `faCoefBound_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `f_A` for a constant matrix `B` in place of `B(s)`: `-Σ_j [(B_mer x_j)·∇V_j + B V_j]`. -/
def fAB (ν s : ℝ) (B : Mat3) (x : ℝ × ℝ) : Vec3 :=
  -(∑' j : ℤ,
    (emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))))

theorem fA_eq_fAB (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    fA ν μ χ A s x = fAB ν s (Bmat ν μ χ A s) x := rfl

/-- Support (source 4953-4955, 5063-5079): `χ_f(s) = χ̂_f(νs) = 0` for `s ≥ 1.1/ν`, so
`A^y = 0` near `s > 1.1/ν`, `B = 0`, `F_A = 0` there. -/
def FAcSupport (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ (A : ℝ → Mat3) (s : ℝ), (11 / 10) / ν < s →
    ∀ x : ℝ × ℝ, FAcoef ν μ χf A (s, x) = 0

/-- Conormal size (source 5063-5079): `|B(s)| ≤ (1+μ) s^{3/2} M(A)` for `0 < s ≤ 1.1/ν`
(`|A^y(s)|, |(s∂_s)A^y(s)| ≤ s^{5/2} M(A)`, `B = s⁻¹((s∂_s)A^y + μ A^y)`; `M(A)` is a `sSup`
over `(0, 1.1/ν]`, bounded because `(s∂_s)^i[χ̂_f(νs)]` are bounded there). -/
def BmatBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → 0 ≤ μ → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
      frob (Bmat ν μ χf A s) ≤ (1 + μ) * s ^ (3 / 2 : ℝ) * affM ν χf A

/-- Gaussian cell norm (source 5063-5079): for constant `B`, the normalized `L²` cell norm of the
meridional part of the lattice sum `f_A` is `≤ K |B|`, uniformly for `a = 1 + νs ∈ [1, 2.1]`
(`ν ≤ 1`, `s ≤ 1.1/ν`). -/
def FAcCellBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ B : Mat3,
    ∫⁻ x, ENNReal.ofReal (‖merOf (fAB ν s B x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * frob B ^ 2)

/-- Measurability of `FAcoef` (continuity on `s > 0`: `A` is `C^6`, Gaussian lattice sums
converge locally uniformly). -/
def FAcMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    AEStronglyMeasurable (FAcoef ν μ χf A) (srcMeasure (cOf ν))

/-- Conversion (source 5063-5079, `lintegral_ageμ`): a cell bound `D² s^5` on `0 < s ≤ T`
(`T ≥ 1`), zero beyond `T`, gives `‖F‖_{L²(π s^{-3/2} dς)} ≤ D T^3`
(exact value `D √(2π/9) T^{9/4}`). -/
def ChartL2Conv : Prop :=
  ∀ (c T D : ℝ) (F : Chart → Merid), 0 < c → 1 ≤ T → 0 ≤ D →
    AEStronglyMeasurable F (srcMeasure c) →
    (∀ s : ℝ, T < s → ∀ x : ℝ × ℝ, F (s, x) = 0) →
    (∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5)) →
    MemLp F 2 (srcMeasure c) ∧ eLpNorm F 2 (srcMeasure c) ≤ ENNReal.ofReal (D * T ^ 3)

theorem faCoefBound_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : FAcSupport χf) (h2 : BmatBound as χf) (h3 : FAcCellBound) (h4 : FAcMeas as χf)
    (h5 : ChartL2Conv) : FACoefBound as χf := by
  obtain ⟨K, hK0, hK⟩ := h3
  intro Kc hKc hKsub
  refine ⟨K * (5 / 4) * (11 / 10) ^ 3, 3, by positivity, ?_⟩
  intro ν μ hν hν1 hμ A hA
  have hμ' := hKsub hμ
  have hμ0 : 0 ≤ μ := hμ'.1.le
  have hμ1 : μ ≤ 1 / 4 := hμ'.2.le
  have hM := affM_nonneg ν χf A
  set M := affM ν χf A with hMdef
  set T : ℝ := (11 / 10) / ν with hT
  have hT1 : 1 ≤ T := by
    rw [hT, le_div_iff₀ hν]; linarith
  set D : ℝ := K * (1 + μ) * M with hD
  have h1mu : 0 ≤ 1 + μ := by linarith
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖FAcoef ν μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
    intro s hs hsT
    have hB := h2 hχ ν μ hν hμ0 A hA s hs hsT
    have hc := hK ν s hν hν1 hs hsT (Bmat ν μ χf A s)
    have hs32 : (s ^ (3 / 2 : ℝ)) ^ 2 = s ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_natCast]; norm_num
    have hco : ∀ x : ℝ × ℝ, ‖FAcoef ν μ χf A (s, x)‖ =
        s * ‖merOf (fAB ν s (Bmat ν μ χf A s) x)‖ := by
      intro x
      have key : (Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • fA ν μ χf A s x) = s • fA ν μ χf A s x := by
        rw [smul_smul]
        congr 1
        have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
        have h32 : s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hs.le (by norm_num)]; norm_num
        rw [h32]; field_simp
      have : FAcoef ν μ χf A (s, x) = s • merOf (fAB ν s (Bmat ν μ χf A s) x) := by
        simp only [FAcoef, FA]
        rw [key, affMerOf_smul, fA_eq_fAB]
      rw [this, norm_smul, Real.norm_of_nonneg hs.le]
    have hB0 : 0 ≤ frob (Bmat ν μ χf A s) := Real.sqrt_nonneg _
    have hBsq : frob (Bmat ν μ χf A s) ^ 2 ≤ ((1 + μ) * s ^ (3 / 2 : ℝ) * M) ^ 2 :=
      pow_le_pow_left₀ hB0 hB 2
    calc ∫⁻ x, ENNReal.ofReal (‖FAcoef ν μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        = ∫⁻ x, ENNReal.ofReal (s ^ 2) *
            ENNReal.ofReal (‖merOf (fAB ν s (Bmat ν μ χf A s) x)‖ ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
          refine lintegral_congr fun x => ?_
          rw [hco x, mul_pow, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (s ^ 2) *
            ∫⁻ x, ENNReal.ofReal (‖merOf (fAB ν s (Bmat ν μ χf A s) x)‖ ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (K ^ 2 * frob (Bmat ν μ χf A s) ^ 2) :=
          by gcongr
      _ = ENNReal.ofReal (s ^ 2 * (K ^ 2 * frob (Bmat ν μ χf A s) ^ 2)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
          apply ENNReal.ofReal_le_ofReal
          have : D ^ 2 * s ^ 5 = s ^ 2 * (K ^ 2 * ((1 + μ) * s ^ (3 / 2 : ℝ) * M) ^ 2) := by
            rw [hD, mul_pow, mul_pow, mul_pow, mul_pow, hs32]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBsq (by positivity))
            (by positivity)
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  obtain ⟨hm, hn⟩ := h5 (cOf ν) T D (FAcoef ν μ χf A) hc0 hT1 hD0 (h4 hχ ν μ hν A hA)
    (fun s hs x => h1 hχ ν μ hν A s hs x) hcell
  refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hT3 : T ^ 3 = (11 / 10) ^ 3 * ν⁻¹ ^ 3 := by
    rw [hT, div_eq_mul_inv, mul_pow]
  rw [hT3, hD]
  have h54 : 1 + μ ≤ 5 / 4 := by linarith
  have hp : 0 ≤ (11 / 10 : ℝ) ^ 3 * ν⁻¹ ^ 3 := by positivity
  calc K * (1 + μ) * M * ((11 / 10) ^ 3 * ν⁻¹ ^ 3)
      ≤ K * (5 / 4) * M * ((11 / 10) ^ 3 * ν⁻¹ ^ 3) := by gcongr
    _ = K * (5 / 4) * (11 / 10) ^ 3 * ν⁻¹ ^ 3 * M := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
