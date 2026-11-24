import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9

/-!
# `PartIII-b:C/inst/10`: `EACoefBound` from source leaves

Source `the November 2 reference manuscript`:
`ret:general-affine-bounds` first line 5009-5016 (for `E_A`), proof 5063-5079 ("The residual
`e_A` has size `C M(A)(s^{3/2}+s^{5/2})`"), cutoff 4953-4963.

`EAcoef = merOf (s^{-1/2} • s^{3/2} • e_A) = s · merOf e_A`, and
`e_A = Σ_j [2 B V_j + 2ν A^y : D²V_j - (A^y + (A^y)ᵀ) ∇p_j]` depends on `s` only through the two
matrices `B = Bmat ν μ χ A s` and `C = Ay ν χ A s`.  Leaves (reusing `BmatBound`, `ChartL2Conv`
of `Sub/PartIII-b_C_inst_9.lean`):

* `EAcSupport` : `E_A = 0` for `s > 1.1/ν`;
* `AyBound` : `|A^y(s)| ≤ s^{5/2} M(A)` for `0 < s ≤ 1.1/ν`;
* `EAcCellBound` : normalized `L²` cell norm of `merOf (e_A)` for constant matrices `B, C`
  is `≤ K (|B| + |C|)` uniformly for `ν ≤ 1`, `s ≤ 1.1/ν`;
* `EAcMeas` : measurability of `EAcoef`.

Proved here: `eaCoefBound_of`.  With `s^{5/2} ≤ T s^{3/2}` (`T = 1.1/ν`) the cell norm of `EAcoef`
is `≤ K M (5/4 + T) s^{5/2}`; the conversion `ChartL2Conv` gives `ν^{-4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `e_A` for constant matrices `B` (in place of `B(s)`) and `C` (in place of `A^y(s)`). -/
def eAB (ν s : ℝ) (B C : Mat3) (x : ℝ × ℝ) : Vec3 :=
  ∑' j : ℤ,
    ((2 : ℝ) • mv B (emb (Vj ν s j x))
      + (2 * ν) • hessContr C (Vj ν s j) x
      - mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x)))

theorem eA_eq_eAB (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    eA ν μ χ A s x = eAB ν s (Bmat ν μ χ A s) (Ay ν χ A s) x := rfl

/-- Support (source 4953-4955, 5063-5079): `χ_f(s) = χ̂_f(νs) = 0` for `s ≥ 1.1/ν`, so
`A^y = 0` near `s > 1.1/ν`, `B = 0`, `E_A = 0` there. -/
def EAcSupport (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ (A : ℝ → Mat3) (s : ℝ), (11 / 10) / ν < s →
    ∀ x : ℝ × ℝ, EAcoef ν μ χf A (s, x) = 0

/-- Size of `A^y` (source 5063-5079): `|A^y(s)| ≤ s^{5/2} M(A)` for `0 < s ≤ 1.1/ν`
(the `j = 0` term of the sum defining the `sSup` `M(A)`; the set is bounded above because
`A ∈ 𝒜` and the derivatives `(s∂_s)^i[χ̂_f(νs)]` are bounded on `(0, 1.1/ν]`). -/
def AyBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → frob (Ay ν χf A s) ≤ s ^ (5 / 2 : ℝ) * affM ν χf A

/-- Gaussian cell norm (source 5063-5079): for constant `B, C`, the normalized `L²` cell norm of
the meridional part of the lattice sum `e_A` is `≤ K (|B| + |C|)`, uniformly for `a = 1 + νs`,
`ν ≤ 1`, `s ≤ 1.1/ν` (Cauchy-Schwarz with Gaussian weights; `V_j, D²V_j, ∇p_j` are Gaussians
times polynomials, `2ν ≤ 2`). -/
def EAcCellBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ B C : Mat3,
    ∫⁻ x, ENNReal.ofReal (‖merOf (eAB ν s B C x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob B + frob C) ^ 2)

/-- Measurability of `EAcoef` (continuity on `s > 0`). -/
def EAcMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    AEStronglyMeasurable (EAcoef ν μ χf A) (srcMeasure (cOf ν))

theorem eaCoefBound_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : EAcSupport χf) (h2 : BmatBound as χf) (h2' : AyBound as χf) (h3 : EAcCellBound)
    (h4 : EAcMeas as χf) (h5 : ChartL2Conv) : EACoefBound as χf := by
  obtain ⟨K, hK0, hK⟩ := h3
  intro Kc hKc hKsub
  refine ⟨K * (9 / 4) * (11 / 10) ^ 4, 4, by positivity, ?_⟩
  intro ν μ hν hν1 hμ A hA
  have hμ' := hKsub hμ
  have hμ0 : 0 ≤ μ := hμ'.1.le
  have hμ1 : μ ≤ 1 / 4 := hμ'.2.le
  have hM := affM_nonneg ν χf A
  set M := affM ν χf A with hMdef
  set T : ℝ := (11 / 10) / ν with hT
  have hT1 : 1 ≤ T := by
    rw [hT, le_div_iff₀ hν]; linarith
  set D : ℝ := K * M * (5 / 4 + T) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖EAcoef ν μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
    intro s hs hsT
    have hB := h2 hχ ν μ hν hμ0 A hA s hs hsT
    have hC := h2' hχ ν hν A hA s hs hsT
    have hc := hK ν s hν hν1 hs hsT (Bmat ν μ χf A s) (Ay ν χf A s)
    have hs32 : (s ^ (3 / 2 : ℝ)) ^ 2 = s ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_natCast]; norm_num
    have hs52 : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
      rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
    have hco : ∀ x : ℝ × ℝ, ‖EAcoef ν μ χf A (s, x)‖ =
        s * ‖merOf (eAB ν s (Bmat ν μ χf A s) (Ay ν χf A s) x)‖ := by
      intro x
      have key : (Real.sqrt s)⁻¹ • (s ^ (3 / 2 : ℝ) • eA ν μ χf A s x) = s • eA ν μ χf A s x := by
        rw [smul_smul]
        congr 1
        have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
        have h32 : s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hs.le (by norm_num)]; norm_num
        rw [h32]; field_simp
      have : EAcoef ν μ χf A (s, x) =
          s • merOf (eAB ν s (Bmat ν μ χf A s) (Ay ν χf A s) x) := by
        simp only [EAcoef, EA]
        rw [key, affMerOf_smul, eA_eq_eAB]
      rw [this, norm_smul, Real.norm_of_nonneg hs.le]
    have hB0 : 0 ≤ frob (Bmat ν μ χf A s) := Real.sqrt_nonneg _
    have hC0 : 0 ≤ frob (Ay ν χf A s) := Real.sqrt_nonneg _
    have hs32' : 0 < s ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
    have hsum : frob (Bmat ν μ χf A s) + frob (Ay ν χf A s) ≤ s ^ (3 / 2 : ℝ) * M * (5 / 4 + T) := by
      have e1 : frob (Bmat ν μ χf A s) ≤ (5 / 4) * (s ^ (3 / 2 : ℝ) * M) := by
        refine hB.trans ?_
        have : (1 + μ) ≤ 5 / 4 := by linarith
        have h0 : 0 ≤ s ^ (3 / 2 : ℝ) * M := by positivity
        nlinarith
      have e2 : frob (Ay ν χf A s) ≤ T * (s ^ (3 / 2 : ℝ) * M) := by
        refine hC.trans ?_
        rw [hs52]
        have h0 : 0 ≤ s ^ (3 / 2 : ℝ) * M := by positivity
        nlinarith
      nlinarith
    have hsq : (frob (Bmat ν μ χf A s) + frob (Ay ν χf A s)) ^ 2
        ≤ (s ^ (3 / 2 : ℝ) * M * (5 / 4 + T)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    calc ∫⁻ x, ENNReal.ofReal (‖EAcoef ν μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        = ∫⁻ x, ENNReal.ofReal (s ^ 2) *
            ENNReal.ofReal (‖merOf (eAB ν s (Bmat ν μ χf A s) (Ay ν χf A s) x)‖ ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
          refine lintegral_congr fun x => ?_
          rw [hco x, mul_pow, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (s ^ 2) *
            ∫⁻ x, ENNReal.ofReal (‖merOf (eAB ν s (Bmat ν μ χf A s) (Ay ν χf A s) x)‖ ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (s ^ 2) *
            ENNReal.ofReal (K ^ 2 * (frob (Bmat ν μ χf A s) + frob (Ay ν χf A s)) ^ 2) :=
          mul_le_mul_of_nonneg_left hc zero_le
      _ = ENNReal.ofReal (s ^ 2 *
            (K ^ 2 * (frob (Bmat ν μ χf A s) + frob (Ay ν χf A s)) ^ 2)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
          apply ENNReal.ofReal_le_ofReal
          have : D ^ 2 * s ^ 5 =
              s ^ 2 * (K ^ 2 * (s ^ (3 / 2 : ℝ) * M * (5 / 4 + T)) ^ 2) := by
            rw [hD, mul_pow, mul_pow, mul_pow, mul_pow, hs32]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity))
            (by positivity)
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  obtain ⟨hm, hn⟩ := h5 (cOf ν) T D (EAcoef ν μ χf A) hc0 hT1 hD0 (h4 hχ ν μ hν A hA)
    (fun s hs x => h1 hχ ν μ hν A s hs x) hcell
  refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hT4 : T ^ 4 = (11 / 10) ^ 4 * ν⁻¹ ^ 4 := by
    rw [hT, div_eq_mul_inv, mul_pow]
  have h94 : 5 / 4 + T ≤ (9 / 4) * T := by linarith
  have hp : 0 ≤ T ^ 3 := by positivity
  calc D * T ^ 3 = K * M * (5 / 4 + T) * T ^ 3 := by rw [hD]
    _ ≤ K * M * ((9 / 4) * T) * T ^ 3 := by gcongr
    _ = K * (9 / 4) * T ^ 4 * M := by ring
    _ = K * (9 / 4) * (11 / 10) ^ 4 * ν⁻¹ ^ 4 * M := by rw [hT4]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
