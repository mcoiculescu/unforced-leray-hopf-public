import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# `PartIII-b:C/inst/11`: `HhatCoefBound` from source leaves

Source `the November 2 reference manuscript`:
`ret:general-affine-bounds` first line 5009-5016 (for `ĥ_A`), proof 5063-5079 ("`C M(A) s^{5/2}`
for both `h^p_A` and `ψ^p_A`"), cutoff 4953-4963, definition of `ĥ_A` 4979-4980.

`hAcoef = merOf (s^{-1/2} • ĥ_A)` and `ĥ_A = √s [(h^p)_r e_r + ((h^p)_z + ε(1-𝒦)ψ^p) e_z]`, so
`|hAcoef|` is controlled pointwise in `s` by `A^y(s)` and `(s∂_s)A^y(s)` (the `𝒦 = η∂_η + 2s∂_s`
term uses one conormal derivative).  Leaves (reusing `AyBound`, `ChartL2Conv` of
`Sub/PartIII-b_C_inst_10.lean` and `Sub/PartIII-b_C_inst_9.lean`):

* `HAcSupport`, `AyDerivBound`, `HAcCellBound`, `HAcMeas`.

Proved here: `hhatCoefBound_of`.  With `|A^y|, |(s∂_s)A^y| ≤ s^{5/2} M` the cell norm of
`hAcoef` is `≤ 2 K M s^{5/2}`; `ChartL2Conv` gives `‖·‖ ≤ D T^3`, `T = 1.1/ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Support (source 4953-4955, 5063-5079): `χ_f(s) = χ̂_f(νs) = 0` for `s ≥ 1.1/ν`, so
`A^y = 0` on a neighbourhood of each `s > 1.1/ν`, hence `h^p_A = ψ^p_A = 0` there with all
`s`-derivatives, and `ĥ_A = 0`. -/
def HAcSupport (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ (A : ℝ → Mat3) (s : ℝ), (11 / 10) / ν < s →
    ∀ x : ℝ × ℝ, hAcoef ν ε χf A (s, x) = 0

/-- Conormal size of the first derivative (source 5063-5079): `|(s∂_s)A^y(s)| ≤ s^{5/2} M(A)`
for `0 < s ≤ 1.1/ν` (the `j = 1` term of the sum defining the `sSup` `M(A)`). -/
def AyDerivBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
      frob (sDeriv (Ay ν χf A) s) ≤ s ^ (5 / 2 : ℝ) * affM ν χf A

/-- Gaussian cell norm (source 5063-5079): the normalized `L²` cell norm of the meridional field
`hAcoef (s, ·)` (lattice sums `h^p_A`, `ψ^p_A`, `𝒦ψ^p_A`, Gaussians times polynomials, uniformly
for `a = 1 + νs ∈ [1, 2.1]`, `ν ≤ 1`, `ε ≤ 1`, `s ≤ 1.1/ν`) is `≤ K (|A^y(s)| + |(s∂_s)A^y(s)|)`,
whenever `A^y` is differentiable at `s`. -/
def HAcCellBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν ε s : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∀ (χf : ℝ → ℝ) (A : ℝ → Mat3), DifferentiableAt ℝ (Ay ν χf A) s →
    ∫⁻ x, ENNReal.ofReal (‖hAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s)) ^ 2)

/-- Measurability of `hAcoef` (continuity on `s > 0`). -/
def HAcMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    AEStronglyMeasurable (hAcoef ν ε χf A) (srcMeasure (cOf ν))

theorem hhatCoefBound_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : HAcSupport χf) (h2 : AyBound as χf) (h2' : AyDerivBound as χf) (h3 : HAcCellBound)
    (h4 : HAcMeas as χf) (h5 : ChartL2Conv) (h6 : AyDiffAt as χf) : HhatCoefBound as χf := by
  obtain ⟨K, hK0, hK⟩ := h3
  refine ⟨K * 2 * (11 / 10) ^ 3, 3, by positivity, ?_⟩
  intro ν ε hν hν1 hε hε1 A hA
  have hM := affM_nonneg ν χf A
  set M := affM ν χf A with hMdef
  set T : ℝ := (11 / 10) / ν with hT
  have hT1 : 1 ≤ T := by
    rw [hT, le_div_iff₀ hν]; linarith
  set D : ℝ := K * M * 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖hAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
    intro s hs hsT
    have hB := h2 hχ ν hν A hA s hs hsT
    have hC := h2' hχ ν hν A hA s hs hsT
    have hc := hK ν ε s hν hν1 hε hε1 hs hsT χf A (h6 ν A hA s hs)
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs52 : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
    have hsum : frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) ≤ s ^ (5 / 2 : ℝ) * M * 2 := by
      linarith
    have h0 : 0 ≤ frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ h0 hsum 2
    have : D ^ 2 * s ^ 5 = K ^ 2 * (s ^ (5 / 2 : ℝ) * M * 2) ^ 2 := by
      rw [hD]; simp only [mul_pow, hs52]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  obtain ⟨hm, hn⟩ := h5 (cOf ν) T D (hAcoef ν ε χf A) hc0 hT1 hD0 (h4 hχ ν ε hν A hA)
    (fun s hs x => h1 hχ ν ε hν A s hs x) hcell
  refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hT3 : T ^ 3 = (11 / 10) ^ 3 * ν⁻¹ ^ 3 := by
    rw [hT, div_eq_mul_inv, mul_pow]
  refine le_of_eq ?_
  calc D * T ^ 3 = K * 2 * T ^ 3 * M := by rw [hD]; ring
    _ = K * 2 * (11 / 10) ^ 3 * ν⁻¹ ^ 3 * M := by rw [hT3]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
