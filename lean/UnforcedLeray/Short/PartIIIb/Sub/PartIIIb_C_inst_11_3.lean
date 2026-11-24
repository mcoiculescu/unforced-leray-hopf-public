import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11

/-!
# `PartIII-b:C/inst/11/3`: `HAcCellBound` from four Gaussian-lattice leaves

Source `the November 2 reference manuscript`:
`ĥ_A` 4979-4980 (`ĥ_A = √s [(h^p)_r e_r + ((h^p)_z + ε(1-𝒦)ψ^p) e_z]`, `𝒦 = η∂_η + 2s∂_s`),
lattice sums 4973-4975, 4978 (Gaussian decay), size 5009-5016, 5063-5079.

With the matrix `C = A^y(s)` frozen the three lattice sums `h^p`, `ψ^p`, `𝒦ψ^p` are
`hpAC`, `psipAC`, `KopC` (the last also depends on `D = (s∂_s)A^y(s)`).  Leaves:
`HAcPieceHp`, `HAcPiecePsi`, `HAcPieceKop` (Gaussian cell bounds, uniform in `a = 1+νs ∈ [1,2.1]`,
`c = ν⁻² ≥ 1`) and `HAcKopEq` (the `s`-derivative of the lattice sum at one differentiability point
of `A^y`).  Proved here: `hAcCellBound_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `h^p_A` with the matrix `A^y(s)` replaced by a constant matrix `C` (source 4973). -/
def hpAC (ν s : ℝ) (C : Mat3) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑' j : ℤ,
    (merApply C (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply C (xj ν j x)))

/-- `ψ^p_A` with `A^y(s)` replaced by a constant matrix `C` (source 4974-4975). -/
def psipAC (ν s : ℝ) (C : Mat3) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ,
    (merTrace C * psij ν s j x - fderiv ℝ (psij ν s j) x (merApply C (xj ν j x)))

/-- `𝒦ψ^p = η∂_η ψ^p + 2 s ∂_s ψ^p` for `ψ^p(s) = psipAC ν s (C(s))` with `C(s)` the frozen
value `C` and `D = (s∂_s)C`: `2s∂_s ψ^p = 2 s ∂_t psipAC ν t C |_{t=s} + 2 psipAC ν s D`. -/
def KopC (ν s : ℝ) (C D : Mat3) (x : ℝ × ℝ) : ℝ :=
  x.2 * fderiv ℝ (psipAC ν s C) x (ei 1) +
    2 * (s * deriv (fun t => psipAC ν t C x) s + psipAC ν s D x)

theorem hpA_eq_hpAC (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hpA ν χ A s x = hpAC ν s (Ay ν χ A s) x := rfl

theorem psipA_eq_psipAC (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    psipA ν χ A s x = psipAC ν s (Ay ν χ A s) x := rfl

/-- Leaf 1 (source 4973, 5063-5079): Gaussian cell bound for `h^p` (lattice sum of Gaussians times
polynomials in `x_j`, linear in `C`; Cauchy-Schwarz over `j` with Gaussian weights, one Gaussian
integral; uniform for `a ∈ [1, 2.1]`, `c = ν⁻² ≥ 1`). -/
def HAcPieceHp : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ C : Mat3,
    Measurable (hpAC ν s C) ∧
    ∫⁻ x, ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob C) ^ 2)

/-- Leaf 2 (source 4974-4975, 5063-5079): Gaussian cell bound for `ψ^p`. -/
def HAcPiecePsi : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ C : Mat3,
    Measurable (psipAC ν s C) ∧
    ∫⁻ x, ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob C) ^ 2)

/-- Leaf 3 (source 4979-4980, 5063-5079): Gaussian cell bound for `𝒦ψ^p` (`η∂_η` of the lattice
sum, `s ∂_s` of the Gaussian weights `ψ_j`, `a = 1+νs`, `2 s ν ≤ 2.2`, and the `D`-term). -/
def HAcPieceKop : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ C D : Mat3,
    Measurable (KopC ν s C D) ∧
    ∫⁻ x, ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob C + frob D) ^ 2)

/-- Leaf 4 (source 4978, 4741-4745): if `C` is differentiable at `s > 0` then
`ψ^p(s') = psipAC ν s' (C s')` has `𝒦ψ^p = KopC ν s (C s) (s C'(s))`.  (Linearity of `psipAC` in
the matrix, via `psipA_eq_phi`/`psiPhi` and `HpPsiTermSummable`; differentiability of
`t ↦ psipAC ν t M x` for a constant matrix `M` as in `PsipADiff/SPart.lean`, so that only
differentiability of `C` at the single point `s` is needed.) -/
def HAcKopEq : Prop :=
  ∀ (ν s : ℝ), 0 < ν → 0 < s → ∀ C : ℝ → Mat3, DifferentiableAt ℝ C s → ∀ x : ℝ × ℝ,
    Kop (fun s' y => psipAC ν s' (C s') y) s x = KopC ν s (C s) (sDeriv C s) x

theorem hA_pt (a b ε ψ κ n : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : a ^ 2 ≤ n ^ 2)
    (hb : b ^ 2 ≤ n ^ 2) :
    a ^ 2 + (b + ε * (ψ - κ)) ^ 2 ≤ 6 * (n ^ 2 + ψ ^ 2 + κ ^ 2) := by
  have h1 : (ε * ψ) ^ 2 ≤ ψ ^ 2 := by nlinarith [sq_nonneg ψ, mul_nonneg hε0 (sub_nonneg.2 hε1)]
  have h2 : (ε * κ) ^ 2 ≤ κ ^ 2 := by nlinarith [sq_nonneg κ, mul_nonneg hε0 (sub_nonneg.2 hε1)]
  have h3 : (b + ε * ψ - ε * κ) ^ 2 ≤ 3 * (b ^ 2 + (ε * ψ) ^ 2 + (ε * κ) ^ 2) := by
    nlinarith [sq_nonneg (b - ε * ψ), sq_nonneg (b + ε * κ), sq_nonneg (ε * ψ + ε * κ)]
  have : b + ε * (ψ - κ) = b + ε * ψ - ε * κ := by ring
  rw [this]
  nlinarith [sq_nonneg n]

theorem hAcoef_norm_sq (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) :
    ‖hAcoef ν ε χf A (s, x)‖ ^ 2 =
      (hpA ν χf A s x).1 ^ 2 + ((hpA ν χf A s x).2 + ε * (psipA ν χf A s x -
        Kop (fun s' y => psipA ν χf A s' y) s x)) ^ 2 := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  unfold hAcoef hhatA
  simp only [smul_smul, inv_mul_cancel₀ hsq, one_smul]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [merOf, emb]

theorem hAcCellBound_of (h1 : HAcPieceHp) (h2 : HAcPiecePsi) (h3 : HAcPieceKop)
    (h4 : HAcKopEq) : HAcCellBound := by
  obtain ⟨K1, hK1, H1⟩ := h1
  obtain ⟨K2, hK2, H2⟩ := h2
  obtain ⟨K3, hK3, H3⟩ := h3
  refine ⟨6 * (K1 + K2 + K3), by positivity, ?_⟩
  intro ν ε s hν hν1 hε hε1 hs hsT χf A hd
  set C := Ay ν χf A s with hC
  set D := sDeriv (Ay ν χf A) s with hD
  obtain ⟨m1, i1⟩ := H1 ν s hν hν1 hs hsT C
  obtain ⟨m2, i2⟩ := H2 ν s hν hν1 hs hsT C
  obtain ⟨m3, i3⟩ := H3 ν s hν hν1 hs hsT C D
  have hK : ∀ x, Kop (fun s' y => psipA ν χf A s' y) s x = KopC ν s C D x :=
    fun x => h4 ν s hν hs (Ay ν χf A) hd x
  have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖hAcoef ν ε χf A (s, x)‖ ^ 2) ≤
      ENNReal.ofReal 6 * (ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2) +
        ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2) + ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2)) := by
    intro x
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hAcoef_norm_sq ν ε χf A s hs x, hK x]
    have e1 : (hpA ν χf A s x).1 ^ 2 ≤ ‖hpAC ν s C x‖ ^ 2 := by
      have := norm_fst_le (hpAC ν s C x)
      have h0 := abs_nonneg (hpAC ν s C x).1
      rw [← sq_abs]
      exact pow_le_pow_left₀ h0 (by simpa [Real.norm_eq_abs] using this) 2
    have e2 : (hpA ν χf A s x).2 ^ 2 ≤ ‖hpAC ν s C x‖ ^ 2 := by
      have := norm_snd_le (hpAC ν s C x)
      have h0 := abs_nonneg (hpAC ν s C x).2
      rw [← sq_abs]
      exact pow_le_pow_left₀ h0 (by simpa [Real.norm_eq_abs] using this) 2
    have := hA_pt (hpA ν χf A s x).1 (hpA ν χf A s x).2 ε (psipA ν χf A s x)
      (KopC ν s C D x) ‖hpAC ν s C x‖ hε.le hε1 e1 e2
    simpa [Real.norm_eq_abs, sq_abs, hpA_eq_hpAC, psipA_eq_psipAC] using this
  have hmeas1 : Measurable (fun x => ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((m1.norm).pow_const 2)
  have hmeas2 : Measurable (fun x => ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((m2.norm).pow_const 2)
  have hm12 : Measurable (fun x => ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2) +
      ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2)) := hmeas1.add hmeas2
  calc ∫⁻ x, ENNReal.ofReal (‖hAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal 6 * (ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2) +
        ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2) + ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_mono hpt
    _ = ENNReal.ofReal 6 * (∫⁻ x, ENNReal.ofReal (‖hpAC ν s C x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        + ∫⁻ x, ENNReal.ofReal (‖psipAC ν s C x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        + ∫⁻ x, ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left hm12, lintegral_add_left hmeas1]
    _ ≤ ENNReal.ofReal 6 * (ENNReal.ofReal (K1 ^ 2 * (frob C) ^ 2) +
        ENNReal.ofReal (K2 ^ 2 * (frob C) ^ 2) +
        ENNReal.ofReal (K3 ^ 2 * (frob C + frob D) ^ 2)) := by
        gcongr
    _ ≤ ENNReal.ofReal ((6 * (K1 + K2 + K3)) ^ 2 * (frob C + frob D) ^ 2) := by
        have hf : 0 ≤ frob C := Real.sqrt_nonneg _
        have hd0 : 0 ≤ frob D := Real.sqrt_nonneg _
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hfd : frob C ≤ frob C + frob D := by linarith
        have a1 : (frob C) ^ 2 ≤ (frob C + frob D) ^ 2 := pow_le_pow_left₀ hf hfd 2
        have a2 : K1 ^ 2 * (frob C) ^ 2 ≤ K1 ^ 2 * (frob C + frob D) ^ 2 :=
          mul_le_mul_of_nonneg_left a1 (sq_nonneg _)
        have a3 : K2 ^ 2 * (frob C) ^ 2 ≤ K2 ^ 2 * (frob C + frob D) ^ 2 :=
          mul_le_mul_of_nonneg_left a1 (sq_nonneg _)
        have a4 : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 ≤ (K1 + K2 + K3) ^ 2 := by
          nlinarith [mul_nonneg hK1 hK2, mul_nonneg hK1 hK3, mul_nonneg hK2 hK3]
        have a5 := mul_le_mul_of_nonneg_right a4 (sq_nonneg (frob C + frob D))
        nlinarith [a2, a3, a5, sq_nonneg (frob C + frob D)]

end UnforcedLeray.Short.PartIIIb.Concrete

end
