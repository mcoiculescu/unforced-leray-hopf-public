import UnforcedLeray.Blueprint.Construction.Gain
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theorem B3: the smallness condition of (2.43) along the phase-locked sequence

`paper/main.tex`, `background:eq:2.43` (lines 5714–5724, unit B0685) and the parameter choice
`lem:late-stress-3-10` (lines 10688–10716, unit B0725), as used at the completion
(lines 13714–13718: "with `ν = ν_n`, `c = ν⁻²`, `R = ε⁻¹` and `P = 2εc`. The common choice
includes (2.41)–(2.43)").

**Manuscript.** With `δ = Pε^{3/11}`, `M = Pe^{m/ν}`, contraction holds if `4PM²δ < 1` and
`2m < 3d/11`; "the first follows for small `ν`" (lines 5719–5724). Lemma 3-10 runs this with
`c = ν⁻²`, `d₀ = γ/3` and `ε = C_*ν^r e^{-d₀/ν}` (line 10692), which is exactly the
construction's `ε_n = (e^{-γ/ν_n}ν_n^{Re κ - 5 - 2σ₀}/(2|C₀|))^{1/3}`
(`ConstructionData.amplitude`, `eq:st18-t00764`): `C_* = (2|C₀|)^{-1/3}`,
`r = (Re κ - 5 - 2σ₀)/3`. The condition `2m < 3d₀/11` reads `22m < γ`.

**Lean form.** A `Budget` is the triple `(C, k, m)`: every polynomial `P_ν = P(c, ν⁻¹)` of
the proof, at `c = ν⁻²` and `ν ≤ 1`, is at most `Cν^{-k}` ("a polynomial `P_ν` has degree
fixed by the budget", line 5076), and `m = m_bg` is the inverse-loss margin. Then
`M = Cν^{-k}e^{m/ν}` (`Budget.loss`), `δ = Cν^{-k}ε^{3/11}` (`Budget.residual`) and the
quantity of (2.43) is `4PM²δ` (`Budget.smallness`).

* `Budget.smallness_eq`: at `ε = (e^{-γ/ν}ν^r/D)^{1/3}`,
  `4PM²δ = (4C⁴/D^{1/11}) x^{4k - r/11} e^{-(γ/11 - 2m)x}` with `x = 1/ν`.
* `eventually_smallness`: along any sequence `ν_n ↓ 0` (`ν_n > 0`, `ν_n → 0`), with
  `C₀ ≠ 0` and `22m < γ`, `4PM²δ < 1` for all large `n` (this is the first inequality of
  (2.43) "for small `ν`").
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint

/-- The polynomial loss budget of Theorem B3 (lines 5075–5078): every polynomial
`P_ν = P(c, ν⁻¹)` is at most `Cν^{-k}`, and `m = m_bg` is the inverse-loss margin of (2.6),
(2.31), (2.41). -/
structure Budget where
  /-- The constant of the polynomial majorant. -/
  C : ℝ
  /-- The degree of the polynomial majorant in `ν⁻¹`. -/
  k : ℕ
  /-- The inverse-loss margin `m_bg`. -/
  m : ℝ

namespace Budget

variable (B : Budget)

/-- `P_ν ≤ Cν^{-k}`. -/
def poly (ν : ℝ) : ℝ := B.C * (ν ^ B.k)⁻¹

/-- `M = P_νe^{m/ν}`, the loss of the augmented inverse (2.31). -/
def loss (ν : ℝ) : ℝ := B.poly ν * Real.exp (B.m / ν)

/-- `δ = P_νε^{3/11}`, the raw residual bound (2.15). -/
def residual (ν ε : ℝ) : ℝ := B.poly ν * ε ^ (3 / 11 : ℝ)

/-- The contraction radius `2Mδ` (line 5721). -/
def radius (ν ε : ℝ) : ℝ := 2 * B.loss ν * B.residual ν ε

/-- The quantity `4PM²δ` of (2.43). -/
def smallness (ν ε : ℝ) : ℝ := 4 * B.poly ν * B.loss ν ^ 2 * B.residual ν ε

/-- The closed form of `4PM²δ` at `ε = (e^{-γ/ν}ν^r/D)^{1/3}`, in `x = 1/ν`. -/
theorem smallness_eq {γ r D ν : ℝ} (hν : 0 < ν) (hD : 0 < D) :
    B.smallness ν ((Real.exp (-(γ / ν)) * ν ^ r / D) ^ (1 / 3 : ℝ)) =
      4 * B.C ^ 4 / D ^ (1 / 11 : ℝ) *
        (ν⁻¹ ^ ((4 * B.k : ℝ) - r / 11) * Real.exp (-(γ / 11 - 2 * B.m) * ν⁻¹)) := by
  set x : ℝ := ν⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr hν
  have hX0 : 0 ≤ Real.exp (-(γ / ν)) * ν ^ r / D := by positivity
  have h1 : ((Real.exp (-(γ / ν)) * ν ^ r / D) ^ (1 / 3 : ℝ)) ^ (3 / 11 : ℝ) =
      (Real.exp (-(γ / ν)) * ν ^ r / D) ^ (1 / 11 : ℝ) := by
    rw [← Real.rpow_mul hX0]
    norm_num
  have hνr : ν ^ (r * (1 / 11)) = x ^ (-(r / 11)) := by
    rw [hx, Real.inv_rpow hν.le, Real.rpow_neg hν.le, inv_inv]
    ring_nf
  have he : -(γ / ν) * (1 / 11) = -(γ / 11) * x := by
    rw [hx]; field_simp
  have h2 : (Real.exp (-(γ / ν)) * ν ^ r / D) ^ (1 / 11 : ℝ) =
      Real.exp (-(γ / 11) * x) * x ^ (-(r / 11)) / D ^ (1 / 11 : ℝ) := by
    rw [Real.div_rpow (by positivity) hD.le,
      Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hν.le _), ← Real.exp_mul,
      ← Real.rpow_mul hν.le, he, hνr]
  have hk : (ν ^ B.k)⁻¹ = x ^ B.k := by rw [hx, inv_pow]
  have hm : Real.exp (B.m / ν) = Real.exp (B.m * x) := by rw [hx, div_eq_mul_inv]
  have hpow : x ^ ((4 * B.k : ℝ) - r / 11) = (x ^ B.k) ^ 4 * x ^ (-(r / 11)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, ← pow_mul,
      show (4 * B.k : ℝ) = ((B.k * 4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hexp : Real.exp (-(γ / 11 - 2 * B.m) * x) =
      Real.exp (-(γ / 11) * x) * (Real.exp (B.m * x) * Real.exp (B.m * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hD' : 0 < D ^ (1 / 11 : ℝ) := Real.rpow_pos_of_pos hD _
  simp only [smallness, poly, loss, residual]
  rw [h1, h2, hk, hm, hpow, hexp]
  field_simp

end Budget

/-- **The smallness of (2.43) along the sequence** (lines 5719–5724, unit B0685; lines
10688–10716, unit B0725): for a record whose viscosities are positive and tend to `0`, with
`C₀ ≠ 0`, and a budget with `22m < γ` (the second inequality `2m < 3d₀/11` of (2.43) at
`d₀ = γ/3`), `4PM²δ < 1` at `(ν_n, ε_n)` for all large `n`. -/
theorem eventually_smallness (F : ConstructionData) (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) (B : Budget) (hm : 22 * B.m < F.growth) :
    ∀ᶠ n in atTop, B.smallness (F.ν n) (F.amplitude n) < 1 := by
  set D : ℝ := 2 * ‖F.C₀‖ with hD
  have hD0 : 0 < D := by have := norm_pos_iff.mpr hC; positivity
  set r : ℝ := F.κ.re - 5 - 2 * F.σ₀ with hr
  set b : ℝ := F.growth / 11 - 2 * B.m with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set s : ℝ := (4 * B.k : ℝ) - r / 11 with hs
  set K : ℝ := 4 * B.C ^ 4 / D ^ (1 / 11 : ℝ) with hK
  have heq : ∀ n, B.smallness (F.ν n) (F.amplitude n) =
      K * ((F.ν n)⁻¹ ^ s * Real.exp (-b * (F.ν n)⁻¹)) := fun n => by
    have := B.smallness_eq (γ := F.growth) (r := r) (hν n) hD0
    simpa only [ConstructionData.amplitude, hr, hD, hK, hs, hb] using this
  have hinv : Tendsto (fun n => (F.ν n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hν0, Eventually.of_forall hν⟩)
  have hlim : Tendsto (fun n => B.smallness (F.ν n) (F.amplitude n)) atTop (𝓝 0) := by
    rw [show (fun n => B.smallness (F.ν n) (F.amplitude n)) =
      fun n => K * ((F.ν n)⁻¹ ^ s * Real.exp (-b * (F.ν n)⁻¹)) from funext heq]
    have h3 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb0).comp hinv).const_mul K
    rw [mul_zero] at h3
    exact h3
  exact hlim.eventually (gt_mem_nhds one_pos)

end UnforcedLeray.Cons.C03
