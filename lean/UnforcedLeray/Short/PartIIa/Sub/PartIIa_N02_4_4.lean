import Mathlib.Analysis.Real.Pi.Bounds
import UnforcedLeray.Short.PartIIa.Sub.N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/4` (`NzFinPotentials`): decomposition into mode-sum lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1727 (per-mode
flat Hodge potentials; the inverse `q`-derivative costs `c/(2π)`) and 1744-1745 (finite Fourier sums).

For a finite family `g : ℤ → ℝ × ℝ → E` the *mode sum* is
`nzModeSum c M g (s, q, η) = Σ_{n ∈ M} e^{2π i n q / c} g_n(s, η)`.
The finite-mode potentials are the mode sums of the per-mode solutions `(φ_n, ψ_n)` of `NzModeSolve`;
the Props below are the generic facts about mode sums (structure, derivatives, Parseval over
`measureH c`) plus one abstract real-analysis inequality (`NzFpFamilyBound`).  `nzFinPotentials_of`
assembles `NzFinPotentials` from them, `NzModeSolve` and `NzModeBounds`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The `q`-frequency `k_n = 2π n / c`. -/
def nzk (c : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / c

/-- Finite mode sum `Σ_{n ∈ M} e^{2π i n q / c} g_n(s, η)` (lines 1744-1745). -/
def nzModeSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℝ) (M : Finset ℤ)
    (g : ℤ → ℝ × ℝ → E) : Profile → E := fun p =>
  ∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ)) •
    g n (p.1, p.2.2)

/-- One-mode coefficient: smooth, `s`-band supported, with `g` and `s ∂_s g` decaying exponentially in
`η` (uniformly in `s`). -/
def NzDecay1 (g : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ g ∧ (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, g x ≠ 0 → x.1 ∈ Icc s0 s1) ∧
    ∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ, ‖g x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ g x (1, 0)‖ ≤ C * Real.exp (-κ * |x.2|)

/-- Mode sums of smooth coefficients are smooth and `c`-periodic in `q` (`e^{2π i n (q + c)/c} =
e^{2π i n q / c}`). -/
def NzFpSmoothPer : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ), (∀ n ∈ M, ContDiff ℝ ∞ (g n)) →
    ContDiff ℝ ∞ (nzModeSum c M g) ∧ QPeriodic c (nzModeSum c M g)

/-- Joint `s`-band of two finite mode sums: finitely many bands have a common hull (the empty family
is `0`). -/
def NzFpBand : Prop :=
  ∀ (c : ℝ) (M : Finset ℤ) (φ ψ : ℤ → ℝ × ℝ → ℂ),
    (∀ n ∈ M, ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, φ n x ≠ 0 → x.1 ∈ Icc s0 s1) →
    (∀ n ∈ M, ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, ψ n x ≠ 0 → x.1 ∈ Icc s0 s1) →
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile,
      (nzModeSum c M φ p ≠ 0 ∨ nzModeSum c M ψ p ≠ 0) → p.1 ∈ Icc s0 s1

/-- `∂_q` and `∂_η` of a mode sum: `∂_q e^{2π i n q/c} = i k_n e^{...}`, `∂_η` acts on the coefficient. -/
def NzFpDeriv : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ), (∀ n ∈ M, ContDiff ℝ ∞ (g n)) →
    pdQ (nzModeSum c M g) =
        nzModeSum c M (fun n x => Complex.I * ((nzk c n : ℂ) * g n x)) ∧
      pdEta (nzModeSum c M g) = nzModeSum c M (fun n x => fderiv ℝ (g n) x (0, 1))

/-- A mode sum of `NzDecay2` coefficients decays exponentially in `η` together with `∂_q`, `∂_η`
(`κ = min κ_n`, constant `Σ C_n (1 + |k_n|)`). -/
def NzFpExpDecay : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (φ : ℤ → ℝ × ℝ → ℂ), (∀ n ∈ M, NzDecay2 (φ n)) →
    NzExpDecay (nzModeSum c M φ)

/-- The mode sums of the per-mode solutions give `f = ∇ φ + stream ψ` pointwise: on each mode
`i k φ_n - ∂_η ψ_n = a_{n,0}`, `∂_η φ_n + i k ψ_n = a_{n,1}`
(`cgradC 0 φ = (∂_q φ, ∂_η φ)`, `streamC 0 ψ = (-∂_η ψ, ∂_q ψ)`). -/
def NzFpIdentity : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (a : ℤ → ℝ × ℝ → MeridC) (φ ψ : ℤ → ℝ × ℝ → ℂ),
    (∀ n ∈ M, ContDiff ℝ ∞ (φ n) ∧ ContDiff ℝ ∞ (ψ n)) →
    (∀ n ∈ M, NzModeEq (nzk c n) (fun x => a n x 0) (fun x => a n x 1) (φ n) (ψ n)) →
    ∀ p : Profile, nzModeSum c M a p =
      cgradC 0 (nzModeSum c M φ) p + streamC 0 (nzModeSum c M ψ) p

/-- Decay of the three coefficient families used: from `NzDecay2 φ` (derivatives of order `≤ 2`
decay), `φ`, `∂_η φ` and `i k φ` satisfy `NzDecay1` (the `s`-band of `∂_η φ` is that of `φ`). -/
def NzFpDecay1 : Prop :=
  ∀ (k : ℝ) (φ : ℝ × ℝ → ℂ), NzDecay2 φ →
    NzDecay1 φ ∧ NzDecay1 (fun x => fderiv ℝ φ x (0, 1)) ∧
      NzDecay1 (fun x => Complex.I * ((k : ℂ) * φ x))

/-- **Parseval for a scalar mode sum on `measureH c`** (`measureH c` is `s^{-3/2} ds dq dη` on the cell
`(0, c]` in `q`, unnormalised): `S` commutes with the finite sum, `∫_0^c` kills the cross terms
(`∫_0^c e^{2π i (n - m) q/c} dq = c δ_{nm}`), so
`‖η^j S^α Σ e_n g_n‖²_{L²(measureH c)} = c Σ_n nzMom2 j α g_n ^ 2`, with integrability from the
exponential decay and the `s`-band. -/
def NzFpParseval : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (g : ℤ → ℝ × ℝ → ℂ), (∀ n ∈ M, NzDecay1 (g n)) →
    nzFin c (nzModeSum c M g) ∧
      ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
        nzSq c α j (nzModeSum c M g) = c * ∑ n ∈ M, nzMom2 j α (g n) ^ 2

/-- **Parseval for a `ℂ²`-valued finite-mode test** (band and compact `η`-support, so everything is
integrable): `nzSq c α i f = c Σ_n (nzMom2 i α a_{n,0}² + nzMom2 i α a_{n,1}²)`. -/
def NzFpParsevalMerid : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (a : ℤ → ℝ × ℝ → MeridC),
    (∀ n ∈ M, ContDiff ℝ ∞ (a n) ∧ ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ x : ℝ × ℝ, a n x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L) →
    ∀ α ∈ Finset.range 2, ∀ i ∈ Finset.range 2,
      nzSq c α i (nzModeSum c M a) =
        c * ∑ n ∈ M, (nzMom2 i α (fun x => a n x 0) ^ 2 + nzMom2 i α (fun x => a n x 1) ^ 2)

/-- Components of a smooth band-supported `ℂ²`-valued coefficient are smooth and `NzBand2`. -/
def NzFpComp : Prop :=
  ∀ (a : ℝ × ℝ → MeridC), ContDiff ℝ ∞ a →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, a x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L) →
    ContDiff ℝ ∞ (fun x => a x 0) ∧ ContDiff ℝ ∞ (fun x => a x 1) ∧
      NzBand2 (fun x => a x 0) ∧ NzBand2 (fun x => a x 1)

/-- Multiplying by `i` does not change the moments `nzMom2` (`S` is `ℂ`-linear). -/
def NzFpMomI : Prop :=
  ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ ∞ h → ∀ j α : ℕ,
    nzMom2 j α (fun x => Complex.I * h x) = nzMom2 j α h

/-- **Abstract family bound** (Minkowski over the finitely many modes; pure real analysis).
Given the Parseval identities for the family `g` and for `f = Σ e_n a_n`, and per-mode bounds
`nzMom2 j α g_n ≤ K Σ_i (nzMom2 i α a_{n,0} + nzMom2 i α a_{n,1})`, one has
`nzMomSum c (Σ e_n g_n) ≤ 2 √2 K nzMomSum c f`: with `x_n = nzMom2 j α g_n`, `y_{n,i} = u + v`,
`(Σ_n x_n²)^{1/2} ≤ K Σ_i (Σ_n y_{n,i}²)^{1/2}` (Minkowski), `y² ≤ 2(u² + v²)`, and
`(c Σ_n (u² + v²))^{1/2} = (nzSq c α i f)^{1/2}`; the constant does not depend on `|M|`. -/
def NzFpFamilyBound : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (M : Finset ℤ) (a : ℤ → ℝ × ℝ → MeridC) (g : ℤ → ℝ × ℝ → ℂ) (K : ℝ),
    0 ≤ K →
    (∀ n ∈ M, ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
      nzMom2 j α (g n) ≤ K * ∑ i ∈ Finset.range 2,
        (nzMom2 i α (fun x => a n x 0) + nzMom2 i α (fun x => a n x 1))) →
    (∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
      nzSq c α j (nzModeSum c M g) = c * ∑ n ∈ M, nzMom2 j α (g n) ^ 2) →
    (∀ α ∈ Finset.range 2, ∀ i ∈ Finset.range 2,
      nzSq c α i (nzModeSum c M a) =
        c * ∑ n ∈ M, (nzMom2 i α (fun x => a n x 0) ^ 2 + nzMom2 i α (fun x => a n x 1) ^ 2)) →
    nzMomSum c (nzModeSum c M g) ≤ 2 * Real.sqrt 2 * K * nzMomSum c (nzModeSum c M a)

theorem nzMom2_nonneg (j α : ℕ) (g : ℝ × ℝ → ℂ) : 0 ≤ nzMom2 j α g := by
  unfold nzMom2
  refine Real.rpow_nonneg (setIntegral_nonneg (measurableSet_Ioi.prod MeasurableSet.univ) ?_) _
  intro x hx
  have : 0 < x.1 := hx.1
  positivity

/-- **`NzFinPotentials` from the mode-sum lemmas, `NzModeSolve` and `NzModeBounds`.** -/
theorem nzFinPotentials_of (h1 : NzFpSmoothPer) (h2 : NzFpBand) (h3 : NzFpDeriv)
    (h4 : NzFpExpDecay) (h5 : NzFpIdentity) (h6 : NzFpDecay1) (h7 : NzFpParseval)
    (h8 : NzFpParsevalMerid) (h9 : NzFpComp) (h10 : NzFpMomI) (h11 : NzFpFamilyBound)
    (hSolve : NzModeSolve) (hBounds : NzModeBounds) : NzFinPotentials := by
  obtain ⟨Cm, hCm0, hCm⟩ := hBounds
  refine ⟨2, 12 * Real.sqrt 2 * Cm, by positivity, ?_⟩
  intro c hc f hf hq hfin
  obtain ⟨M, a, h0M, hsm, hband, hfeq⟩ := hfin
  have hfe : f = nzModeSum c M a := funext hfeq
  subst hfe
  have hk0 : ∀ n ∈ M, nzk c n ≠ 0 := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (fun h : n = 0 => h0M (h ▸ hn))
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn0) hc.ne'
  have hex : ∀ n ∈ M, ∃ φ ψ : ℝ × ℝ → ℂ, NzDecay2 φ ∧ NzDecay2 ψ ∧
      NzModeEq (nzk c n) (fun x => a n x 0) (fun x => a n x 1) φ ψ := by
    intro n hn
    obtain ⟨c0, c1, b0, b1⟩ := h9 (a n) (hsm n hn) (hband n hn)
    obtain ⟨φ, ψ, hφ, hψ, he⟩ := hSolve (nzk c n) (hk0 n hn) _ _ c0 c1 b0 b1
    exact ⟨φ, ψ, hφ, hψ, he⟩
  choose! φ ψ hφ hψ heq using hex
  have hφs : ∀ n ∈ M, ContDiff ℝ ∞ (φ n) := fun n hn => (hφ n hn).1
  have hψs : ∀ n ∈ M, ContDiff ℝ ∞ (ψ n) := fun n hn => (hψ n hn).1
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Cm * (1 + c + c⁻¹) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hPA := h8 c hc M a (fun n hn => ⟨hsm n hn, hband n hn⟩)
  have key : ∀ g : ℤ → ℝ × ℝ → ℂ, (∀ n ∈ M, NzDecay1 (g n)) →
      (∀ n ∈ M, ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2, nzMom2 j α (g n) ≤
        K * ∑ i ∈ Finset.range 2,
          (nzMom2 i α (fun x => a n x 0) + nzMom2 i α (fun x => a n x 1))) →
      nzFin c (nzModeSum c M g) ∧
        nzMomSum c (nzModeSum c M g) ≤ 2 * Real.sqrt 2 * K * nzMomSum c (nzModeSum c M a) := by
    intro g hg hm
    obtain ⟨hF, hP⟩ := h7 c hc M g hg
    exact ⟨hF, h11 c hc M a g K hK0 hm hP hPA⟩
  have hmode : ∀ n ∈ M, ∀ α ∈ Finset.range 2, ∀ j ∈ Finset.range 2,
      ∀ g ∈ ({φ n, fun x => fderiv ℝ (φ n) x (0, 1), fun x => ((nzk c n : ℝ) : ℂ) * φ n x,
          ψ n, fun x => fderiv ℝ (ψ n) x (0, 1), fun x => ((nzk c n : ℝ) : ℂ) * ψ n x} :
          Set (ℝ × ℝ → ℂ)),
        nzMom2 j α g ≤ K * ∑ i ∈ Finset.range 2,
          (nzMom2 i α (fun x => a n x 0) + nzMom2 i α (fun x => a n x 1)) := by
    intro n hn α hα j hj g hg
    obtain ⟨c0, c1, b0, b1⟩ := h9 (a n) (hsm n hn) (hband n hn)
    have h := hCm (nzk c n) (hk0 n hn) (fun x => a n x 0) (fun x => a n x 1)
      (φ n) (ψ n) c0 c1 b0 b1 (hφ n hn) (hψ n hn) (heq n hn) α hα j hj g hg
    have hS0 : 0 ≤ ∑ i ∈ Finset.range 2,
        (nzMom2 i α (fun x => a n x 0) + nzMom2 i α (fun x => a n x 1)) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (nzMom2_nonneg _ _ _) (nzMom2_nonneg _ _ _))
    have hinv : |nzk c n|⁻¹ ≤ c := by
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hn0 : n ≠ 0 := fun h => h0M (h ▸ hn)
        exact_mod_cast Int.one_le_abs hn0
      have habs : |nzk c n| = 2 * Real.pi * |(n : ℝ)| / c := by
        unfold nzk
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos Real.pi_pos]
        norm_num
      rw [habs, inv_div, div_le_iff₀ (by positivity)]
      have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
      exact le_mul_of_one_le_right hc.le (by nlinarith [abs_nonneg (n : ℝ)])
    have hle : (1 + |nzk c n|⁻¹) ^ 2 ≤ (1 + c + c⁻¹) ^ 2 := by
      have : 0 ≤ |nzk c n|⁻¹ := by positivity
      have hc' : 0 < c⁻¹ := inv_pos.2 hc
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [hKdef]
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hCm0) hS0)
  have hdec : ∀ n ∈ M, NzDecay1 (φ n) ∧ NzDecay1 (fun x => fderiv ℝ (φ n) x (0, 1)) ∧
      NzDecay1 (fun x => Complex.I * (((nzk c n : ℝ) : ℂ) * φ n x)) :=
    fun n hn => h6 (nzk c n) (φ n) (hφ n hn)
  have hdecψ : ∀ n ∈ M, NzDecay1 (ψ n) ∧ NzDecay1 (fun x => fderiv ℝ (ψ n) x (0, 1)) ∧
      NzDecay1 (fun x => Complex.I * (((nzk c n : ℝ) : ℂ) * ψ n x)) :=
    fun n hn => h6 (nzk c n) (ψ n) (hψ n hn)
  have hI : ∀ (g : ℝ × ℝ → ℂ) (k : ℝ), ContDiff ℝ ∞ g → ∀ j α : ℕ,
      nzMom2 j α (fun x => Complex.I * (((k : ℝ) : ℂ) * g x)) =
        nzMom2 j α (fun x => ((k : ℝ) : ℂ) * g x) :=
    fun g k hg j α => h10 (fun x => ((k : ℝ) : ℂ) * g x) (contDiff_const.mul hg) j α
  obtain ⟨Fφ, Bφ⟩ := key φ (fun n hn => (hdec n hn).1)
    (fun n hn α hα j hj => hmode n hn α hα j hj _ (by simp))
  obtain ⟨FQφ, BQφ⟩ := key (fun n x => Complex.I * ((nzk c n : ℂ) * φ n x))
    (fun n hn => (hdec n hn).2.2)
    (fun n hn α hα j hj => by
      rw [hI (φ n) (nzk c n) (hφs n hn) j α]
      exact hmode n hn α hα j hj _ (by simp))
  obtain ⟨FEφ, BEφ⟩ := key (fun n x => fderiv ℝ (φ n) x (0, 1)) (fun n hn => (hdec n hn).2.1)
    (fun n hn α hα j hj => hmode n hn α hα j hj _ (by simp))
  obtain ⟨Fψ, Bψ⟩ := key ψ (fun n hn => (hdecψ n hn).1)
    (fun n hn α hα j hj => hmode n hn α hα j hj _ (by simp))
  obtain ⟨FQψ, BQψ⟩ := key (fun n x => Complex.I * ((nzk c n : ℂ) * ψ n x))
    (fun n hn => (hdecψ n hn).2.2)
    (fun n hn α hα j hj => by
      rw [hI (ψ n) (nzk c n) (hψs n hn) j α]
      exact hmode n hn α hα j hj _ (by simp))
  obtain ⟨FEψ, BEψ⟩ := key (fun n x => fderiv ℝ (ψ n) x (0, 1)) (fun n hn => (hdecψ n hn).2.1)
    (fun n hn α hα j hj => hmode n hn α hα j hj _ (by simp))
  obtain ⟨hQφ, hEφ⟩ := h3 c hc M φ hφs
  obtain ⟨hQψ, hEψ⟩ := h3 c hc M ψ hψs
  obtain ⟨hs1, hp1⟩ := h1 c hc M φ hφs
  obtain ⟨hs2, hp2⟩ := h1 c hc M ψ hψs
  refine ⟨nzModeSum c M φ, nzModeSum c M ψ, hs1, hs2, hp1, hp2,
    h2 c M φ ψ (fun n hn => (hφ n hn).2.1) (fun n hn => (hψ n hn).2.1),
    h5 c hc M a φ ψ (fun n hn => ⟨hφs n hn, hψs n hn⟩) heq,
    h4 c hc M φ hφ, h4 c hc M ψ hψ, Fφ, Fψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQφ]; exact FQφ
  · rw [hEφ]; exact FEφ
  · rw [hQψ]; exact FQψ
  · rw [hEψ]; exact FEψ
  · unfold nzPot
    rw [hQφ, hEφ, hQψ, hEψ]
    calc _ ≤ 6 * (2 * Real.sqrt 2 * K * nzMomSum c (nzModeSum c M a)) := by linarith
      _ = _ := by rw [hKdef]; ring

end UnforcedLeray.Short.PartIIa
