import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5` (`RqPolyAt`): decomposition

Source of record: `the November 2 reference manuscript`
lines 2349-2352 (planar eigenstream: `R q = -¼ (r⁻² ∫₀^r s³ q + r² ∫_r^∞ s⁻¹ q)` is polynomially
bounded together with the derivatives allowed by the Gaussian bounds on `q`).

`greenInverse q = -¼ (r⁻² A + r² B)` with `A r = ∫₀^r s³ q`, `B r = ∫_r^∞ s⁻¹ q`.  The
derivatives of `A`, `B` are `r³ q`, `-r⁻¹ q`, so only the Leibniz bookkeeping and the tail
estimates are needed; `rqPolyAt_of` assembles `RqPolyAt` from the leaves below.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- Leibniz bound: product of two smooth functions on `(0,∞)` with polynomially bounded
derivatives of orders `< n` has polynomially bounded derivatives of orders `< n`
(`iteratedDeriv` Leibniz sum over `Nat.choose`, products of `C r^N` bounds). -/
def PolyMulPoly : Prop :=
  ∀ (f g : ℝ → ℂ) (n : ℕ), ContDiffOn ℝ ∞ f (Ioi 0) → ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j < n, PolyAt f j) → (∀ j < n, PolyAt g j) →
      ∀ j < n, PolyAt (fun r => f r * g r) j

/-- Linear combinations of polynomially bounded functions. -/
def PolyLin : Prop :=
  ∀ (a b : ℂ) (f g : ℝ → ℂ) (n : ℕ), ContDiffOn ℝ ∞ f (Ioi 0) → ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j < n, PolyAt f j) → (∀ j < n, PolyAt g j) →
      ∀ j < n, PolyAt (fun r => a * f r + b * g r) j

/-- `A r = ∫₀^r s³ q` has polynomially bounded derivatives of order `≤ j` when the derivatives of
`q` of orders `< j` are Gaussian bounded.  Order `0`: `|A| ≤ ∫₀^∞ s³|q| < ∞` (`xGInt`,
Cauchy-Schwarz / AM-GM with the `X_G` weight).  Order `i ≥ 1`: `A^{(i)} = (r³ q)^{(i-1)}` is a
finite sum of `r^k q^{(m)}`, `m ≤ i-1`, bounded by `r^N` times a Gaussian (`iteratedDeriv`
Leibniz on `r³ q`, `HasDerivAt A (r³ q r) r` by `intervalIntegral.integral_hasDerivAt_right`). -/
def PolyIntA : Prop :=
  ∀ (q : Planar.Profile), Planar.MemXG q → ContDiffOn ℝ ∞ q (Ioi 0) → ∀ j : ℕ,
    (∀ i < j, GaussAt q i) →
      ∀ i ≤ j, PolyAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) i

/-- `B r = ∫_r^∞ s⁻¹ q` has polynomially bounded derivatives of order `≤ j` when the derivatives
of `q` of orders `< j` are Gaussian bounded.  Order `0`: `|B r| ≤ ∫_1^∞ s⁻¹|q| < ∞` for `r ≥ 1`
(`xGInt`).  Order `i ≥ 1`: `B^{(i)} = -(r⁻¹ q)^{(i-1)}` (`B' = -r⁻¹ q`, Ioi split at a fixed base
point). -/
def PolyIntB : Prop :=
  ∀ (q : Planar.Profile), Planar.MemXG q → ContDiffOn ℝ ∞ q (Ioi 0) → ∀ j : ℕ,
    (∀ i < j, GaussAt q i) →
      ∀ i ≤ j, PolyAt (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) i

/-- **`RqPolyAt` from the leaves.** -/
theorem rqPolyAt_of (hZ : PolyZpow) (hM : PolyMulPoly) (hL : PolyLin) (hSA : SmoothA)
    (hSB : SmoothB) (hPA : PolyIntA) (hPB : PolyIntB) : RqPolyAt := by
  intro lam q hq j hj
  have hA : ∀ i < j + 1, PolyAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) i :=
    fun i hi => hPA q hq.memXG hq.smooth j hj i (by omega)
  have hB : ∀ i < j + 1, PolyAt (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) i :=
    fun i hi => hPB q hq.memXG hq.smooth j hj i (by omega)
  have hAs := hSA q hq.memXG hq.smooth
  have hBs := hSB q hq.memXG hq.smooth
  have h1 := hM (fun r : ℝ => (r : ℂ) ^ (-2 : ℤ))
    (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) (j + 1) (hZ (-2)).1 hAs
    (fun i _ => (hZ (-2)).2 i) hA
  have h2 := hM (fun r : ℝ => (r : ℂ) ^ (2 : ℤ))
    (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) (j + 1) (hZ 2).1 hBs
    (fun i _ => (hZ 2).2 i) hB
  have h3 := hL (-(1 / 4 : ℂ)) (-(1 / 4 : ℂ))
    (fun r : ℝ => (r : ℂ) ^ (-2 : ℤ) * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s)
    (fun r : ℝ => (r : ℂ) ^ (2 : ℤ) * ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) (j + 1)
    ((hZ (-2)).1.mul hAs) ((hZ 2).1.mul hBs) h1 h2 j (by omega)
  obtain ⟨C, N, hb⟩ := h3
  refine ⟨C, N, fun r hr => ?_⟩
  have heq : Planar.greenInverse q =ᶠ[𝓝 r] fun s : ℝ =>
      -(1 / 4 : ℂ) * ((s : ℂ) ^ (-2 : ℤ) * ∫ s in (0 : ℝ)..s, (s : ℂ) ^ 3 * q s) +
        -(1 / 4 : ℂ) * ((s : ℂ) ^ (2 : ℤ) * ∫ s in Ioi s, (s : ℂ)⁻¹ * q s) := by
    filter_upwards with s
    simp only [Planar.greenInverse, zpow_neg, zpow_ofNat]
    ring
  rw [heq.iteratedDeriv_eq]
  exact hb r hr

end UnforcedLeray.Short.IIb
