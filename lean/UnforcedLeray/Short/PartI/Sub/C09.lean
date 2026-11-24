import UnforcedLeray.Units.B0122

/-!
# Part I, task `PartI:C09`: global elliptic regularity of the Green inverse (conditional)

Source of record: `the November 2 reference manuscript`, lines 1134-1143 (the
paragraph "For completeness, conjugation by `G^{1/2}` turns `D` into a shifted harmonic
oscillator ..."): "The radial Green formula for `Δ₂⁻¹` first gives `‖Δ₂⁻¹ f‖₂ ≤ C‖f‖_{X_G}`;
elliptic regularity and boundedness of `G^{-1/2}∂^α k` then show `L : X_{G,j} → X_{G,j}` is
bounded."  The elliptic regularity step is `B0122.GreenEllipticRegularity j`: for
`u = Rf(r) e^{2iϑ}` on `ℝ²`, `‖u‖_{H^j} ≤ C_j (‖f‖_{H^{j-2}} + ‖f‖_{X_G})`.

## Route (why five lemmas)

1. `GreenWeakPunctured`: `Δ u = f(r)e^{2iϑ}` weakly on `ℝ² \ {0}` (radial ODE `Δ₂ R f = f`,
   `B0011.R_isGreenInverse`, polar Laplacian of an angular-two function, `B0013/PolarLaplacian`);
   split into the one-dimensional identity `RadialGreenIdentity` (Step 1a) and the polar
   reduction `PolarReduction` (Step 1b).
2. `RemovableOrigin`: a locally integrable `u` with `|u| ≤ C|z|` near `0` that solves `Δu = F`
   weakly on `ℝ² \ {0}` solves it weakly on `ℝ²` (cutoff `χ(z/ε)`; no delta term).  Applied with
   `|Rf(r)| ≤ C‖f‖ r` (`B0086.green_bound_XG`).
3. `PlanarGreenL2`: `‖u‖₂ ≤ C‖f‖_{X_G}` and `‖planar f‖₂ ≤ C‖f‖_{X_G}`.
4. `PlanarEllipticH2` (`Lib/SobolevC/Elliptic.lean : ellipticH2` transferred to `ℝ × ℝ`),
   `PlanarLapOfDeriv` (`Δ` commutes with weak derivatives) and `PlanarBootstrap j` (iterate the
   `H²` step on `∂^γ u`, `|γ| ≤ j-2`) give all orders.

`greenEllipticRegularity_of` derives `B0122.GreenEllipticRegularity j` from
`GreenWeakPunctured`, `RemovableOrigin`, `PlanarGreenL2` and `PlanarBootstrap j`.  The unconditional
statement is task `PartI:C09` (`Short/PartI/Tasks/GreenEllipticRegularity.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

/-- `Δu = F` in the sense of distributions on the open set `V ⊆ ℝ²`
(`∫ u (∂₁∂₁φ + ∂₂∂₂φ) = ∫ F φ` for every test function `φ` supported in `V`), with the sign
convention of `HasWeakDerivOn` for the even order two. -/
def WeakLapOn (V : Set (ℝ × ℝ)) (u F : ℝ × ℝ → ℂ) : Prop :=
  ∀ φ : ℝ × ℝ → ℂ, IsTestFn V φ →
    ∫ z, u z * (iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) =
      ∫ z, F z * φ z

/-- The radial weak form of `Δ₂ψ = f` on `(0, ∞)` (`Δ₂ψ = ψ'' + ψ'/r - 4ψ/r²`, measure `r dr`):
`∫₀^∞ ψ (Φ'' + Φ'/r - 4Φ/r²) r dr = ∫₀^∞ f Φ r dr` for every `Φ` smooth on `(0, ∞)` that vanishes
for `r` outside a compact subinterval `[a, b] ⊆ (0, ∞)`. -/
def RadialWeakEq (ψ f : ℝ → ℂ) : Prop :=
  ∀ Φ : ℝ → ℂ, ContDiffOn ℝ ∞ Φ (Ioi 0) →
    (∃ a b : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r → (r < a ∨ b < r) → Φ r = 0) →
    ∫ r in Ioi (0 : ℝ), ψ r * (deriv (deriv Φ) r + deriv Φ r / (r : ℂ) - 4 * Φ r / (r : ℂ) ^ 2) *
        (r : ℂ) = ∫ r in Ioi (0 : ℝ), f r * Φ r * (r : ℂ)

/-- **Step 1a** (radial integration by parts; `B0011.IsDelta2Sol`): a locally integrable `f` on
`(0, ∞)` and a solution `ψ` of `Δ₂ψ = f` in the integrated form of `IsDelta2Sol` satisfy
`RadialWeakEq ψ f`.  (`ψ'` is absolutely continuous with `(rψ')' = r f + 4ψ/r` a.e.) -/
def RadialGreenIdentity : Prop :=
  ∀ f ψ : ℝ → ℂ, LocallyIntegrableOn f (Ioi 0) volume → B0011.IsDelta2Sol f ψ →
    RadialWeakEq ψ f

/-- **Step 1b** (polar coordinates): the radial weak equation `RadialWeakEq ψ f` for locally
integrable profiles gives `Δ(ψ(r)e^{2iϑ}) = f(r)e^{2iϑ}` weakly on `ℝ² \ {0}`.  (Angular mode
`Φ(r) = ∫_{-π}^{π} e^{2iϑ} φ(r cos ϑ, r sin ϑ) dϑ` of the test function; `Δφ` in polar form;
`∫_{-π}^{π} e^{2iϑ} ∂_ϑ² φ dϑ = -4Φ`.) -/
def PolarReduction : Prop :=
  ∀ ψ f : ℝ → ℂ, LocallyIntegrableOn ψ (Ioi 0) volume → LocallyIntegrableOn f (Ioi 0) volume →
    RadialWeakEq ψ f →
      WeakLapOn ({0}ᶜ : Set (ℝ × ℝ)) (B0010.angularTwoField ψ) (B0010.angularTwoField f)

/-- **Step 1** (source lines 1139-1140, "the radial Green formula for `Δ₂⁻¹`"): for `f ∈ X_G`,
the planar function `u = Rf(r)e^{2iϑ}` solves `Δu = f(r)e^{2iϑ}` weakly on `ℝ² \ {0}`. -/
def GreenWeakPunctured : Prop :=
  ∀ f : B0010.XG,
    WeakLapOn ({0}ᶜ : Set (ℝ × ℝ)) (B0010.angularTwoField (B0011.R ⇑f)) (planar f)

/-- **Step 2** (removable origin; no delta term): a locally integrable `u` that is `O(|z|)` near
`0` and solves `Δu = F` weakly on `ℝ² \ {0}` with `F` locally integrable solves it weakly on
`ℝ²`. -/
def RemovableOrigin : Prop :=
  ∀ u F : ℝ × ℝ → ℂ, LocallyIntegrable u volume → LocallyIntegrable F volume →
    (∃ C δ : ℝ, 0 < δ ∧ ∀ z : ℝ × ℝ, ‖z‖ < δ → ‖u z‖ ≤ C * ‖z‖) →
    WeakLapOn ({0}ᶜ : Set (ℝ × ℝ)) u F → WeakLapOn univ u F

/-- **Step 3** (source line 1140): `‖Rf‖₂ ≤ C‖f‖_{X_G}` for the planar function of `Rf`
(`B0086.green_bound_XG`, polar integration), and `planar f ∈ L²(ℝ²)` with `‖planar f‖₂ ≤ C‖f‖_{X_G}`
(`G ≤ (4π)⁻¹`, `B0122.integral_sq_le_gauss`). -/
def PlanarGreenL2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : B0010.XG,
    MemLp (B0010.angularTwoField (B0011.R ⇑f)) 2 volume ∧ MemLp (planar f) 2 volume ∧
    ∫ z, ‖B0010.angularTwoField (B0011.R ⇑f) z‖ ^ 2 ≤ C * ‖f‖ ^ 2 ∧
    ∫ z, ‖planar f z‖ ^ 2 ≤ C * ‖f‖ ^ 2

/-- **Step 4a** (the `H²` estimate, source line 1141, "elliptic regularity"): if `u, g ∈ L²(ℝ²)`
and `Δu = g` weakly on `ℝ²`, then `u` has weak derivatives of all orders `≤ 2` in `L²`, with
`∑_{|β|≤2} ‖∂^β u‖² ≤ C (‖u‖² + ‖g‖²)`. -/
def PlanarEllipticH2 : Prop :=
  ∃ C : ℝ, ∀ u g : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp g 2 volume → WeakLapOn univ u g →
    ∃ v : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ β ∈ multiIdx 2, MemLp (v β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (v β)) ∧
      ∑ β ∈ multiIdx 2, ∫ z, ‖v β z‖ ^ 2 ≤ C * ((∫ z, ‖u z‖ ^ 2) + ∫ z, ‖g z‖ ^ 2)

/-- **Step 4b**: the Laplacian commutes with weak derivatives.  If `Δu = F` weakly on `ℝ²`,
`∂^γ u = v` and `∂^γ F = g` weakly, then `Δv = g` weakly on `ℝ²`. -/
def PlanarLapOfDeriv : Prop :=
  ∀ (γ : ℕ × ℕ) (u F v g : ℝ × ℝ → ℂ), WeakLapOn univ u F →
    HasWeakDerivOn univ (pdListR γ) u v → HasWeakDerivOn univ (pdListR γ) F g →
    WeakLapOn univ v g

/-- **Step 4c** (source lines 1141-1142, "elliptic regularity"): all orders `≤ j`.  If
`u, f ∈ L²(ℝ²)`, `Δu = f` weakly, and `∂^α f = gF α ∈ L²` for `|α| ≤ j - 2` (natural subtraction),
then `∂^β u = gu β ∈ L²` for `|β| ≤ j` and
`∑_{|β|≤j} ‖gu β‖² ≤ C_j (∑_{|α|≤j-2} ‖gF α‖² + ‖u‖²)`.  Follows from `PlanarEllipticH2` and
`PlanarLapOfDeriv` by induction on `j`. -/
def PlanarBootstrap (j : ℕ) : Prop :=
  ∃ C : ℝ, ∀ u f : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp f 2 volume → WeakLapOn univ u f →
    ∀ gF : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ α ∈ multiIdx (j - 2), MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α)) →
      ∃ gu : ℕ × ℕ → ℝ × ℝ → ℂ,
        (∀ β ∈ multiIdx j, MemLp (gu β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (gu β)) ∧
        ∑ β ∈ multiIdx j, ∫ z, ‖gu β z‖ ^ 2 ≤
          C * ((∑ α ∈ multiIdx (j - 2), ∫ z, ‖gF α z‖ ^ 2) + ∫ z, ‖u z‖ ^ 2)

/-- `|angularTwoField (R f) z| ≤ 2 C ‖f‖ ‖z‖` for all `z` (`Rf(0) = 0`, `|Rf(r)| ≤ C‖f‖ r`). -/
theorem planarR_le_mul_norm (f : B0010.XG) :
    ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖B0010.angularTwoField (B0011.R ⇑f) z‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC0, hC⟩ := B0086.green_bound_XG
  refine ⟨2 * C * ‖f‖, fun z => ?_⟩
  rw [B0010.angularTwoField, norm_mul, B0121.norm_exp_two_mul_I, mul_one]
  rcases eq_or_ne z 0 with h | h
  · have h0 : (polarCoord z).1 = 0 := by
      rw [h]
      show Real.sqrt ((0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2) = 0
      simp
    rw [h0]
    simp only [B0011.R, Complex.ofReal_zero, intervalIntegral.integral_same, mul_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, norm_zero]
    rw [h]
    simp
  · have hr := B0122.polarRadius_pos h
    have hrle : (polarCoord z).1 ≤ 2 * ‖z‖ := by
      show Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ 2 * ‖z‖
      have h1 : |z.1| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_fst_le z
      have h2 : |z.2| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_snd_le z
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [sq_abs z.1, sq_abs z.2, abs_nonneg z.1, abs_nonneg z.2, norm_nonneg z]
    refine (hC f _ hr).1.trans ?_
    have hmin : min (polarCoord z).1 ((polarCoord z).1 ^ 2)⁻¹ ≤
        (polarCoord z).1 := min_le_left _ _
    have h0 : 0 ≤ C * ‖f‖ := by positivity
    calc C * ‖f‖ * min (polarCoord z).1 ((polarCoord z).1 ^ 2)⁻¹
        ≤ C * ‖f‖ * (2 * ‖z‖) := by
          gcongr
          exact hmin.trans hrle
      _ = 2 * C * ‖f‖ * ‖z‖ := by ring

/-- **The elliptic estimate for the Green inverse from the five lemmas.**  Conditional form of
`B0122.GreenEllipticRegularity j`; the unconditional statement is `PartI:C09`. -/
theorem greenEllipticRegularity_of (j : ℕ) (h1 : GreenWeakPunctured) (h2 : RemovableOrigin)
    (h3 : PlanarGreenL2) (h4 : PlanarBootstrap j) : B0122.GreenEllipticRegularity j := by
  obtain ⟨C0, hC0, hL2⟩ := h3
  obtain ⟨Cb, hCb⟩ := h4
  refine ⟨max Cb 0 * max 1 C0, fun f gF hgF => ?_⟩
  obtain ⟨hu, hF, hu2, hF2⟩ := hL2 f
  have hlap : WeakLapOn univ (B0010.angularTwoField (B0011.R ⇑f)) (planar f) := by
    refine h2 _ _ (B0122.locallyIntegrable_planarR f)
      (hF.locallyIntegrable (by norm_num)) ?_ (h1 f)
    obtain ⟨C, hC⟩ := planarR_le_mul_norm f
    exact ⟨C, 1, one_pos, fun z _ => hC z⟩
  obtain ⟨gu, hgu, hbd⟩ := hCb _ _ hu hF hlap gF hgF
  refine ⟨gu, hgu, hbd.trans ?_⟩
  set S := ∑ α ∈ multiIdx (j - 2), ∫ z, ‖gF α z‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun α _ => integral_nonneg fun z => by positivity
  have hI0 : 0 ≤ ∫ z, ‖B0010.angularTwoField (B0011.R ⇑f) z‖ ^ 2 :=
    integral_nonneg fun z => by positivity
  have hf0 : 0 ≤ ‖f‖ ^ 2 := by positivity
  have hm1 : 1 ≤ max 1 C0 := le_max_left _ _
  have hm2 : C0 ≤ max 1 C0 := le_max_right _ _
  calc Cb * (S + ∫ z, ‖B0010.angularTwoField (B0011.R ⇑f) z‖ ^ 2)
      ≤ max Cb 0 * (S + ∫ z, ‖B0010.angularTwoField (B0011.R ⇑f) z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS0 hI0)
    _ ≤ max Cb 0 * (S + C0 * ‖f‖ ^ 2) := by
        gcongr
    _ ≤ max Cb 0 * (max 1 C0 * (S + ‖f‖ ^ 2)) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hm1 hS0, mul_le_mul_of_nonneg_right hm2 hf0]
    _ = max Cb 0 * max 1 C0 * (S + ‖f‖ ^ 2) := by ring

end UnforcedLeray.Short.PartI
