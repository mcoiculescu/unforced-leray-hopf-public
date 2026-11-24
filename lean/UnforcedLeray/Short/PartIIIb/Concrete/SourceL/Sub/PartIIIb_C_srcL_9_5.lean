import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9

/-!
# Decomposition of `streamCutJet` (source 4178-4186, 4917-4937)

Source: `the November 2 reference manuscript`.

`X = 𝒞_y Z = χ_y Z + (χ_y'/r) Ψ_Z e_z` with `Z` `C^7` and `‖∂^m Z(w)‖ ≤ B|w|^{-4-m}` on
`{|w|² > 11ν/12}`.  Chain: `SCPsiSmooth`, `SCPsiBound`, `SCChiJet` give `SCXJet`
(`‖∂^m X(y)‖ ≤ C B r^{-4-m}`, Leibniz); `SCXJet` plus the generic receiver statement `SCSDeriv`
(`(s∂_s)^j` of `D X(s^{-1/2},0,0)`) give `StreamCutJet` (`streamCutJet_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The standing hypotheses on `Z` (source 4917-4937). -/
def SCZHyp (ν B : ℝ) (Z : Vec3 → Vec3) : Prop :=
  ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} ∧
    ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)

/-- `Ψ_Z` is `C^7` on `{|w|² > 11ν/12, r > 0}` (every outward ray stays in `{|w|² > 11ν/12}`;
differentiate `-∫_r^∞ ρ Z_z(rayPt y ρ) dρ` under the integral, dominating function
`≲ B ρ^{-3-m}`, integrable on `(r,∞)`). -/
def SCPsiSmooth : Prop :=
  ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ContDiffOn ℝ 7 (streamPsi Z) {y | ν * (11 / 12) < eucSq y ∧ 0 < cylR y}

/-- `‖∂^m Ψ_Z(y)‖ ≤ C₁ B r^{-2-m}` for `m ≤ 7` and `ν ≤ r²` (`∫_r^∞ ρ·Bρ^{-4} = B r^{-2}/2`;
each derivative costs `r^{-1}`, `D^j rayPt ≲ ρ^j r^{-j}`), with `C₁` absolute. -/
def SCPsiBound : Prop :=
  ∃ C1 : ℝ, ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ m : ℕ, m ≤ 7 → ∀ y : Vec3, ν ≤ cylR y ^ 2 →
      ‖iteratedFDeriv ℝ m (streamPsi Z) y‖ ≤ C1 * B * cylR y ^ (-(2 : ℝ) - m)

/-- The cutoff factors on `r > 0` (source 4161-4166, 4178-4186): `y ↦ χ_y(ν/r²)` and
`y ↦ χ_y'(r)/r` are `C^7` and `‖∂^m‖ ≤ C₂ r^{-m}`, resp. `C₂ r^{-2-m}` (`ν ≤ r²` on the support of
`χ_y`; `(ν/r²)^k ≤ 1`; zero where `r² < ν`), `C₂` depending only on `χ̂_y`. -/
def SCChiJet (χy : ℝ → ℝ) : Prop :=
  ∃ C2 : ℝ, ∀ ν : ℝ, 0 < ν → IsStreamCutoff χy → ∀ y : Vec3, 0 < cylR y →
    ContDiffAt ℝ 7 (fun y => chiYr ν 1 χy (cylR y)) y ∧
    ContDiffAt ℝ 7 (fun y => deriv (chiYr ν 1 χy) (cylR y) / cylR y) y ∧
    ∀ m : ℕ, m ≤ 7 →
      ‖iteratedFDeriv ℝ m (fun y => chiYr ν 1 χy (cylR y)) y‖ ≤ C2 * cylR y ^ (-(m : ℝ)) ∧
      ‖iteratedFDeriv ℝ m (fun y => deriv (chiYr ν 1 χy) (cylR y) / cylR y) y‖ ≤
        C2 * cylR y ^ (-(2 : ℝ) - m)

/-- The jets of the stream cutoff: `X` is `C^7` at every `y` with `r > 0` and
`‖∂^m X(y)‖ ≤ C₄ B r^{-4-m}`, `m ≤ 7` (Leibniz from `SCPsiSmooth`, `SCPsiBound`, `SCChiJet`;
`|w| ≥ r`; near `r² < ν`, `X = 0`). -/
def SCXJet (χy : ℝ → ℝ) : Prop :=
  ∃ C4 : ℝ, ∀ (ν B : ℝ), 0 < ν → 0 ≤ B → ∀ Z : Vec3 → Vec3, SCZHyp ν B Z → IsStreamCutoff χy →
    ∀ y : Vec3, 0 < cylR y → ContDiffAt ℝ 7 (streamCut ν 1 χy Z) y ∧
      ∀ m : ℕ, m ≤ 7 → ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y‖ ≤ C4 * B * cylR y ^ (-(4 : ℝ) - m)

/-- Receiver jets of any field (source 4917-4937): `(s∂_s) = -½ r∂_r` on `r = s^{-1/2}`, so
`(s∂_s)^j D X(s^{-1/2},0,0)` is a combination of `r^k D^{k+1}X`, `k ≤ j ≤ 6`, each
`≤ K r^{-5} = K s^{5/2}`. -/
def SCSDeriv : Prop :=
  ∃ C3 : ℝ, ∀ (X : Vec3 → Vec3) (K : ℝ), 0 ≤ K → (∀ y : Vec3, 0 < cylR y → ContDiffAt ℝ 7 X y) →
    (∀ m : ℕ, m ≤ 7 → ∀ y : Vec3, 0 < cylR y →
      ‖iteratedFDeriv ℝ m X y‖ ≤ K * cylR y ^ (-(4 : ℝ) - m)) →
    ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      frob (sDerivIter j (fun s : ℝ => if 0 < s then
        (fun i j => fderiv ℝ X ![(1 : ℝ)⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i)
        else (0 : Mat3)) s) ≤ C3 * K * s ^ (5 / 2 : ℝ)

theorem streamCutJet_of {χy : ℝ → ℝ} (hX : SCXJet χy) (hD : SCSDeriv) : StreamCutJet χy := by
  obtain ⟨C4, hC4⟩ := hX
  obtain ⟨C3, hC3⟩ := hD
  refine ⟨C3 * |C4|, ?_⟩
  intro ν B hν hB Z hZ hb hχ s hs j hj
  have hZH : SCZHyp ν B Z := ⟨hZ, hb⟩
  have hK : 0 ≤ |C4| * B := mul_nonneg (abs_nonneg _) hB
  have hbd : ∀ y : Vec3, 0 < cylR y → ContDiffAt ℝ 7 (streamCut ν 1 χy Z) y ∧
      ∀ m : ℕ, m ≤ 7 → ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y‖ ≤
        |C4| * B * cylR y ^ (-(4 : ℝ) - m) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hC4 ν B hν hB Z hZH hχ y hy
    refine ⟨h1, fun m hm => (h2 m hm).trans ?_⟩
    have hp : 0 ≤ cylR y ^ (-(4 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hB) hp
  have := hC3 (streamCut ν 1 χy Z) (|C4| * B) hK (fun y hy => (hbd y hy).1)
    (fun m hm y hy => (hbd y hy).2 m hm) s hs j hj
  calc _ ≤ C3 * (|C4| * B) * s ^ (5 / 2 : ℝ) := this
    _ = C3 * |C4| * B * s ^ (5 / 2 : ℝ) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
