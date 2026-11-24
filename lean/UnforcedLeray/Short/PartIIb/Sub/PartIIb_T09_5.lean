import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1
import UnforcedLeray.Short.PartIIb.Sub.T07

/-!
# Part II-b, task `PartII-b:T09/5` (`LapSmooth`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`A_ε`, `Q_ε = ∂_q - ε(K+1)`, `K = 2S + η∂_η`) and 1912-1916 (`∂_ρ(√s b) = s Q_ε b`,
`∂_z(√s b) = s ∂_η b`).

For nice `b` the weak derivatives are the classical ones (`classQ`, `classEta`); the Cartesian
Laplacian of the lift is computed pointwise (`vecLap_liftMer`, `LapPtwise`); the lift is a `C²`
function with compact support in `y`, so the phase-space Green identity applies (`LapGreen`).

Leaves: `LapWeakQ`, `LapWeakEta`, `LapNiceClass`, `WeakFOCongr`, `LapPtwise`, `LapNvCSmooth`,
`LapGreen`.  Proved here: `lapSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- The classical `Q_ε b = Σ_j (vQ ε)_j ∂_j b + dQ ε · b = ∂_q b - ε(2 s ∂_s + η ∂_η + 1) b`. -/
def classQ (ε : ℝ) (b : CProf) : CProf := fun x =>
  (∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) + dQ ε x • b x

/-- The classical `∂_η b`. -/
def classEta (b : CProf) : CProf := fun x => fderiv ℝ b x (cdir 2)

/-- **Leaf `T09/5/1`** (SP 1912-1916; as `DriftWeakS`, `Tasks/DriftNvC/Smooth/WeakS.lean`, with the
transpose `-div(vφ) + dφ` of `Q_ε`, using `ibp_test`-type integration by parts and
du Bois-Reymond): for nice `b`, `HasWeakVec (vQ ε) (dQ ε) b Qb` gives `Qb = classQ ε b` a.e. on
`s > 0`. -/
def LapWeakQ : Prop :=
  ∀ (c ε : ℝ) (b Qb : CProf), NiceProf c b → HasWeakVec (vQ ε) (dQ ε) b Qb →
    ∀ᵐ x : Coord, 0 < x.1 → Qb x = classQ ε b x

/-- **Leaf `T09/5/2`**: as `LapWeakQ` for `∂_η`: `HasWeakVec vEta dZero b Eb` gives
`Eb = classEta b` a.e. on `s > 0`. -/
def LapWeakEta : Prop :=
  ∀ (c : ℝ) (b Eb : CProf), NiceProf c b → HasWeakVec vEta dZero b Eb →
    ∀ᵐ x : Coord, 0 < x.1 → Eb x = classEta b x

/-- **Leaf `T09/5/3`**: `classQ ε b` and `classEta b` are again nice (smooth; `c`-periodic in `q`
since the coefficients of `vQ` do not depend on `q`; the derivative of a profile vanishing on
`s < s₀`, `s > s₁`, `|η| > L` vanishes on `s < s₀/2`, `s > 2 s₁`, `|η| > 2L` (shrink the box
by factors, `s₀ > 0`; take `s₁, L ≥ 1`)). -/
def LapNiceClass : Prop :=
  ∀ (c ε : ℝ) (b : CProf), NiceProf c b → NiceProf c (classQ ε b) ∧ NiceProf c (classEta b)

/-- **Leaf `T09/5/4`**: `HasWeakVec` only sees the function a.e. on `s > 0` (test functions are
supported in `s > 0`; `Integrable.congr`, `integral_congr_ae`). -/
def WeakFOCongr : Prop :=
  ∀ (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b b' g : CProf),
    (∀ᵐ x : Coord, 0 < x.1 → b x = b' x) → HasWeakVec v d b g → HasWeakVec v d b' g

/-- **Leaf `T09/5/5`** (SP 1651-1653, 1912-1916, `vecLap_liftMer`, `Lib/Axisymmetric/Laplacian.lean`):
the pointwise Cartesian Laplacian of the lift of a nice profile (real and imaginary parts
separately; `Δ(f e_r) = (Δf - f/ρ²) e_r`, `Δ(g e_z) = Δg e_z`, `∂_ρ(√s F) = s Q_ε F`,
`Q_ε(√s h) = √s (Q_ε - ε) h`, `∂_z(√s F) = s ∂_η F`).  On the axis both sides vanish since the
lift vanishes near it. -/
def LapPtwise : Prop :=
  ∀ (c ε ν : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b →
    ∀ (t : ℝ) (y : Space), nuLapT ν (NvC ε⁻¹ b) (t, y) =
      NvC ε⁻¹ (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b))) (t, y)

/-- **Leaf `T09/5/6`**: the lift of a nice profile is `C²` on `ℝ × ℝ³`, `P`-periodic in `t`
(`P = 2εc`: `q ↦ q + c` is `τ ↦ τ + 2c/R`), and vanishes outside `ℝ × K` for a compact `K` of
`ℝ³` (`s ∈ [s₀, s₁]` means `ρ ∈ [R/√s₁, R/√s₀]`, `|η| ≤ L` means `|z| ≤ ρL/R`; smoothness of
`(τ, y) ↦ chart R τ y` and `frameL` off the axis, and vanishing near the axis). -/
def LapNvCSmooth : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b →
    ContDiff ℝ 2 (NvC ε⁻¹ b) ∧
    (∀ (t : ℝ) (y : Space), NvC ε⁻¹ b (t + 2 * ε * c, y) = NvC ε⁻¹ b (t, y)) ∧
    ∃ K : Set Space, IsCompact K ∧ ∀ (t : ℝ) (y : Space), y ∉ K → NvC ε⁻¹ b (t, y) = 0

/-- **Leaf `T09/5/7`** (Green's identity on `(ℝ/Pℤ) × ℝ³`): for a phase test `Φ` and a `C²`
`P`-periodic field `w` with compact support in `y`, `⟪νΔΦ, w⟫ = ⟪Φ, νΔw⟫` (integrate by parts twice
in the Cartesian variables; the boundary terms vanish because `w` has compact `y`-support;
`dotL` is bilinear and symmetric). -/
def LapGreen : Prop :=
  ∀ (P ν : ℝ) (Φ w : ℝ × Space → CVec3), 0 < P → IsPhaseTest P Φ → ContDiff ℝ 2 w →
    (∀ (t : ℝ) (y : Space), w (t + P, y) = w (t, y)) →
    (∃ K : Set Space, IsCompact K ∧ ∀ (t : ℝ) (y : Space), y ∉ K → w (t, y) = 0) →
    pairF P (nuLapT ν Φ) w = pairF P Φ (nuLapT ν w)

/-- **Target** `LapSmooth` from its leaves (and `DriftNvCCongr`, `ChartNullPullback` of T07/T08). -/
theorem lapSmooth_of (h1 : LapWeakQ) (h2 : LapWeakEta) (h3 : LapNiceClass) (h4 : WeakFOCongr)
    (h5 : LapPtwise) (h6 : LapNvCSmooth) (h7 : LapGreen) (hCong : DriftNvCCongr)
    (hNull : ChartNullPullback) : LapSmooth := by
  intro c ε ν b Qb Eb Q2b E2b hc hε hb hQ hE hQ2 hE2 Φ hΦ
  have hbn := h3 c ε b hb
  have eQ := h1 c ε b Qb hb hQ
  have eE := h2 c b Eb hb hE
  have hQ2' : HasWeakVec (vQ ε) (dQ ε) (classQ ε b) Q2b := h4 _ _ Qb (classQ ε b) Q2b eQ hQ2
  have hE2' : HasWeakVec vEta dZero (classEta b) E2b := h4 _ _ Eb (classEta b) E2b eE hE2
  have eQ2 := h1 c ε (classQ ε b) Q2b hbn.1 hQ2'
  have eE2 := h2 c (classEta b) E2b hbn.2 hE2'
  obtain ⟨hC2, hper, K, hK, hsupp⟩ := h6 c ε b hc hε hb
  have hP : 0 < 2 * ε * c := by positivity
  rw [h7 (2 * ε * c) ν Φ (NvC ε⁻¹ b) hP hΦ hC2 hper ⟨K, hK, hsupp⟩]
  have e1 : nuLapT ν (NvC ε⁻¹ b) = NvC ε⁻¹
      (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b))) := by
    funext p
    obtain ⟨t, y⟩ := p
    exact h5 c ε ν b hc hε hb t y
  rw [e1]
  refine hCong hNull c ε _ _ Φ hc hε ?_
  filter_upwards [eQ2, eE2] with x hx1 hx2 hx
  simp only [lapProf]
  rw [hx1 hx, hx2 hx]

end UnforcedLeray.Short.IIb
