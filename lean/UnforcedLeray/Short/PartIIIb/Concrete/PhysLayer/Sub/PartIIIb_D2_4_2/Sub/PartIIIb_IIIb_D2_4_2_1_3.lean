import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.Absorb

/-!
# Decomposition of `PsiProfileGaussBound` (task `PartIII-b:IIIb-D2/4/2/1/3`)

Source of record: `the November 2 reference manuscript`, lines 4963-4991
("the sums and their required derivatives converge by Gaussian decay").  The profile is
`Ψ(s,y) = G(s,y) · P(s,y)` with the Gaussian `G = e^{-|y|²/(4a)}`, `a = 1+νs`, and the polynomial
factor `P = -2a⁻¹ (tr M - c₁(y, M y))`, `M = χ(νs)A(s)`.  On `s ∈ [s₀/2, 2s₀]` one has
`a ≤ K = 1+2νs₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Gaussian factor `e^{-|y|²/(4a(s))}` of the profile, on the chart. -/
def psiGauss (ν : ℝ) : Chart → ℝ :=
  fun p => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))

/-- The polynomial factor `-2a⁻¹ (tr M - c₁(y, M y))`, `M = Ay ν χf A s`, of the profile. -/
def psiPoly (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → ℝ :=
  fun p => (-2 * (ageA ν p.1)⁻¹) *
    (merTrace (Ay ν χf A p.1) -
      (-(2 * p.2.1 * (merApply (Ay ν χf A p.1) p.2).1 +
        2 * p.2.2 * (merApply (Ay ν χf A p.1) p.2).2) / (4 * ageA ν p.1)))

theorem psiProfile_eq_mul (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    psiProfile ν χf A = fun p => psiGauss ν p * psiPoly ν χf A p := by
  funext p
  simp only [psiProfile, psiPhi, psiGauss, psiPoly]
  ring

/-- **Leaf G (Gaussian factor)**: `psiGauss ν` is `C²` on `s > 0` and, for `s ∈ [s₀/2, 2s₀]`,
`‖D^k G(p)‖ ≤ C (1+‖p.2‖)^N e^{-|y|²/(4K)}`, `K = 1+2νs₀`, `k ≤ 2`.  (`D G = G · (polynomial in y,
a⁻¹, νa⁻²)`; `a ≤ K` on the range gives `e^{-|y|²/(4a)} ≤ e^{-|y|²/(4K)}`.  Route: write
`G = exp ∘ q`, `q(s,y) = -|y|²/(4a(s))`, `C²` on `s > 0`; `norm_iteratedFDerivWithin_comp_le`/
explicit first and second derivatives (`HasFDerivAt` of `q`), bounded coefficients on the compact
range.) -/
def PsiGaussFactor : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ s0 : ℝ, 0 < s0 →
    ContDiffOn ℝ 2 (psiGauss ν) (Ioi 0 ×ˢ univ) ∧
    ∃ (N : ℕ) (C : ℝ), ∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (psiGauss ν) p‖ ≤
        C * (1 + ‖p.2‖) ^ N * Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0)))

/-- **Leaf P (polynomial factor)** (`A ∈ 𝒜` is `C⁶` on `(0,∞)`, `χ` is `C^∞`): `psiPoly` is `C²` on
`s > 0` and has polynomial growth in `y` of its derivatives of order `≤ 2`, uniformly for
`s ∈ [s₀/2, 2s₀]`: `‖D^k P(p)‖ ≤ C (1+‖p.2‖)^N`.  (`P` is a quadratic polynomial in `y` with
coefficients `-2a⁻¹ χ(νs)A_{ij}(s)`, `-2a⁻¹ (νa)⁻¹…` that are `C²` in `s`; bound the coefficient
derivatives on the compact `[s₀/2, 2s₀]`.) -/
def PsiPolyFactor (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s0 : ℝ, 0 < s0 →
      ContDiffOn ℝ 2 (psiPoly ν χf A) (Ioi 0 ×ˢ univ) ∧
      ∃ (N : ℕ) (C : ℝ), ∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (psiPoly ν χf A) p‖ ≤ C * (1 + ‖p.2‖) ^ N

/-- **Leaf M (Leibniz bound for a product on the open set `s > 0`)**: if `f, g` are `C²` on
`Ioi 0 ×ˢ univ`, `‖D^k f(p)‖ ≤ C₁ (1+‖p.2‖)^{N₁} G(p)` and `‖D^k g(p)‖ ≤ C₂ (1+‖p.2‖)^{N₂}`
for `p.1 ∈ [s₀/2, 2s₀]`, `k ≤ 2`, with `G ≥ 0`, then
`‖D^k (f·g)(p)‖ ≤ C (1+‖p.2‖)^{N₁+N₂} G(p)` there.  (`iteratedFDeriv_mul`-type bound
`norm_iteratedFDerivWithin_mul_le` on the open set, `iteratedFDerivWithin_of_isOpen`,
`‖p.2‖ ≤ ‖p‖`; the `s`-component is bounded on the range; `(1+x)^a ≤ (1+x)^b` for `a ≤ b`.) -/
def LeibnizMulBound : Prop :=
  ∀ (f g : Chart → ℝ) (G : Chart → ℝ) (s0 : ℝ) (N₁ N₂ : ℕ) (C₁ C₂ : ℝ),
    0 < s0 → (∀ p, 0 ≤ G p) →
    ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ) → ContDiffOn ℝ 2 g (Ioi 0 ×ˢ univ) →
    (∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k f p‖ ≤ C₁ * (1 + ‖p.2‖) ^ N₁ * G p) →
    (∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k g p‖ ≤ C₂ * (1 + ‖p.2‖) ^ N₂) →
    ∃ C : ℝ, ∀ p : Chart, p.1 ∈ Icc (s0 / 2) (2 * s0) → ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun q => f q * g q) p‖ ≤ C * (1 + ‖p.2‖) ^ (N₁ + N₂) * G p

theorem psiProfileGaussBound_of (as : ℝ) (χf : ℝ → ℝ) (hG : PsiGaussFactor)
    (hP : PsiPolyFactor as χf) (hM : LeibnizMulBound) : PsiProfileGaussBound as χf := by
  intro hχ ν hν A hA s0 hs0
  obtain ⟨hGs, N₁, C₁, hG1⟩ := hG ν hν s0 hs0
  obtain ⟨hPs, N₂, C₂, hP2⟩ := hP hχ ν hν A hA s0 hs0
  have hK : 0 < 1 + 2 * ν * s0 := by positivity
  obtain ⟨C₃, hC₃⟩ := hM (psiGauss ν) (psiPoly ν χf A)
    (fun p => Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0)))) s0 N₁ N₂ C₁ C₂ hs0
    (fun p => (Real.exp_pos _).le) hGs hPs hG1 hP2
  obtain ⟨C₄, hC₄⟩ := gauss_poly_absorb (N₁ + N₂) hK
  refine ⟨|C₃| * C₄, fun p hp k hk => ?_⟩
  rw [psiProfile_eq_mul]
  have h1 := hC₃ p hp k hk
  have h2 := hC₄ p.2
  have hE : (0 : ℝ) ≤ Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0))) := (Real.exp_pos _).le
  have hpow : (0 : ℝ) ≤ (1 + ‖p.2‖) ^ (N₁ + N₂) := by positivity
  have h3 : ‖iteratedFDeriv ℝ k (fun q => psiGauss ν q * psiPoly ν χf A q) p‖ ≤
      |C₃| * ((1 + ‖p.2‖) ^ (N₁ + N₂) *
        Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0)))) := by
    refine h1.trans ?_
    have : C₃ * (1 + ‖p.2‖) ^ (N₁ + N₂) *
        Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0))) =
        C₃ * ((1 + ‖p.2‖) ^ (N₁ + N₂) * Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0)))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_abs_self C₃) (mul_nonneg hpow hE)
  calc _ ≤ |C₃| * ((1 + ‖p.2‖) ^ (N₁ + N₂) *
        Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0)))) := h3
    _ ≤ |C₃| * (C₄ * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * s0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have : sq2 p.2 = p.2.1 ^ 2 + p.2.2 ^ 2 := rfl
        rw [this]; exact h2
    _ = |C₃| * C₄ * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * s0))) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
