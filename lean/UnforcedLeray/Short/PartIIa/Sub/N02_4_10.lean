import UnforcedLeray.Short.PartIIa.Sub.N02_4_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.Split

/-!
# Decomposition of `PartII-a:N02/4/10` (`NzTruncMoment`)

Source: `the November 2 reference manuscript` lines 1744-1749 (finite Fourier sums
are dense in the displayed norm; truncation does not increase the moments).

`S = s ∂_s` and `η` commute with the `q`-Fourier truncation `f_N`; for each `(s, η)` Bessel in
`L²(0, c)` gives `∫_0^c ‖g_N‖² dq ≤ ∫_0^c ‖g‖² dq`, which integrates (Fubini over `measureH c`,
compact band) to `nzSq c a j f_N ≤ nzSq c a j f`.  Five leaves: `NtmSTest`, `NtmTruncTest`,
`NtmComm`, `NtmBesselPt`, `NtmMeasureMono`; `nzTruncMoment_of` assembles.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Leaf `/1`: `S = s ∂_s` preserves smooth meridional tests (smoothness, `q`-periodicity; the
support of `S f` lies in the closure of that of `f`, so the same closed band `[s₀, s₁] × [-L, L]`
works). -/
def NtmSTest : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → ∀ a : ℕ,
    IsMeridTest c (opS^[a] f)

/-- Leaf `/2`: the `q`-Fourier truncation of a smooth test is a smooth test (no mean-zero
hypothesis; parametric integral over `[0, c]`, band inherited, periodicity of the exponentials). -/
def NtmTruncTest : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Profile → MeridC), IsMeridTest c g → ∀ N : ℕ,
    IsMeridTest c (nzTrunc c N g)

/-- Leaf `/3`: `S` commutes with the `q`-truncation of a smooth test: `nzCoeff c n (S f) = s ·
nzCoeff c n (∂_s f)` by differentiation under the integral over `[0, c]`
(`intervalParamSmooth_proof`), hence `S^a f_N = (S^a f)_N`. -/
def NtmComm : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f : Profile → MeridC), IsMeridTest c f → ∀ N a : ℕ,
    opS^[a] (nzTrunc c N f) = nzTrunc c N (opS^[a] f)

/-- Leaf `/4` (Bessel in `q`): for a smooth test `g` and each `(s, η)`,
`∫_0^c ‖g_N(s,q,η)‖² dq ≤ ∫_0^c ‖g(s,q,η)‖² dq` (Parseval for `g_N` is `nzQParseval`; orthogonality
`nzqp_integral_conj_mul`; or `Orthonormal.sum_inner_products_le`). -/
def NtmBesselPt : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Profile → MeridC), IsMeridTest c g → ∀ (N : ℕ) (s η : ℝ),
    ∫ q in (0 : ℝ)..c, ‖nzTrunc c N g (s, q, η)‖ ^ 2 ≤ ∫ q in (0 : ℝ)..c, ‖g (s, q, η)‖ ^ 2

/-- Leaf `/5` (Fubini over the cell): for two smooth tests, a pointwise `(s, η)` comparison of the
`q`-integrals of `‖·‖²` gives the comparison of the weighted `measureH c` integrals
(`cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`, `measureH c = (volume.restrict cell).withDensity weightH`,
`integral_withDensity_eq_integral_smul`, `integral_prod`; integrability from the compact band and
continuity). -/
def NtmMeasureMono : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g₁ g₂ : Profile → MeridC), IsMeridTest c g₁ → IsMeridTest c g₂ →
    (∀ s η : ℝ, ∫ q in (0 : ℝ)..c, ‖g₁ (s, q, η)‖ ^ 2 ≤ ∫ q in (0 : ℝ)..c, ‖g₂ (s, q, η)‖ ^ 2) →
    ∀ j : ℕ, ∫ p, (|p.2.2| ^ j) ^ 2 * ‖g₁ p‖ ^ 2 ∂(measureH c) ≤
      ∫ p, (|p.2.2| ^ j) ^ 2 * ‖g₂ p‖ ^ 2 ∂(measureH c)

theorem nzTruncMoment_of (h1 : NtmSTest) (h2 : NtmTruncTest) (h3 : NtmComm) (h4 : NtmBesselPt)
    (h5 : NtmMeasureMono) : NzTruncMoment := by
  intro c hc f hf _ N
  have key : ∀ a j : ℕ, nzSq c a j (nzTrunc c N f) ≤ nzSq c a j f := by
    intro a j
    have hS := h1 c hc f hf a
    have hcm := h3 c hc f hf N a
    have hT := h2 c hc (opS^[a] f) hS N
    unfold nzSq
    rw [hcm]
    exact h5 c hc _ _ hT hS (fun s η => h4 c hc _ hS N s η) j
  unfold nzMomSum
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ => ?_
  refine Real.rpow_le_rpow ?_ (key a j) (by norm_num)
  exact integral_nonneg fun p => by positivity

end UnforcedLeray.Short.PartIIa
