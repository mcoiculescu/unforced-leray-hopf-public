import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3

/-!
# Decomposition of `PartII-a:N01/9/1/1/3/2` (`ProdTestOrth`), source lines 1684-1689

`ProdTestOrth` reduces to: the product tests `Φ = θ(s)ψ(q,η)` are profile tests / stream functions
(`ProdIsProfileTest`, `ProdIsStreamFn`); pairing with them is the weighted slice integral
(`DivPairing`, `CurlPairing`); and the slice integrals are locally integrable (`SliceLocInt`).
The fundamental lemma in `s` (Mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) is
applied here.  Note `sliceFn` already uses the `q`-periodic extension (`reduceIoc`), so the
slice integrals over `Cyl.cell c` are the integrals over the profile cell `(0,c]` by periodicity
of the test `ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa

/-- The product test `θ(s) ψ(q,η)`. -/
def prodFn (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) : Profile → ℝ := fun p => θ p.1 * ψ p.2

/-- `θ` is a smooth function with compact support in `(0,∞)`. -/
def IsSBump (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ Ioi 0

/-- `θ(s)ψ(q,η)` is a profile test. -/
def ProdIsProfileTest : Prop :=
  ∀ (c : ℝ) (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ), IsSBump θ → UnforcedLeray.Sob.IsCylTest c ψ →
    UnforcedLeray.B0226.IsProfileTest c (prodFn θ ψ)

/-- `θ(s)ψ(q,η)` (cast to `ℂ`) is a stream function. -/
def ProdIsStreamFn : Prop :=
  ∀ (c : ℝ) (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ), IsSBump θ → UnforcedLeray.Sob.IsCylTest c ψ →
    IsStreamFn c (fun p => ((prodFn θ ψ p : ℝ) : ℂ))

/-- Pairing with the profile gradient `cgrad 0 (θψ) = (∂_q(θψ), ∂_η(θψ))` (an element of
`(solenoidalHC 0 c)ᗮ`) is the weighted slice divergence integral
`∫ θ(s) s^{-3/2} divI(slice_s) ds` (Fubini on `measureH c = s^{-3/2} ds dq dη` on the cell,
`q`-periodicity of `ψ`). -/
def DivPairing : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ), IsSBump θ → UnforcedLeray.Sob.IsCylTest c ψ →
    ∃ g : HSpace c MeridC, g ∈ (solenoidalHC 0 c)ᗮ ∧ ∀ h : HSpace c MeridC,
      inner ℂ g h = ∫ s : ℝ, ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * divI c (sliceFn h s) ψ

/-- Pairing with the stream field `(∂_η(θψ), -∂_q(θψ))` (an element of `StreamSet c`) is the
weighted slice curl integral `∫ θ(s) s^{-3/2} curlI(slice_s) ds`. -/
def CurlPairing : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ), IsSBump θ → UnforcedLeray.Sob.IsCylTest c ψ →
    ∃ g ∈ StreamSet c, ∀ h : HSpace c MeridC,
      inner ℂ g h = ∫ s : ℝ, ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * curlI c (sliceFn h s) ψ

/-- The weighted slice div and curl integrands are locally integrable on `(0,∞)`
(Cauchy-Schwarz against the weight `s^{-3/2}` and `h ∈ L²(measureH)`, Fubini). -/
def SliceLocInt : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ h : HSpace c MeridC, ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.Sob.IsCylTest c ψ →
    LocallyIntegrableOn (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * divI c (sliceFn h s) ψ)
        (Ioi 0) volume ∧
    LocallyIntegrableOn (fun s : ℝ => ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * curlI c (sliceFn h s) ψ)
        (Ioi 0) volume

theorem fundamental_s (F : ℝ → ℂ) (hF : LocallyIntegrableOn F (Ioi 0) volume)
    (hint : ∀ θ : ℝ → ℝ, IsSBump θ → ∫ s, ((θ s : ℝ) : ℂ) * F s = 0) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), F s = 0 := by
  have := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hF
    (fun θ hθ hc hs => by
      have := hint θ ⟨hθ, hc, hs⟩
      simpa [Complex.real_smul] using this)
  exact (ae_restrict_iff' measurableSet_Ioi).2 this

theorem prodTestOrth_of (h1 : DivPairing) (h2 : CurlPairing) (h3 : SliceLocInt) :
    ProdTestOrth := by
  intro c hc h hs ho ψ hψ
  obtain ⟨hli1, hli2⟩ := h3 c hc h ψ hψ
  have hd := fundamental_s _ hli1 (fun θ hθ => by
    obtain ⟨g, hg, hgh⟩ := h1 c hc θ ψ hθ hψ
    have h0 : inner ℂ g h = 0 := Submodule.inner_left_of_mem_orthogonal hs hg
    rw [hgh h] at h0
    rw [← h0]
    congr 1
    ext s
    push_cast
    ring)
  have hcu := fundamental_s _ hli2 (fun θ hθ => by
    obtain ⟨g, hg, hgh⟩ := h2 c hc θ ψ hθ hψ
    have h0 : inner ℂ g h = 0 := ho g hg
    rw [hgh h] at h0
    rw [← h0]
    congr 1
    ext s
    push_cast
    ring)
  filter_upwards [hd, hcu, ae_restrict_mem measurableSet_Ioi] with s a b hs0
  have hne : ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < s ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
    exact_mod_cast this.ne'
  exact ⟨(mul_eq_zero.1 a).resolve_left hne, (mul_eq_zero.1 b).resolve_left hne⟩

end UnforcedLeray.Short.PartIIa.N01.Sub
