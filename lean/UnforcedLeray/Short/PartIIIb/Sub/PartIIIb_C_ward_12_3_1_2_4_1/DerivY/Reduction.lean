import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1

/-!
# `RawResidualDerivY` from the slice derivative bound and slice integration by parts

Source of record `the November 2 reference manuscript`,
lines 2542-2551 and 1206-1222 (and 1305-1322 for the ring residual).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF)
open UnforcedLeray.Short.IIb (trainStream trainPressure)
open UnforcedLeray.Short.PartIIa (ringResidual)

/-- **Spatial derivative of the ring residual** (source 1206-1222, 1305-1322, 2542-2551).  For the
BUC train, `c = ν⁻²`, `R ≥ 2`, `ν` small, period `≤ 1`, the ring residual `F_R(τ)` is `P`-periodic,
in `L^{q₀}` and `L^{q₀}`-continuous in `τ`, and each coordinate derivative `∂_j F_R(τ)` (a weak
spatial derivative: off the axis the classical derivative, with the residual smooth through the
axis) is `P`-periodic, in `L^{q₀}` and `L^{q₀}`-continuous in `τ`.  Reason: the unprojected
derivatives of the train complete source are `O(ϱ^{-3-k}(1+|y₃|/ϱ)^{-N})`, whose `q₀`-th integral
is finite. -/
def RingResidualDerivBound : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j : Fin 3,
      ∃ G : ℝ → SpatialField,
        (∀ τ, ringResidual p.R p.ν (trainStream p) (trainPressure p) (τ + p.period) =
          ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) ∧
        (∀ τ, G (τ + p.period) = G τ) ∧
        (∀ τ, MemLp (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) q0E volume) ∧
        (∀ τ, MemLp (G τ) q0E volume) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (ringResidual p.R p.ν (trainStream p)
            (trainPressure p) τ - ringResidual p.R p.ν (trainStream p) (trainPressure p) τ₀)
            q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (G τ - G τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ, HasWeakSpatialDerivative j
          (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) (G τ))

/-- **Slice integration by parts** (source 2542-2551): if `F, G : ℝ → ℝ³-fields` are `P`-periodic,
slice-wise in `L^{q₀}`, `L^{q₀}`-continuous, and `G τ` is the weak `∂_j` derivative of `F τ`, then
for every phase test `Φ`, `⟪∂_jΦ, F⟫ = ⟪Φ, -G⟫` (Fubini in the period cell and the slice weak
identity, applied to the real and imaginary parts of each component of `Φ`). -/
def SliceIntegrationByParts : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (j : Fin 3) (F G : ℝ → SpatialField),
    (∀ τ, F (τ + P) = F τ) → (∀ τ, G (τ + P) = G τ) →
    (∀ τ, MemLp (F τ) q0E volume) → (∀ τ, MemLp (G τ) q0E volume) →
    (∀ τ₀, Tendsto (fun τ => (eLpNorm (F τ - F τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) →
    (∀ τ₀, Tendsto (fun τ => (eLpNorm (G τ - G τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) →
    (∀ τ, HasWeakSpatialDerivative j (F τ) (G τ)) →
    ∀ Φ, IsPhaseTest P Φ →
      pairF P (dy j Φ) (fun x => realC (F x.1 x.2)) =
        pairF P Φ (fun x => realC (-(G x.1 x.2)))

theorem derivY_of (h₁ : UnforcedLeray.Short.IIb.SliceFieldElem) (h₂ : RingResidualDerivBound)
    (h₃ : SliceIntegrationByParts) : RawResidualDerivY := by
  obtain ⟨ν₀, hν₀, H⟩ := h₂
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP j => ?_⟩
  obtain ⟨G, hFper, hGper, hFmem, hGmem, hFc, hGc, hw⟩ := H p htr hν hc hR hP j
  have hmem : ∀ τ, MemLp (-(G τ)) q0E volume := fun τ => (hGmem τ).neg
  obtain ⟨f, hf, -, -, -⟩ := h₁ p (fun τ => -(G τ))
    (fun τ => by simp only [hGper]) hmem
    (fun τ₀ => by
      refine (hGc τ₀).congr (fun τ => ?_)
      rw [neg_sub_neg, eLpNorm_sub_comm])
  refine ⟨f, fun Φ hΦ => ?_⟩
  rw [hf Φ hΦ.1]
  exact h₃ p.period p.period_pos j _ G hFper hGper hFmem hGmem hFc hGc hw Φ hΦ.1

end UnforcedLeray.Short.PartIIIb.Concrete
