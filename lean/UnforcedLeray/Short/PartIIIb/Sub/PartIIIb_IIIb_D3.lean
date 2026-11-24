import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq

/-!
# `PartIII-b:IIIb-D3`: decomposition of `FlatLimit` on the concrete sequence (source 4821-4916)

`FlatLimit` has four clauses.  The first (`‖𝒦^flat - a_μΛ‖`) is the Newton-field/Taylor comparison of
4863-4870 combined with the scalar flat estimates (`FlatCoefficientC`, `FlatScalarEstimateC`,
`FlatAllMomentsC`, `FlatClassAmplitudeC`) at the concrete flat setting; the other three are the
bounds on `a_μ` and `Λ` and the identity `Λ(a_μ) = unitResp + O(·)` of 4709-4730 (`a0Unit`).
`flatLimit_of_parts` proves `FlatLimit` from the two named parts (single `C`, `k`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Clause 1 of `FlatLimit` (source 4821-4845, proof 4846-4916). -/
def FlatLimitKflatPart (D : SeqData) (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) :
    Prop :=
  ∃ (ωcan : ℕ → ℝ) (C : ℝ) (γ' : ℝ) (N k₀ : ℕ), Tendsto ωcan atTop (𝓝 0) ∧ 0 < C ∧
    0 < γ' ∧ γ' < D.Pl.eigenvalue.re ∧ ∀ k ≥ k₀, ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ‖((concreteReturnSeq D G).ops n z).Kflat -
          ((concreteReturnSeq D G).ops n z).Lam.smulRight ((concreteReturnSeq D G).ops n z).aMu‖ ≤
        C * Astar D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
            (planarJ D.Pl) (D.σ₀ : ℂ)) D.σ₀ ((concreteReturnSeq D G).ν n) z *
          ((concreteReturnSeq D G).ν n + ωcan n + ((concreteReturnSeq D G).ν n)⁻¹ ^ k *
              Real.exp (-γ' / Real.sqrt ((concreteReturnSeq D G).ν n))
            + ((concreteReturnSeq D G).ν n)⁻¹ ^ k *
              Real.exp (-(4 * D.K.as / 5) / (concreteReturnSeq D G).ν n))

/-- Clauses 2-4 of `FlatLimit` (source 4709-4730, 4846-4916). -/
def FlatLimitCoefPart (D : SeqData) (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) :
    Prop :=
  ∃ (C b : ℝ) (N k₀ : ℕ), 0 < C ∧ 0 < b ∧ ∀ k ≥ k₀, ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ‖((concreteReturnSeq D G).ops n z).aMu‖ ≤ C ∧
      ‖((concreteReturnSeq D G).ops n z).Lam‖ ≤
        C * Astar D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
            (planarJ D.Pl) (D.σ₀ : ℂ)) D.σ₀ ((concreteReturnSeq D G).ν n) z ∧
      |((concreteReturnSeq D G).ops n z).Lam ((concreteReturnSeq D G).ops n z).aMu -
          unitResp D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
            (planarJ D.Pl))
            (epsCube D.Pl.eigenvalue.re D.Pl.kappa D.σ₀ (mellinC D.Pl.eigenvalue
              D.Pl.strainCoupling (planarJ D.Pl) (D.σ₀ : ℂ)) ((concreteReturnSeq D G).ν n))
            ((concreteReturnSeq D G).ν n) (muWin D.σ₀ ((concreteReturnSeq D G).ν n) z)| ≤
        C * Astar D.Pl.eigenvalue D.Pl.kappa (mellinC D.Pl.eigenvalue D.Pl.strainCoupling
            (planarJ D.Pl) (D.σ₀ : ℂ)) D.σ₀ ((concreteReturnSeq D G).ν n) z *
          ((concreteReturnSeq D G).ν n)⁻¹ ^ k * Real.exp (-b / (concreteReturnSeq D G).ν n)

lemma aux1 {x C1 C A : ℝ} (hx : 0 ≤ x) (hC1 : 0 < C1) (hC : C1 ≤ C) (h : x ≤ C1 * A) :
    x ≤ C * A := by
  have hY : 0 ≤ A := by
    by_contra hneg
    push Not at hneg
    nlinarith
  nlinarith

lemma aux2 {x C1 C A B : ℝ} (hx : 0 ≤ x) (hC1 : 0 < C1) (hC : C1 ≤ C) (h : x ≤ C1 * A * B) :
    x ≤ C * A * B := by
  rw [mul_assoc] at h ⊢
  exact aux1 hx hC1 hC h

lemma aux3 {x C1 C A B E : ℝ} (hx : 0 ≤ x) (hC1 : 0 < C1) (hC : C1 ≤ C) (h : x ≤ C1 * A * B * E) :
    x ≤ C * A * B * E := by
  rw [mul_assoc, mul_assoc] at h ⊢
  exact aux1 hx hC1 hC h

theorem flatLimit_of_parts (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))
    (h1 : FlatLimitKflatPart D G) (h2 : FlatLimitCoefPart D G) :
    FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
      (planarJ D.Pl) D.σ₀ D.K.as := by
  obtain ⟨ω, C1, γ', N1, k1, hω, hC1, hγ, hγ2, H1⟩ := h1
  obtain ⟨C2, b, N2, k2, hC2, hb, H2⟩ := h2
  refine ⟨ω, max C1 C2, max k1 k2, γ', b, max N1 N2, hω, hγ, hγ2, hb, ?_⟩
  intro n hn z hz
  have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right _ _) hn
  have a := H1 (max k1 k2) (le_max_left _ _) n hn1 z hz
  obtain ⟨b1, b2, b4⟩ := H2 (max k1 k2) (le_max_right _ _) n hn2 z hz
  exact ⟨aux2 (norm_nonneg _) hC1 (le_max_left _ _) a, b1.trans (le_max_right _ _),
    aux1 (norm_nonneg _) hC2 (le_max_right _ _) b2,
    aux3 (abs_nonneg _) hC2 (le_max_right _ _) b4⟩

end UnforcedLeray.Short.PartIIIb.Concrete
