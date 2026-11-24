import UnforcedLeray.Short.PartI.Sub.T08Statement

/-!
# Part I, task `PartI:T08/7` (`JetTransportBound`): decomposition

Source: `the November 2 reference manuscript` lines 352-358 (differentiated
transport: `‖[D^j, e·∇]e‖₂ ≤ C_j ‖∇e‖_∞ ‖D^j e‖₂`, constants independent of the period).

The bracket `(V+f)·∇(V+f) - V·∇V` is split as `linTerm V f + (f·∇)f`, where
`linTerm V f = adv(V+f) - adv V - adv f = (V·∇)f + (f·∇)V`. The split of the pairing is the leaf
`JetSplit`; the two bounds are the leaves `JTLin` (cross terms, `M_i √J_{j+1-i} √J_j`) and `JTQuad`
(the quadratic term, `G J_j`). `jetTransportBound_of` assembles `JetTransportBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- The hypotheses of `JetTransportBound` on `(c, V, f, G, M)`: `c ≥ 1`; `V` smooth, `c`-periodic,
divergence free; `f` smooth periodic with all words in `L²(cell)`, divergence free, with bounded
words, `|∂_β f_k| ≤ G`; `|∂_w V_k| ≤ M_{|w|}`. -/
def JTHyp (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ) : Prop :=
  1 ≤ c ∧ ContDiff ℝ ∞ V ∧ Cyl.IsPeriodic c V ∧ (∀ z : Plane, Cyl.divergence V z = 0) ∧
    CellSmoothL2 c f ∧ (∀ z : Plane, Cyl.divergence f z = 0) ∧
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w f k z| ≤ M) ∧
    (∀ (β : Bool) (k : Fin 2) (z : Plane), |wordComp [β] f k z| ≤ G) ∧
    (∀ (w : List Bool) (k : Fin 2) (z : Plane), |wordComp w V k z| ≤ M w.length)

/-- Integrability on the centred cell of the integrand of `jetPair c j f g`. -/
def JetInt (c : ℝ) (j : ℕ) (f g : Plane → Vec) : Prop :=
  Integrable (fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g k z)
    (Cyl.cellμ c)

/-- The bilinear cross part `(V·∇)f + (f·∇)V` of the bracket, by polarization of the advection. -/
def linTerm (V f : Plane → Vec) : Plane → Vec :=
  fun z => Train.advection (fun x => V x + f x) z - Train.advection V z - Train.advection f z

/-- **Leaf (additivity of the jet pairing)** (lines 352-358, linearity of `⟨D^j f, D^j ·⟩`): for
smooth `g₁, g₂` with integrable pairing integrands,
`⟨D^j f, D^j(g₁+g₂)⟩ = ⟨D^j f, D^j g₁⟩ + ⟨D^j f, D^j g₂⟩`. Route: `derivWord_add_smooth`
(`Tasks/DifferentiatedEnergy/ForcingIBP.lean`) on the components (`(g₁+g₂) k = g₁ k + g₂ k`),
`mul_add`, `Finset.sum_add_distrib`, `integral_add`. -/
def JetSplit : Prop :=
  ∀ (c : ℝ) (j : ℕ) (f g₁ g₂ : Plane → Vec), ContDiff ℝ ∞ g₁ → ContDiff ℝ ∞ g₂ →
    JetInt c j f g₁ → JetInt c j f g₂ →
    jetPair c j f (fun z => g₁ z + g₂ z) = jetPair c j f g₁ + jetPair c j f g₂

/-- **Leaf (cross terms)** (lines 352-358): `⟨D^j f, D^j((V·∇)f + (f·∇)V)⟩` is bounded by
`A ∑_{i=1}^{j+1} M_i ‖D^{j+1-i} f‖ ‖D^j f‖` (Leibniz over `2^j` splittings of the word, `V` and `f`
bounded; `(V·∇)D^j f` pairs to zero by `div V = 0`; Cauchy-Schwarz). -/
def JTLin : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ),
    JTHyp c V f G M → ContDiff ℝ ∞ (linTerm V f) ∧ JetInt c j f (linTerm V f) ∧
      |jetPair c j f (linTerm V f)| ≤
        A * ∑ i ∈ Finset.Icc 1 (j + 1),
          M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f)

/-- **Leaf (quadratic term)** (lines 352-358): `⟨D^j f, D^j((f·∇)f)⟩` is bounded by
`A G ‖D^j f‖²`, `A` independent of `c ≥ 1` (`(f·∇)D^j f` pairs to zero; the commutator terms are
bounded by Hölder and the period-independent `CylGN`, `PartI:T07`). -/
def JTQuad : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ),
    JTHyp c V f G M → ContDiff ℝ ∞ (Train.advection f) ∧ JetInt c j f (Train.advection f) ∧
      |jetPair c j f (Train.advection f)| ≤ A * (G * jetEnergy c j f)

theorem jetTransportBound_of (hS : JetSplit) (hL : JTLin) (hQ : JTQuad) : JetTransportBound := by
  intro j
  obtain ⟨A₁, hA₁, h₁⟩ := hL j
  obtain ⟨A₂, hA₂, h₂⟩ := hQ j
  refine ⟨A₁ + A₂, add_nonneg hA₁ hA₂, ?_⟩
  intro c hc V f hV hVp hVd hf hfd hfb G M hG hM
  have H : JTHyp c V f G M := ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hM⟩
  obtain ⟨s₁, i₁, b₁⟩ := h₁ c V f G M H
  obtain ⟨s₂, i₂, b₂⟩ := h₂ c V f G M H
  have e : (fun z => Train.advection (fun x => V x + f x) z - Train.advection V z) =
      fun z => linTerm V f z + Train.advection f z := by
    funext z; simp only [linTerm]; abel
  rw [e, hS c j f _ _ s₁ s₂ i₁ i₂]
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG true 0 (0, 0))
  have hM0 : ∀ i, 0 ≤ M i := fun i =>
    le_trans (abs_nonneg _) (by simpa using hM (List.replicate i true) 0 (0, 0))
  have hT : 0 ≤ G * jetEnergy c j f := mul_nonneg hG0 (jetEnergy_nonneg c j f)
  have hSm : 0 ≤ ∑ i ∈ Finset.Icc 1 (j + 1),
      M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f) :=
    Finset.sum_nonneg fun i _ => by have := hM0 i; positivity
  calc |jetPair c j f (linTerm V f) + jetPair c j f (Train.advection f)|
      ≤ |jetPair c j f (linTerm V f)| + |jetPair c j f (Train.advection f)| := abs_add_le _ _
    _ ≤ A₁ * ∑ i ∈ Finset.Icc 1 (j + 1),
          M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f) +
        A₂ * (G * jetEnergy c j f) := add_le_add b₁ b₂
    _ ≤ _ := by nlinarith [mul_nonneg hA₁ hT, mul_nonneg hA₂ hSm]

end UnforcedLeray.Short.PartI
