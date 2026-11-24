import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform
import UnforcedLeray.Short.PartIIIb.Proofs.Young.FrozenPairC
import UnforcedLeray.Short.PartIIIb.Proofs.Young.DuhamelC
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks

/-!
# `ORG:D3/2/G1`: group G1 (young map, state at `H`, later output)

Source: `the November 2 reference manuscript` (73 pp): finite band 4386-4431,
uniform tested estimate 4432-4460 (`eq:young-later-output` 4454), frozen pair
`eq:young-frozen-pair` 4407-4412, young source theorem 4461-4553 (state at `H` 4501-4508).

Plan.  `GroupYoung D` has two conjuncts (state at `H`; later output) for every actual flat
sequence `S` (`FlatUnif.ForActual`).

* the state at `H` follows from `YoungSourceFacts` (frozen pair + block inputs from Part III-a,
  `G1/1`), `youngFrozenPair_actual` (`G1/2`), the window-uniform Duhamel bound
  `youngDuhamelUnif` (`G1/3`, constants independent of `μ`: the constants of
  `youngDuhamelC_holds` are `|C|(1+2Cb²)`, with `C` from the frozen pair, so they do not see `μ`)
  and the admissibility of `g_B` (`G1/4`), plus the elementary bounds
  `‖a_±(f)‖ ≤ Cb ‖f‖_𝓘`, `‖𝒰(H,0)q_{+,0}‖ ≤ C ‖F_+(H,0)‖` (frozen pair at `t = 0`);
* the later output is `LaterOutputSource D` (`G1/5`, from `eq:ct-absolute-impulse` 3277 and
  `eq:young-later-output`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G1

/-- **Source facts of the finite band** (source 4376-4406, from `prop:short-full-clock` and the
per-frame facts `IIIa.PerFrameFactsAll`), for every actual flat sequence and `Σ = 2`, `α = 1.1`:
for large `n` the frozen pair and its dual are bounded on `0 ≤ s ≤ 2/ν` (heat-scaled endpoint maps
have uniform norms, 4376-4380), and the retained block estimates hold with a residual
`δ_n ≤ C ν_n²` (4382-4384, 4396-4406; `c = ν⁻²`). -/
def YoungSourceFacts (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (N0 : ℕ) (δ : ℕ → ℝ),
    (∃ C : ℝ, ∀ n ≥ N0, ∀ s ∈ Icc (0 : ℝ) (2 / nu D n), ∀ j : Bool,
      ‖(S n).pk.q j s‖ ≤ C ∧ ‖(S n).pk.ell j s‖ ≤ C) ∧
    (∃ C : ℝ, ∀ n ≥ N0, 0 ≤ δ n ∧ δ n ≤ C * nu D n ^ 2) ∧
    RetainedBlocks (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1 δ

/-- The later output (second conjunct of `GroupYoung`; source 4432-4460, `eq:young-later-output`
4454, from `eq:ct-absolute-impulse` 3277 and `prop:short-full-clock`). -/
def LaterOutputSource (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
        (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) k B ≤
          C * (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
            (S n).c) * nu D n ^ k * (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
              ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖ +
              testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
                ((S n).gB B))

/-- `g_B` is an admissible Duhamel forcing for the young source theorem at `α = 1.1`
(source 4463-4471, 4480-4487, 4597-4612): supported in `0 < s ≤ 1.1/ν` and with the four
integrability conditions of `YoungDuhamelC`, for all window points. -/
def GBAdmissible (D : SeqData) : Prop :=
  ForActual D fun S => ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
    (∀ t, 1.1 / nu D n < t → (S n).gB B t = 0) ∧ (∀ t, t ≤ 0 → (S n).gB B t = 0) ∧
    Integrable (fun t : ℝ => ((t : ℂ) ^ (D.mu n z : ℂ)) •
      ((S n).pk.Uev (2 / nu D n) t ((S n).gB B t))) (volume.restrict (Ioc 0 (2 / nu D n))) ∧
    Integrable (fun t : ℝ => ((t : ℂ) ^ (D.mu n z : ℂ)) *
      (Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) t 0)⁻¹ * ((S n).pk.ell true t) ((S n).gB B t))
      (volume.restrict (Ioc 0 (1.1 / nu D n))) ∧
    Integrable (fun t : ℝ => ((t : ℂ) ^ (D.mu n z : ℂ)) *
      (Fpm false D.Pl.eigenvalue D.Pl.kappa (nu D n) t 0)⁻¹ * ((S n).pk.ell false t) ((S n).gB B t))
      (volume.restrict (Ioc 0 (1.1 / nu D n))) ∧
    Integrable (fun t : ℝ => t ^ (D.mu n z) * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) t 0‖⁻¹ *
      ‖(S n).gB B t‖) (volume.restrict (Ioc 0 (1.1 / nu D n)))

/-- `YoungDuhamelC` with the constant uniform in `μ ∈ ℂ` (source 4461-4508, "uniformly for
`μ ∈ K`" 4825): same body, `∃ C N` before `∀ μ`. -/
def YoungDuhamelUnifC (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X)
    (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  (∀ n, YoungLaws (pk n) (conjX n)) → YoungHyp ν lam Sg α → YoungBounded pk ν Sg →
    YoungFrozenPair pk ν lam κ Sg α →
    ∃ (C : ℝ) (N : ℕ), ∀ μ : ℂ, ∀ n ≥ N, ∀ f : ℝ → (pk n).X,
      (∀ t, α / ν n < t → f t = 0) → (∀ t, t ≤ 0 → f t = 0) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t))) (volume.restrict (Ioc 0 (Sg / ν n))) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm true lam κ (ν n) t 0)⁻¹ * ((pk n).ell true t) (f t))
        (volume.restrict (Ioc 0 (α / ν n))) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm false lam κ (ν n) t 0)⁻¹ * ((pk n).ell false t) (f t))
        (volume.restrict (Ioc 0 (α / ν n))) →
      Integrable (fun t : ℝ => t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖)
        (volume.restrict (Ioc 0 (α / ν n))) →
      ‖duhamel (pk n) μ f (Sg / ν n) -
          (aFrozen (pk n) true lam κ (ν n) μ (α / ν n) f • (pk n).Uev (Sg / ν n) 0 ((pk n).q true 0)
            + aFrozen (pk n) false lam κ (ν n) μ (α / ν n) f •
                conjX n ((pk n).Uev (Sg / ν n) 0 ((pk n).q true 0)))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ * testedNorm (pk n) lam κ (ν n) μ (α / ν n) f

/-- Shifting the index: `YoungFrozenPair` of the shifted sequence gives the original. -/
theorem youngFrozenPair_of_shift (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (N0 : ℕ)
    (h : YoungFrozenPair (fun n => pk (n + N0)) (fun n => ν (n + N0)) lam κ Sg α) :
    YoungFrozenPair pk ν lam κ Sg α := by
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + N0, fun n hn t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + N0 := ⟨n - N0, by omega⟩
  exact hC m (by omega) t ht

/-- The block estimates of the shifted sequence give the original. -/
theorem youngBlockEstimates_of_shift (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (N0 : ℕ) (h : YoungBlockEstimates (fun n => pk (n + N0)) (fun n => ν (n + N0)) lam κ Sg α) :
    YoungBlockEstimates pk ν lam κ Sg α := by
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + N0, fun n hn t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + N0 := ⟨n - N0, by omega⟩
  exact hC m (by omega) t ht

end G1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
