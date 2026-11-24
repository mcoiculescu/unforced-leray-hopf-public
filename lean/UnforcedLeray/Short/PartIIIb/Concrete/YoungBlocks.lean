import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Block estimates of the frozen pair: retained inputs and the Gronwall target (source 4376-4411)

`ConcreteYF.YoungBlockEstimates` (`YoungFlat.lean`) is the Gronwall consequence of the retained block
estimates of Proposition `short-full-clock` (PartIII-a).  This file

* defines the residual `δ_c`, `η_ν` (source 4390-4395);
* defines the normalised block coordinates of a solution `s ↦ 𝒰(s,t)x`: the amplitudes
  `A_j(s) = ℓ_{j,s}𝒰(s,t)x / F_j(s,t)` and the complement `R(s) = ‖P_{c,s}𝒰(s,t)x‖/|F_+(s,t)|`
  (source 4396-4397: "divide the two amplitudes by `F_±(s,t)` and the complement by their common
  modulus");
* states the retained block estimates (`RetainedBlocks`, source 4382-4384, 4396-4406) in integral
  form (the form in which the variation of constants for the complement and the amplitude
  equations is used; continuity is the strong continuity of the weak flow);
* links the `YoungPkg` to the actual train evolution of PartIII-a (`IsTrainPkg`, via
  `Defs.IsLinearisedFlow`) and states the source fact producing the retained estimates from
  the full clock (`TrainBlockInput`);
* states the real-analysis Gronwall step (`BlockGronwall`, source 4396-4406) and the conclusion
  (`BlocksFromRetained`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

/-! ## Residuals (source 4390-4395) -/

/-- `δ_base = P_ν e^{C_Σ/ν - b_Σ c²}`; `Pn` stands for the polynomial `P_ν` in `ν⁻¹`. -/
def deltaBase (Pn CS bS ν c : ℝ) : ℝ := Pn * Real.exp (CS / ν - bS * c ^ 2)

/-- `δ_c = C_Σ (c⁻² + δ_base)`. -/
def deltaC (Pn CS bS ν c : ℝ) : ℝ := CS * (c⁻¹ ^ 2 + deltaBase Pn CS bS ν c)

/-- `η_ν = ν + δ_c/ν`. -/
def etaNu (ν δ : ℝ) : ℝ := ν + δ / ν

/-- `η_ν = O(ν)`, i.e. `0 ≤ δ_n ≤ C ν_n²` (source 4392-4395). -/
def DeltaSmall (ν δ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n, 0 ≤ δ n ∧ δ n ≤ C * ν n ^ 2

/-- `δ_c ≤ C ν²` for `c = ν⁻²`, `P_ν = K ν^{-p}` (a polynomial in `ν⁻¹`), `b_Σ > 0`, for small `ν`. -/
def DeltaCSmall : Prop :=
  ∀ (CS bS K : ℝ) (p : ℕ), 0 < bS → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    deltaC (K * ν⁻¹ ^ p) CS bS ν (ν ^ (-2 : ℝ)) ≤ C * ν ^ 2

/-! ## Normalised block coordinates -/

/-- Gram normalisation `ℓ_{i,s} q_{j,s} = δ_ij`. -/
def GramLaw (pk : YoungPkg) : Prop :=
  ∀ s i j, pk.ell i s (pk.q j s) = if i = j then 1 else 0

/-- Amplitude `A_j(s) = ℓ_{j,s}(𝒰(s,t)x)/F_j(s,t)`. -/
def ampN (pk : YoungPkg) (lam κ : ℂ) (ν t : ℝ) (x : pk.X) (j : Bool) (s : ℝ) : ℂ :=
  pk.ell j s (pk.Uev s t x) / Fpm j lam κ ν s t

/-- Complement `R(s) = ‖P_{c,s}𝒰(s,t)x‖/|F_+(s,t)|`. -/
def cmpN (pk : YoungPkg) (lam κ : ℂ) (ν t : ℝ) (x : pk.X) (s : ℝ) : ℝ :=
  ‖Pc pk s (pk.Uev s t x)‖ / ‖Fpm true lam κ ν s t‖

/-- The retained block estimates (source 4382-4384, 4396-4406), integral form, for the sequence
`pk n`, on `t ≤ s ≤ H = Σ/ν`, `0 ≤ t ≤ T_f = α/ν`: with `δ = δ_c`, `g > 0`,
complement: `R(s) ≤ C e^{-g(s-t)}R(t) + C(ν+δ)∫_t^s e^{-g(s-r)}(|A_+|+|A_-|)(r)dr`;
amplitudes: `|A_j(s)-A_j(t)| ≤ ∫_t^s [Cδ(|A_+|+|A_-|) + C(ν+δ)R](r)dr`;
plus continuity of `A_±`, `R` (strong continuity of the weak flow). -/
def RetainedBlocks (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) : Prop :=
  ∃ (C g : ℝ) (N : ℕ), 0 < C ∧ 0 < g ∧ ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n), ∀ x : (pk n).X,
    (∀ j, ContinuousOn (ampN (pk n) lam κ (ν n) t x j) (Icc t (Sg / ν n))) ∧
    ContinuousOn (cmpN (pk n) lam κ (ν n) t x) (Icc t (Sg / ν n)) ∧
    (∀ s ∈ Icc t (Sg / ν n),
      cmpN (pk n) lam κ (ν n) t x s ≤
        C * Real.exp (-g * (s - t)) * cmpN (pk n) lam κ (ν n) t x t +
        C * (ν n + δ n) * ∫ r in t..s, Real.exp (-g * (s - r)) *
          (‖ampN (pk n) lam κ (ν n) t x true r‖ + ‖ampN (pk n) lam κ (ν n) t x false r‖)) ∧
    (∀ j, ∀ s ∈ Icc t (Sg / ν n),
      ‖ampN (pk n) lam κ (ν n) t x j s - ampN (pk n) lam κ (ν n) t x j t‖ ≤
        ∫ r in t..s, (C * δ n *
            (‖ampN (pk n) lam κ (ν n) t x true r‖ + ‖ampN (pk n) lam κ (ν n) t x false r‖) +
          C * (ν n + δ n) * cmpN (pk n) lam κ (ν n) t x r))

/-! ## Link with the actual train evolution (PartIII-a) -/

/-- The evolution `Uev` of the package is the actual linearised train flow of
`Short.IIIa.IsLinearisedFlow` for the embedding `emb : X → (ℝ×ℝ → ℂ)` of `X_{m,c}` into planar
vorticities: for each age `t ≥ 0` and datum `x`, `s ↦ emb(𝒰(s,t)x)` is a weak flow from `emb x`. -/
def IsTrainPkg (pk : YoungPkg) (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (emb : pk.X → ℝ × ℝ → ℂ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : pk.X, ∃ u,
    UnforcedLeray.Short.IIIa.IsLinearisedFlow ν c m tr t (emb x) (fun s => emb (pk.Uev s t x)) u

/-- Source fact (4376-4384, 4396-4406; from `prop:short-full-clock`, `FullClock.lean`): for packages
that are train evolutions with `c = ν⁻²`, the retained block estimates hold with the residual
`δ_c`. -/
def TrainBlockInput (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) (m : ℝ)
    (tr : ∀ n, UnforcedLeray.B0140.TrainSol (ν n) (ν n ^ (-2 : ℝ)))
    (emb : ∀ n, (pk n).X → ℝ × ℝ → ℂ) : Prop :=
  (∀ n, IsTrainPkg (pk n) (ν n) (ν n ^ (-2 : ℝ)) m (tr n) (emb n)) →
    RetainedBlocks pk ν lam κ Sg α δ

/-! ## The Gronwall step and the conclusion -/

/-- Abstract Gronwall step (source 4396-4406), for continuous `α_±`, `ρ ≥ 0` on `[t, t+L]`
satisfying the two integral inequalities with `ε = δ_c`, `k = ν + δ_c`, `εL, k, k²L ≤ B`:
(1) `|α_+|+|α_-|` is bounded by `K(|α_+(t)|+|α_-(t)|+ρ(t))`;
(2) `|α_j(s)-α_j(t)| ≤ K(εL + k + k²L)(|α_+(t)|+|α_-(t)|+ρ(t))`;
(3) `ρ(s) ≤ K(e^{-g(s-t)}ρ(t) + k(|α_+(t)|+|α_-(t)|+ρ(t)))`. -/
def BlockGronwall : Prop :=
  ∀ (C g B : ℝ), 0 < C → 0 < g → 0 < B → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (ε k L t : ℝ) (α : Bool → ℝ → ℂ) (ρ : ℝ → ℝ),
      0 ≤ ε → 0 ≤ k → 0 ≤ L → ε * L ≤ B → k ≤ B → k ^ 2 * L ≤ B →
      (∀ s, 0 ≤ ρ s) →
      (∀ j, ContinuousOn (α j) (Icc t (t + L))) → ContinuousOn ρ (Icc t (t + L)) →
      (∀ s ∈ Icc t (t + L), ρ s ≤ C * Real.exp (-g * (s - t)) * ρ t +
          C * k * ∫ r in t..s, Real.exp (-g * (s - r)) * (‖α true r‖ + ‖α false r‖)) →
      (∀ j, ∀ s ∈ Icc t (t + L), ‖α j s - α j t‖ ≤
          ∫ r in t..s, (C * ε * (‖α true r‖ + ‖α false r‖) + C * k * ρ r)) →
      ∀ s ∈ Icc t (t + L),
        ‖α true s‖ + ‖α false s‖ ≤ K * (‖α true t‖ + ‖α false t‖ + ρ t) ∧
        (∀ j, ‖α j s - α j t‖ ≤ K * (ε * L + k + k ^ 2 * L) * (‖α true t‖ + ‖α false t‖ + ρ t)) ∧
        ρ s ≤ K * (Real.exp (-g * (s - t)) * ρ t + k * (‖α true t‖ + ‖α false t‖ + ρ t))

/-- The four parts of `YoungBlockEstimates` as separate statements (each with its own `C, N`). -/
def YBE1 (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n), ∀ i j : Bool,
      ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t)) -
          (if i = j then Fpm j lam κ (ν n) (Sg / ν n) t else 0)‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖

def YBE2 (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n), ∀ j : Bool,
    ‖Pc (pk n) (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖

def YBE3 (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n), ∀ (i : Bool) (y : (pk n).X),
    ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t (Pc (pk n) t y))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖y‖

def YBE4 (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n),
    ‖(Pc (pk n) (Sg / ν n)).comp (((pk n).Uev (Sg / ν n) t).comp (Pc (pk n) t))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖

/-- Standing hypotheses of the conclusion. `refl` is the reflexivity `𝒰(s,s) = 1` of the actual
train evolution `𝒰(s,t)` (source 4352; `YoungLaws.refl`); it ties the normalised block
coordinates of `s ↦ 𝒰(s,t)x` at `s = t` to `x`: `A_j(t) = ℓ_{j,t}x`, `R(t) = ‖P_{c,t}x‖`
(source 4388-4390, with `F_±(t,t) = 1`). -/
structure BlockSetup (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) : Prop where
  hyp : YoungHyp ν lam Sg α
  gram : ∀ n, GramLaw (pk n)
  bdd : YoungBounded pk ν Sg
  small : DeltaSmall ν δ
  ret : RetainedBlocks pk ν lam κ Sg α δ
  refl : ∀ n s, (pk n).Uev s s = ContinuousLinearMap.id ℂ (pk n).X

/-- **Target**: the Gronwall consequence of the retained block estimates is
`YoungBlockEstimates` (source 4396-4411). -/
def BlocksFromRetained (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) : Prop :=
  BlockSetup pk ν lam κ Sg α δ → YoungBlockEstimates pk ν lam κ Sg α

/-- Full chain: train evolution plus the source fact give `YoungBlockEstimates`. The reflexivity
hypothesis `𝒰(s,s) = 1` is `YoungLaws.refl` of every package (the evolution of source 4352). -/
def BlocksFromTrain (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) (m : ℝ)
    (tr : ∀ n, UnforcedLeray.B0140.TrainSol (ν n) (ν n ^ (-2 : ℝ)))
    (emb : ∀ n, (pk n).X → ℝ × ℝ → ℂ) : Prop :=
  YoungHyp ν lam Sg α → (∀ n, GramLaw (pk n)) → YoungBounded pk ν Sg → DeltaSmall ν δ →
    (∀ n s, (pk n).Uev s s = ContinuousLinearMap.id ℂ (pk n).X) →
    TrainBlockInput pk ν lam κ Sg α δ m tr emb →
    (∀ n, IsTrainPkg (pk n) (ν n) (ν n ^ (-2 : ℝ)) m (tr n) (emb n)) →
    YoungBlockEstimates pk ν lam κ Sg α

/-- The chain is the composition of the source fact and `BlocksFromRetained` (proved here). -/
theorem blocksFromTrain_of (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ)
    (m : ℝ) (tr : ∀ n, UnforcedLeray.B0140.TrainSol (ν n) (ν n ^ (-2 : ℝ)))
    (emb : ∀ n, (pk n).X → ℝ × ℝ → ℂ) (h : BlocksFromRetained pk ν lam κ Sg α δ) :
    BlocksFromTrain pk ν lam κ Sg α δ m tr emb := by
  intro hh hg hb hs hrefl hT hP
  exact h ⟨hh, hg, hb, hs, hT hP, hrefl⟩

/-- `BlockSetup` from the structural laws of the packages: `gram` and `refl` are
`YoungLaws.gram`/`YoungLaws.refl` (Gram normalisation `ℓ_{i,s}q_{j,s} = δ_ij` of source
4354-4355 and reflexivity of the evolution of source 4352). -/
theorem blockSetup_of_laws (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X) (ν : ℕ → ℝ)
    (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ) (hL : ∀ n, YoungLaws (pk n) (conjX n))
    (hh : YoungHyp ν lam Sg α) (hb : YoungBounded pk ν Sg) (hs : DeltaSmall ν δ)
    (hr : RetainedBlocks pk ν lam κ Sg α δ) : BlockSetup pk ν lam κ Sg α δ :=
  ⟨hh, fun n => (hL n).gram, hb, hs, hr, fun n => (hL n).refl⟩

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
