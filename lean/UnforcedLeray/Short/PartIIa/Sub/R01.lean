import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Sub.R02

/-!
# Part II-a, task `PartII-a:R01`: the early residual table (decomposition, audit file)

Source of record: `the November 2 reference manuscript`, lines 1294-1297 ("at zero
age the integrands are bounded"), with Lemma `sct:heat` (lines 437-481: `sct:fluctuation` 439-446,
`sct:expansion` 447-459, read at ages `0 < s ≤ 1`).

`RingEarlyBound` (`StatementsRing.lean`, line 166) has no hypotheses and is a statement about the
five coefficients `A₁, A₂, B₁, B₂, B₃` of `B0188` (`eq:st18-t00192`).  This file

1. splits it into five statements `RingEarlyA1, RingEarlyA2, RingEarlyB1, RingEarlyB2, RingEarlyB3`
   (one coefficient each) and proves `ringEarlyBound_of` (take `ν₀ = min`, `C = max (…) 0`,
   `d = max`; the bounds are monotone in `B`);
2. states the two ingredients from which every block follows by algebra: the zero-age bounds on the
   mixed jets `∂_s^ℓ ∂_η^a ∂_q^b` of the stream profile `ψ` and of the pressure profile `p`
   (`EarlyStreamProfile`, `EarlyPressureProfile`; the zero-age readings of Part I's
   `TrainFluctuationDecay` and `TrainMeanExpansion`);
3. defines the class `EarlyBdd ρ X` of zero-age bounded families of profiles and the closure
   properties `EarlyCalculus` (sums, products, `∂_η, ∂_q, ∂_s`, `K = η∂_η + 2s∂_s`, multiplication
   by `η`, `s`, `ν`): the coefficients are built from `ψ, p` by these operations, so each block is
   a composition of closure lemmas (`earlyGroupBdd` ⇒ `EarlyStmt`, proved here:
   `earlyStmt_of_groupBdd`).

Why the table is true (source 1294-1297): at ages `0 < s ≤ 1` the factors `e^{-κνs/c²} ≤ 1`, the
mean stream is bounded by `(1+s)^{…} ≤ 2^{…}` and every polynomial factor in `s` is `≤ 1`; each
coefficient is a polynomial expression in the derivatives of `ψ, p` of order at most `5` with
coefficients polynomial in `η, s, ν`, and the `η` factors are absorbed by raising the weight.

WARNING (same as `PartI:T01`, `PartII-a:R02`): the time smoothness of the stream `ψ`
(`TrainStreamSmooth`) is not a field of `B0140.IsTrain`; it enters through `LateProfileSmooth`
(`Sub/R02.lean`; `lateProfileSmooth_of` in `Tasks/R02/ProfileSmooth.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-! ### Blocks of the early table -/

/-- The four bounds for one coefficient `X` at a point `x`: `X`, `∂_η X`, `∂_q X`, `(K+3) X`,
each weighted by `⟨η⟩^{2m}` and bounded by `B`. -/
def EarlyGrp (m : ℕ) (B : ℝ) (X : ProfilePoint → ℝ) (x : ProfilePoint) : Prop :=
  (1 + x.2.1 ^ 2) ^ m * |X x| ≤ B ∧
  (1 + x.2.1 ^ 2) ^ m * |partialEta X x| ≤ B ∧
  (1 + x.2.1 ^ 2) ^ m * |partialQ X x| ≤ B ∧
  (1 + x.2.1 ^ 2) ^ m * |ageShift 3 X x| ≤ B

theorem EarlyGrp.mono {m : ℕ} {B B' : ℝ} {X : ProfilePoint → ℝ} {x : ProfilePoint}
    (h : B ≤ B') (hg : EarlyGrp m B X x) : EarlyGrp m B' X x :=
  ⟨hg.1.trans h, hg.2.1.trans h, hg.2.2.1.trans h, hg.2.2.2.trans h⟩

/-- A family of profiles `X ν ψ p` built from the stream and pressure profile of an exact train. -/
abbrev ProfFam : Type := ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ

/-- The shape of an early-table statement for the coefficient family `X`: for `0 < s ≤ 1` the
group of four weighted bounds holds with `B = C (1 + c + ν⁻¹)^d`, `c = ν^{-ρ}`. -/
def EarlyStmt (X : ProfFam) : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ),
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
        EarlyGrp m (polyConst C d ν (ν ^ (-ρ))) (X ν ψ p) x

/-- **Early table, `A₁` block** (source lines 1294-1297). -/
def RingEarlyA1 : Prop := EarlyStmt fun ν ψ p => coeffA₁ ν ψ p

/-- **Early table, `A₂` block** (source lines 1294-1297). -/
def RingEarlyA2 : Prop := EarlyStmt fun ν ψ _ => coeffA₂ ν ψ

/-- **Early table, `B₁` block** (source lines 1294-1297). -/
def RingEarlyB1 : Prop := EarlyStmt fun ν ψ _ => coeffB₁ ν ψ

/-- **Early table, `B₂` block** (source lines 1294-1297). -/
def RingEarlyB2 : Prop := EarlyStmt fun ν ψ _ => coeffB₂ ν ψ

/-- **Early table, `B₃` block** (source lines 1294-1297). -/
def RingEarlyB3 : Prop := EarlyStmt fun ν ψ _ => coeffB₃ ν ψ

/-- **`PartII-a:R01`, conditional on the five coefficient blocks.** -/
theorem ringEarlyBound_of (h1 : RingEarlyA1) (h2 : RingEarlyA2) (h3 : RingEarlyB1)
    (h4 : RingEarlyB2) (h5 : RingEarlyB3) : RingEarlyBound := by
  intro ρ m hρ
  obtain ⟨ν₁, hν₁, C₁, d₁, H₁⟩ := h1 ρ m hρ
  obtain ⟨ν₂, hν₂, C₂, d₂, H₂⟩ := h2 ρ m hρ
  obtain ⟨ν₃, hν₃, C₃, d₃, H₃⟩ := h3 ρ m hρ
  obtain ⟨ν₄, hν₄, C₄, d₄, H₄⟩ := h4 ρ m hρ
  obtain ⟨ν₅, hν₅, C₅, d₅, H₅⟩ := h5 ρ m hρ
  refine ⟨min (min (min (min ν₁ ν₂) ν₃) ν₄) ν₅,
    lt_min (lt_min (lt_min (lt_min hν₁ hν₂) hν₃) hν₄) hν₅,
    max (max (max (max (max C₁ C₂) C₃) C₄) C₅) 0,
    max (max (max (max d₁ d₂) d₃) d₄) d₅, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1 X hX
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hC0 : 0 ≤ max (max (max (max (max C₁ C₂) C₃) C₄) C₅) 0 := le_max_right _ _
  have hlt : ν < min (min (min (min ν₁ ν₂) ν₃) ν₄) ν₅ := hν.2
  have m1 : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m2 : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m3 : ν ∈ Ioo 0 ν₃ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m4 : ν ∈ Ioo 0 ν₄ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m5 : ν ∈ Ioo 0 ν₅ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl
  · exact (H₁ ν m1 ψ p hψ x hx0 hx1).mono
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))
  · exact (H₂ ν m2 ψ p hψ x hx0 hx1).mono
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))
  · exact (H₃ ν m3 ψ p hψ x hx0 hx1).mono
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))
  · exact (H₄ ν m4 ψ p hψ x hx0 hx1).mono
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))
  · exact (H₅ ν m5 ψ p hψ x hx0 hx1).mono
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))

/-! ### The ingredients: zero-age bounds on the stream and pressure profiles -/

/-- **Zero-age bound for the stream profile** (`sct:fluctuation`, source lines 439-446, together with
`sct:expansion`, lines 447-459, at ages `0 < s ≤ 1`): every mixed jet `∂_s^ℓ ∂_η^a ∂_q^b ψ` of the
stream profile of an exact train, weighted by `⟨η⟩^{2m} = (1+η²)^m`, is bounded by `C (1+c+ν⁻¹)^d`
for `0 < s ≤ 1`.  (`ψ = S + ψ̃`: the fluctuation obeys `P e^{-κνs/c²} ≤ P`; the mean stream `S` is
`q`-independent, so `∂_q^b S = 0` for `b ≥ 1`, and `‖η^{m'} ∂_η^a ∂_s^ℓ S‖_∞ ≤ P (1+s)^{…} ≤ 2^{…}P`
for `0 ≤ s ≤ 1`.) -/
def EarlyStreamProfile : Prop :=
  ∀ (ρ : ℝ) (m a b ℓ : ℕ), 1 / 2 < ρ → ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
        (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] ψ))) x| ≤
          polyConst C d ν (ν ^ (-ρ))

/-- **Zero-age bound for the pressure profile** (`sct:fluctuation`, source lines 439-446, third
component, `p` itself): the same bound for `∂_s^ℓ ∂_η^a ∂_q^b p`, `0 < s ≤ 1`. -/
def EarlyPressureProfile : Prop :=
  ∀ (ρ : ℝ) (m a b ℓ : ℕ), 1 / 2 < ρ → ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
        (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] p))) x| ≤
          polyConst C d ν (ν ^ (-ρ))

/-! ### The class of zero-age bounded families and its closure properties -/

/-- `X` is a **zero-age bounded family** for `ρ`: for every exact train the profile `X ν ψ p` is
`C^∞` for `s > 0`, and every mixed jet `∂_s^ℓ ∂_η^a ∂_q^b (X ν ψ p)` weighted by `(1+η²)^m` is bounded
by `C (1+c+ν⁻¹)^d` on `0 < s ≤ 1`, for `ν` small. -/
def EarlyBdd (ρ : ℝ) (X : ProfFam) : Prop :=
  (∀ ν : ℝ, 0 < ν → ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ContDiffOn ℝ ∞ (X ν ψ p) {x : ProfilePoint | 0 < x.2.2}) ∧
  ∀ m a b ℓ : ℕ, ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
        (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] (X ν ψ p)))) x| ≤
          polyConst C d ν (ν ^ (-ρ))

/-- **Closure of `EarlyBdd`** (calculus on profiles; Leibniz rule for the mixed jets, commutation
of `∂_s, ∂_η, ∂_q` on `C^∞` profiles (`ProfileCommutators`, proved in `Tasks/R02/Commutators.lean`),
`(1+η²)^m ≤ (1+η²)^{m+1}` to absorb a factor `η`, `s ≤ 1` and `ν ≤ 1` to absorb factors `s`, `ν`):
bounded families are closed under sums, differences, products, constant multiples, multiplication by
`η`, `s`, `ν`, the partial derivatives `∂_η, ∂_q, ∂_s`, the scaling operator `K = η∂_η + 2s∂_s`
and the shifts `K + a`. -/
structure EarlyCalculus : Prop where
  add : ∀ (ρ : ℝ) (X Y : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X → EarlyBdd ρ Y →
    EarlyBdd ρ (fun ν ψ p => X ν ψ p + Y ν ψ p)
  sub : ∀ (ρ : ℝ) (X Y : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X → EarlyBdd ρ Y →
    EarlyBdd ρ (fun ν ψ p => X ν ψ p - Y ν ψ p)
  neg : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => -X ν ψ p)
  mul : ∀ (ρ : ℝ) (X Y : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X → EarlyBdd ρ Y →
    EarlyBdd ρ (fun ν ψ p => X ν ψ p * Y ν ψ p)
  constMul : ∀ (ρ r : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p x => r * X ν ψ p x)
  nuMul : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p x => ν * X ν ψ p x)
  etaMul : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p x => x.2.1 * X ν ψ p x)
  ageMul : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p x => x.2.2 * X ν ψ p x)
  dEta : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => partialEta (X ν ψ p))
  dQ : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => partialQ (X ν ψ p))
  dAge : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => partialAge (X ν ψ p))
  scaling : ∀ (ρ : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => ageOperator (X ν ψ p))
  shift : ∀ (ρ a : ℝ) (X : ProfFam), 1 / 2 < ρ → EarlyBdd ρ X →
    EarlyBdd ρ (fun ν ψ p => ageShift a (X ν ψ p))

/-- The stream profile is a zero-age bounded family, from `EarlyStreamProfile` and the profile
smoothness `LateProfileSmooth`. -/
theorem earlyBdd_stream (hS : LateProfileSmooth) (h : EarlyStreamProfile) {ρ : ℝ}
    (hρ : 1 / 2 < ρ) : EarlyBdd ρ (fun _ ψ _ => ψ) := by
  refine ⟨?_, fun m a b ℓ => h ρ m a b ℓ hρ⟩
  intro ν hν ψ p hψ
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  exact (hS ν (ν ^ (-ρ)) hν (Real.rpow_pos_of_pos hν _) T hT).1

/-- The pressure profile is a zero-age bounded family, from `EarlyPressureProfile` and the profile
smoothness `LateProfileSmooth`. -/
theorem earlyBdd_pressure (hS : LateProfileSmooth) (h : EarlyPressureProfile) {ρ : ℝ}
    (hρ : 1 / 2 < ρ) : EarlyBdd ρ (fun _ _ p => p) := by
  refine ⟨?_, fun m a b ℓ => h ρ m a b ℓ hρ⟩
  intro ν hν ψ p hψ
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  exact (hS ν (ν ^ (-ρ)) hν (Real.rpow_pos_of_pos hν _) T hT).2

/-- The zero-order bound of a zero-age bounded family, for one weight `m`. -/
theorem EarlyBdd.bound0 {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) (m : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
        ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 →
          (1 + x.2.1 ^ 2) ^ m * |X ν ψ p x| ≤ polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m 0 0 0
  exact ⟨ν₀, C, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => H ν hν ψ p hψ x hx0 hx1⟩

/-- The four bounds of a block from the zero-age boundedness of `X`, `∂_η X`, `∂_q X`, `(K+3) X`. -/
def EarlyGroupBdd (ρ : ℝ) (X : ProfFam) : Prop :=
  EarlyBdd ρ X ∧ EarlyBdd ρ (fun ν ψ p => partialEta (X ν ψ p)) ∧
    EarlyBdd ρ (fun ν ψ p => partialQ (X ν ψ p)) ∧
    EarlyBdd ρ (fun ν ψ p => ageShift 3 (X ν ψ p))

/-- A coefficient family with the four groups zero-age bounded gives the early statement. -/
theorem earlyStmt_of_groupBdd {X : ProfFam} (h : ∀ ρ : ℝ, 1 / 2 < ρ → EarlyGroupBdd ρ X) :
    EarlyStmt X := by
  intro ρ m hρ
  obtain ⟨h1, h2, h3, h4⟩ := h ρ hρ
  obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := h1.bound0 m
  obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := h2.bound0 m
  obtain ⟨ν₃, C₃, d₃, hν₃, H₃⟩ := h3.bound0 m
  obtain ⟨ν₄, C₄, d₄, hν₄, H₄⟩ := h4.bound0 m
  refine ⟨min (min (min ν₁ ν₂) ν₃) ν₄, lt_min (lt_min (lt_min hν₁ hν₂) hν₃) hν₄,
    max (max (max (max C₁ C₂) C₃) C₄) 0, max (max (max d₁ d₂) d₃) d₄, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hC0 : 0 ≤ max (max (max (max C₁ C₂) C₃) C₄) 0 := le_max_right _ _
  have hlt : ν < min (min (min ν₁ ν₂) ν₃) ν₄ := hν.2
  have m1 : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m2 : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m3 : ν ∈ Ioo 0 ν₃ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  have m4 : ν ∈ Ioo 0 ν₄ := ⟨hν0, lt_of_lt_of_le hlt (by simp)⟩
  exact ⟨(H₁ ν m1 ψ p hψ x hx0 hx1).trans
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega)),
    (H₂ ν m2 ψ p hψ x hx0 hx1).trans
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega)),
    (H₃ ν m3 ψ p hψ x hx0 hx1).trans
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega)),
    (H₄ ν m4 ψ p hψ x hx0 hx1).trans
      (polyConst_mono hν0 hc (by simp [le_max_iff]) hC0 (by omega))⟩

end UnforcedLeray.Short.PartIIa
