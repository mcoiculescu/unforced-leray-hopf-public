import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-a, task `PartII-a:R02`: the late residual table (decomposition, audit file)

Source of record: `the November 2 reference manuscript`, lines 1259-1276 (late
residual table) with Lemma `sct:heat` (lines 437-481: `sct:fluctuation` 439-446, `sct:expansion`
447-459) and the mean equations `sct:mean` (lines 397-404).

`RingLateTable` (`StatementsRing.lean`, line 139) has no hypotheses and is a conjunction of five
blocks, one per coefficient `A₁, B₁, B₂, B₃, A₂`.  This file

1. splits it into five statements `RingLateA1, RingLateB1, RingLateB2, RingLateB3, RingLateA2`
   (one block each) and proves `ringLateTable_of`: the five blocks give the table, by taking
   `ν₀ = min`, `C = max (…) 0`, `d = max`, `κ = min` (the bounds are monotone in `B` and anti-monotone
   in `κ`);
2. states the ingredient `Prop`s from which each block follows by algebra and elementary
   estimates (`LateIngredients`): the fluctuation profile bounds (from `TrainFluctuationDecay`),
   the mean-remainder profile bounds (from `TrainMeanExpansion`), a bound on the coefficients
   `a_{2j}`, the heat-kernel profile calculus (`K`-eigenvalue and weighted size), the mean-stress
   bounds, the commutators of `K` with `∂_η, ∂_q, ∂_s`, and the profile smoothness (from
   `TrainStreamSmooth`, `PartI/Sub/T01.lean`).

Weighted sizes in the table use the normalized weight `(1 + η²/s)^m` (`WtdBound`); the Part I
estimates use `⟨η⟩^{2m} = (1+η²)^m ≥ (1 + η²/s)^m` for `s ≥ 1`.

Why the table is true (source 1259-1276): `ψ = S + ψ̃` with `S` the mean stream (`q`-independent),
`v₂ = ∂_qψ̃`, `v₁ = -S_η - ψ̃_η`, `H = (1-K)ψ`; every term with a fluctuation factor or with a
`∂_q` is exponentially small by `sct:fluctuation`; the mean terms use
`S = a₀G + a₂∂_η²G + R₁` (`sct:expansion`, `G = G_{νs}`) and the heat identity
`K ∂_η^j G = -(j+1) ∂_η^j G`: `(K+2)∂_ηG = 0` makes `B₁ = -νK(K+2)v₁` of size `s^{-2}`;
`(K+1)G = 0` makes `B₃ = -ν(K+1)²H` of size `s^{-3/2}` with leading mean `-16 ν a₂ ∂_η²G`;
`B₂`'s leading mean is `4a₀² G ∂_ηG`; both have `K`-degree `-3`, so `(K+3)` gains `s^{-1}`;
`(∂_s - ν∂_η²)(S - KS) = -(K+1)g` (with `g = \overline{v₁v₂}` exponentially small) makes `A₂`
exponentially small.

WARNING (same as `PartI:T01`): the time smoothness of the stream `ψ` (`TrainStreamSmooth`) is not a
field of `B0140.IsTrain`; without it the profile derivatives `partialAge`, `ageOperator` of
`trainProfile T.ψ` are junk values.  It enters through `LateProfileSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff meanStress heatKernel1)

/-! ### Blocks of the table -/

/-- One coefficient block with weighted-power sizes: `X`, `∂_ηX`, `(K+3)X` in `s^{-a}, s^{-b}, s^{-e}`
and `∂_qX` exponentially small. -/
def LateGrpW (m : ℕ) (κ ν c B : ℝ) (X : ProfilePoint → ℝ) (a b e : ℝ) : Prop :=
  WtdBound m X a B ∧ WtdBound m (partialEta X) b B ∧ WtdBound m (ageShift 3 X) e B ∧
    ExpBound κ ν c m (partialQ X) B

/-- One exponentially small block: `X`, `∂_ηX`, `(K+3)X`, `∂_qX`. -/
def LateGrpE (m : ℕ) (κ ν c B : ℝ) (X : ProfilePoint → ℝ) : Prop :=
  ExpBound κ ν c m X B ∧ ExpBound κ ν c m (partialEta X) B ∧
    ExpBound κ ν c m (ageShift 3 X) B ∧ ExpBound κ ν c m (partialQ X) B

/-- The shape of a late-table statement: for a predicate `Φ ν c κ B m ψ p` on the data. -/
def LateStmt
    (Φ : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop) : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ (C : ℝ) (d : ℕ) (κ : ℝ), 0 < κ ∧
    ∀ ν ∈ Ioo 0 ν₀, ∀ ψ p : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ p →
      Φ ν (ν ^ (-ρ)) κ (polyConst C d ν (ν ^ (-ρ))) m ψ p

/-- The `A₁` block of `RingLateTable`: sizes `s^{-2}`, `s^{-5/2}`, `s^{-2}`. -/
def phiA1 : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop :=
  fun ν c κ B m ψ p => LateGrpW m κ ν c B (coeffA₁ ν ψ p) 2 (5 / 2) 2

/-- The `B₁` block: sizes `s^{-2}`, `s^{-5/2}`, `s^{-2}`. -/
def phiB1 : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop :=
  fun ν c κ B m ψ _ => LateGrpW m κ ν c B (coeffB₁ ν ψ) 2 (5 / 2) 2

/-- The `B₂` block: sizes `s^{-3/2}`, `s^{-2}`, `s^{-5/2}`. -/
def phiB2 : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop :=
  fun ν c κ B m ψ _ => LateGrpW m κ ν c B (coeffB₂ ν ψ) (3 / 2) 2 (5 / 2)

/-- The `B₃` block: sizes `s^{-3/2}`, `s^{-2}`, `s^{-5/2}`. -/
def phiB3 : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop :=
  fun ν c κ B m ψ _ => LateGrpW m κ ν c B (coeffB₃ ν ψ) (3 / 2) 2 (5 / 2)

/-- The `A₂` block: exponentially small. -/
def phiA2 : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop :=
  fun ν c κ B m ψ _ => LateGrpE m κ ν c B (coeffA₂ ν ψ)

/-- **Late table, `A₁` block** (source lines 1259-1276, entries `A₁`). -/
def RingLateA1 : Prop := LateStmt phiA1

/-- **Late table, `B₁` block** (entries `B₁`). -/
def RingLateB1 : Prop := LateStmt phiB1

/-- **Late table, `B₂` block** (entries `B₂`). -/
def RingLateB2 : Prop := LateStmt phiB2

/-- **Late table, `B₃` block** (entries `B₃`). -/
def RingLateB3 : Prop := LateStmt phiB3

/-- **Late table, `A₂` block** (entries `A₂`). -/
def RingLateA2 : Prop := LateStmt phiA2

/-! ### Monotonicity and merging -/

/-- `Φ` is monotone: larger `B` and smaller `κ` keep it true (for `ν, c > 0`). -/
def LateMono
    (Φ : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop) : Prop :=
  ∀ (ν c κ κ' B B' : ℝ) (m : ℕ) (ψ p : ProfilePoint → ℝ), 0 < ν → 0 < c → κ' ≤ κ → B ≤ B' →
    Φ ν c κ B m ψ p → Φ ν c κ' B' m ψ p

theorem polyConst_mono {C C' : ℝ} {d d' : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hd : d ≤ d') : polyConst C d ν c ≤ polyConst C' d' ν c := by
  unfold polyConst
  have hinv : 0 < ν⁻¹ := inv_pos.2 hν
  have hb : 1 ≤ 1 + c + ν⁻¹ := by linarith
  have h1 : 0 ≤ (1 + c + ν⁻¹) ^ d := pow_nonneg (by linarith) d
  calc C * (1 + c + ν⁻¹) ^ d ≤ C' * (1 + c + ν⁻¹) ^ d := mul_le_mul_of_nonneg_right hC h1
    _ ≤ C' * (1 + c + ν⁻¹) ^ d' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb hd) hC'

theorem WtdBound.mono' {m : ℕ} {X : ProfilePoint → ℝ} {a B B' : ℝ} (hB : B ≤ B')
    (h : WtdBound m X a B) : WtdBound m X a B' := by
  intro x hx
  have h1 := h x hx
  have hpos : 0 ≤ x.2.2 ^ (-a) := Real.rpow_nonneg (by linarith) _
  exact h1.trans (mul_le_mul_of_nonneg_right hB hpos)

theorem ExpBound.mono' {κ κ' ν c : ℝ} {m : ℕ} {X : ProfilePoint → ℝ} {B B' : ℝ} (hν : 0 < ν)
    (hc : 0 < c) (hκ : κ' ≤ κ) (hB : B ≤ B') (h : ExpBound κ ν c m X B) :
    ExpBound κ' ν c m X B' := by
  intro x hx
  have h1 := h x hx
  have hs : 0 ≤ x.2.2 := by linarith
  have hpos := Real.exp_pos (-(κ * ν * x.2.2 / c ^ 2))
  have hlhs : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x| :=
    mul_nonneg (pow_nonneg (by have := div_nonneg (sq_nonneg x.2.1) hs; linarith) _)
      (abs_nonneg _)
  have h0 : 0 ≤ B * Real.exp (-(κ * ν * x.2.2 / c ^ 2)) := hlhs.trans h1
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right hpos).1 h0
  have hexp : Real.exp (-(κ * ν * x.2.2 / c ^ 2)) ≤ Real.exp (-(κ' * ν * x.2.2 / c ^ 2)) := by
    apply Real.exp_le_exp.2
    have h2 : κ' * ν * x.2.2 / c ^ 2 ≤ κ * ν * x.2.2 / c ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hν.le hs]
    linarith
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X x|
      ≤ B * Real.exp (-(κ * ν * x.2.2 / c ^ 2)) := h1
    _ ≤ B * Real.exp (-(κ' * ν * x.2.2 / c ^ 2)) := mul_le_mul_of_nonneg_left hexp hB0
    _ ≤ B' * Real.exp (-(κ' * ν * x.2.2 / c ^ 2)) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le

theorem LateGrpW.mono' {m : ℕ} {κ κ' ν c B B' : ℝ} {X : ProfilePoint → ℝ} {a b e : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hκ : κ' ≤ κ) (hB : B ≤ B') (h : LateGrpW m κ ν c B X a b e) :
    LateGrpW m κ' ν c B' X a b e := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨WtdBound.mono' hB h1, WtdBound.mono' hB h2, WtdBound.mono' hB h3,
    ExpBound.mono' hν hc hκ hB h4⟩

theorem LateGrpE.mono' {m : ℕ} {κ κ' ν c B B' : ℝ} {X : ProfilePoint → ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hκ : κ' ≤ κ) (hB : B ≤ B') (h : LateGrpE m κ ν c B X) :
    LateGrpE m κ' ν c B' X := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨ExpBound.mono' hν hc hκ hB h1, ExpBound.mono' hν hc hκ hB h2,
    ExpBound.mono' hν hc hκ hB h3, ExpBound.mono' hν hc hκ hB h4⟩

theorem monoA1 : LateMono phiA1 :=
  fun _ _ _ _ _ _ _ _ _ hν hc hκ hB h => LateGrpW.mono' hν hc hκ hB h

theorem monoB1 : LateMono phiB1 :=
  fun _ _ _ _ _ _ _ _ _ hν hc hκ hB h => LateGrpW.mono' hν hc hκ hB h

theorem monoB2 : LateMono phiB2 :=
  fun _ _ _ _ _ _ _ _ _ hν hc hκ hB h => LateGrpW.mono' hν hc hκ hB h

theorem monoB3 : LateMono phiB3 :=
  fun _ _ _ _ _ _ _ _ _ hν hc hκ hB h => LateGrpW.mono' hν hc hκ hB h

theorem monoA2 : LateMono phiA2 :=
  fun _ _ _ _ _ _ _ _ _ hν hc hκ hB h => LateGrpE.mono' hν hc hκ hB h

theorem LateMono.and
    {Φ Ψ : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop}
    (hΦ : LateMono Φ) (hΨ : LateMono Ψ) :
    LateMono (fun ν c κ B m ψ p => Φ ν c κ B m ψ p ∧ Ψ ν c κ B m ψ p) :=
  fun ν c κ κ' B B' m ψ p hν hc hκ hB h =>
    ⟨hΦ ν c κ κ' B B' m ψ p hν hc hκ hB h.1, hΨ ν c κ κ' B B' m ψ p hν hc hκ hB h.2⟩

/-- Two late statements with monotone predicates give their conjunction (take `ν₀ = min`,
`C = max (max C₁ C₂) 0`, `d = max`, `κ = min`). -/
theorem LateStmt.and
    {Φ Ψ : ℝ → ℝ → ℝ → ℝ → ℕ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → Prop}
    (hΦ : LateMono Φ) (hΨ : LateMono Ψ) (h1 : LateStmt Φ) (h2 : LateStmt Ψ) :
    LateStmt (fun ν c κ B m ψ p => Φ ν c κ B m ψ p ∧ Ψ ν c κ B m ψ p) := by
  intro ρ m hρ
  obtain ⟨ν₁, hν₁, C₁, d₁, κ₁, hκ₁, H₁⟩ := h1 ρ m hρ
  obtain ⟨ν₂, hν₂, C₂, d₂, κ₂, hκ₂, H₂⟩ := h2 ρ m hρ
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, max (max C₁ C₂) 0, max d₁ d₂, min κ₁ κ₂,
    lt_min hκ₁ hκ₂, ?_⟩
  intro ν hν ψ p hψ
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hm1 : ν ∈ Ioo 0 ν₁ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hm2 : ν ∈ Ioo 0 ν₂ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have hC0 : 0 ≤ max (max C₁ C₂) 0 := le_max_right _ _
  refine ⟨hΦ ν (ν ^ (-ρ)) κ₁ (min κ₁ κ₂) _ _ m ψ p hν0 hc (min_le_left _ _)
    (polyConst_mono hν0 hc ((le_max_left _ _).trans (le_max_left _ _)) hC0 (le_max_left _ _))
    (H₁ ν hm1 ψ p hψ),
    hΨ ν (ν ^ (-ρ)) κ₂ (min κ₁ κ₂) _ _ m ψ p hν0 hc (min_le_right _ _)
    (polyConst_mono hν0 hc ((le_max_right _ _).trans (le_max_left _ _)) hC0 (le_max_right _ _))
    (H₂ ν hm2 ψ p hψ)⟩

/-- **`PartII-a:R02`, conditional on the five coefficient blocks.** -/
theorem ringLateTable_of (h1 : RingLateA1) (h2 : RingLateB1) (h3 : RingLateB2)
    (h4 : RingLateB3) (h5 : RingLateA2) : RingLateTable := by
  have h45 := LateStmt.and monoB3 monoA2 h4 h5
  have h345 := LateStmt.and monoB2 (monoB3.and monoA2) h3 h45
  have h2345 := LateStmt.and monoB1 (monoB2.and (monoB3.and monoA2)) h2 h345
  have h12345 := LateStmt.and monoA1 (monoB1.and (monoB2.and (monoB3.and monoA2))) h1 h2345
  exact h12345

/-! ### The ingredients of the five blocks -/

/-- **Profile smoothness**: the stream and pressure profiles `(q, η, s) ↦ ψ(s, (q, η))`,
`p(s, (q, η))` of a train are `C^∞` for `s > 0` (profile form of `PartI.TrainStreamSmooth` and
`B0140.IsTrain.smooth_p`). -/
def LateProfileSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ContDiffOn ℝ ∞ (trainProfile tr.ψ) {x : ProfilePoint | 0 < x.2.2} ∧
    ContDiffOn ℝ ∞ (trainProfile tr.p) {x : ProfilePoint | 0 < x.2.2}

/-- **Fluctuation profile bounds** (`sct:fluctuation`, source lines 439-446, in the profile
variables): for fixed weight `m` and fixed numbers `a, b, ℓ` of `∂_η, ∂_q, K`, there are a
polynomial majorant `C (1+c+ν⁻¹)^N` and `κ > 0` with
`(1+η²/s)^m |K^ℓ ∂_η^a ∂_q^b f| ≤ P e^{-κνs/c²}` for `s ≥ 1`, where `f` is the fluctuation
`ψ̃ = ψ - \bar ψ` of the stream, or the pressure `p`.  (From `TrainFluctuationDecay`: `K^ℓ` expands
into `η^i s^k ∂_η^i ∂_s^k` and the polynomial factors in `s` are absorbed by halving `κ`; the
weight `(1+η²/s)^m ≤ (1+η²)^m` for `s ≥ 1`.) -/
def LateFluctuationProfile : Prop :=
  ∀ (ρ : ℝ) (m a b ℓ : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m *
            |(ageOperator^[ℓ] (partialEta^[a] (partialQ^[b]
              (trainProfile fun s z => tr.ψ s z - meanStream tr s z.2)))) x| ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) ∧
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m *
            |(ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (trainProfile tr.p)))) x| ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)))

/-- **Mean-remainder profile bounds** (`sct:expansion`, source lines 447-459, with `p = ∞`, in the
profile variables): for the remainder `R_N = S - ∑_{j≤N} a_{2j} ∂_η^{2j} G_{νs}` of the mean stream,
`(1+η²/s)^m |K^ℓ ∂_η^b R_N| ≤ P s^{-(b+2N+3)/2}` for `s ≥ 1`.  (From `TrainMeanExpansion`:
`‖η^{m'} ∂_η^b ∂_s^ℓ R_N‖_∞ ≤ P s^{(m'-b-2N-3)/2-ℓ}`; expand the weight and `K^ℓ`.) -/
def LateMeanRemainder : Prop :=
  ∀ (ρ : ℝ) (N m b ℓ : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + x.2.1 ^ 2 / x.2.2) ^ m *
            |(ageOperator^[ℓ] (partialEta^[b]
              (trainProfile fun s z => meanRemainder tr N s z.2))) x| ≤
          polyConst C M ν (ν ^ (-ρ)) * x.2.2 ^ (-(((b : ℝ) + 2 * N + 3) / 2))

/-- **The coefficients `a_{2j}` are polynomially bounded** (`sct:expansion`, source lines 450-453:
`a_{2j} = (∫η^{2j}S(0))/(2j)! + ∫₀^∞ ∑ … ∫η^{2i} g dt`): `|a_{2j}| ≤ P`.  (The first term is an
explicit Gaussian moment; in the second, `g = \overline{ṽ₁ṽ₂}` is exponentially small by
`sct:fluctuation` and `\bar v₂ = 0` (`sct:mean`), so the `t`-integral is `≲ c²/ν`.) -/
def LateMeanCoeff : Prop :=
  ∀ (ρ : ℝ) (j : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      |meanCoeff tr j| ≤ polyConst C N ν (ν ^ (-ρ))

/-- The heat-kernel profile `(q, η, s) ↦ G_{νs}(η)`. -/
def heatProfile (ν : ℝ) : ProfilePoint → ℝ := fun x => heatKernel1 (ν * x.2.2) x.2.1

/-- **Heat-kernel profile calculus** (source lines 1255-1257 and 1268-1272; unit `B0191`):
(i) `K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}` for `s > 0` (`B0191.K_iteratedDeriv_heatKernel`; note
`B0191.heatKernel ν s η = heatKernel1 (ν s) η`); (ii) for `ν ≤ 1`, `s ≥ 1`:
`(1+η²/s)^m |∂_η^j G_{νs}(η)| ≤ C_{m,j} (νs)^{-(j+1)/2}` (with `u = η/√(νs)`: `η²/s = ν u² ≤ u²`,
and `∂_η^j G_t = t^{-(j+1)/2} p_j(u) e^{-u²/4}`, `p_j` a polynomial); (iii) the profile derivative
`partialEta^[j]` of `heatProfile ν` is the one-variable `iteratedDeriv j (heatKernel1 (ν s))` at
`η` (this is the identification used to read the expansion `S = ∑ a_{2j} ∂_η^{2j} G + R_N`
of `meanRemainder` at the profile level). -/
def LateHeatProfile : Prop :=
  (∀ ν : ℝ, 0 < ν → ∀ (j : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      ageOperator (partialEta^[j] (heatProfile ν)) x =
        -((j : ℝ) + 1) * (partialEta^[j] (heatProfile ν)) x) ∧
  (∀ m j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ x : ProfilePoint, 1 ≤ x.2.2 →
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[j] (heatProfile ν)) x| ≤
        C * (ν * x.2.2) ^ (-(((j : ℝ) + 1) / 2))) ∧
  (∀ ν : ℝ, 0 < ν → ∀ (j : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      (partialEta^[j] (heatProfile ν)) x = iteratedDeriv j (heatKernel1 (ν * x.2.2)) x.2.1)

/-- **Mean-stress profile bounds** (`sct:mean`, source lines 397-404, `g = \overline{v₁v₂}`): the
mean stress `g` is exponentially small with all its `η`-derivatives and `K`-powers,
`(1+η²/s)^m |K^ℓ ∂_η^a g| ≤ P e^{-κνs/c²}`, `s ≥ 1`.  (From `TrainFluctuationDecay` and
`\bar v₂ = 0`: `g = \overline{ṽ₁ṽ₂}`.) -/
def LateMeanStress : Prop :=
  ∀ (ρ : ℝ) (m a ℓ : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + x.2.1 ^ 2 / x.2.2) ^ m *
            |(ageOperator^[ℓ] (partialEta^[a] (trainProfile fun s z => meanStress tr s z.2))) x| ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))

/-- **Commutators of `K = η∂_η + 2s∂_s`** (calculus on profiles, `C²` at the point):
`[K, ∂_η] = -∂_η`, `[K, ∂_q] = 0`, `[∂_s, K] = 2∂_s`. -/
def ProfileCommutators : Prop :=
  ∀ (f : ProfilePoint → ℝ) (x : ProfilePoint), ContDiffAt ℝ 2 f x →
    ageOperator (partialEta f) x = partialEta (ageOperator f) x - partialEta f x ∧
    ageOperator (partialQ f) x = partialQ (ageOperator f) x ∧
    partialAge (ageOperator f) x = ageOperator (partialAge f) x + 2 * partialAge f x

/-- All ingredients of the five coefficient blocks. -/
structure LateIngredients : Prop where
  smooth : LateProfileSmooth
  fluct : LateFluctuationProfile
  remainder : LateMeanRemainder
  coeff : LateMeanCoeff
  heat : LateHeatProfile
  stress : LateMeanStress
  comm : ProfileCommutators

end UnforcedLeray.Short.PartIIa
