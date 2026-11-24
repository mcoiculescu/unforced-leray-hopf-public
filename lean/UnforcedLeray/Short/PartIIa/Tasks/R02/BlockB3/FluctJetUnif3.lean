import UnforcedLeray.Short.PartIIa.Calc.BlockB3
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, block `B₃`: the leaf `FluctJetUnif3` (task `PartII-a:R02/11/8`)

Target: `fluctJetUnif3_of : LateFluctuationProfile → FluctJetUnif3`.

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`).

Route (as in `Calc/BlockB1/FluctJetUnif.lean`): index the finitely many instances by
`(ℓ, a, b)` in `range 5 ×ˢ range 2 ×ˢ range 2`, use `finite_uniform` with weights `w ≡ 1`
on the family `T p j = (1+η²/s)^m |jet p (fluctP j.2.1) j.2.2|` over the admissible index
`j = (ν, train, point)`, and read off the first conjunct of `LateFluctuationProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)

/-- Index type of the finitely many instances: a viscosity `ν`, a train at `ν`, and a point. -/
abbrev FluctIdx3 (ρ : ℝ) : Type :=
  Σ ν : ℝ, (UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)) × ProfilePoint)

/-- Admissible indices: `ν > 0`, the train is BUC, and `s ≥ 1`. -/
def fluctAdm3 (ρ : ℝ) (j : FluctIdx3 ρ) : Prop :=
  0 < j.1 ∧ UnforcedLeray.Short.PartI.IsBUCTrain j.2.1 ∧ 1 ≤ j.2.2.2.2

/-- Weighted jet of the fluctuation at an index. -/
def fluctT3 (ρ : ℝ) (m ℓ a b : ℕ) (j : FluctIdx3 ρ) : ℝ :=
  (1 + j.2.2.2.1 ^ 2 / j.2.2.2.2) ^ m * |jet ℓ a b (fluctP j.2.1) j.2.2|

/-- Exponential majorant at an index. -/
def fluctD3 (ρ κ : ℝ) (j : FluctIdx3 ρ) : ℝ :=
  Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2))

theorem fluctT3_nonneg (ρ : ℝ) (m ℓ a b : ℕ) (j : FluctIdx3 ρ) (hs : 1 ≤ j.2.2.2.2) :
    0 ≤ fluctT3 ρ m ℓ a b j := by
  unfold fluctT3
  apply mul_nonneg
  · apply pow_nonneg
    have : 0 ≤ j.2.2.2.1 ^ 2 / j.2.2.2.2 := div_nonneg (sq_nonneg _) (by linarith)
    linarith
  · exact abs_nonneg _

theorem fluctJetUnif3_of (hF : LateFluctuationProfile) : FluctJetUnif3 := by
  intro ρ m hρ
  have hterm : ∀ p ∈ (Finset.range 5 ×ˢ Finset.range 2 ×ˢ Finset.range 2 : Finset (ℕ × ℕ × ℕ)),
      ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
        ∀ j : FluctIdx3 ρ, fluctAdm3 ρ j → j.1 ≤ ν₀ →
          fluctT3 ρ m p.1 p.2.1 p.2.2 j ≤ polyConst C N (j.1) (j.1 ^ (-ρ)) * fluctD3 ρ κ j := by
    intro p _
    obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := hF ρ m p.2.1 p.2.2 p.1 hρ
    refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
    intro j hj hνj
    obtain ⟨hν, hBUC, hs⟩ := hj
    exact (H j.1 hν hνj j.2.1 hBUC j.2.2 hs).1
  obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ :=
    finite_uniform (ι := FluctIdx3 ρ) (α := ℕ × ℕ × ℕ)
      (Finset.range 5 ×ˢ Finset.range 2 ×ˢ Finset.range 2)
      (fluctAdm3 ρ) (fun j => j.1) (fun j => j.1 ^ (-ρ)) (fluctD3 ρ)
      (fun κ j _ => (Real.exp_pos _).le)
      (by
        intro κ κ' j hj hκ' hle
        obtain ⟨hν, _, hs⟩ := hj
        unfold fluctD3
        apply Real.exp_le_exp.2
        have hK : 0 ≤ j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2 :=
          div_nonneg (mul_nonneg hν.le (by linarith)) (sq_nonneg _)
        have h2 := mul_le_mul_of_nonneg_right hle hK
        have e1 : κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2 =
            κ * (j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2) := by ring
        have e2 : κ' * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2 =
            κ' * (j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2) := by ring
        rw [e1, e2]
        linarith)
      (fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _⟩)
      (fun _ => (1 : ℝ)) (fun p j => fluctT3 ρ m p.1 p.2.1 p.2.2 j)
      hterm
  refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνν₀ tr hBUC ℓ a b hℓ ha hb x hx
  have hmem : (ℓ, a, b) ∈ (Finset.range 5 ×ˢ Finset.range 2 ×ˢ Finset.range 2 : Finset (ℕ × ℕ × ℕ)) := by
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have key := H ⟨ν, tr, x⟩ ⟨hν, hBUC, hx⟩ hνν₀
  have hsingle : fluctT3 ρ m ℓ a b ⟨ν, tr, x⟩ ≤
      ∑ p ∈ (Finset.range 5 ×ˢ Finset.range 2 ×ˢ Finset.range 2 : Finset (ℕ × ℕ × ℕ)),
        fluctT3 ρ m p.1 p.2.1 p.2.2 ⟨ν, tr, x⟩ :=
    Finset.single_le_sum (f := fun p : ℕ × ℕ × ℕ => fluctT3 ρ m p.1 p.2.1 p.2.2 ⟨ν, tr, x⟩)
      (fun p _ => fluctT3_nonneg ρ m p.1 p.2.1 p.2.2 ⟨ν, tr, x⟩ hx) hmem
  have key' : ∑ p ∈ (Finset.range 5 ×ˢ Finset.range 2 ×ˢ Finset.range 2 : Finset (ℕ × ℕ × ℕ)),
      fluctT3 ρ m p.1 p.2.1 p.2.2 ⟨ν, tr, x⟩ ≤
        polyConst C N ν (ν ^ (-ρ)) * fluctD3 ρ κ ⟨ν, tr, x⟩ := by
    simpa only [abs_one, one_mul] using key
  exact le_trans hsingle key'

end UnforcedLeray.Short.PartIIa.BlockB3
