import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1Org
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# `PartIII-b:C/rep/5/1/1/org`: the far mask `Sop - SNop` on thin sources

Source `the November 2 reference manuscript` 5569-5600, 5618-5619.

Correction (organizer `PartIII-b:C/rep/5/1/cancel/org`).  The source never bounds `S_far = Sop - SNop`
alone in the gain norms: the margins `γ/18` (late output) and `γ/10` (early source) of 5594-5599
are for the pieces of the SUM `S_far T + Y[T]` (5306-5316, 5688-5689), because on output ages
`s <= 4/(5ν)` the young-old rectangle of `S_far` cancels `Y` exactly (4171-4199).  Hence the former
`GainMarginAt`, `GainMarginSeq`, `FarThinGainedAt`, `FarThinGainedSeq` and `ageVelSopThin_of`
(which asserted the gain-normed bound for `S_far` alone, false for a source of age `2/ν` and an
output of age `O(1)`) are retired; the kernel bound `PerBinVelocityAt` is the true single-term
bound (5585-5593), and the gain bookkeeping is in
`PartIII-b_C_rep_5_1_cancel/{Bridge,FarBins}.lean` (`FarLateBin`, `FarEarlyBin`).

Chain of the far mask:

1. `SopSubIsFarSeq` : `Sop - SNop = S_far` with `IsFarMaskG` (the near split pin, 3902-3920, 5785).
2. `ThinMassBoundSlice` : the thin mass `N_0(a) <= C(a^{-3/4}+a^{-1/2})‖T‖_{Z_1}` (5569-5584).
3. `PerBinVelocityAt` : the per-bin normalized velocity bound for the exact kernel realization
   `IsFarMaskG`, on a logarithmic output bin of width `h < δ/2` and upper age `s`, from the
   sources of age `>= e^{δ-h}s` (5585-5593).
4. `binDecomp` (proved here) : the output age range `(0,S]` is the disjoint union of the bins.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The far mask part of `Sop - SNop` -/

/-- **`S_μ - S_N = S_far`** along the sequence (3902-3920, 5785): for large `n` and `z ∈ [-1,1]`
there is a far part `S_far` with the exact kernel realization `IsFarMaskG` (log gap `δ`, output cut
`S = ε^{-b}`) with `Sop - SNop = S_far`.  (This is `IsNearSplit` of the concrete base; see
`seqNearSplit_of` in `ReturnInst/Inverses/Seq.lean`.) -/
def SopSubIsFarSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Sf : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
        IsFarMaskG (D.level n).ε⁻¹ (D.mu n z) D.K.δ ((D.level n).Scut D.K) Sf ∧
          Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf

/-! ## 2. The thin mass bound -/

/-- The unweighted `Z_1` norm `‖F‖_{Z_1}` of a chart tensor field (source 2697), as an extended
real. -/
def z1Norm (c mZ : ℝ) (F : Chart → Ten3) : ℝ≥0∞ :=
  (∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ) ^ (1 / 2 : ℝ)

/-- The `L²_q` norm over the cell `q ∈ [-c/2, c/2)` with the normalized measure `c⁻¹ dq`, of the
slice `(t, ·, η)` of `F`. -/
def sliceL2q (c : ℝ) (F : Chart → Ten3) (t η : ℝ) : ℝ≥0∞ :=
  (∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * ‖F (t, q, η)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- The thin mass `N_0(a) = ∫_a^∞ t^{-3/2} ∫ ‖T(t,·,η)‖_{L²_q} dη dt` (5569-5575). -/
def thinMass (c : ℝ) (F : Chart → Ten3) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c F t η

/-- **The thin mass bound** (5569-5584): for `m_Z > 3/2` there is `C` with
`N_0(a) ≤ C(a^{-3/4}+a^{-1/2})‖T‖_{Z_1}` for all `c > 0`, `a > 0` and measurable `T`
(transverse Cauchy-Schwarz gives `(1+t)^{1/4}`, then `∫_a^∞ t^{-5/2}(1+t)^{1/2}dt`). -/
def ThinMassBoundSlice (mZ : ℝ) : Prop :=
  3 / 2 < mZ → ∃ C : ℝ, ∀ (c : ℝ), 0 < c → ∀ a : ℝ, 0 < a → ∀ F : Chart → Ten3, Measurable F →
    thinMass c F a ≤ ENNReal.ofReal (C * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) * z1Norm c mZ F

/-! ## 3. The per-bin velocity bound -/

/-- The unweighted `Z_1` norm of `F` restricted to the source ages `t` satisfying `P t`. -/
def z1Part (c mZ : ℝ) (P : ℝ → Prop) (F : Chart → Ten3) : ℝ≥0∞ :=
  (∫⁻ p in {p : Chart | P p.1}, ‖F p‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ) ^ (1 / 2 : ℝ)

/-- The unweighted `Z_1` norm of `F` restricted to the source ages `≥ a`. -/
def z1Tail (c mZ : ℝ) (a : ℝ) (F : Chart → Ten3) : ℝ≥0∞ :=
  z1Part c mZ (fun t => a ≤ t) F

/-- The normalized body norm `R⁻¹‖v‖_{Y_2}` (measure `srcMeasure c`) of `v` on the output age bin
`(s₀, s₁]`. -/
def velBin (c : ℝ) (s₀ s₁ : ℝ) (v : Chart → Merid) : ℝ≥0∞ :=
  (∫⁻ p in {p : Chart | s₀ < p.1 ∧ p.1 ≤ s₁}, ‖v p‖ₑ ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ)

/-- (Not used by `PerBinVelocityAt` any more; kept for the drafts that mention it.)  The bin
`(s e^{-h}, s]` is a *late-output* bin (5601-5605): every output age `u` in it has `ν u ≥ 4/5`. -/
def LateOutBin (ν s h : ℝ) : Prop := 4 / 5 ≤ ν * (s * Real.exp (-h))

/-- (Not used by `PerBinVelocityAt` any more.)  The two regimes of a source's gain margins. -/
def MarginSrc (ν s h : ℝ) (t : ℝ) : Prop := LateOutBin ν s h ∨ ν * t ≤ 3 / 2

/-- **Per-bin velocity bound** (5585-5593, true single-term form): at the level `L` and Floquet
exponent `μ`, every `S_far` with the exact kernel realization `IsFarMaskG` (log gap `δ`, output cut
`S = ε^{-b}`) satisfies, for a logarithmic output bin `(s e^{-h}, s]` of width `0 < h < δ/2` and
`0 < s ≤ S`, and every `T`, with `T_1` the thin part: the normalized velocity on the bin is at most
`C ν^{-k} ε^{3/2}(s^{1/2}+s^{3/4})` times the unweighted `Z_1` norm of the sources of age
`≥ e^{δ-h}s` (the mask `t > e^δ u` and `u > s e^{-h}`; uniform radial gap `D ≍ R/√s`, order-four
kernel with `L²` norm `C D^{-5/2}`, Minkowski and the thin mass bound).  This is sharp for a source
with nonzero mass (`ε^2 s^2 N_0` pointwise, 5347); the `ε^3` of 4925-4934 is the pointwise jet of
`D_y X` in the norm of `A`, not this velocity. -/
def PerBinVelocityAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
      ∀ T : LStr Pl K L,
        velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf (thinPart T) : Chart → Merid) ≤
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) *
            z1Tail (cOf L.ν) K.mZ (Real.exp (K.δ - h) * s)
              (((thinPart T).fst : Lp Ten3 2 _) : Chart → Ten3)

/-- The sequence-level per-bin bound: constants uniform for large `n` and `z ∈ [-1,1]`. -/
def PerBinVelocitySeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      PerBinVelocityAt D.Pl D.K (D.level n) (D.mu n z) C k

/-! ## 3b. The far mask vanishes above the output cut -/

/-- **Output cut** (3905-3912): every `S_far` with `IsFarMaskG` vanishes a.e. at output ages
`≥ S = ε^{-b}` (the kernel formula has `1_{s<S}`; it extends from the dense class `IsBoxTensor` to
all `T` by continuity of `S_far`). -/
def FarVanishAboveAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
    ∀ T : LStr Pl K L, ∀ᵐ p ∂(srcMeasure (cOf L.ν)), L.Scut K ≤ p.1 →
      (Sf T : Chart → Merid) p = 0

/-- Sequence-level `FarVanishAboveAt`. -/
def FarVanishAboveSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      FarVanishAboveAt D.Pl D.K (D.level n) (D.mu n z)

/-! ## 4. The bins partition the output range -/

/-- **Bin decomposition** (5585-5594): for a measurable age function `φ`, `S > 0`, `h > 0`, the
integral over `{0 < φ ≤ S}` is the sum over the logarithmic bins
`(S e^{-(j+1)h}, S e^{-jh}]`, `j ≥ 0`. -/
theorem binDecomp {α : Type*} [MeasurableSpace α] (m : Measure α) (φ : α → ℝ) (hφ : Measurable φ)
    (S h : ℝ) (hS : 0 < S) (hh : 0 < h) (f : α → ℝ≥0∞) :
    ∫⁻ p in {p | 0 < φ p ∧ φ p ≤ S}, f p ∂m =
      ∑' j : ℕ, ∫⁻ p in {p | S * Real.exp (-((j + 1 : ℕ) * h)) < φ p ∧
        φ p ≤ S * Real.exp (-(j * h))}, f p ∂m := by
  set B : ℕ → Set α := fun j => {p | S * Real.exp (-((j + 1 : ℕ) * h)) < φ p ∧
        φ p ≤ S * Real.exp (-(j * h))} with hB
  have hmeas : ∀ j, MeasurableSet (B j) := fun j =>
    (measurableSet_lt measurable_const hφ).inter (measurableSet_le hφ measurable_const)
  have hrw : {p | 0 < φ p ∧ φ p ≤ S} = ⋃ j, B j := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, hB]
    constructor
    · rintro ⟨h0, h1⟩
      -- the least `j` with `φ p > S e^{-(j+1)h}`
      have hex : ∃ j : ℕ, S * Real.exp (-((j + 1 : ℕ) * h)) < φ p := by
        have ht : Tendsto (fun j : ℕ => S * Real.exp (-((j + 1 : ℕ) * h))) atTop (nhds 0) := by
          have h1' : Tendsto (fun j : ℕ => -(((j + 1 : ℕ) : ℝ) * h)) atTop atBot := by
            refine tendsto_neg_atTop_atBot.comp ?_
            exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const hh
          simpa using (Real.tendsto_exp_atBot.comp h1').const_mul S
        exact (ht.eventually (gt_mem_nhds h0)).exists
      classical
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0' | hpos
      · rw [h0']; simpa using h1
      · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        push_neg at this
        have e : ((Nat.find hex - 1 + 1 : ℕ) : ℝ) = (Nat.find hex : ℝ) := by
          rw [Nat.sub_add_cancel hpos]
        rw [e] at this
        exact this
    · rintro ⟨j, hj1, hj2⟩
      refine ⟨lt_of_le_of_lt (by positivity) hj1, hj2.trans ?_⟩
      have : Real.exp (-(j * h)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ (j : ℝ) * h := by positivity
        linarith)
      nlinarith
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro p hi hj
    simp only [hB, mem_setOf_eq] at hi hj
    rcases lt_or_gt_of_ne hij with hl | hl
    · -- i < j : bin j lies below bin i
      have : (j : ℝ) ≥ (i : ℝ) + 1 := by exact_mod_cast hl
      have hle : S * Real.exp (-(j * h)) ≤ S * Real.exp (-(((i + 1 : ℕ) : ℝ) * h)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hS.le
        push_cast
        nlinarith
      linarith [hi.1, hj.2]
    · have : (i : ℝ) ≥ (j : ℝ) + 1 := by exact_mod_cast hl
      have hle : S * Real.exp (-(i * h)) ≤ S * Real.exp (-(((j + 1 : ℕ) : ℝ) * h)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hS.le
        push_cast
        nlinarith
      linarith [hj.1, hi.2]
  rw [hrw]
  exact lintegral_iUnion hmeas hdisj f

/-! ## 5. The gap-term gain margin (retained for the accepted `…_5_1_1/GainMarginMid.lean`) -/

/-- **Gain margin of the gap term** (`ε^3` with `d₀ = γ/3` cancels the full gain `e^{γ/ν}`; cf.
4925-4937, where `ε^3 N_0 ≤ P_ν e^{γ/ν}‖g^{-1}M‖_Z`): with no regime hypothesis,
`ε^3(s^{1/2}+s^{3/4}) gainG t ≤ C ν^{-k} e^{(γ/10+ω_b+3m₀/2)/ν} gainG u` for `s ≤ S`. -/
def GainMarginMidAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (ωb C : ℝ) (k : ℕ) :
    Prop :=
  ∀ (h s t u : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K → Real.exp (K.δ - h) * s ≤ t →
    s * Real.exp (-h) < u → u ≤ s →
      L.ε ^ (3 : ℝ) * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ)) *
          UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν t ≤
        C * L.ν⁻¹ ^ k * Real.exp ((gRate Pl / 10 + ωb + 3 * K.m0 / 2) / L.ν) *
          UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν u

/-- Sequence-level `GainMarginMidAt`, `k₀` chosen before `b`. -/
def GainMarginMidSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      GainMarginMidAt D.Pl D.K (D.level n) ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) C k

/-! ## 6. The geometric bin sum (real analysis) -/

/-- **Geometric bin sum** (5594-5600, "summing geometric bins down to age zero is convergent"):
if the bin `j` (output upper age `S e^{-jh}`) contributes `x_j ≤ B·r^j` with `0 ≤ r < 1`, the
squares sum to at most `B²/(1-r²)`. -/
theorem binSumGeometric (B r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℕ → ℝ) (hx0 : ∀ j, 0 ≤ x j)
    (hx : ∀ j, x j ≤ B * r ^ j) : ∑' j, x j ^ 2 ≤ B ^ 2 / (1 - r ^ 2) := by
  have hB : 0 ≤ B := by
    have := (hx0 0).trans (hx 0)
    simpa using this
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun j : ℕ => B ^ 2 * (r ^ 2) ^ j) (B ^ 2 * (1 - r ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hr2).mul_left (B ^ 2)
  have hle : ∀ j, x j ^ 2 ≤ B ^ 2 * (r ^ 2) ^ j := fun j => by
    have h0 := hx0 j
    have h1 := hx j
    calc x j ^ 2 ≤ (B * r ^ j) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = B ^ 2 * (r ^ 2) ^ j := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
  have := hasSum_le hle (Summable.of_nonneg_of_le (fun j => sq_nonneg _) hle hg.summable).hasSum hg
  rw [div_eq_mul_inv]
  exact this.trans (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIIb.Concrete
