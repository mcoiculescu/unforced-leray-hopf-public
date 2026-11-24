import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Sub.C04
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.SharpBoundAll
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Exists

/-!
# Part I, task `PartI:C05`: small diffusion on the complementary space (decomposition)

Source of record: `the November 2 reference manuscript`, lines 1005-1058.

This file contains the block-iteration argument (`decay_of_blocks`, proved) and the assembly
`smallDiffusionComplement_of`, which derives `SmallDiffusionComplement` from the block limit
(`complement_block_limit`, task `PartI:C03`), the deflated decay (`exp_deflated_decay_minrate`,
`PartI:C04`), the sharp bound and existence of the free evolutions (`PartI:C02`) and four open
leaf lemmas about the mild complementary evolution plus the bound of the inviscid free group.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Infra.Dunford (rankOneProj)

namespace UnforcedLeray.Short.PartI

/-- Block iteration (source lines 1048-1058): if the cocycle `U` is a contraction by `1/2` on
every block of length `B` and bounded by `K` on shorter blocks, it decays exponentially. -/
theorem decay_of_blocks {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : ℝ → ℝ → E →L[ℂ] E) {B K : ℝ} (hB : 0 < B) (hK : 1 ≤ K)
    (hself : ∀ s, U s s = 1)
    (hcoc : ∀ s r t, s ≤ r → r ≤ t → U t s = U t r * U r s)
    (hblock : ∀ s, ‖U (s + B) s‖ ≤ 1 / 2)
    (hshort : ∀ s t, s ≤ t → t ≤ s + B → ‖U t s‖ ≤ K) :
    ∀ s t, s ≤ t → ‖U t s‖ ≤ (2 * K) * Real.exp (-((Real.log 2 / B) * (t - s))) := by
  have hn : ∀ (n : ℕ) (s : ℝ), ‖U (s + n * B) s‖ ≤ (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, hself s]
      exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      intro s
      have h1 : s + (n : ℝ) * B ≤ s + ((n + 1 : ℕ) : ℝ) * B := by
        push_cast; nlinarith
      have h2 : s ≤ s + (n : ℝ) * B := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [hcoc s (s + n * B) _ h2 h1]
      have : s + ((n + 1 : ℕ) : ℝ) * B = (s + n * B) + B := by push_cast; ring
      rw [this]
      calc ‖U ((s + n * B) + B) (s + n * B) * U (s + n * B) s‖
          ≤ ‖U ((s + n * B) + B) (s + n * B)‖ * ‖U (s + n * B) s‖ := norm_mul_le _ _
        _ ≤ (1 / 2) * (1 / 2) ^ n := mul_le_mul (hblock _) (ih s) (norm_nonneg _) (by norm_num)
        _ = (1 / 2) ^ (n + 1) := by ring
  intro s t hst
  set n : ℕ := ⌊(t - s) / B⌋₊ with hndef
  have hq0 : 0 ≤ (t - s) / B := div_nonneg (sub_nonneg.2 hst) hB.le
  have hn1 : (n : ℝ) ≤ (t - s) / B := Nat.floor_le hq0
  have hn2 : (t - s) / B < n + 1 := Nat.lt_floor_add_one _
  have hnB : (n : ℝ) * B ≤ t - s := by
    have := mul_le_mul_of_nonneg_right hn1 hB.le
    rwa [div_mul_cancel₀ _ hB.ne'] at this
  have hnB2 : t - s < (n + 1) * B := by
    have := mul_lt_mul_of_pos_right hn2 hB
    rwa [div_mul_cancel₀ _ hB.ne'] at this
  have h2 : s ≤ s + n * B := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h3 : s + n * B ≤ t := by linarith
  rw [hcoc s (s + n * B) t h2 h3]
  have hA : ‖U t (s + n * B)‖ ≤ K := hshort _ _ h3 (by linarith)
  have hB' := hn n s
  have hhalf : ((1 : ℝ) / 2) ^ n = Real.exp (-(n * Real.log 2)) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
      rw [Real.exp_neg, Real.exp_log two_pos]; simp, ← Real.exp_nat_mul]
    ring_nf
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-(n * Real.log 2)) ≤
      2 * Real.exp (-((Real.log 2 / B) * (t - s))) := by
    have hnn : (t - s) / B - 1 ≤ n := by linarith
    have e1 : -(n * Real.log 2) ≤ Real.log 2 + -((Real.log 2 / B) * (t - s)) := by
      have : (Real.log 2 / B) * (t - s) = ((t - s) / B) * Real.log 2 := by ring
      rw [this]; nlinarith
    calc Real.exp (-(n * Real.log 2)) ≤ Real.exp (Real.log 2 + -((Real.log 2 / B) * (t - s))) :=
          Real.exp_le_exp.2 e1
      _ = 2 * Real.exp (-((Real.log 2 / B) * (t - s))) := by
          rw [Real.exp_add, Real.exp_log two_pos]
  calc ‖U t (s + n * B) * U (s + n * B) s‖
      ≤ ‖U t (s + n * B)‖ * ‖U (s + n * B) s‖ := norm_mul_le _ _
    _ ≤ K * Real.exp (-(n * Real.log 2)) := by
        rw [← hhalf]; exact mul_le_mul hA hB' (norm_nonneg _) (by linarith)
    _ ≤ K * (2 * Real.exp (-((Real.log 2 / B) * (t - s)))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = (2 * K) * Real.exp (-((Real.log 2 / B) * (t - s))) := by ring

/-- Triangle inequality for the block decomposition `U = (U - F - (E₁ - E₂)) + F + E₁ - E₂`. -/
theorem norm_four_le {E : Type*} [NormedAddCommGroup E] (u f e1 e2 : E) :
    ‖u‖ ≤ ‖u - f - (e1 - e2)‖ + ‖f‖ + ‖e1‖ + ‖e2‖ := by
  have h : u = (u - f - (e1 - e2)) + f + e1 + (-e2) := by abel
  have h1 := norm_add_le ((u - f - (e1 - e2)) + f + e1) (-e2)
  have h2 := norm_add_le ((u - f - (e1 - e2)) + f) e1
  have h3 := norm_add_le (u - f - (e1 - e2)) f
  rw [norm_neg] at h1
  calc ‖u‖ = ‖(u - f - (e1 - e2)) + f + e1 + (-e2)‖ := congrArg norm h
    _ ≤ _ := by linarith

/-- The mild complementary evolution of `IsSeedXG lam q l` (abbreviation). -/
abbrev MildCtx (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ) (qd : B0010.XG)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ)
    (U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) : Prop :=
  IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U

/-- **Leaf 1** (existence of the mild complementary evolution; source lines 1014-1030, "the
evolution exists for measurable `β` by the Dyson series based on `exp(D∫β)`"): for measurable
`0 ≤ β ≤ 1` there is `U` with `IsMildComplementEvolution`.  Sketch: with `F` the free evolution
(`freeDiffusionEvolutionExists`) and the interaction `complementInteraction`, take
`U t s := (Evolution.dyson E_{[s,t]} Ap).U t s` on the block `[s,t]` (as `fdeAuxF` in
`Tasks/FreeDiffusionEvolution/Exists.lean`); the Duhamel identity for `U` w.r.t. `e^{D∫β}` comes
from `Evolution.dyson_sum_regroup` / `dyson_left` and `complementDyson_gen`
(`Tasks/ComplementBlockLimit/ComplementDysonFamily.lean`). -/
def MildComplementExists : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∃ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U

/-- **Leaf 2** (cocycle; source lines 1048-1052, iteration over blocks): every mild
complementary evolution satisfies `U(t,s) = U(t,r) U(r,s)` for `s ≤ r ≤ t`.  Sketch: both sides
solve the same mild equation in `t ≥ r` with initial value `U(r,s)x`; uniqueness by the Gronwall
argument for the Duhamel identity (`Lib/BudgetsGronwall`), or `Evolution.dyson_unique`
via `complementDysonFamily` on `[s,t]`. -/
def MildComplementCocycle : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U →
        ∀ s r t : ℝ, s ≤ r → r ≤ t → U t s = U t r * U r s

/-- **Leaf 3** (uniform short-block bound; source lines 1055-1058, "short block bound
`‖U‖ ≤ C_B` by Gronwall on the Duhamel identity"): for each `B > 0` there is `K` such that every
mild complementary evolution with measurable `0 ≤ β ≤ 1` has `‖U(t,s)‖ ≤ K` for
`s ≤ t ≤ s + B`.  Sketch: `‖e^{aD}‖ ≤ 1` (`B0123.expD` is a contraction semigroup), the
generator `L₀ - λ - P - βκ + βR_f` has norm at most `M := ‖L₀ - λ - P‖ + |κ| + ‖R_f‖`, so
`‖U(t,s)x‖ ≤ ‖x‖ + M ∫_s^t ‖U(r,s)x‖ dr`; Gronwall (`Lib/BudgetsGronwall`) gives `e^{MB}‖x‖`. -/
def MildComplementShortBound : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (B : ℝ), 0 < B →
      ∃ K : ℝ, ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
        ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U →
          ∀ s t : ℝ, s ≤ t → t ≤ s + B → ‖U t s‖ ≤ K

/-- **Leaf 4** (invariance of `ker ℓ`; source lines 1056-1058, "testing the mild equation against
`q†` in `dom D` gives `ℓ(U(t,s)x) = e^{-(t-s)} ℓ(x)`"): for every mild complementary evolution,
`ℓ(U(t,s)x) = e^{-(t-s)} ℓ(x)`.  Sketch: `u(t) = ℓ(U(t,s)x)` satisfies, using `ℓ L₀ = λ ℓ`,
`ℓ(q) = 1`, `ℓ(e^{aD}y) = ⟨e^{aD}q†, y⟩`, `ℓ R_f f = κ ℓ(f) - ⟨Dq†, f⟩` and
`⟨Dq†, f⟩ = ⟨q†, D f⟩`, the scalar mild equation whose `β`-terms cancel, i.e.
`u(t) = u(s) - ∫_s^t u`; conclude by uniqueness of that linear scalar integral equation. -/
def MildComplementInvariant : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ),
      Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ 1) →
      ∀ U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, MildCtx lam q l qd hq hqd β U →
        ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG, l (U t s x) = Real.exp (-(t - s)) * l x

/-- **Leaf 5** (norm of the inviscid free group; source lines 1038-1046, the term
`e^{B(T-λ)}`): `T = -2iΩ` is skew-adjoint (`Ω` self-adjoint, `B0012.omegaOp`), so
`‖e^{B(T-λ)}‖ = e^{-Re λ · B}` for `B ≥ 0`. -/
def FreeLimitExpBound : Prop :=
  ∀ (lam : ℂ) (B : ℝ), 0 ≤ B →
    ‖NormedSpace.exp ((B : ℂ) • freeLimitGen lam)‖ ≤ Real.exp (-(lam.re * B))

/-- **`PartI:C05` from the five leaves** (source lines 1005-1058). -/
theorem smallDiffusionComplement_of (hE : MildComplementExists) (hC : MildComplementCocycle)
    (hS : MildComplementShortBound) (hI : MildComplementInvariant) (hT : FreeLimitExpBound) :
    SmallDiffusionComplement := by
  intro lam q l hseed qd hl hq hqd
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = min lam.re 1 := ⟨_, rfl⟩
  have hmpos : 0 < m := hmdef ▸ lt_min hseed.re_pos one_pos
  have hmlam : m ≤ lam.re := hmdef ▸ min_le_left _ _
  obtain ⟨C0, hC0, hC0b⟩ := exp_deflated_decay_minrate hseed (δ := m / 2) (by positivity)
  rw [← hmdef] at hC0b
  have hlogpos : 0 < Real.log (4 * (C0 + 2)) := Real.log_pos (by linarith)
  have hr : 0 < m / 2 := by positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.log (4 * (C0 + 2)) / (m / 2) := ⟨_, rfl⟩
  have hBpos : 0 < B := hBdef ▸ div_pos hlogpos hr
  have hex : Real.exp (-(m / 2 * B)) = 1 / (4 * (C0 + 2)) := by
    have : m / 2 * B = Real.log (4 * (C0 + 2)) := by rw [hBdef]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    simp
  have hexC : (C0 + 2) * Real.exp (-(m / 2 * B)) = 1 / 4 := by
    rw [hex]; field_simp
  obtain ⟨βs2, hβs2, hblk⟩ :=
    complement_block_limit hseed hl hq hqd B hBpos (1 / 4) (by norm_num)
  obtain ⟨βs1, hβs1def⟩ : ∃ x : ℝ, x = m / (4 * (|(seedKappa l q hq).re| + 1)) := ⟨_, rfl⟩
  have hβs1 : 0 < βs1 := hβs1def ▸ by positivity
  obtain ⟨K, hK⟩ := hS lam q l hseed qd hl hq hqd B hBpos
  have hβspos : 0 < min (min βs1 βs2) 1 := lt_min (lt_min hβs1 hβs2) one_pos
  refine ⟨min (min βs1 βs2) 1, Real.log 2 / B, 2 * max K 1, hβspos,
    div_pos (Real.log_pos (by norm_num)) hBpos, by positivity, ?_⟩
  intro β hβm hβ
  have hβ1 : ∀ t, 0 ≤ β t ∧ β t ≤ 1 := fun t =>
    ⟨(hβ t).1, (hβ t).2.trans (min_le_right _ _)⟩
  obtain ⟨U, hU⟩ := hE lam q l hseed qd hl hq hqd β hβm hβ1
  refine ⟨U, hU, ?_⟩
  have hβ2 : ∀ t, 0 ≤ β t ∧ β t ≤ βs2 := fun t =>
    ⟨(hβ t).1, (hβ t).2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hβle1 : min (min βs1 βs2) 1 ≤ βs1 := (min_le_left _ _).trans (min_le_left _ _)
  have hκa : |(seedKappa l q hq).re| * min (min βs1 βs2) 1 ≤ m / 4 := by
    have h1 : (|(seedKappa l q hq).re| + 1) * βs1 = m / 4 := by
      rw [hβs1def]; field_simp
    have h2 : |(seedKappa l q hq).re| * min (min βs1 βs2) 1 ≤ (|(seedKappa l q hq).re| + 1) * βs1 := by
      have := abs_nonneg (seedKappa l q hq).re
      nlinarith [hβspos]
    linarith
  have hblock : ∀ s, ‖U (s + B) s‖ ≤ 1 / 2 := by
    intro s
    obtain ⟨F, hF⟩ := freeDiffusionEvolutionExists lam (seedKappa l q hq) (min (min βs1 βs2) 1) β hβm hβ
    have hsharp := freeSharpBoundAll lam (seedKappa l q hq) (min (min βs1 βs2) 1) β hβm hβ F hF s (s + B)
      (by linarith)
    rw [add_sub_cancel_left] at hsharp
    have h1 := hblk β hβm hβ2 U F hU hF s
    have hE2 : ‖NormedSpace.exp ((B : ℂ) • ((-2 * Complex.I) • B0012.omegaOp -
        lam • (1 : B0010.XG →L[ℂ] B0010.XG)))‖ ≤ Real.exp (-(lam.re * B)) :=
      hT lam B hBpos.le
    have hE1 := hC0b B hBpos.le
    have e1 : -(m - m / 2) * B = -(m / 2 * B) := by ring
    rw [e1] at hE1
    have hF1 : ‖F (s + B) s‖ ≤ Real.exp (-(m / 2 * B)) := by
      refine hsharp.trans (Real.exp_le_exp.2 ?_)
      nlinarith [mul_le_mul_of_nonneg_right hκa hBpos.le,
        mul_le_mul_of_nonneg_right hmlam hBpos.le]
    have hE2' : ‖NormedSpace.exp ((B : ℂ) • ((-2 * Complex.I) • B0012.omegaOp -
        lam • (1 : B0010.XG →L[ℂ] B0010.XG)))‖ ≤ Real.exp (-(m / 2 * B)) :=
      hE2.trans (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hmlam hBpos.le]))
    have h4 := norm_four_le (U (s + B) s) (F (s + B) s)
      (NormedSpace.exp ((B : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
        rankOneProj l q)))
      (NormedSpace.exp ((B : ℂ) • ((-2 * Complex.I) • B0012.omegaOp -
        lam • (1 : B0010.XG →L[ℂ] B0010.XG))))
    have hC0e : C0 * Real.exp (-(m / 2 * B)) + 2 * Real.exp (-(m / 2 * B)) = 1 / 4 := by
      rw [← hexC]; ring
    linarith
  have hdec := decay_of_blocks U hBpos (le_max_right K 1) hU.self_eq
    (hC lam q l hseed qd hl hq hqd β hβm hβ1 U hU) hblock
    (fun s t hst hts => (hK β hβm hβ1 U hU s t hst hts).trans (le_max_left _ _))
  intro s t hst x hx
  refine ⟨?_, ?_⟩
  · rw [hI lam q l hseed qd hl hq hqd β hβm hβ1 U hU s t hst x, hx, mul_zero]
  · calc ‖U t s x‖ ≤ ‖U t s‖ * ‖x‖ := (U t s).le_opNorm x
      _ ≤ (2 * max K 1) * Real.exp (-((Real.log 2 / B) * (t - s))) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hdec s t hst) (norm_nonneg x)

end UnforcedLeray.Short.PartI
