import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UnforcedLeray.Units.B0104.Gronwall

/-!
# B0104, helper: bounded-perturbation Duhamel evolutions on blocks

Helper for blueprint unit `B0104` (`lem:compact-duhamel`, `paper/main.tex` lines 1586-1621).

The full evolution `U` of the lemma is "defined by bounded-perturbation Duhamel iteration"
(line 1597), i.e. it is the strong solution of
`U(t,s) = F(t,s) + ∫_s^t F(t,r) A(r) U(r,s) dr` (line 1617) for `0 ≤ t - s ≤ B`.
`IsDuhamelEvolution B F A U` records exactly this: the Duhamel integrand is Bochner integrable
(so the Lean integral is the genuine strong integral, not the junk value `0`), the Duhamel
identity holds, and `U(·,s)` is bounded on each block (true of the Dyson series, which has the
majorant `Σ_k M (MK(t-s))^k / k!`). `IsDuhamelEvolution.unique` shows these conditions determine
`U`, so they characterize the Duhamel-iteration evolution.

* `IsDuhamelEvolution.norm_le`: the uniform exponential majorant
  `‖U(t,s)‖ ≤ 2 M e^{(2MK+1)B}` (line 1608, "uniform exponential majorants");
* `IsDuhamelEvolution.unique`: uniqueness;
* `adjoint_step`, `remainder_step`: the two Duhamel comparison estimates used in `B0104.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace UnforcedLeray.B0104

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

/-- `U` is the bounded-perturbation Duhamel evolution of the free evolution `F` and the bounded
interaction `A` on blocks `s ≤ t ≤ s + B` (`paper/main.tex` lines 1597, 1617; unit `B0104`).
All families depend on an auxiliary parameter `p : ι`. -/
structure IsDuhamelEvolution (B : ℝ) (F : ι → ℝ → ℝ → H →L[ℂ] H) (A : ι → ℝ → H →L[ℂ] H)
    (U : ι → ℝ → ℝ → H →L[ℂ] H) : Prop where
  /-- The Duhamel integrand `r ↦ F(t,r) A(r) U(r,s) x` is integrable on `[s,t]`. -/
  integrable : ∀ p s t, s ≤ t → t ≤ s + B → ∀ x : H,
    IntervalIntegrable (fun r => F p t r (A p r (U p r s x))) volume s t
  /-- The Duhamel identity `U(t,s) x = F(t,s) x + ∫_s^t F(t,r) A(r) U(r,s) x dr`. -/
  duhamel : ∀ p s t, s ≤ t → t ≤ s + B → ∀ x : H,
    U p t s x = F p t s x + ∫ r in s..t, F p t r (A p r (U p r s x))
  /-- `U(·,s)` is bounded on the block `[s, s+B]`. -/
  bounded : ∀ p s, ∃ C, ∀ t, s ≤ t → t ≤ s + B → ‖U p t s‖ ≤ C

theorem norm_adjoint_eq (T : H →L[ℂ] H) : ‖(T†)‖ = ‖T‖ := LinearIsometryEquiv.norm_map _ T

theorem norm_adjoint_apply_le (T : H →L[ℂ] H) (y : H) : ‖(T†) y‖ ≤ ‖T‖ * ‖y‖ :=
  ((T†).le_opNorm y).trans_eq (by rw [norm_adjoint_eq])

theorem norm_apply_apply_le {T S : H →L[ℂ] H} {M K : ℝ} (hT : ‖T‖ ≤ M) (hS : ‖S‖ ≤ K)
    (y : H) : ‖T (S y)‖ ≤ M * K * ‖y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hT
  calc ‖T (S y)‖ ≤ ‖T‖ * ‖S y‖ := T.le_opNorm _
    _ ≤ M * (K * ‖y‖) :=
      mul_le_mul hT ((S.le_opNorm y).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _)))
        (norm_nonneg _) hM
    _ = M * K * ‖y‖ := by ring

/-- A vector is bounded by `c` if all its inner products are bounded by `c ‖x‖`. -/
theorem norm_le_of_forall_inner_le (v : H) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : H, ‖⟪v, x⟫_ℂ‖ ≤ c * ‖x‖) : ‖v‖ ≤ c := by
  have h1 : ‖v‖ ^ 2 ≤ c * ‖v‖ := by
    calc ‖v‖ ^ 2 = RCLike.re ⟪v, v⟫_ℂ := (inner_self_eq_norm_sq v).symm
      _ ≤ ‖⟪v, v⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ c * ‖v‖ := h v
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; exact hc
  · nlinarith

/-- Scaling: a bound on unit vectors gives `‖T (S v)‖ ≤ ‖v‖ c`. -/
theorem norm_apply_apply_le_of_unit {T S : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u : H, ‖u‖ ≤ 1 → ‖T (S u)‖ ≤ c) (v : H) : ‖T (S v)‖ ≤ ‖v‖ * c := by
  have hTS : ‖T.comp S‖ ≤ c :=
    ContinuousLinearMap.opNorm_le_of_unit_norm hc fun u hu => h u hu.le
  calc ‖T (S v)‖ = ‖(T.comp S) v‖ := rfl
    _ ≤ ‖T.comp S‖ * ‖v‖ := (T.comp S).le_opNorm v
    _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right hTS (norm_nonneg _)
    _ = ‖v‖ * c := mul_comm _ _

/-- If `‖T* A* u‖ ≤ c` on the unit ball, then `‖A T x‖ ≤ c ‖x‖` (duality). -/
theorem norm_apply_apply_le_of_adjoint {A T : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u : H, ‖u‖ ≤ 1 → ‖(T†) ((A†) u)‖ ≤ c) (x : H) : ‖A (T x)‖ ≤ c * ‖x‖ := by
  refine norm_le_of_forall_inner_le _ (mul_nonneg hc (norm_nonneg _)) fun y => ?_
  rw [← ContinuousLinearMap.adjoint_inner_right A (T x) y,
    ← ContinuousLinearMap.adjoint_inner_right T x ((A†) y)]
  calc ‖⟪x, (T†) ((A†) y)⟫_ℂ‖ ≤ ‖x‖ * ‖(T†) ((A†) y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖y‖ * c) :=
        mul_le_mul_of_nonneg_left (norm_apply_apply_le_of_unit hc h y) (norm_nonneg _)
    _ = c * ‖x‖ * ‖y‖ := by ring

namespace IsDuhamelEvolution

variable {B M K : ℝ} {F : ι → ℝ → ℝ → H →L[ℂ] H} {A : ι → ℝ → H →L[ℂ] H}
  {U : ι → ℝ → ℝ → H →L[ℂ] H}

/-- **Uniform exponential majorant** of the Duhamel evolution: if `‖F(t,s)‖ ≤ M` on blocks and
`‖A(r)‖ ≤ K`, then `‖U(t,s)‖ ≤ 2 M e^{(2MK+1)B}` on blocks. -/
theorem norm_le (hU : IsDuhamelEvolution B F A U)
    (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M) (hA : ∀ p r, ‖A p r‖ ≤ K) :
    ∀ p t s, s ≤ t → t ≤ s + B → ‖U p t s‖ ≤ 2 * M * exp ((2 * (M * K) + 1) * B) := by
  intro p t s hst hts
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF p t s hst hts)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA p 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  obtain ⟨C, hC⟩ := hU.bounded p s
  have G := gronwall_family (I := Unit) (fun _ t => ‖U p t s x‖) (s := s) (B := B)
    (a := M * ‖x‖) (L := M * K) (C := C * ‖x‖) (by positivity) (by positivity)
    (fun _ t h1 h2 => ((U p t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hC t h1 h2) (norm_nonneg _)))
    (fun g hg t h1 h2 _ hφ _ => by
      rw [hU.duhamel p s t h1 h2 x]
      calc ‖F p t s x + ∫ r in s..t, F p t r (A p r (U p r s x))‖
          ≤ ‖F p t s x‖ + ‖∫ r in s..t, F p t r (A p r (U p r s x))‖ := norm_add_le _ _
        _ ≤ M * ‖x‖ + ∫ r in s..t, M * K * g r := by
          refine add_le_add (((F p t s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hF p t s h1 h2) (norm_nonneg _))) ?_
          refine intervalIntegral.norm_integral_le_of_norm_le h1
            (ae_of_all _ fun r hr => ?_) ((hg.const_mul _).intervalIntegrable _ _)
          calc ‖F p t r (A p r (U p r s x))‖ ≤ M * K * ‖U p r s x‖ :=
                norm_apply_apply_le (hF p t r hr.2 (by linarith [hr.1])) (hA p r) _
            _ ≤ M * K * g r :=
                mul_le_mul_of_nonneg_left (hφ () r hr.1.le hr.2) (by positivity)
        _ = M * ‖x‖ + M * K * ∫ r in s..t, g r := by
          rw [intervalIntegral.integral_const_mul]) () t hst hts
  calc ‖U p t s x‖ ≤ 2 * (M * ‖x‖) * exp ((2 * (M * K) + 1) * (t - s)) := G
    _ ≤ 2 * (M * ‖x‖) * exp ((2 * (M * K) + 1) * B) := by
        gcongr
        linarith
    _ = 2 * M * exp ((2 * (M * K) + 1) * B) * ‖x‖ := by ring

/-- **Uniqueness**: the bounded strong solution of the Duhamel equation is unique, so
`IsDuhamelEvolution` determines the Duhamel-iteration evolution. -/
theorem unique {U' : ι → ℝ → ℝ → H →L[ℂ] H} (hU : IsDuhamelEvolution B F A U)
    (hU' : IsDuhamelEvolution B F A U')
    (hF : ∀ p t s, s ≤ t → t ≤ s + B → ‖F p t s‖ ≤ M) (hA : ∀ p r, ‖A p r‖ ≤ K) :
    ∀ p t s, s ≤ t → t ≤ s + B → U p t s = U' p t s := by
  intro p t s hst hts
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF p t s hst hts)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA p 0)
  ext x
  obtain ⟨C, hC⟩ := hU.bounded p s
  obtain ⟨C', hC'⟩ := hU'.bounded p s
  have G := gronwall_family (I := Unit) (fun _ t => ‖U p t s x - U' p t s x‖) (s := s) (B := B)
    (a := 0) (L := M * K) (C := C * ‖x‖ + C' * ‖x‖) le_rfl (by positivity)
    (fun _ t h1 h2 => (norm_sub_le _ _).trans (add_le_add
      (((U p t s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC t h1 h2) (norm_nonneg _)))
      (((U' p t s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC' t h1 h2) (norm_nonneg _)))))
    (fun g hg t h1 h2 _ hφ _ => by
      rw [hU.duhamel p s t h1 h2 x, hU'.duhamel p s t h1 h2 x, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hU.integrable p s t h1 h2 x)
          (hU'.integrable p s t h1 h2 x), zero_add, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le h1
        (ae_of_all _ fun r hr => ?_) ((hg.const_mul _).intervalIntegrable _ _)
      rw [← map_sub, ← map_sub]
      calc ‖F p t r (A p r (U p r s x - U' p r s x))‖
          ≤ M * K * ‖U p r s x - U' p r s x‖ :=
            norm_apply_apply_le (hF p t r hr.2 (by linarith [hr.1])) (hA p r) _
        _ ≤ M * K * g r :=
            mul_le_mul_of_nonneg_left (hφ () r hr.1.le hr.2) (by positivity)) () t hst hts
  have h0 : ‖U p t s x - U' p t s x‖ ≤ 0 := by simpa using G
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end IsDuhamelEvolution

/-- The pointwise identity behind the adjoint comparison:
`⟪z, F₁A₁U₁x - F₀A₀U₀x⟫ = ⟪A₁* F₁* z - A₀* F₀* z, U₁x⟫ + ⟪(U₁ - U₀)* A₀* F₀* z, x⟫`. -/
theorem inner_duhamel_diff (z x : H) (F₁ F₀ A₁ A₀ U₁ U₀ : H →L[ℂ] H) :
    ⟪z, F₁ (A₁ (U₁ x)) - F₀ (A₀ (U₀ x))⟫_ℂ =
      ⟪(A₁†) ((F₁†) z) - (A₀†) ((F₀†) z), U₁ x⟫_ℂ + ⟪((U₁ - U₀)†) ((A₀†) ((F₀†) z)), x⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left, map_sub,
    sub_apply]
  ring

variable {B M K CU η ρ ψ : ℝ} {F₁ F₀ : ι → ℝ → ℝ → H →L[ℂ] H} {A₁ A₀ : ι → ℝ → H →L[ℂ] H}
  {U₁ U₀ : ι → ℝ → ℝ → H →L[ℂ] H}

/-- **Adjoint comparison step.** For Duhamel evolutions `U₁, U₀` of `(F₁, A₁)`, `(F₀, A₀)`, a
block `s ≤ t ≤ s + B` and a vector `z`, `‖(U₁ - U₀)(t,s)* z‖` is bounded by the smallness `η`
of `(F₁ - F₀)(t,·)* z` and `A₁ - A₀`, plus `M ρ ∫_s^t g` where `g` controls
`(U₁ - U₀)(r,s)* A₀(r)*` (the reversed-order adjoint Duhamel series, line 1607). -/
theorem adjoint_step (hU₁ : IsDuhamelEvolution B F₁ A₁ U₁) (hU₀ : IsDuhamelEvolution B F₀ A₀ U₀)
    {p : ι} {s t : ℝ} (hst : s ≤ t) (hts : t ≤ s + B)
    (hF₁ : ∀ r, s ≤ r → r ≤ t → ‖F₁ p t r‖ ≤ M) (hF₀ : ∀ r, s ≤ r → r ≤ t → ‖F₀ p t r‖ ≤ M)
    (hA₀ : ∀ r, ‖A₀ p r‖ ≤ K) (hU : ∀ r, s ≤ r → r ≤ t → ‖U₁ p r s‖ ≤ CU)
    (hA : ∀ r, ‖A₁ p r - A₀ p r‖ ≤ η)
    {z : H} (hz : ‖z‖ ≤ ρ) (hFz : ∀ r, s ≤ r → r ≤ t → ‖((F₁ p t r - F₀ p t r)†) z‖ ≤ η)
    {g : ℝ → ℝ} (hgi : IntervalIntegrable g volume s t) (hg0 : ∀ r, s ≤ r → r ≤ t → 0 ≤ g r)
    (hg : ∀ r, s ≤ r → r ≤ t → ∀ v : H, ‖((U₁ p r s - U₀ p r s)†) (((A₀ p r)†) v)‖ ≤ ‖v‖ * g r) :
    ‖((U₁ p t s - U₀ p t s)†) z‖ ≤
      η + (t - s) * (CU * (M * ρ + K) * η) + M * ρ * ∫ r in s..t, g r := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF₁ s le_rfl hst)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA₀ s)
  have hCU : 0 ≤ CU := (norm_nonneg _).trans (hU s le_rfl hst)
  have hη : 0 ≤ η := (norm_nonneg _).trans (hA s)
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hz
  have hgint : 0 ≤ ∫ r in s..t, g r :=
    intervalIntegral.integral_nonneg hst fun r hr => hg0 r hr.1 hr.2
  have hts' : 0 ≤ t - s := sub_nonneg.2 hst
  refine norm_le_of_forall_inner_le _ (by positivity) fun x => ?_
  have hint₁ := hU₁.integrable p s t hst hts x
  have hint₀ := hU₀.integrable p s t hst hts x
  set c₁ := CU * (M * ρ + K) * η with hc₁
  have hUx : (U₁ p t s - U₀ p t s) x = (F₁ p t s - F₀ p t s) x +
      ∫ r in s..t, (F₁ p t r (A₁ p r (U₁ p r s x)) - F₀ p t r (A₀ p r (U₀ p r s x))) := by
    rw [intervalIntegral.integral_sub hint₁ hint₀, sub_apply, sub_apply,
      hU₁.duhamel p s t hst hts x, hU₀.duhamel p s t hst hts x]
    abel
  have hinner : ⟪z, ∫ r in s..t, (F₁ p t r (A₁ p r (U₁ p r s x)) -
      F₀ p t r (A₀ p r (U₀ p r s x)))⟫_ℂ = ∫ r in s..t, ⟪z, F₁ p t r (A₁ p r (U₁ p r s x)) -
      F₀ p t r (A₀ p r (U₀ p r s x))⟫_ℂ := by
    have := (innerSL ℂ z).intervalIntegral_comp_comm (hint₁.sub hint₀)
    simpa only [innerSL_apply_apply] using this.symm
  have hkey : ⟪((U₁ p t s - U₀ p t s)†) z, x⟫_ℂ = ⟪((F₁ p t s - F₀ p t s)†) z, x⟫_ℂ +
      ∫ r in s..t, ⟪z, F₁ p t r (A₁ p r (U₁ p r s x)) - F₀ p t r (A₀ p r (U₀ p r s x))⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hUx,
      inner_add_right, hinner]
  have hpt : ∀ r, s ≤ r → r ≤ t → ‖⟪z, F₁ p t r (A₁ p r (U₁ p r s x)) -
      F₀ p t r (A₀ p r (U₀ p r s x))⟫_ℂ‖ ≤ ‖x‖ * (c₁ + M * ρ * g r) := by
    intro r hr1 hr2
    rw [inner_duhamel_diff]
    have htr : t ≤ r + B := by linarith
    have hFz₁ : ‖((F₁ p t r)†) z‖ ≤ M * ρ :=
      (norm_adjoint_apply_le _ _).trans (mul_le_mul (hF₁ r hr1 hr2) hz (norm_nonneg _) hM)
    have hFz₀ : ‖((F₀ p t r)†) z‖ ≤ M * ρ :=
      (norm_adjoint_apply_le _ _).trans (mul_le_mul (hF₀ r hr1 hr2) hz (norm_nonneg _) hM)
    have ha : ‖((A₁ p r)†) (((F₁ p t r)†) z) - ((A₀ p r)†) (((F₀ p t r)†) z)‖ ≤ (M * ρ + K) * η := by
      have hsplit : ((A₁ p r)†) (((F₁ p t r)†) z) - ((A₀ p r)†) (((F₀ p t r)†) z) =
          ((A₁ p r - A₀ p r)†) (((F₁ p t r)†) z) + ((A₀ p r)†) (((F₁ p t r - F₀ p t r)†) z) := by
        simp only [map_sub, sub_apply]
        abel
      rw [hsplit]
      calc _ ≤ ‖((A₁ p r - A₀ p r)†) (((F₁ p t r)†) z)‖ + ‖((A₀ p r)†) (((F₁ p t r - F₀ p t r)†) z)‖ :=
            norm_add_le _ _
        _ ≤ η * (M * ρ) + K * η := add_le_add
            ((norm_adjoint_apply_le _ _).trans (mul_le_mul (hA r) hFz₁ (norm_nonneg _) hη))
            ((norm_adjoint_apply_le _ _).trans
              (mul_le_mul (hA₀ r) (hFz r hr1 hr2) (norm_nonneg _) hK))
        _ = (M * ρ + K) * η := by ring
    have hUx₁ : ‖U₁ p r s x‖ ≤ CU * ‖x‖ :=
      ((U₁ p r s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hU r hr1 hr2) (norm_nonneg _))
    have hb : ‖((U₁ p r s - U₀ p r s)†) (((A₀ p r)†) (((F₀ p t r)†) z))‖ ≤ M * ρ * g r :=
      (hg r hr1 hr2 _).trans (mul_le_mul_of_nonneg_right hFz₀ (hg0 r hr1 hr2))
    calc _ ≤ ‖⟪((A₁ p r)†) (((F₁ p t r)†) z) - ((A₀ p r)†) (((F₀ p t r)†) z), U₁ p r s x⟫_ℂ‖ +
          ‖⟪((U₁ p r s - U₀ p r s)†) (((A₀ p r)†) (((F₀ p t r)†) z)), x⟫_ℂ‖ := norm_add_le _ _
      _ ≤ (M * ρ + K) * η * (CU * ‖x‖) + M * ρ * g r * ‖x‖ := add_le_add
          ((norm_inner_le_norm _ _).trans (mul_le_mul ha hUx₁ (norm_nonneg _) (by positivity)))
          ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
      _ = ‖x‖ * (c₁ + M * ρ * g r) := by rw [hc₁]; ring
  have hintb : ∫ r in s..t, ‖x‖ * (c₁ + M * ρ * g r) =
      ‖x‖ * ((t - s) * c₁ + M * ρ * ∫ r in s..t, g r) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      (hgi.const_mul _), intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      smul_eq_mul]
  have hI : ‖∫ r in s..t, ⟪z, F₁ p t r (A₁ p r (U₁ p r s x)) -
      F₀ p t r (A₀ p r (U₀ p r s x))⟫_ℂ‖ ≤ ‖x‖ * ((t - s) * c₁ + M * ρ * ∫ r in s..t, g r) := by
    rw [← hintb]
    exact intervalIntegral.norm_integral_le_of_norm_le hst
      (ae_of_all _ fun r hr => hpt r hr.1.le hr.2)
      ((intervalIntegrable_const.add (hgi.const_mul _)).const_mul _)
  rw [hkey]
  calc _ ≤ ‖⟪((F₁ p t s - F₀ p t s)†) z, x⟫_ℂ‖ + ‖∫ r in s..t, ⟪z, F₁ p t r (A₁ p r (U₁ p r s x)) -
        F₀ p t r (A₀ p r (U₀ p r s x))⟫_ℂ‖ := norm_add_le _ _
    _ ≤ η * ‖x‖ + ‖x‖ * ((t - s) * c₁ + M * ρ * ∫ r in s..t, g r) :=
        add_le_add ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hFz s le_rfl hst) (norm_nonneg _))) hI
    _ = (η + (t - s) * c₁ + M * ρ * ∫ r in s..t, g r) * ‖x‖ := by ring

/-- **Remainder comparison step.** On a block `s ≤ t ≤ s + B`,
`(U₁ - F₁)(t,s) x - (U₀ - F₀)(t,s) x = ∫_s^t (F₁A₁U₁ - F₀A₀U₀)(…) x dr`, and the integrand splits
as `F₁(A₁ - A₀)U₁x + (F₁ - F₀)A₀U₁x + F₀A₀(U₁ - U₀)x` (line 1609-1617). -/
theorem remainder_step (hU₁ : IsDuhamelEvolution B F₁ A₁ U₁)
    (hU₀ : IsDuhamelEvolution B F₀ A₀ U₀) {p : ι} {s t : ℝ} (hst : s ≤ t) (hts : t ≤ s + B)
    (hF₁ : ∀ r, s ≤ r → r ≤ t → ‖F₁ p t r‖ ≤ M) (hF₀ : ∀ r, s ≤ r → r ≤ t → ‖F₀ p t r‖ ≤ M)
    (hA : ∀ r, ‖A₁ p r - A₀ p r‖ ≤ η) {x : H} (hU : ∀ r, s ≤ r → r ≤ t → ‖U₁ p r s x‖ ≤ CU)
    (hFv : ∀ r, s ≤ r → r ≤ t → ‖(F₁ p t r - F₀ p t r) (A₀ p r (U₁ p r s x))‖ ≤ η)
    (hψ : ∀ r, s ≤ r → r ≤ t → ‖A₀ p r ((U₁ p r s - U₀ p r s) x)‖ ≤ ψ) :
    ‖((U₁ p t s - F₁ p t s) - (U₀ p t s - F₀ p t s)) x‖ ≤
      (t - s) * (M * (η * CU) + η + M * ψ) := by
  have hint₁ := hU₁.integrable p s t hst hts x
  have hint₀ := hU₀.integrable p s t hst hts x
  have hRx : ((U₁ p t s - F₁ p t s) - (U₀ p t s - F₀ p t s)) x =
      ∫ r in s..t, (F₁ p t r (A₁ p r (U₁ p r s x)) - F₀ p t r (A₀ p r (U₀ p r s x))) := by
    rw [intervalIntegral.integral_sub hint₁ hint₀]
    simp only [sub_apply]
    rw [hU₁.duhamel p s t hst hts x, hU₀.duhamel p s t hst hts x]
    abel
  rw [hRx]
  calc _ ≤ (M * (η * CU) + η + M * ψ) * |t - s| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    _ = (t - s) * (M * (η * CU) + η + M * ψ) := by
        rw [abs_of_nonneg (sub_nonneg.2 hst), mul_comm]
  rw [uIoc_of_le hst] at hr
  have hr1 : s ≤ r := hr.1.le
  have hr2 : r ≤ t := hr.2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF₁ s le_rfl hst)
  have hsplit : F₁ p t r (A₁ p r (U₁ p r s x)) - F₀ p t r (A₀ p r (U₀ p r s x)) =
      F₁ p t r ((A₁ p r - A₀ p r) (U₁ p r s x)) + (F₁ p t r - F₀ p t r) (A₀ p r (U₁ p r s x)) +
        F₀ p t r (A₀ p r ((U₁ p r s - U₀ p r s) x)) := by
    simp only [sub_apply, map_sub]
    abel
  rw [hsplit]
  calc _ ≤ ‖F₁ p t r ((A₁ p r - A₀ p r) (U₁ p r s x)) +
        (F₁ p t r - F₀ p t r) (A₀ p r (U₁ p r s x))‖ +
        ‖F₀ p t r (A₀ p r ((U₁ p r s - U₀ p r s) x))‖ := norm_add_le _ _
    _ ≤ (‖F₁ p t r ((A₁ p r - A₀ p r) (U₁ p r s x))‖ +
        ‖(F₁ p t r - F₀ p t r) (A₀ p r (U₁ p r s x))‖) +
        ‖F₀ p t r (A₀ p r ((U₁ p r s - U₀ p r s) x))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (M * (η * CU) + η) + M * ψ := by
        gcongr
        · calc ‖F₁ p t r ((A₁ p r - A₀ p r) (U₁ p r s x))‖ ≤ M * η * ‖U₁ p r s x‖ :=
                norm_apply_apply_le (hF₁ r hr1 hr2) (hA r) _
            _ ≤ M * η * CU := mul_le_mul_of_nonneg_left (hU r hr1 hr2)
                (mul_nonneg hM ((norm_nonneg _).trans (hA r)))
            _ = M * (η * CU) := by ring
        · exact hFv r hr1 hr2
        · exact ((F₀ p t r).le_opNorm _).trans
            (mul_le_mul (hF₀ r hr1 hr2) (hψ r hr1 hr2) (norm_nonneg _) hM)

end UnforcedLeray.B0104
