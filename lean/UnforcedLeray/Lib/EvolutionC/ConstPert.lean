import UnforcedLeray.Lib.EvolutionFamilies.Dyson
import UnforcedLeray.Lib.Semigroups.ExpSemigroup

/-!
# Constant perturbations of semigroups and Dyson of a bounded generator (INF08 T8.6, abstract part)


§5, Layer 3, target **T8.6** (bypass BP1; blueprint units B0064, B0250); plan
`scoping/README.md` §5, Wave 3, block 3E (EVOL-S).

Manuscript (`paper/main.tex`): line 1245 (unit B0064) obtains the generator `𝓛 = -D_E - A_E` from
the transport group `T(t)` (`eq:st18-t00050`, lines 1228-1231) "by the bounded-perturbation
theorem [Engel–Nagel, Theorem III.1.3]". With the evolution families of `Lib/EvolutionFamilies`
(frozen interfaces `EvolutionFamily`, `BoundedPert`, `dyson` of decision D17), the
bounded-perturbation theorem is the Dyson series; this file shows that a *constant* perturbation
of a *semigroup* gives a semigroup, and identifies the result with `NormedSpace.exp` when the
generator is bounded.

Main declarations (namespace `UnforcedLeray.Evolution`):
* `EvolutionFamily.ofExpSemigroup S a b`: the evolution family `U(t,s) = S(t-s)` of an
  `Infra.ExpSemigroup` on `[a,b]`; `BoundedPert.const K`: the constant interaction `A(r) = K`;
* `dyson_congr_of_subset`: Dyson evolutions are compatible with restriction to a subinterval
  (uniqueness);
* `dyson_ofExpSemigroup_const_eq_shift`: time-translation invariance,
  `U(t,s) = U_{[0,b-a]}(t-s, 0)`;
* `Infra.ExpSemigroup.perturb S K`: the perturbed semigroup `τ ↦ U_{[0,τ]}(τ,0)` with
  `M = S.M`, `ω = S.ω + S.M ‖K‖`; `dyson_ofExpSemigroup_const`:
  `(dyson (ofExpSemigroup S a b) (const K)).U t s = (S.perturb K).T (t - s)`;
  `perturb_T_apply_eq_duhamel` (variation of constants) and `perturb_unique`;
* `exp_smul_add_apply_eq_duhamel`: the Duhamel formula for `exp((t-s)(S+K)) x` on `[s,t]`
  (from the vendored `BanachExp.exp_add_eq_duhamel`);
* `dyson_ofExp_const`: **Dyson(e^{tS}, K) = exp(t(S+K))** for bounded `S`, i.e.
  `(dyson (ofExpSemigroup (ofExp S) a b) (const K)).U t s = exp((t-s)(S+K))`, and
  `perturb_ofExp_T`.

No junk values: every statement is on the triangle `a ≤ s ≤ t ≤ b` or at times `t ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

open UnforcedLeray.Infra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

namespace EvolutionFamily

/-- **The evolution family of a semigroup** on `[a,b]`: `U(t,s) = S(t-s)` (INF08 T8.6;
`paper/main.tex`, lines 1228-1231, the transport group `T(t)` as a free evolution). -/
def ofExpSemigroup (S : ExpSemigroup X) (a b : ℝ) : EvolutionFamily X a b where
  U t s := S.T (t - s)
  U_diag t _ := by rw [sub_self, S.T_zero]
  U_comp s r t _ hsr hrt _ := by
    rw [← S.T_add (t - r) (r - s) (sub_nonneg.2 hrt) (sub_nonneg.2 hsr)]
    congr 1
    ring
  U_cont x := (S.T_cont x).comp (continuous_snd.sub continuous_fst).continuousOn
    fun p hp => Set.mem_Ici.2 (sub_nonneg.2 hp.2.1)
  U_bdd := ⟨S.M * Real.exp (|S.ω| * (b - a)), fun s t hs hst ht =>
    S.norm_T_le_of_le (sub_nonneg.2 hst) (by linarith)⟩

@[simp] theorem ofExpSemigroup_U (S : ExpSemigroup X) (a b t s : ℝ) :
    (ofExpSemigroup S a b).U t s = S.T (t - s) := rfl

end EvolutionFamily

namespace BoundedPert

/-- **The constant interaction** `A(r) = K` on `[a,b]` (`paper/main.tex`, line 1245: the
perturbation `-A_E` of the transport group is a fixed bounded operator). -/
def const {a b : ℝ} (K : X →L[ℂ] X) : BoundedPert X a b where
  A _ := K
  meas _ := aestronglyMeasurable_const
  bdd := ⟨‖K‖, fun _ _ => le_rfl⟩

@[simp] theorem const_A {a b : ℝ} (K : X →L[ℂ] X) (r : ℝ) :
    (const (a := a) (b := b) K).A r = K := rfl

end BoundedPert

open EvolutionFamily BoundedPert

variable [CompleteSpace X]

/-- **Restriction to a subinterval.** If `[a₂,b₂] ⊆ [a₁,b₁]` and the free families and the
interactions agree on the small interval, then so do the Dyson evolutions (by `dyson_unique`). -/
theorem dyson_congr_of_subset {a₁ b₁ a₂ b₂ : ℝ} (F₁ : EvolutionFamily X a₁ b₁)
    (A₁ : BoundedPert X a₁ b₁) (F₂ : EvolutionFamily X a₂ b₂) (A₂ : BoundedPert X a₂ b₂)
    (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁)
    (hF : ∀ s t, a₂ ≤ s → s ≤ t → t ≤ b₂ → F₂.U t s = F₁.U t s)
    (hA : ∀ r ∈ Icc a₂ b₂, A₂.A r = A₁.A r) :
    ∀ s t, a₂ ≤ s → s ≤ t → t ≤ b₂ → (dyson F₂ A₂).U t s = (dyson F₁ A₁).U t s := by
  intro s t hs hst ht
  refine (dyson_unique F₂ A₂ (dyson F₁ A₁).U ?_ ?_ s t hs hst ht).symm
  · intro s hs _ x
    exact ((dyson F₁ A₁).continuousOn_fst (ha.trans hs) x).mono (Icc_subset_Icc le_rfl hb)
  · intro s t hs hst ht x
    rw [dyson_left F₁ A₁ ⟨ha.trans hs, hst, ht.trans hb⟩ x, hF s t hs hst ht]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hst] at hr
    simp only [hF r t (hs.trans hr.1) hr.2 ht, hA r ⟨hs.trans hr.1, hr.2.trans ht⟩]

/-- **Time-translation invariance** of the Dyson evolution of a semigroup with a constant
interaction: `U(t,s) = U_{[0,b-a]}(t-s, 0)`. -/
theorem dyson_ofExpSemigroup_const_eq_shift (S : ExpSemigroup X) (K : X →L[ℂ] X) {a b : ℝ} :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (dyson (ofExpSemigroup S a b) (const K)).U t s =
        (dyson (ofExpSemigroup S 0 (b - a)) (const K)).U (t - s) 0 := by
  intro s t hs hst ht
  set G := dyson (ofExpSemigroup S 0 (b - a)) (const (a := 0) (b := b - a) K) with hG
  refine (dyson_unique (ofExpSemigroup S a b) (const K) (fun t s => G.U (t - s) 0) ?_ ?_
    s t hs hst ht).symm
  · intro s hs hsb x
    exact (G.continuousOn_fst le_rfl x).comp (continuous_sub_right s).continuousOn
      fun τ hτ => ⟨sub_nonneg.2 hτ.1, by linarith [hτ.2]⟩
  · intro s t hs hst ht x
    have h1 := dyson_left (ofExpSemigroup S 0 (b - a)) (const (a := 0) (b := b - a) K)
      ⟨le_rfl, sub_nonneg.2 hst, by linarith⟩ x
    rw [← hG] at h1
    simp only [ofExpSemigroup_U, const_A, sub_zero] at h1 ⊢
    rw [h1]
    congr 1
    have h2 := intervalIntegral.integral_comp_sub_right
      (fun r => S.T (t - s - r) (K (G.U r 0 x))) (a := s) (b := t) s
    rw [sub_self] at h2
    rw [← h2]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have e : t - s - (r - s) = t - r := by ring
    simp only [e]

/-- Restriction for semigroup data with a constant interaction. -/
theorem dyson_ofExpSemigroup_const_mono (S : ExpSemigroup X) (K : X →L[ℂ] X)
    {a₁ b₁ a₂ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁) :
    ∀ s t, a₂ ≤ s → s ≤ t → t ≤ b₂ →
      (dyson (ofExpSemigroup S a₂ b₂) (const K)).U t s =
        (dyson (ofExpSemigroup S a₁ b₁) (const K)).U t s :=
  dyson_congr_of_subset (ofExpSemigroup S a₁ b₁) (const K) (ofExpSemigroup S a₂ b₂) (const K)
    ha hb (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)

/-! ### The perturbed semigroup -/

/-- **Constant perturbation gives a semigroup** (INF08 T8.6; `paper/main.tex`, line 1245, the
bounded-perturbation theorem): `(S.perturb K).T τ = U_{[0,τ]}(τ, 0)`, the Dyson evolution of
`(S, K)` on `[0, τ]` from `0` to `τ`. Growth constants `M = S.M`, `ω = S.ω + S.M ‖K‖`
(the bound of `norm_dyson_le`). Negative times carry no meaning. -/
def _root_.UnforcedLeray.Infra.ExpSemigroup.perturb (S : ExpSemigroup X) (K : X →L[ℂ] X) :
    ExpSemigroup X where
  T τ := (dyson (ofExpSemigroup S 0 τ) (const K)).U τ 0
  T_zero := (dyson (ofExpSemigroup S 0 0) (const K)).U_diag 0 ⟨le_rfl, le_rfl⟩
  T_add s t hs ht := by
    have hst : 0 ≤ s + t := add_nonneg hs ht
    set D := dyson (ofExpSemigroup S 0 (s + t)) (const (a := 0) (b := s + t) K) with hD
    have h1 : D.U (s + t) t = (dyson (ofExpSemigroup S 0 s) (const K)).U s 0 := by
      rw [hD, dyson_ofExpSemigroup_const_eq_shift S K t (s + t) ht (by linarith) le_rfl,
        add_sub_cancel_right, sub_zero]
      exact (dyson_ofExpSemigroup_const_mono S K le_rfl (by linarith) 0 s le_rfl hs le_rfl).symm
    have h2 : D.U t 0 = (dyson (ofExpSemigroup S 0 t) (const K)).U t 0 :=
      (dyson_ofExpSemigroup_const_mono S K le_rfl (by linarith) 0 t le_rfl ht le_rfl).symm
    rw [← h1, ← h2]
    exact (D.U_comp le_rfl ht (by linarith) le_rfl).symm
  T_cont x := by
    intro τ₀ hτ₀
    have hτ₀' : (0 : ℝ) ≤ τ₀ := hτ₀
    set D := dyson (ofExpSemigroup S 0 (τ₀ + 1)) (const (a := 0) (b := τ₀ + 1) K) with hD
    have hc : ContinuousOn (fun τ => (dyson (ofExpSemigroup S 0 τ) (const K)).U τ 0 x)
        (Icc 0 (τ₀ + 1)) := by
      refine (D.continuousOn_fst le_rfl x).congr fun τ hτ => ?_
      exact congrArg (fun T : X →L[ℂ] X => T x)
        (dyson_ofExpSemigroup_const_mono S K le_rfl hτ.2 0 τ le_rfl hτ.1 le_rfl)
    refine (hc τ₀ ⟨hτ₀', by linarith⟩).mono_of_mem_nhdsWithin ?_
    have : Icc (0 : ℝ) (τ₀ + 1) = Ici 0 ∩ Iic (τ₀ + 1) := (Ici_inter_Iic).symm
    rw [this]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  M := S.M
  ω := S.ω + S.M * ‖K‖
  M_nonneg := S.M_nonneg
  T_le τ hτ := by
    have h := norm_dyson_le (ofExpSemigroup S 0 τ) (const K) (M := S.M) (ω := S.ω) (C := ‖K‖)
      (fun s t _ hst _ => S.T_le (t - s) (sub_nonneg.2 hst)) (fun _ _ => le_rfl)
      0 τ le_rfl hτ le_rfl
    simpa only [sub_zero] using h

/-- **Constant perturbation of a semigroup** (INF08 T8.6): on every `[a,b]`, the Dyson evolution
of the semigroup `S` perturbed by the constant `K` is the perturbed semigroup at time `t - s`. -/
theorem dyson_ofExpSemigroup_const (S : ExpSemigroup X) (K : X →L[ℂ] X) {a b : ℝ} :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (dyson (ofExpSemigroup S a b) (const K)).U t s = (S.perturb K).T (t - s) := by
  intro s t hs hst ht
  rw [dyson_ofExpSemigroup_const_eq_shift S K s t hs hst ht]
  exact (dyson_ofExpSemigroup_const_mono S K le_rfl (by linarith) 0 (t - s) le_rfl
    (sub_nonneg.2 hst) le_rfl).symm

@[simp] theorem perturb_M (S : ExpSemigroup X) (K : X →L[ℂ] X) : (S.perturb K).M = S.M := rfl

@[simp] theorem perturb_ω (S : ExpSemigroup X) (K : X →L[ℂ] X) :
    (S.perturb K).ω = S.ω + S.M * ‖K‖ := rfl

/-- **Variation of constants** for the perturbed semigroup:
`P(t)x = S(t)x + ∫₀ᵗ S(t-r) K P(r) x dr` for `t ≥ 0`. -/
theorem perturb_T_apply_eq_duhamel (S : ExpSemigroup X) (K : X →L[ℂ] X) {t : ℝ} (ht : 0 ≤ t)
    (x : X) :
    (S.perturb K).T t x = S.T t x + ∫ r in (0 : ℝ)..t, S.T (t - r) (K ((S.perturb K).T r x)) := by
  have h := dyson_left (ofExpSemigroup S 0 t) (const (a := 0) (b := t) K) ⟨le_rfl, ht, le_rfl⟩ x
  simp only [ofExpSemigroup_U, const_A, sub_zero] at h
  rw [show (S.perturb K).T t = (dyson (ofExpSemigroup S 0 t) (const K)).U t 0 from rfl, h]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht] at hr
  have e := dyson_ofExpSemigroup_const S K (a := 0) (b := t) 0 r le_rfl hr.1 hr.2
  rw [sub_zero] at e
  simp only [e]

/-- **Uniqueness**: a family `V` with `V(t)x` continuous on `[0, ∞)` that satisfies the
variation-of-constants formula of `(S, K)` is the perturbed semigroup on `[0, ∞)`. -/
theorem perturb_unique (S : ExpSemigroup X) (K : X →L[ℂ] X) (V : ℝ → X →L[ℂ] X)
    (hcont : ∀ x, ContinuousOn (fun t => V t x) (Ici 0))
    (heq : ∀ t, 0 ≤ t → ∀ x, V t x = S.T t x + ∫ r in (0 : ℝ)..t, S.T (t - r) (K (V r x))) :
    ∀ t, 0 ≤ t → V t = (S.perturb K).T t := by
  intro t ht
  have h := dyson_unique (ofExpSemigroup S 0 t) (const (a := 0) (b := t) K)
    (fun τ σ => V (τ - σ)) ?_ ?_ 0 t le_rfl ht le_rfl
  · simp only [sub_zero] at h
    rw [h, dyson_ofExpSemigroup_const S K 0 t le_rfl ht le_rfl, sub_zero]
  · intro s hs _ x
    exact (hcont x).comp (continuous_sub_right s).continuousOn
      fun τ hτ => Set.mem_Ici.2 (sub_nonneg.2 hτ.1)
  · intro s τ hs hsτ hτ x
    simp only [ofExpSemigroup_U, const_A]
    rw [heq (τ - s) (sub_nonneg.2 hsτ) x]
    congr 1
    have h2 := intervalIntegral.integral_comp_sub_right
      (fun r => S.T (τ - s - r) (K (V r x))) (a := s) (b := τ) s
    rw [sub_self] at h2
    rw [← h2]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have e : τ - s - (r - s) = τ - r := by ring
    simp only [e]

/-! ### Bounded generators: Dyson of `e^{tS}` and `K` is `exp(t(S+K))` -/

/-- Continuity of `τ ↦ exp(τA)` in operator norm. -/
theorem continuous_exp_smul_real (A : X →L[ℂ] X) :
    Continuous fun τ : ℝ => NormedSpace.exp ((τ : ℂ) • A) :=
  continuous_iff_continuousAt.2 fun τ => (BanachExp.hasDerivAt_exp_smul A τ).1.continuousAt

/-- **The Duhamel formula on `[s,t]`** for bounded operators:
`exp((t-s)(S+K)) x = exp((t-s)S) x + ∫_s^t exp((t-r)S) K exp((r-s)(S+K)) x dr`
(the vendored `BanachExp.exp_add_eq_duhamel`, NonUniqueEuler `SectorSpace/BanachExp.lean`,
applied to `x` and translated by `s`). -/
theorem exp_smul_add_apply_eq_duhamel (S K : X →L[ℂ] X) (s t : ℝ) (x : X) :
    NormedSpace.exp (((t - s : ℝ) : ℂ) • (S + K)) x =
      NormedSpace.exp (((t - s : ℝ) : ℂ) • S) x +
        ∫ r in s..t, NormedSpace.exp (((t - r : ℝ) : ℂ) • S)
          (K (NormedSpace.exp (((r - s : ℝ) : ℂ) • (S + K)) x)) := by
  have hint : IntervalIntegrable (fun τ : ℝ => NormedSpace.exp (((t - s - τ : ℝ) : ℂ) • S) * K *
      NormedSpace.exp ((τ : ℂ) • (S + K))) volume 0 (t - s) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (((continuous_exp_smul_real S).comp (continuous_const.sub continuous_id)).mul
      continuous_const).mul (continuous_exp_smul_real (S + K))
  have h := congrArg (fun T : X →L[ℂ] X => T x) (BanachExp.exp_add_eq_duhamel S K (t - s))
  simp only [add_apply] at h
  rw [h, ContinuousLinearMap.intervalIntegral_apply hint]
  congr 1
  have h2 := intervalIntegral.integral_comp_sub_right
    (fun τ : ℝ => (NormedSpace.exp (((t - s - τ : ℝ) : ℂ) • S) * K *
      NormedSpace.exp ((τ : ℂ) • (S + K))) x) (a := s) (b := t) s
  rw [sub_self] at h2
  rw [← h2]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have e : t - s - (r - s) = t - r := by ring
  simp only [e, mul_apply_eq_comp]

/-- **Dyson of a bounded generator is `NormedSpace.exp`** (INF08 T8.6; BP1):
`Dyson(e^{tS}, K) = exp(t(S+K))`, i.e. on every `[a,b]`
`(dyson (ofExpSemigroup (ofExp S) a b) (const K)).U t s = exp((t-s)(S+K))`. -/
theorem dyson_ofExp_const (S K : X →L[ℂ] X) {a b : ℝ} :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (dyson (ofExpSemigroup (ExpSemigroup.ofExp S) a b) (const K)).U t s =
        NormedSpace.exp (((t - s : ℝ) : ℂ) • (S + K)) := by
  intro s t hs hst ht
  refine (dyson_unique (ofExpSemigroup (ExpSemigroup.ofExp S) a b) (const K)
    (fun t s => NormedSpace.exp (((t - s : ℝ) : ℂ) • (S + K))) ?_ ?_ s t hs hst ht).symm
  · intro s _ _ x
    exact ((continuous_exp_smul_apply (S + K) x).comp (continuous_sub_right s)).continuousOn
  · intro s t _ _ _ x
    simp only [ofExpSemigroup_U, const_A, ExpSemigroup.ofExp_T]
    exact exp_smul_add_apply_eq_duhamel S K s t x

/-- The perturbed semigroup of `e^{tS}` by `K` is `exp(t(S+K))` (`t ≥ 0`). -/
theorem perturb_ofExp_T (S K : X →L[ℂ] X) {t : ℝ} (ht : 0 ≤ t) :
    ((ExpSemigroup.ofExp S).perturb K).T t = NormedSpace.exp ((t : ℂ) • (S + K)) := by
  have h := dyson_ofExp_const S K (a := 0) (b := t) 0 t le_rfl ht le_rfl
  have e := dyson_ofExpSemigroup_const (ExpSemigroup.ofExp S) K (a := 0) (b := t) 0 t le_rfl ht
    le_rfl
  rw [e, sub_zero] at h
  exact h

end UnforcedLeray.Evolution
