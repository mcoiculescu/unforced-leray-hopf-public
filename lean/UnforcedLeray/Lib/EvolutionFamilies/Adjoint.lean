import UnforcedLeray.Lib.EvolutionFamilies.DysonRight
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The adjoint of the Dyson evolution in a Hilbert space (INF08 T8.3)

Scoping note `scoping/INF07-INF08-INF09-Evolution.md`, §5, target T8.3 (`paper/main.tex`,
lines 1586-1621 "converge strongly with their adjoints", 1669-1676; blueprint B0104, B0108,
B0245, B0246).

On a complex Hilbert space `H`, with `F*` strongly continuous on the triangle
(`EvolutionFamily.AdjointContinuous`) and `r ↦ A(r)* y` strongly measurable
(`BoundedPert.AdjointMeasurable`; automatic for operator-norm measurable `A`, see
`BoundedPert.adjointMeasurable_of_aestronglyMeasurable`, or for separable `H`):

* `EvolutionFamily.adjointRefl F`: `F'(τ,σ) = F(a+b-σ, a+b-τ)*`, the time-reflected adjoint
  family, again an evolution family on `[a,b]`; `BoundedPert.adjointRefl A`:
  `A'(ρ) = A(a+b-ρ)*`.
* `adjoint_dyson_eq`: `U(t,s)* = (dyson F' A')(a+b-s, a+b-t)` for `U = dyson F A`. The proof is
  a Gronwall argument on the weak defect `⟪y, U(t,s)x⟫ - ⟪V(a+b-s,a+b-t)y, x⟫`, which needs no
  strong measurability of `r ↦ U(t,r)* y` (it uses `dyson_right` for `U` and `dyson_left` for
  `V`).
* `continuousOn_adjoint_dyson`: the adjoint family `(s,t) ↦ U(t,s)* y` is strongly continuous
  on the triangle.
* `adjoint_dyson`: the adjoint Duhamel identity of the scoping note,
  `U(t,s)* y = F(t,s)* y + ∫_s^t F(r,s)* A(r)* U(t,r)* y dr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace Nat

namespace UnforcedLeray.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {a b : ℝ}

local notation "adj" => ContinuousLinearMap.adjoint

/-- `⟪∫ f, x⟫ = ∫ ⟪f r, x⟫` for an interval integrable `f` (`s ≤ t`). -/
theorem inner_integral_left {s t : ℝ} (hst : s ≤ t) {f : ℝ → H}
    (hf : IntervalIntegrable f volume s t) (x : H) :
    ⟪∫ r in s..t, f r, x⟫_ℂ = ∫ r in s..t, ⟪f r, x⟫_ℂ := by
  have h := (innerSL ℂ x).intervalIntegral_comp_comm hf
  simp only [innerSL_apply_apply] at h
  rw [← inner_conj_symm, ← h]
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst, ← integral_conj]
  congr 1
  ext r
  exact inner_conj_symm _ _

/-- `⟪x, ∫ f⟫ = ∫ ⟪x, f r⟫` for an interval integrable `f`. -/
theorem inner_integral_right {s t : ℝ} {f : ℝ → H} (hf : IntervalIntegrable f volume s t)
    (x : H) : ⟪x, ∫ r in s..t, f r⟫_ℂ = ∫ r in s..t, ⟪x, f r⟫_ℂ := by
  have h := (innerSL ℂ x).intervalIntegral_comp_comm hf
  simp only [innerSL_apply_apply] at h
  exact h.symm

omit [CompleteSpace H] in
theorem IntervalIntegrable.const_inner' {s t : ℝ} {f : ℝ → H}
    (hf : IntervalIntegrable f volume s t) (y : H) :
    IntervalIntegrable (fun r => ⟪y, f r⟫_ℂ) volume s t :=
  ⟨Integrable.const_inner y hf.1, Integrable.const_inner y hf.2⟩

/-- `∫_s^t (t - r)^n dr = (t - s)^{n+1}/(n+1)`. -/
theorem integral_sub_pow_left (s t : ℝ) (n : ℕ) :
    ∫ r in s..t, (t - r) ^ n = (t - s) ^ (n + 1) / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun r => r ^ n) t, integral_pow, sub_self,
    zero_pow (Nat.succ_ne_zero n), sub_zero]

/-- The reflection `(s,t) ↦ (a+b-t, a+b-s)` of the time triangle. -/
def reflectPair (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (a + b - p.2, a + b - p.1)

theorem continuous_reflectPair (a b : ℝ) : Continuous (reflectPair a b) :=
  (continuous_const.sub continuous_snd).prodMk (continuous_const.sub continuous_fst)

theorem reflectPair_mem {p : ℝ × ℝ} (hp : p ∈ {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}) :
    reflectPair a b p ∈ {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨by simp only [reflectPair]; linarith, by simp only [reflectPair]; linarith,
    by simp only [reflectPair]; linarith⟩

namespace EvolutionFamily

/-- Strong continuity of the adjoint family on the triangle (hypothesis of INF08 T8.3). -/
def AdjointContinuous (F : EvolutionFamily H a b) : Prop :=
  ∀ y, ContinuousOn (fun p : ℝ × ℝ => adj (F.U p.2 p.1) y) {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}

/-- **The time-reflected adjoint family** `F'(τ,σ) = F(a+b-σ, a+b-τ)*`. -/
def adjointRefl (F : EvolutionFamily H a b) (hF : F.AdjointContinuous) : EvolutionFamily H a b where
  U τ σ := adj (F.U (a + b - σ) (a + b - τ))
  U_diag t ht := by
    rw [F.U_diag _ ⟨by linarith [ht.2], by linarith [ht.1]⟩, ContinuousLinearMap.adjoint_one]
  U_comp s r t hs hsr hrt ht := by
    have h := F.U_comp (s := a + b - t) (r := a + b - r) (t := a + b - s) (by linarith)
      (by linarith) (by linarith) (by linarith)
    rw [← h, ContinuousLinearMap.adjoint_comp]
  U_cont y := by
    have h := (hF y).comp (continuous_reflectPair a b).continuousOn fun _ hp => reflectPair_mem hp
    refine h.congr fun p _ => ?_
    simp only [Function.comp, reflectPair]
  U_bdd := ⟨F.M, fun s t hs hst ht => by
    rw [LinearIsometryEquiv.norm_map]
    exact F.norm_le (by linarith) (by linarith) (by linarith)⟩

theorem adjointRefl_U (F : EvolutionFamily H a b) (hF : F.AdjointContinuous) (τ σ : ℝ) :
    (F.adjointRefl hF).U τ σ = adj (F.U (a + b - σ) (a + b - τ)) := rfl

end EvolutionFamily

namespace BoundedPert

/-- Strong measurability of `r ↦ A(r)* y` (hypothesis of INF08 T8.3). -/
def AdjointMeasurable (A : BoundedPert H a b) : Prop :=
  ∀ y, AEStronglyMeasurable (fun r => adj (A.A r) y) (volume.restrict (Icc a b))

/-- Operator-norm measurability (bypass BP6) implies `AdjointMeasurable`. -/
theorem adjointMeasurable_of_aestronglyMeasurable (A : BoundedPert H a b)
    (hA : AEStronglyMeasurable A.A (volume.restrict (Icc a b))) : A.AdjointMeasurable := fun y =>
  (ContinuousLinearMap.apply ℂ H y).continuous.comp_aestronglyMeasurable
    ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := H) (F := H)).continuous.comp_aestronglyMeasurable
      hA)

theorem measurePreserving_reflect (a b : ℝ) :
    MeasurePreserving (fun ρ : ℝ => a + b - ρ) (volume.restrict (Icc a b))
      (volume.restrict (Icc a b)) := by
  have h := (Measure.measurePreserving_sub_left volume (a + b)).restrict_preimage
    (measurableSet_Icc (a := a) (b := b))
  have hpre : (fun ρ : ℝ => a + b - ρ) ⁻¹' Icc a b = Icc a b := by
    ext ρ
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rwa [hpre] at h

/-- **The time-reflected adjoint interaction** `A'(ρ) = A(a+b-ρ)*`. -/
def adjointRefl (A : BoundedPert H a b) (hA : A.AdjointMeasurable) : BoundedPert H a b where
  A ρ := adj (A.A (a + b - ρ))
  meas y := (hA y).comp_measurePreserving (measurePreserving_reflect a b)
  bdd := ⟨A.C, fun ρ hρ => by
    rw [LinearIsometryEquiv.norm_map]
    exact A.norm_le ⟨by linarith [hρ.2], by linarith [hρ.1]⟩⟩

theorem adjointRefl_A (A : BoundedPert H a b) (hA : A.AdjointMeasurable) (ρ : ℝ) :
    (A.adjointRefl hA).A ρ = adj (A.A (a + b - ρ)) := rfl

end BoundedPert

variable (F : EvolutionFamily H a b) (A : BoundedPert H a b)

/-- **Identification of the adjoint Dyson evolution** (INF08 T8.3): for `a ≤ s ≤ t ≤ b`,
`(dyson F A)(t,s)* = (dyson F' A')(a+b-s, a+b-t)` with `F' = F.adjointRefl hF`,
`A' = A.adjointRefl hA`. -/
theorem adjoint_dyson_eq (hF : F.AdjointContinuous) (hA : A.AdjointMeasurable) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    adj ((dyson F A).U t s) =
      (dyson (F.adjointRefl hF) (A.adjointRefl hA)).U (a + b - s) (a + b - t) := by
  set U := dyson F A with hU
  set F' := F.adjointRefl hF with hF'
  set A' := A.adjointRefl hA with hA'
  set V := dyson F' A' with hV
  -- the weak defect, for fixed `t` and `y`
  have key : ∀ y : H, ∀ s ∈ Icc a t, ∀ x : H,
      ⟪y, U.U t s x⟫_ℂ = ⟪V.U (a + b - s) (a + b - t) y, x⟫_ℂ := by
    intro y
    set δ : ℝ → H → ℂ := fun s x => ⟪y, U.U t s x⟫_ℂ - ⟪V.U (a + b - s) (a + b - t) y, x⟫_ℂ
      with hδ
    have hσ : a ≤ a + b - t := by linarith
    -- the integral identity `δ s x = ∫_s^t δ r (A r F(r,s) x) dr`
    have hrec : ∀ s ∈ Icc a t, ∀ x : H,
        δ s x = ∫ r in s..t, δ r (A.A r (F.U r s x)) := by
      intro s hs' x
      have hs := hs'.1
      have hst := hs'.2
      have hτ : a + b - s ≤ b := by linarith
      have hστ : a + b - t ≤ a + b - s := by linarith
      have hFc : ContinuousOn (fun r => F.U r s x) (Icc s t) :=
        (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht)
      -- the `U` side (right Duhamel identity)
      have hiU := U.intervalIntegrable_integrand A hs hst ht hFc
      have hU1 : ⟪y, U.U t s x⟫_ℂ = ⟪y, F.U t s x⟫_ℂ +
          ∫ r in s..t, ⟪y, U.U t r (A.A r (F.U r s x))⟫_ℂ := by
        rw [hU, dyson_right F A ⟨hs, hst, ht⟩ x, inner_add_right, ← hU,
          inner_integral_right hiU]
      -- the `V` side (left Duhamel identity, then the reflection `ρ = a + b - r`)
      have hiV := F'.intervalIntegrable_integrand A' hσ hστ hτ
        ((V.continuousOn_fst hσ y).mono (Icc_subset_Icc le_rfl hτ))
      have hV1 : ⟪V.U (a + b - s) (a + b - t) y, x⟫_ℂ = ⟪y, F.U t s x⟫_ℂ +
          ∫ r in s..t, ⟪V.U (a + b - r) (a + b - t) y, A.A r (F.U r s x)⟫_ℂ := by
        rw [hV, dyson_left F' A' ⟨hσ, hστ, hτ⟩ y, inner_add_left, ← hV,
          inner_integral_left hστ hiV]
        congr 1
        · rw [hF', EvolutionFamily.adjointRefl_U, ContinuousLinearMap.adjoint_inner_left,
            sub_sub_cancel, sub_sub_cancel]
        · have hφ : ∀ ρ, ⟪F'.U (a + b - s) ρ (A'.A ρ (V.U ρ (a + b - t) y)), x⟫_ℂ =
              (fun r => ⟪V.U (a + b - r) (a + b - t) y, A.A r (F.U r s x)⟫_ℂ) (a + b - ρ) := by
            intro ρ
            simp only [hF', hA', EvolutionFamily.adjointRefl_U, BoundedPert.adjointRefl_A,
              ContinuousLinearMap.adjoint_inner_left, sub_sub_cancel]
          simp only [hφ]
          rw [intervalIntegral.integral_comp_sub_left
            (fun r => ⟪V.U (a + b - r) (a + b - t) y, A.A r (F.U r s x)⟫_ℂ) (a + b),
            sub_sub_cancel, sub_sub_cancel]
      -- integrability of the two scalar integrands
      have hi1 : IntervalIntegrable (fun r => ⟪y, U.U t r (A.A r (F.U r s x))⟫_ℂ) volume s t :=
        IntervalIntegrable.const_inner' hiU y
      have hi2 : IntervalIntegrable
          (fun r => ⟪V.U (a + b - r) (a + b - t) y, A.A r (F.U r s x)⟫_ℂ) volume s t := by
        have hVc : ContinuousOn (fun r => V.U (a + b - r) (a + b - t) y) (Icc s t) :=
          (V.continuousOn_fst hσ y).comp (continuous_const.sub continuous_id).continuousOn
            fun r hr => ⟨by show a + b - t ≤ a + b - r; linarith [hr.2],
              by show a + b - r ≤ b; linarith [hr.1]⟩
        have hw : AEStronglyMeasurable (fun r => A.A r (F.U r s x)) (volume.restrict (Ioc s t)) :=
          aestronglyMeasurable_clm_apply (fun v => (A.meas v).mono_measure
            (Measure.restrict_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs ht)) le_rfl))
            ((hFc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
        refine intervalIntegrable_of_bound (K := V.M * ‖y‖ * (A.C * (F.M * ‖x‖))) hst
          (((hVc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).inner hw)
          fun r hr => ?_
        refine (norm_inner_le_norm _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
          (mul_nonneg V.M_nonneg (norm_nonneg _)))
        · exact V.norm_apply_le hσ (by linarith [hr.2]) (by linarith [hr.1]) y
        · refine ((A.A r).le_opNorm _).trans (mul_le_mul (A.norm_le ⟨by linarith [hr.1], by
            linarith [hr.2]⟩) (F.norm_apply_le hs hr.1.le (hr.2.trans ht) x) (norm_nonneg _)
            A.C_nonneg)
      show δ s x = _
      rw [hδ]
      simp only
      rw [hU1, hV1, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hi1 hi2]
    -- Gronwall: `‖δ s x‖ ≤ K (m (t - s))^n / n! ‖x‖`
    obtain ⟨m, hm_def⟩ : ∃ m, m = F.M * A.C := ⟨_, rfl⟩
    have hm : 0 ≤ m := hm_def ▸ mul_nonneg F.M_nonneg A.C_nonneg
    set K := (U.M + V.M) * ‖y‖ with hK
    have hind : ∀ n : ℕ, ∀ s ∈ Icc a t, ∀ x : H,
        ‖δ s x‖ ≤ K * ((m * (t - s)) ^ n / n !) * ‖x‖ := by
      intro n
      induction n with
      | zero =>
        intro s hs x
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, hδ]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖⟪y, U.U t s x⟫_ℂ‖ ≤ ‖y‖ * (U.M * ‖x‖) :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
            (U.norm_apply_le hs.1 hs.2 ht x) (norm_nonneg _))
        have h2 : ‖⟪V.U (a + b - s) (a + b - t) y, x⟫_ℂ‖ ≤ V.M * ‖y‖ * ‖x‖ :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
            (V.norm_apply_le hσ (by linarith [hs.2]) (by linarith [hs.1]) y) (norm_nonneg _))
        calc ‖⟪y, U.U t s x⟫_ℂ‖ + ‖⟪V.U (a + b - s) (a + b - t) y, x⟫_ℂ‖
            ≤ ‖y‖ * (U.M * ‖x‖) + V.M * ‖y‖ * ‖x‖ := add_le_add h1 h2
          _ = (U.M + V.M) * ‖y‖ * ‖x‖ := by ring
      | succ n ih =>
        intro s hs x
        rw [hrec s hs x]
        calc ‖∫ r in s..t, δ r (A.A r (F.U r s x))‖
            ≤ ∫ r in s..t, (K * (m ^ (n + 1) / n !) * ‖x‖) * (t - r) ^ n := by
              refine intervalIntegral.norm_integral_le_of_norm_le hs.2
                (ae_of_all _ fun r hr => ?_)
                ((continuous_const.mul ((continuous_const.sub continuous_id).pow n)).intervalIntegrable
                  _ _)
              have hr' : r ∈ Icc a t := ⟨hs.1.trans hr.1.le, hr.2⟩
              have hw : ‖A.A r (F.U r s x)‖ ≤ m * ‖x‖ := by
                rw [hm_def, mul_comm F.M, mul_assoc]
                exact ((A.A r).le_opNorm _).trans (mul_le_mul (A.norm_le ⟨hr'.1, hr.2.trans ht⟩)
                  (F.norm_apply_le hs.1 hr.1.le (hr.2.trans ht) x) (norm_nonneg _) A.C_nonneg)
              have hK0 : 0 ≤ K := mul_nonneg (add_nonneg U.M_nonneg V.M_nonneg) (norm_nonneg _)
              calc ‖δ r (A.A r (F.U r s x))‖
                  ≤ K * ((m * (t - r)) ^ n / n !) * ‖A.A r (F.U r s x)‖ := ih r hr' _
                _ ≤ K * ((m * (t - r)) ^ n / n !) * (m * ‖x‖) :=
                    mul_le_mul_of_nonneg_left hw (mul_nonneg hK0 (by
                      have : 0 ≤ m * (t - r) := mul_nonneg hm (by linarith [hr.2])
                      positivity))
                _ = (K * (m ^ (n + 1) / n !) * ‖x‖) * (t - r) ^ n := by
                    rw [mul_pow, pow_succ]; ring
          _ = (K * (m ^ (n + 1) / n !) * ‖x‖) * ((t - s) ^ (n + 1) / (n + 1)) := by
              rw [intervalIntegral.integral_const_mul, integral_sub_pow_left]
          _ = K * ((m * (t - s)) ^ (n + 1) / (n + 1)!) * ‖x‖ := by
              rw [mul_pow m (t - s), Nat.factorial_succ]
              push_cast
              field_simp <;> ring
    intro s hs x
    have hlim : Tendsto (fun n : ℕ => K * ((m * (t - s)) ^ n / n !) * ‖x‖) atTop
        (𝓝 (K * 0 * ‖x‖)) :=
      ((FloorSemiring.tendsto_pow_div_factorial_atTop (m * (t - s))).const_mul K).mul_const _
    rw [mul_zero, zero_mul] at hlim
    have h0 : ‖δ s x‖ ≤ 0 := ge_of_tendsto' hlim fun n => hind n s hs x
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  ext y
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact key y s ⟨hs, hst⟩ x

/-- **Strong continuity of the adjoint Dyson family** (INF08 T8.3): `(s,t) ↦ U(t,s)* y` is
continuous on the triangle. -/
theorem continuousOn_adjoint_dyson (hF : F.AdjointContinuous) (hA : A.AdjointMeasurable) (y : H) :
    ContinuousOn (fun p : ℝ × ℝ => adj ((dyson F A).U p.2 p.1) y)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
  have h := ((dyson (F.adjointRefl hF) (A.adjointRefl hA)).U_cont y).comp
    (continuous_reflectPair a b).continuousOn fun _ hp => reflectPair_mem hp
  refine h.congr fun p hp => ?_
  show _ = (dyson (F.adjointRefl hF) (A.adjointRefl hA)).U (a + b - p.1) (a + b - p.2) y
  rw [adjoint_dyson_eq F A hF hA hp.1 hp.2.1 hp.2.2]

/-- **Adjoint Duhamel identity** (INF08 T8.3 `adjoint_dyson`; `paper/main.tex`, lines
1669-1676, B0108): for `U = dyson F A`,
`U(t,s)* y = F(t,s)* y + ∫_s^t F(r,s)* A(r)* U(t,r)* y dr`. -/
theorem adjoint_dyson (hF : F.AdjointContinuous) (hA : A.AdjointMeasurable) {s t : ℝ} (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (y : H) :
    adj ((dyson F A).U t s) y =
      adj (F.U t s) y +
      ∫ r in s..t, adj (F.U r s) (adj (A.A r) (adj ((dyson F A).U t r) y)) := by
  obtain ⟨hs, hst, ht⟩ := h
  have hσ : a ≤ a + b - t := by linarith
  have hστ : a + b - t ≤ a + b - s := by linarith
  have hτ : a + b - s ≤ b := by linarith
  rw [adjoint_dyson_eq F A hF hA hs hst ht,
    dyson_left (F.adjointRefl hF) (A.adjointRefl hA) ⟨hσ, hστ, hτ⟩ y]
  congr 1
  · rw [EvolutionFamily.adjointRefl_U, sub_sub_cancel, sub_sub_cancel]
  · have hφ : ∀ ρ ∈ uIcc (a + b - t) (a + b - s),
        (F.adjointRefl hF).U (a + b - s) ρ ((A.adjointRefl hA).A ρ
          ((dyson (F.adjointRefl hF) (A.adjointRefl hA)).U ρ (a + b - t) y)) =
        (fun r => adj (F.U r s) (adj (A.A r) (adj ((dyson F A).U t r) y))) (a + b - ρ) := by
      intro ρ hρ
      rw [uIcc_of_le hστ] at hρ
      simp only [EvolutionFamily.adjointRefl_U, BoundedPert.adjointRefl_A, sub_sub_cancel]
      rw [adjoint_dyson_eq F A hF hA (by linarith [hρ.2]) (by linarith [hρ.1]) ht,
        sub_sub_cancel]
    rw [intervalIntegral.integral_congr hφ, intervalIntegral.integral_comp_sub_left
      (fun r => adj (F.U r s) (adj (A.A r) (adj ((dyson F A).U t r) y))) (a + b),
      sub_sub_cancel, sub_sub_cancel]

/-- **Adjoint Duhamel identity, other order** (INF08 T8.3; the adjoint of `dyson_left`):
for `U = dyson F A`, `U(t,s)* y = F(t,s)* y + ∫_s^t U(r,s)* A(r)* F(t,r)* y dr`. -/
theorem adjoint_dyson_left (hF : F.AdjointContinuous) (hA : A.AdjointMeasurable) {s t : ℝ}
    (h : a ≤ s ∧ s ≤ t ∧ t ≤ b) (y : H) :
    adj ((dyson F A).U t s) y =
      adj (F.U t s) y +
      ∫ r in s..t, adj ((dyson F A).U r s) (adj (A.A r) (adj (F.U t r) y)) := by
  obtain ⟨hs, hst, ht⟩ := h
  have hσ : a ≤ a + b - t := by linarith
  have hστ : a + b - t ≤ a + b - s := by linarith
  have hτ : a + b - s ≤ b := by linarith
  rw [adjoint_dyson_eq F A hF hA hs hst ht,
    dyson_right (F.adjointRefl hF) (A.adjointRefl hA) ⟨hσ, hστ, hτ⟩ y]
  congr 1
  · rw [EvolutionFamily.adjointRefl_U, sub_sub_cancel, sub_sub_cancel]
  · have hφ : ∀ ρ ∈ uIcc (a + b - t) (a + b - s),
        (dyson (F.adjointRefl hF) (A.adjointRefl hA)).U (a + b - s) ρ
          ((A.adjointRefl hA).A ρ ((F.adjointRefl hF).U ρ (a + b - t) y)) =
        (fun r => adj ((dyson F A).U r s) (adj (A.A r) (adj (F.U t r) y))) (a + b - ρ) := by
      intro ρ hρ
      rw [uIcc_of_le hστ] at hρ
      simp only [EvolutionFamily.adjointRefl_U, BoundedPert.adjointRefl_A, sub_sub_cancel]
      rw [adjoint_dyson_eq F A hF hA hs (by linarith [hρ.2]) (by linarith [hρ.1]),
        sub_sub_cancel]
    rw [intervalIntegral.integral_congr hφ, intervalIntegral.integral_comp_sub_left
      (fun r => adj ((dyson F A).U r s) (adj (A.A r) (adj (F.U t r) y))) (a + b),
      sub_sub_cancel, sub_sub_cancel]

end UnforcedLeray.Evolution
