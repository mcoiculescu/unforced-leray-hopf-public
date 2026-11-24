import UnforcedLeray.Cons.L2.CanonicalBranch.DysonConvergence

/-!
# Passage from bounded Yosida transport to the actual first Dyson stage

This downstream leaf preserves the audited Hermite convergence boundary while developing the
varying-base mild comparison needed to transfer the sharp energy estimate to the concrete family.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate Topology

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-- Subtracting the two concrete left mild equations with a common bounded perturbation leaves
the free-base difference and the difference of their Duhamel integrands. -/
theorem dyson_common_interaction_sub_integral {a b s t : ℝ}
    (E₁ E₂ : EvolutionFamily XG a b) (A : BoundedPert XG a b)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    (Evolution.dyson E₁ A).U t s x - (Evolution.dyson E₂ A).U t s x =
      (E₁.U t s x - E₂.U t s x) +
        ∫ r in s..t,
          E₁.U t r (A.A r ((Evolution.dyson E₁ A).U r s x)) -
            E₂.U t r (A.A r ((Evolution.dyson E₂ A).U r s x)) := by
  have hcont₁ : ContinuousOn
      (fun r => (Evolution.dyson E₁ A).U r s x) (Icc s t) :=
    ((Evolution.dyson E₁ A).continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hcont₂ : ContinuousOn
      (fun r => (Evolution.dyson E₂ A).U r s x) (Icc s t) :=
    ((Evolution.dyson E₂ A).continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hI₁ : IntervalIntegrable
      (fun r => E₁.U t r (A.A r ((Evolution.dyson E₁ A).U r s x))) volume s t :=
    E₁.intervalIntegrable_integrand A has hst ht hcont₁
  have hI₂ : IntervalIntegrable
      (fun r => E₂.U t r (A.A r ((Evolution.dyson E₂ A).U r s x))) volume s t :=
    E₂.intervalIntegrable_integrand A has hst ht hcont₂
  rw [Evolution.dyson_left E₁ A ⟨has, hst, ht⟩ x,
    Evolution.dyson_left E₂ A ⟨has, hst, ht⟩ x,
    intervalIntegral.integral_sub hI₁ hI₂]
  exact add_sub_add_comm _ _ _ _

/-- Quantitative varying-base mild comparison. A small base error on the fixed compact orbit,
combined with contraction of the approximating base, yields the usual Volterra inequality. -/
theorem dyson_common_interaction_difference_golden_rule {a b s t L η η₀ : ℝ}
    (E₁ E₂ : EvolutionFamily XG a b) (A : BoundedPert XG a b)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hη₀ : 0 ≤ η₀)
    (hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ L)
    (hE₁ : ∀ r ∈ Icc s t, ‖E₁.U t r‖ ≤ 1)
    (x : XG)
    (hinit : ‖E₁.U t s x - E₂.U t s x‖ ≤ η₀)
    (herr : ∀ r ∈ Icc s t,
      ‖(E₁.U t r - E₂.U t r) (A.A r ((Evolution.dyson E₂ A).U r s x))‖ ≤ η) :
    ‖(Evolution.dyson E₁ A).U t s x - (Evolution.dyson E₂ A).U t s x‖ ≤
      η₀ + (t-s) * η + L *
        (∫ r in s..t,
          ‖(Evolution.dyson E₁ A).U r s x - (Evolution.dyson E₂ A).U r s x‖) := by
  let F₁ := Evolution.dyson E₁ A
  let F₂ := Evolution.dyson E₂ A
  have hF₁cont : ContinuousOn (fun r => F₁.U r s x) (Icc s t) :=
    (F₁.continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hF₂cont : ContinuousOn (fun r => F₂.U r s x) (Icc s t) :=
    (F₂.continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hdiffcont : ContinuousOn (fun r => F₁.U r s x - F₂.U r s x) (Icc s t) :=
    hF₁cont.sub hF₂cont
  have hVol : IntervalIntegrable
      (fun r => E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x))) volume s t :=
    E₁.intervalIntegrable_integrand A has hst ht hdiffcont
  have hBase₁ : IntervalIntegrable
      (fun r => E₁.U t r (A.A r (F₂.U r s x))) volume s t :=
    E₁.intervalIntegrable_integrand A has hst ht hF₂cont
  have hBase₂ : IntervalIntegrable
      (fun r => E₂.U t r (A.A r (F₂.U r s x))) volume s t :=
    E₂.intervalIntegrable_integrand A has hst ht hF₂cont
  have hErr : IntervalIntegrable
      (fun r => (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x))) volume s t := by
    have hh := hBase₁.sub hBase₂
    refine hh.congr ?_
    intro r hr
    simp only [ContinuousLinearMap.sub_apply]
  have hsplit : ∀ r ∈ uIcc s t,
      E₁.U t r (A.A r (F₁.U r s x)) - E₂.U t r (A.A r (F₂.U r s x)) =
        E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x)) +
          (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x)) := by
    intro r hr
    simpa [F₁, F₂] using clm_mild_integrand_split
      (E := E₁.U t r) (A := A.A r) (G := E₂.U t r)
      (F₁.U r s x) (F₂.U r s x)
  have hsub := dyson_common_interaction_sub_integral E₁ E₂ A has hst ht x
  have hsplitInt :
      (∫ r in s..t,
        E₁.U t r (A.A r (F₁.U r s x)) - E₂.U t r (A.A r (F₂.U r s x))) =
      (∫ r in s..t, E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x))) +
        ∫ r in s..t, (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x)) := by
    rw [intervalIntegral.integral_congr (fun r hr => hsplit r hr)]
    exact intervalIntegral.integral_add hVol hErr
  rw [hsplitInt] at hsub
  have hy : IntervalIntegrable
      (fun r => L * ‖F₁.U r s x - F₂.U r s x‖) volume s t :=
    (continuous_norm.comp_continuousOn hdiffcont).const_mul L |>.intervalIntegrable_of_Icc hst
  have hVolBound :
      ‖∫ r in s..t, E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x))‖ ≤
        L * (∫ r in s..t, ‖F₁.U r s x - F₂.U r s x‖) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hst
      (ae_of_all _ fun r hr => ?_) hy).trans_eq ?_
    · have hr' : r ∈ Icc s t := ⟨hr.1.le, hr.2⟩
      have hAr := hA r ⟨has.trans hr'.1, hr'.2.trans ht⟩
      calc
        ‖E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x))‖ ≤
            ‖E₁.U t r‖ * ‖A.A r (F₁.U r s x - F₂.U r s x)‖ := (E₁.U t r).le_opNorm _
        _ ≤ 1 * (L * ‖F₁.U r s x - F₂.U r s x‖) := by
          calc
            _ ≤ ‖E₁.U t r‖ * (‖A.A r‖ * ‖F₁.U r s x - F₂.U r s x‖) := by
              gcongr
              exact (A.A r).le_opNorm _
            _ ≤ 1 * (L * ‖F₁.U r s x - F₂.U r s x‖) := by
              gcongr
              exact hE₁ r hr'
        _ = L * ‖F₁.U r s x - F₂.U r s x‖ := by ring
    · rw [intervalIntegral.integral_const_mul]
  have hErrBound :
      ‖∫ r in s..t, (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x))‖ ≤ (t-s) * η := by
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun _ : ℝ => η) hst
      (ae_of_all _ fun r hr => ?_)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => η) volume s t)).trans_eq ?_
    · exact herr r ⟨hr.1.le, hr.2⟩
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  calc
    ‖F₁.U t s x - F₂.U t s x‖ ≤
        ‖E₁.U t s x - E₂.U t s x‖ +
          ‖(∫ r in s..t, E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x))) +
            (∫ r in s..t, (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x)))‖ := by
      rw [hsub]
      exact norm_add_le _ _
    _ ≤ η₀ +
        (‖(∫ r in s..t, E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x)))‖ +
          ‖(∫ r in s..t, (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x)))‖) := by
      exact add_le_add hinit
        (norm_add_le
          (∫ r in s..t, E₁.U t r (A.A r (F₁.U r s x - F₂.U r s x)))
          (∫ r in s..t, (E₁.U t r - E₂.U t r) (A.A r (F₂.U r s x))))
    _ ≤ η₀ + (L * (∫ r in s..t, ‖F₁.U r s x - F₂.U r s x‖) + (t-s) * η) := by
      gcongr
    _ = η₀ + (t-s) * η + L *
        (∫ r in s..t, ‖F₁.U r s x - F₂.U r s x‖) := by ring

/-- Uniform compact-orbit convergence of the free bases passes through a common bounded Dyson
perturbation by the golden-rule estimate and Gronwall. The compact set need only contain the
initial vector and the fixed orbit `A(r)F(r,s)x`. -/
theorem dyson_common_interaction_tendstoUniformlyOn_of_base_tendsto
    {a b s t L : ℝ} (Eₙ : ℕ → EvolutionFamily XG a b) (E : EvolutionFamily XG a b)
    (A : BoundedPert XG a b) (x : XG)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (hL : 0 ≤ L)
    (hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ L)
    (hcontract : ∀ N r u, r ∈ Icc s t → u ∈ Icc s t → r ≤ u →
      ‖(Eₙ N).U u r‖ ≤ 1)
    {K : Set XG} (hK : IsCompact K) (hxK : x ∈ K)
    (horbit : ∀ r ∈ Icc s t, A.A r ((Evolution.dyson E A).U r s x) ∈ K)
    (hbase : TendstoUniformlyOn
      (fun N : ℕ => fun p : XG × (ℝ × ℝ) => (Eₙ N).U p.2.2 p.2.1 p.1)
      (fun p : XG × (ℝ × ℝ) => E.U p.2.2 p.2.1 p.1)
      atTop (K ×ˢ Evolution.triangle s t)) :
    TendstoUniformlyOn
      (fun N : ℕ => fun u : Icc s t => (Evolution.dyson (Eₙ N) A).U u.1 s x)
      (fun u : Icc s t => (Evolution.dyson E A).U u.1 s x) atTop Set.univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let Δ := t - s
  let C := Real.exp (L * Δ)
  let η := ε / (2 * (1 + Δ) * C)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hst
  have hC : 0 < C := Real.exp_pos _
  have hη : 0 < η := by dsimp [η, C]; positivity
  have hbaseN := Metric.tendstoUniformlyOn_iff.1 hbase η hη
  filter_upwards [hbaseN] with N hbaseN u hu
  have hus : s ≤ u.1 := u.2.1
  have hut : u.1 ≤ t := u.2.2
  have hFcont₁ : ContinuousOn
      (fun r => (Evolution.dyson (Eₙ N) A).U r s x) (Icc s t) :=
    ((Evolution.dyson (Eₙ N) A).continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hFcont₂ : ContinuousOn
      (fun r => (Evolution.dyson E A).U r s x) (Icc s t) :=
    ((Evolution.dyson E A).continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
  have hy : ContinuousOn
      (fun r => ‖(Evolution.dyson (Eₙ N) A).U r s x -
        (Evolution.dyson E A).U r s x‖) (Icc s t) :=
    continuous_norm.comp_continuousOn (hFcont₁.sub hFcont₂)
  have hineq : ∀ v ∈ Icc s t,
      ‖(Evolution.dyson (Eₙ N) A).U v s x - (Evolution.dyson E A).U v s x‖ ≤
        η * (1 + Δ) + ∫ r in s..v,
          L * ‖(Evolution.dyson (Eₙ N) A).U r s x - (Evolution.dyson E A).U r s x‖ := by
    intro v hv
    have hinit : ‖(Eₙ N).U v s x - E.U v s x‖ ≤ η := by
      have hpair : (s, v) ∈ Evolution.triangle s t := ⟨le_rfl, hv.1, hv.2⟩
      have hh := hbaseN (x, (s, v)) ⟨hxK, hpair⟩
      have hh' : dist (E.U v s x) ((Eₙ N).U v s x) < η := by simpa using hh
      rw [dist_eq_norm, norm_sub_rev] at hh'
      exact hh'.le
    have herr : ∀ r ∈ Icc s v,
        ‖((Eₙ N).U v r - E.U v r)
          (A.A r ((Evolution.dyson E A).U r s x))‖ ≤ η := by
      intro r hr
      have hrK := horbit r ⟨hr.1, hr.2.trans hv.2⟩
      have hpair : (r, v) ∈ Evolution.triangle s t :=
        ⟨hr.1, hr.2, hv.2⟩
      have hh := hbaseN (A.A r ((Evolution.dyson E A).U r s x), (r, v))
        ⟨hrK, hpair⟩
      have hh' : dist
          (E.U v r (A.A r ((Evolution.dyson E A).U r s x)))
          ((Eₙ N).U v r (A.A r ((Evolution.dyson E A).U r s x))) < η := by
        simpa using hh
      rw [dist_eq_norm, norm_sub_rev] at hh'
      exact hh'.le
    have hgold := dyson_common_interaction_difference_golden_rule
      (Eₙ N) E A has hv.1 (le_trans hv.2 ht) hL hη.le hη.le
      hA (fun r hr => hcontract N r v ⟨hr.1, hr.2.trans hv.2⟩
        ⟨hv.1, hv.2⟩ hr.2)
      x hinit herr
    have htime : (v - s) * η ≤ Δ * η := by
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right hv.2 s) hη.le
    have hscale : η + Δ * η = η * (1 + Δ) := by ring
    have hInt : L * (∫ r in s..v,
        ‖(Evolution.dyson (Eₙ N) A).U r s x - (Evolution.dyson E A).U r s x‖) =
        ∫ r in s..v, L *
          ‖(Evolution.dyson (Eₙ N) A).U r s x - (Evolution.dyson E A).U r s x‖ := by
      rw [← intervalIntegral.integral_const_mul]
    have hgold' := hgold
    change ‖(Evolution.dyson (Eₙ N) A).U v s x - (Evolution.dyson E A).U v s x‖ ≤
      η + (v-s)*η + L *
        (∫ r in s..v, ‖(Evolution.dyson (Eₙ N) A).U r s x -
          (Evolution.dyson E A).U r s x‖) at hgold'
    rw [hInt] at hgold'
    calc
      ‖(Evolution.dyson (Eₙ N) A).U v s x - (Evolution.dyson E A).U v s x‖ ≤
          η + (v-s)*η + ∫ r in s..v,
            L * ‖(Evolution.dyson (Eₙ N) A).U r s x -
              (Evolution.dyson E A).U r s x‖ := hgold'
      _ ≤ η * (1 + Δ) + ∫ r in s..v,
            L * ‖(Evolution.dyson (Eₙ N) A).U r s x -
              (Evolution.dyson E A).U r s x‖ := by
        rw [← hscale]
        gcongr
  have hG := UnforcedLeray.Gronwall.le_exp_of_integral_le
    (y := fun r => ‖(Evolution.dyson (Eₙ N) A).U r s x -
      (Evolution.dyson E A).U r s x‖)
    (β := fun _ => L) (A := η * (1 + Δ)) (s := s) (T := t)
    hy continuousOn_const (fun _ _ => hL) hineq
  have hmain := hG u.1 ⟨hus, hut⟩
  have hmain' :
      ‖(Evolution.dyson (Eₙ N) A).U u.1 s x - (Evolution.dyson E A).U u.1 s x‖ ≤
        (η * (1 + Δ)) * Real.exp (L * (u.1 - s)) := by
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmain
  have hfactor : (η * (1 + Δ)) * Real.exp (L * (u.1 - s)) < ε := by
    have huΔ : u.1 - s ≤ Δ := sub_le_sub_right hut s
    have hexp : Real.exp (L * (u.1 - s)) ≤ C := by
      dsimp [C]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huΔ hL)
    dsimp [η, C] at *
    have : (ε / (2 * (1 + Δ) * Real.exp (L * Δ))) * (1 + Δ) *
        Real.exp (L * (u.1 - s)) ≤ ε / 2 := by
      have hden : 0 < 2 * (1 + Δ) * Real.exp (L * Δ) := by positivity
      calc
        _ ≤ (ε / (2 * (1 + Δ) * Real.exp (L * Δ))) * (1 + Δ) *
              Real.exp (L * Δ) := by gcongr
        _ = ε / 2 := by field_simp
    linarith
  have hnorm := hmain'.trans_lt hfactor
  simpa [dist_eq_norm, norm_sub_rev] using hnorm

/-- The actual first-stage transport family is the strong limit of its bounded-Yosida
approximants, uniformly in the output time on a fixed block. The perturbation is the very same
`transportDysonPert` value in both Dyson constructions. -/
theorem canonicalYosidaTransportFamily_actualPert_tendstoUniformlyOn_actual
    {a b s t δ : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (hβ : ContinuousOn β (Icc a b))
    (hβi : ∀ r u, IntervalIntegrable β volume r u)
    (hβ0 : ∀ r, 0 ≤ β r) (M : ℝ) (hβM : ∀ r, |β r| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Icc a b, |β r| ≤ C)
    (hβδ : ∀ r ∈ Icc a b, β r ≤ δ) (hδ : 0 ≤ δ)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    TendstoUniformlyOn
      (fun N : ℕ => fun u : Icc s t =>
        (canonicalYosidaTransportFamily_actualPert lam κ β N hβ hβsm hβblock).U
          u.1 s x)
      (fun u : Icc s t =>
        (canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U
          u.1 s x) atTop Set.univ := by
  let A := transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock
  let Eₙ := fun N => canonicalYosidaDiffusionFamily β N hβ
  let E : EvolutionFamily XG a b := freeDiffusionFamily β hβi hβ0 M hβM
  let F := Evolution.dyson E A
  let φ : Icc s t → XG := fun r => A.A r.1 (F.U r.1 s x)
  have hβ0' : ∀ r ∈ Icc a b, 0 ≤ β r := fun r _ => hβ0 r
  have hβδ' : ∀ r ∈ Icc a b, β r ≤ δ := hβδ
  have hAcont : ContinuousOn (fun r => A.A r) (Icc s t) := by
    have hβc := hβ.mono (Icc_subset_Icc has ht)
    have hβc' : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc s t) :=
      Complex.continuous_ofReal.continuousOn.comp hβc
        (fun r hr => Set.mem_univ (β r))
    have hβκ : ContinuousOn (fun r => ((β r : ℝ) : ℂ) * κ) (Icc s t) :=
      hβc'.mul continuousOn_const
    have hβκI : ContinuousOn
        (fun r => (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc s t) :=
      hβκ.smul continuousOn_const
    change ContinuousOn
      (fun r => UnforcedLeray.B0087.imMulOp - lam • (1 : XG →L[ℂ] XG) -
        (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc s t)
    exact (continuousOn_const.sub continuousOn_const).sub hβκI
  have hφcont : Continuous φ := by
    have hFcont' : ContinuousOn (fun r => F.U r s x) (Icc s t) :=
      (F.continuousOn_fst has x).mono (Icc_subset_Icc le_rfl ht)
    have hψ : ContinuousOn (fun r => A.A r (F.U r s x)) (Icc s t) :=
      hAcont.clm_apply hFcont'
    exact continuousOn_iff_continuous_domRestrict.1 hψ
  have hK : IsCompact (insert x (Set.range φ)) :=
    (isCompact_range hφcont).insert x
  have hxK : x ∈ insert x (Set.range φ) := mem_insert x _
  have horbit : ∀ r ∈ Icc s t, A.A r (F.U r s x) ∈ insert x (Set.range φ) := by
    intro r hr
    apply Or.inr
    refine ⟨⟨r, hr⟩, ?_⟩
    rfl
  have hρ : ∀ p ∈ Evolution.triangle s t,
      0 ≤ (∫ q in p.1..p.2, β q) ∧
        (∫ q in p.1..p.2, β q) ≤ δ * (t - s) := by
    intro p hp
    rcases Evolution.mem_triangle.mp hp with ⟨hsp, hpu, hut⟩
    have hpu' : p.1 ≤ p.2 := hpu
    have hInt : IntervalIntegrable β volume p.1 p.2 := hβi p.1 p.2
    have hnonneg : 0 ≤ (∫ q in p.1..p.2, β q) :=
      intervalIntegral.integral_nonneg hpu' (fun q _ => hβ0 q)
    have hmono := intervalIntegral.integral_mono_on hpu' hInt intervalIntegrable_const
      (fun q hq => hβδ q ⟨le_trans (le_trans has hsp) hq.1,
        le_trans hq.2 (le_trans hut ht)⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hlength : p.2 - p.1 ≤ t - s := by linarith
    have hup := mul_le_mul_of_nonneg_right hlength hδ
    constructor
    · exact hnonneg
    · calc
        (∫ q in p.1..p.2, β q) ≤ (p.2 - p.1) * δ := hmono
        _ ≤ (t - s) * δ := hup
        _ = δ * (t - s) := by ring
  have hbase := canonicalYosidaDiffusionFamily_tendstoUniformlyOn_freeDiffusion_triangle
      β hβ hβ0' has hst ht (R := δ * (t - s))
        (mul_nonneg hδ (sub_nonneg.mpr hst)) hρ hK
  have hcontract : ∀ N r u, r ∈ Icc s t → u ∈ Icc s t → r ≤ u →
      ‖(Eₙ N).U u r‖ ≤ 1 := by
    intro N r u hr hu hru
    have har : a ≤ r := le_trans has hr.1
    have hub : u ≤ b := le_trans hu.2 ht
    have hnorm := ContinuousLinearMap.opNorm_le_bound
      ((canonicalYosidaDiffusionFamily β N hβ).U u r) zero_le_one (fun z => by
        calc
          ‖(canonicalYosidaDiffusionFamily β N hβ).U u r z‖ ≤ ‖z‖ :=
            canonicalYosidaDiffusionFamily_norm_le β N hβ hβ0' hβδ' hδ
              har hru hub z
          _ = 1 * ‖z‖ := by ring)
    exact hnorm
  have hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ A.C := fun r hr => A.norm_le hr
  have h := dyson_common_interaction_tendstoUniformlyOn_of_base_tendsto
    Eₙ E A x has hst ht (L := A.C) A.C_nonneg hA hcontract hK hxK horbit hbase
  simpa [Eₙ, E, A, F, canonicalYosidaTransportFamily_actualPert,
    canonicalTransportDysonFamily, UnforcedLeray.B0087.imMulOp] using h

/-- The sharp first-stage energy estimate passes from the bounded Hermite truncations to the
actual canonical transport-diffusion family. -/
theorem canonicalTransportDysonFamily_sharp_norm_le
    {a b s t δ : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (hβ : ContinuousOn β (Icc a b))
    (hβi : ∀ r u, IntervalIntegrable β volume r u)
    (hβ0 : ∀ r, 0 ≤ β r) (M : ℝ) (hβM : ∀ r, |β r| ≤ M)
    (hβsm : AEStronglyMeasurable β (volume.restrict (Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Icc a b, |β r| ≤ C)
    (hβδ : ∀ r ∈ Icc a b, β r ≤ δ) (hδ : 0 ≤ δ)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  let hconv := canonicalYosidaTransportFamily_actualPert_tendstoUniformlyOn_actual
    lam κ β hβ hβi hβ0 M hβM hβsm hβblock hβδ hδ has hst ht x
  have hpoint : Tendsto
      (fun N : ℕ =>
        (canonicalYosidaTransportFamily_actualPert lam κ β N hβ hβsm hβblock).U t s x)
      atTop (𝓝 ((canonicalTransportDysonFamily lam κ β hβi hβ0 M hβM hβsm hβblock).U t s x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hclose := Metric.tendstoUniformlyOn_iff.1 hconv ε hε
    filter_upwards [hclose] with N hclose
    have hh := hclose ⟨t, hst, le_rfl⟩ (Set.mem_univ _)
    simpa [dist_eq_norm, norm_sub_rev] using hh
  have hnormlim := continuous_norm.continuousAt.tendsto.comp hpoint
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(canonicalYosidaTransportFamily_actualPert lam κ β N hβ hβsm hβblock).U t s x‖ ≤
        Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ :=
    Filter.Eventually.of_forall fun N =>
      canonicalYosidaTransportFamily_actualPert_norm_le lam κ β N hβ
        (fun r _ => hβ0 r)
        hβδ hδ hβsm hβblock has hst ht x
  exact isClosed_Iic.mem_of_tendsto hnormlim hbound

end UnforcedLeray.Cons.G3b
