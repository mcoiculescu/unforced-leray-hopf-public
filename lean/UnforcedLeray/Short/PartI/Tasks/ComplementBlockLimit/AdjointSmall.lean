import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.SharpBoundAll
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.StrongSmall
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonAdjointConvergence

/-!
# Target `PartI:C03/3`: `freeAdjointSmall`

Source of record: `the November 2 reference manuscript`, lines 1034-1036
("For the adjoints, reverse time on the block").

Method: the proof of `Cons` `DysonAdjointConvergence.lean:223-358` for continuous `β`, with the
adjoint sharp bound replaced by `freeSharpBoundAll` (`‖F†‖ = ‖F‖`) and the direct compact-set
smallness replaced by a finite-net argument from `freeStrongSmall`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Cons.G3b UnforcedLeray.B0010

private theorem adjSmall_exists_uniform_pos_on_finset {α : Type*} (S : Finset α)
    (P : α → ℝ → Prop)
    (hmono : ∀ x δ δ', δ ≤ δ' → P x δ' → P x δ)
    (hP : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ P x δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, P x δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x S hx ih =>
      have hrest : ∀ y ∈ S, ∃ δ : ℝ, 0 < δ ∧ P y δ := by
        intro y hy
        exact hP y (Finset.mem_insert_of_mem hy)
      obtain ⟨δS, hδS, hPS⟩ := ih hrest
      obtain ⟨δx, hδx, hPx⟩ := hP x (Finset.mem_insert_self x S)
      refine ⟨min δS δx, lt_min hδS hδx, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact hmono _ _ _ (min_le_right _ _) hPx
      · exact hmono y (min δS δx) δS (min_le_left _ _) (hPS y hyS)

theorem adjSmall_freeLimitGen (lam : ℂ) : freeLimitGen lam = canonicalTransportLimitGenerator lam := by
  simp [freeLimitGen, complementT, canonicalTransportLimitGenerator]

theorem adjSmall_limit_apply (lam : ℂ) (a b s t : ℝ) :
    (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s =
      NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) := by
  simp [canonicalTransportLimitFamily,
    UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
    UnforcedLeray.Infra.ExpSemigroup.ofExp_T, freeLimitGen, complementT,
    canonicalTransportLimitGenerator]

/-- Direct uniform smallness on a compact set, from `freeStrongSmall` and a finite net. -/
theorem adjSmall_compact {B : ℝ} (hB : 0 < B) (lam kappa : ℂ) {K : Set XG} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ δ) →
      ∀ F : ℝ → ℝ → XG →L[ℂ] XG, IsFreeDiffusionEvolution lam kappa β F →
        ∀ s t : ℝ, s ≤ t → t ≤ s + B → ∀ z ∈ K,
          ‖F t s z - NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) z‖ < η := by
  classical
  let P (x : XG) (δ : ℝ) : Prop :=
    ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ δ) →
      ∀ F : ℝ → ℝ → XG →L[ℂ] XG, IsFreeDiffusionEvolution lam kappa β F →
        ∀ s t : ℝ, s ≤ t → t ≤ s + B →
          ‖F t s x - NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) x‖ < η / 2
  have hmono : ∀ x δ δ', δ ≤ δ' → P x δ' → P x δ := by
    intro x δ δ' hδ hP β hβm hβ F hF s t hst hts
    exact hP β hβm (fun r => ⟨(hβ r).1, (hβ r).2.trans hδ⟩) F hF s t hst hts
  let LT := |lam.re| + |kappa.re|
  let C := Real.exp ((LT + ‖freeLimitGen lam‖ + 1) * B)
  have hC : 0 < C := Real.exp_pos _
  have hCr : η / 8 / C > 0 := by positivity
  by_cases hKn : K.Nonempty
  · obtain ⟨N, hNK, hNfin, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (η / 8 / C) hCr
    let Ns : Finset XG := hNfin.toFinset
    have hpoint : ∀ y ∈ Ns, ∃ δ : ℝ, 0 < δ ∧ P y δ := by
      intro y _
      obtain ⟨δ, hδ, hsmall⟩ := freeStrongSmall lam kappa B y (η / 2) hB (by positivity)
      exact ⟨δ, hδ, hsmall⟩
    obtain ⟨δ₀, hδ₀, hP₀⟩ := adjSmall_exists_uniform_pos_on_finset Ns P hmono hpoint
    let δ := min δ₀ 1
    have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
    have hδ₁ : δ ≤ 1 := min_le_right _ _
    have hδ₀' : δ ≤ δ₀ := min_le_left _ _
    refine ⟨δ, hδ, hδ₁, ?_⟩
    intro β hβm hβ F hF s t hst hts z hz
    obtain ⟨y, hyN, hxy⟩ := Set.mem_iUnion₂.mp (hcov hz)
    have hyNs : y ∈ Ns := (Set.Finite.mem_toFinset hNfin).mpr hyN
    have hdist : ‖z - y‖ < η / 8 / C := by
      rwa [Metric.mem_ball, dist_eq_norm] at hxy
    have hsmall := hP₀ y hyNs β hβm (fun r => ⟨(hβ r).1, (hβ r).2.trans hδ₀'⟩) F hF s t hst hts
    let V := NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam)
    have hspan : t - s ≤ B := by linarith
    have hFb := freeSharpBoundAll lam kappa δ β hβm hβ F hF s t hst
    have hFbound : ‖F t s‖ ≤ C := by
      refine hFb.trans ?_
      dsimp [C, LT]
      apply Real.exp_le_exp_of_le
      have h0 : 0 ≤ t - s := sub_nonneg.mpr hst
      have hG := norm_nonneg (freeLimitGen lam)
      have e1 : -(lam.re * (t - s)) ≤ |lam.re| * B := by
        have := neg_le_abs lam.re
        nlinarith [mul_le_mul this hspan h0 (abs_nonneg _)]
      have e2 : |kappa.re| * δ * (t - s) ≤ |kappa.re| * B := by
        have : δ * (t - s) ≤ 1 * B := mul_le_mul hδ₁ hspan h0 zero_le_one
        nlinarith [abs_nonneg kappa.re]
      nlinarith [mul_nonneg hG hB.le, abs_nonneg lam.re, abs_nonneg kappa.re]
    have hVbound : ‖V‖ ≤ C := by
      have hG : ‖V‖ ≤ Real.exp (‖canonicalTransportLimitGenerator lam‖ * B) := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
        have := canonicalTransportLimitFamily_apply_norm_le (a := s) (b := t) (s := s) (t := t)
          (B := B) lam le_rfl hst le_rfl hspan w
        rwa [adjSmall_limit_apply, ← adjSmall_freeLimitGen] at this
      rw [← adjSmall_freeLimitGen] at hG
      refine hG.trans ?_
      dsimp [C, LT]
      apply Real.exp_le_exp_of_le
      nlinarith [mul_nonneg (add_nonneg (abs_nonneg lam.re) (abs_nonneg kappa.re)) hB.le]
    have hleft : ‖F t s z - F t s y‖ ≤ C * ‖z - y‖ := by
      calc
        _ = ‖F t s (z - y)‖ := by rw [map_sub]
        _ ≤ ‖F t s‖ * ‖z - y‖ := (F t s).le_opNorm _
        _ ≤ C * ‖z - y‖ := mul_le_mul_of_nonneg_right hFbound (norm_nonneg _)
    have hright : ‖V y - V z‖ ≤ C * ‖z - y‖ := by
      calc
        _ = ‖V (y - z)‖ := by rw [map_sub]
        _ ≤ ‖V‖ * ‖y - z‖ := V.le_opNorm _
        _ ≤ C * ‖z - y‖ := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_right hVbound (norm_nonneg _)
    have hdist' : C * ‖z - y‖ < η / 8 := by
      calc
        C * ‖z - y‖ < C * (η / 8 / C) := mul_lt_mul_of_pos_left hdist hC
        _ = η / 8 := by field_simp
    calc
      ‖F t s z - V z‖ ≤ ‖F t s z - F t s y‖ + ‖F t s y - V y‖ + ‖V y - V z‖ := by
        calc
          _ = ‖(F t s z - F t s y) + (F t s y - V y) + (V y - V z)‖ := by congr 1; abel
          _ ≤ ‖(F t s z - F t s y) + (F t s y - V y)‖ + ‖V y - V z‖ := norm_add_le _ _
          _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
      _ < η := by
        have := hsmall
        have h2 : ‖F t s z - F t s y‖ + ‖F t s y - V y‖ + ‖V y - V z‖ ≤
            C * ‖z - y‖ + η / 2 + C * ‖z - y‖ := add_le_add (add_le_add hleft this.le) hright
        linarith
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro β _ _ F _ s t _ _ z hz
    exact False.elim (hKn ⟨z, hz⟩)

/-- **Target `PartI:C03/3`** (source lines 1034-1036): uniform adjoint strong convergence of the
free evolutions to `exp((t-s)(T-λ))` on blocks of length `B`. -/
theorem freeAdjointSmall : FreeAdjointSmall := by
  classical
  intro lam κ B x ε hB hε
  let G := canonicalTransportLimitGenerator lam
  let g (u : ℝ) := NormedSpace.exp ((u : ℂ) • ContinuousLinearMap.adjoint G) x
  have hg : Continuous g :=
    UnforcedLeray.Infra.continuous_exp_smul_apply (ContinuousLinearMap.adjoint G) x
  let K : Set XG := Set.range (fun u : Set.Icc (0 : ℝ) B => g u)
  have hK : IsCompact K := by
    exact isCompact_range (hg.comp continuous_subtype_val)
  let η := ε ^ 2 / (8 * (‖x‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δd, hδd, hδd1, hdirect⟩ := adjSmall_compact hB lam κ hK hη
  let E := Real.exp (2 * |lam.re| * B) * ‖x‖ ^ 2
  let ηe := ε ^ 2 / (4 * (E + 1))
  have hηe : 0 < ηe := by dsimp [ηe, E]; positivity
  have hExpTendsto : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have h := (Real.continuous_exp.continuousAt (x := (0 : ℝ))).tendsto
    simpa only [Real.exp_zero] using h
  have hevent : {q : ℝ | dist (Real.exp q) 1 < ηe} ∈ 𝓝 (0 : ℝ) := by
    have hh := hExpTendsto.eventually (Metric.ball_mem_nhds 1 hηe)
    change {q : ℝ | dist (Real.exp q) 1 < ηe} ∈ 𝓝 (0 : ℝ)
    exact hh
  obtain ⟨δq, hδq, hball⟩ := Metric.mem_nhds_iff.1 hevent
  have hsmallq (q : ℝ) (hq : |q| < δq) : |Real.exp q - 1| < ηe := by
    have hqball : q ∈ Metric.ball (0 : ℝ) δq := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have hh := hball hqball
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  let S := 2 * |κ.re| * B + 1
  have hS : 0 < S := by dsimp [S]; positivity
  let δ := min δd (δq / S)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδd (div_pos hδq hS)
  have hδd' : δ ≤ δd := min_le_left _ _
  have hδq' : δ ≤ δq / S := min_le_right _ _
  have hδ1 : δ ≤ 1 := le_trans hδd' hδd1
  refine ⟨δ, hδ, ?_⟩
  intro β hβm hβ F hF s t hst hts
  have hspan : t - s ≤ B := by linarith
  have hβM' : ∀ r, 0 ≤ β r ∧ β r ≤ δd := fun r => ⟨(hβ r).1, (hβ r).2.trans hδd'⟩
  have hdir : ∀ y ∈ K,
      ‖F t s y - NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) y‖ < η :=
    hdirect β hβm hβM' F hF s t hst hts
  let Δ := t - s
  let ρ := Real.exp (-lam.re * Δ)
  let q := 2 * δ * |κ.re| * Δ
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqS : q < δq := by
    dsimp [q, Δ, S]
    have hprod : 2 * δ * |κ.re| * B < δ * (2 * |κ.re| * B + 1) := by
      have hδpos : 0 < δ := hδ
      nlinarith [abs_nonneg κ.re, hB]
    have hle : δ * (2 * |κ.re| * B + 1) ≤ δq := by
      calc
        δ * S ≤ (δq / S) * S := mul_le_mul_of_nonneg_right hδq' hS.le
        _ = δq := div_mul_cancel₀ _ hS.ne'
    have htime : 2 * δ * |κ.re| * Δ ≤ 2 * δ * |κ.re| * B := by
      have hcoef : 0 ≤ 2 * δ * |κ.re| := by positivity
      exact mul_le_mul_of_nonneg_left hspan hcoef
    exact lt_of_le_of_lt htime (lt_of_lt_of_le hprod hle)
  have hqexp : |Real.exp q - 1| < ηe := by
    exact hsmallq q (by simpa [abs_of_nonneg hq0] using hqS)
  have hqminus : 0 ≤ Real.exp q - 1 := by
    have h := Real.exp_le_exp.mpr hq0
    have hz : Real.exp 0 = 1 := Real.exp_zero
    rw [hz] at h
    linarith
  have hqminus' : Real.exp q - 1 < ηe := by
    have := abs_le.mp (le_of_lt hqexp)
    have h := abs_lt.mp hqexp
    nlinarith
  have hρbound' : ρ ^ 2 ≤ Real.exp (2 * |lam.re| * B) := by
    dsimp [ρ]
    have hpow : (Real.exp (-lam.re * Δ)) ^ 2 = Real.exp (-2 * lam.re * Δ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [hpow]
    apply Real.exp_le_exp_of_le
    dsimp [Δ]
    have h1 : -lam.re ≤ |lam.re| := neg_le_abs _
    have htime : 0 ≤ t - s := sub_nonneg.mpr hst
    have h2 := mul_le_mul_of_nonneg_right h1 htime
    have h3 := mul_le_mul_of_nonneg_left hspan (by positivity : 0 ≤ 2 * |lam.re|)
    nlinarith
  let Bop : XG →L[ℂ] XG := NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam)
  let A : XG →L[ℂ] XG := F t s
  have hBscaled : Bop ∘L ContinuousLinearMap.adjoint Bop =
      (ρ ^ 2 : ℂ) • (1 : XG →L[ℂ] XG) := by
    have h := canonicalTransportLimitFamily_comp_adjoint_eq_exp (a := s) (b := t) lam le_rfl hst le_rfl
    rw [adjSmall_limit_apply] at h
    dsimp [Bop, ρ, Δ] at h ⊢
    have hreal : Real.exp (-2 * lam.re * (t - s)) =
        (Real.exp (-lam.re * (t - s))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [hreal] at h
    convert h using 1 <;> norm_cast
  have hVadj : ContinuousLinearMap.adjoint Bop x = g Δ := by
    dsimp [Bop, g, Δ]
    rw [adjSmall_freeLimitGen]
    change (star (NormedSpace.exp (((t - s : ℝ) : ℂ) • G))) x = _
    rw [NormedSpace.star_exp, star_smul]
    simp only [ContinuousLinearMap.star_eq_adjoint]
    have hstar : star ((↑(t - s : ℝ)) : ℂ) = ((t - s : ℝ) : ℂ) := by simp
    rw [hstar]
    congr 2 <;> rfl
  have hmem : ContinuousLinearMap.adjoint Bop x ∈ K := by
    rw [hVadj]
    refine ⟨⟨Δ, ?_⟩, rfl⟩
    constructor
    · exact sub_nonneg.mpr hst
    · exact hspan
  have hpert : ‖(A - Bop) (ContinuousLinearMap.adjoint Bop x)‖ < η := by
    have hh := hdir (ContinuousLinearMap.adjoint Bop x) hmem
    simpa [A, Bop, ContinuousLinearMap.sub_apply] using hh
  have hAadj : ‖ContinuousLinearMap.adjoint A x‖ ≤ Real.exp ((-lam.re + δ * |κ.re|) * Δ) * ‖x‖ := by
    have h1 := freeSharpBoundAll lam κ δ β hβm hβ F hF s t hst
    have h2 : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
    calc ‖ContinuousLinearMap.adjoint A x‖ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖x‖ :=
          (ContinuousLinearMap.adjoint A).le_opNorm x
      _ ≤ Real.exp ((-lam.re + δ * |κ.re|) * Δ) * ‖x‖ := by
          rw [h2]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine h1.trans (le_of_eq ?_)
          congr 1; dsimp [Δ]; ring
  have hfactor : (Real.exp ((-lam.re + δ * |κ.re|) * Δ)) ^ 2 = ρ ^ 2 * Real.exp q := by
    dsimp [ρ, q]
    calc
      _ = Real.exp (((-lam.re + δ * |κ.re|) * Δ) + ((-lam.re + δ * |κ.re|) * Δ)) := by
        rw [pow_two, ← Real.exp_add]
      _ = Real.exp ((-lam.re * Δ + -lam.re * Δ) + (2 * δ * |κ.re| * Δ)) := by
        congr 1 <;> dsimp [Δ] <;> ring
      _ = Real.exp (-lam.re * Δ) * Real.exp (-lam.re * Δ) * Real.exp (2 * δ * |κ.re| * Δ) := by
        rw [Real.exp_add, Real.exp_add]
      _ = ρ ^ 2 * Real.exp q := by
        dsimp [ρ, q]
        rw [pow_two]
  have hA2 : ‖ContinuousLinearMap.adjoint A x‖ ^ 2 ≤
      ρ ^ 2 * Real.exp q * ‖x‖ ^ 2 := by
    calc
      ‖ContinuousLinearMap.adjoint A x‖ ^ 2 ≤
          (Real.exp ((-lam.re + δ * |κ.re|) * Δ) * ‖x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hAadj
      _ = ρ ^ 2 * Real.exp q * ‖x‖ ^ 2 := by rw [mul_pow, hfactor]
  have henergy : ‖ContinuousLinearMap.adjoint A x‖ ^ 2 - ρ ^ 2 * ‖x‖ ^ 2 ≤
      ρ ^ 2 * (Real.exp q - 1) * ‖x‖ ^ 2 := by nlinarith [hA2]
  have henergyBound : ρ ^ 2 * (Real.exp q - 1) * ‖x‖ ^ 2 < ε ^ 2 / 4 := by
    have hbound : ρ ^ 2 * (Real.exp q - 1) * ‖x‖ ^ 2 ≤ E * ηe := by
      calc
        ρ ^ 2 * (Real.exp q - 1) * ‖x‖ ^ 2 ≤
            Real.exp (2 * |lam.re| * B) * (Real.exp q - 1) * ‖x‖ ^ 2 := by
              gcongr
        _ ≤ Real.exp (2 * |lam.re| * B) * ηe * ‖x‖ ^ 2 := by
              gcongr
        _ = E * ηe := by dsimp [E]; ring
    have hbase : E * ηe < ε ^ 2 / 4 := by
      dsimp [ηe]
      have hE : 0 ≤ E := by dsimp [E]; positivity
      have hden : 0 < E + 1 := by linarith
      field_simp
      nlinarith
    exact lt_of_le_of_lt hbound hbase
  have htail : 2 * ‖x‖ * η < ε ^ 2 / 4 := by
    dsimp [η]
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have hden : 0 < 8 * (‖x‖ + 1) := by positivity
    field_simp
    nlinarith [hε]
  have hnormsq := adjoint_sub_scaledUnitary_norm_sq_le A Bop ρ x hBscaled
  have hfinalsq : ‖ContinuousLinearMap.adjoint A x - ContinuousLinearMap.adjoint Bop x‖ ^ 2 < ε ^ 2 := by
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint A x‖ ^ 2 - ρ ^ 2 * ‖x‖ ^ 2 +
          2 * ‖x‖ * ‖(A - Bop) (ContinuousLinearMap.adjoint Bop x)‖ := hnormsq
      _ ≤ ρ ^ 2 * (Real.exp q - 1) * ‖x‖ ^ 2 + 2 * ‖x‖ * η := by
        have hpert' : 2 * ‖x‖ * ‖(A - Bop) (ContinuousLinearMap.adjoint Bop x)‖ ≤ 2 * ‖x‖ * η :=
          mul_le_mul_of_nonneg_left (le_of_lt hpert) (by positivity)
        exact add_le_add (le_of_le_of_eq henergy rfl) hpert'
      _ < ε ^ 2 := by
        calc
          _ < ε ^ 2 / 4 + ε ^ 2 / 4 := add_lt_add henergyBound htail
          _ = ε ^ 2 / 2 := by ring
          _ < ε ^ 2 := by
            exact div_lt_self (sq_pos_of_pos hε) (by norm_num : (1 : ℝ) < 2)
  have hnonneg : 0 ≤ ‖ContinuousLinearMap.adjoint A x - ContinuousLinearMap.adjoint Bop x‖ := norm_nonneg _
  have hεsq : 0 ≤ ε := le_of_lt hε
  exact (sq_lt_sq₀ hnonneg hε.le).1 hfinalsq

end UnforcedLeray.Short.PartI
