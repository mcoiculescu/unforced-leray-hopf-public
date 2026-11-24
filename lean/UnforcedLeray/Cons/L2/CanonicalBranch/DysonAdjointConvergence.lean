import UnforcedLeray.Cons.L2.CanonicalBranch.DysonAdjointStrong

open Filter MeasureTheory
open scoped InnerProductSpace ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010

/-- Exact Hilbert-space expansion of the adjoint difference around a scaled-unitary reference. -/
theorem adjoint_sub_scaledUnitary_norm_sq_le
    (A B : XG →L[ℂ] XG) (ρ : ℝ) (x : XG)
    (hBB : B ∘L ContinuousLinearMap.adjoint B =
      (ρ ^ 2 : ℂ) • (1 : XG →L[ℂ] XG)) :
    ‖ContinuousLinearMap.adjoint A x - ContinuousLinearMap.adjoint B x‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint A x‖ ^ 2 - ρ ^ 2 * ‖x‖ ^ 2 +
        2 * ‖x‖ * ‖(A - B) (ContinuousLinearMap.adjoint B x)‖ := by
  let y := ContinuousLinearMap.adjoint B x
  have hBy : B y = (ρ ^ 2 : ℂ) • x := by
    change (B ∘L ContinuousLinearMap.adjoint B) x = _
    rw [hBB]
    simp
  have hself : (↑(ρ ^ 2 : ℝ) * ⟪x, x⟫_ℂ).re = ρ ^ 2 * ‖x‖ ^ 2 := by
    rw [Complex.re_ofReal_mul, norm_sq_eq_re_inner (𝕜 := ℂ) x]
    rfl
  have hy : ‖y‖ ^ 2 = ρ ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖y‖ ^ 2 = (⟪y, y⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) y
      _ = (⟪x, B y⟫_ℂ).re := by
        dsimp [y]
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ρ ^ 2 * ‖x‖ ^ 2 := by
        rw [hBy, inner_smul_right, ← Complex.ofReal_pow]
        exact hself
  have hcross : RCLike.re ⟪ContinuousLinearMap.adjoint A x,
      ContinuousLinearMap.adjoint B x⟫_ℂ =
      ρ ^ 2 * ‖x‖ ^ 2 + RCLike.re ⟪x, (A - B) y⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hsplit : A y = B y + (A - B) y := by simp
    rw [hsplit, inner_add_right, hBy]
    rw [inner_smul_right, map_add, ← Complex.ofReal_pow]
    change (↑(ρ ^ 2 : ℝ) * ⟪x, x⟫_ℂ).re + RCLike.re ⟪x, (A - B) y⟫_ℂ = _
    rw [hself]
  rw [@norm_sub_sq ℂ _ _ _ _ _ _, hy, hcross]
  have hinner : |RCLike.re ⟪x, (A - B) y⟫_ℂ| ≤ ‖x‖ * ‖(A - B) y‖ := by
    calc
      |RCLike.re ⟪x, (A - B) y⟫_ℂ| ≤ ‖⟪x, (A - B) y⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖(A - B) y‖ := norm_inner_le_norm x ((A - B) y)
  have hlow : -2 * RCLike.re ⟪x, (A - B) y⟫_ℂ ≤
      2 * ‖x‖ * ‖(A - B) y‖ := by
    calc
      -2 * RCLike.re ⟪x, (A - B) y⟫_ℂ ≤
          2 * |RCLike.re ⟪x, (A - B) y⟫_ℂ| := by
        have h := neg_le_abs (RCLike.re ⟪x, (A - B) y⟫_ℂ)
        nlinarith
      _ ≤ 2 * (‖x‖ * ‖(A - B) y‖) := mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 2 * ‖x‖ * ‖(A - B) y‖ := by ring
  nlinarith [hlow]

end UnforcedLeray.Cons.G3b

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010

private theorem exists_uniform_pos_on_finset {α : Type*} (S : Finset α)
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

/-- A common small-coefficient threshold makes the first Dyson family close to its inviscid
limit uniformly on a compact set of initial vectors. The sharp energy bound supplies the
operator majorant needed to extend from a finite net. -/
theorem exists_delta_canonicalTransportDysonFamily_uniform_strong_small_on_compact
    {a b B : ℝ} (hB : 0 < B) (lam κ : ℂ) {K : Set XG} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (β : ℝ → ℝ)
      (hβ : ContinuousOn β (Set.Icc a b))
      (hβi : ∀ u v, IntervalIntegrable β volume u v)
      (hβ0 : ∀ τ, 0 ≤ β τ)
      (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
      (hβM : ∀ r, |β r| ≤ δ) (s t : ℝ),
      a ≤ s → s ≤ t → t ≤ b → t - s ≤ B → ∀ x ∈ K,
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
        (⟨δ, fun r _ => hβM r⟩ : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)).U t s x -
        (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ < ε := by
  classical
  let P (x : XG) (δ : ℝ) : Prop :=
    ∀ (β : ℝ → ℝ) (hβi : ∀ u v, IntervalIntegrable β volume u v)
      (hβ0 : ∀ τ, 0 ≤ β τ)
      (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
      (hβM : ∀ r, |β r| ≤ δ) (s t : ℝ),
      a ≤ s → s ≤ t → t ≤ b → t - s ≤ B →
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
        (⟨δ, fun r _ => hβM r⟩ : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)).U t s x -
        (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ < ε / 2
  have hmono : ∀ x δ δ', δ ≤ δ' → P x δ' → P x δ := by
    intro x δ δ' hδ hP β hβi hβ0 hβsm hβM s t hs hst ht hspan
    apply hP β hβi hβ0 hβsm (fun r => (hβM r).trans hδ) s t hs hst ht hspan
  let LT := ‖(-2 * Complex.I) • UnforcedLeray.B0012.omegaOp‖ + ‖lam‖ + ‖κ‖
  let C := Real.exp ((LT + ‖canonicalTransportLimitGenerator lam‖ + 1) * B)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCr : ε / 16 / C > 0 := by positivity
  by_cases hKn : K.Nonempty
  · obtain ⟨N, hNK, hNfin, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (ε / 16 / C) hCr
    let Ns : Finset XG := hNfin.toFinset
    have hpoint : ∀ y ∈ Ns, ∃ δ : ℝ, 0 < δ ∧ P y δ := by
      intro y hy
      have hyN : y ∈ N := (Set.Finite.mem_toFinset hNfin).mp hy
      obtain ⟨δ, hδ, hsmall⟩ :=
        exists_delta_canonicalTransportDysonFamily_uniform_strong_small
          hB lam κ y (ε := ε / 2) (by positivity)
      exact ⟨δ, hδ, fun β hβi hβ0 hβsm hβM s t hs hst ht hspan =>
        hsmall β hβi hβ0 hβsm hβM s t hs hst ht hspan⟩
    have hPmono : ∀ y δ δ', δ ≤ δ' → P y δ' → P y δ := hmono
    obtain ⟨δ₀, hδ₀, hP₀⟩ := exists_uniform_pos_on_finset Ns P hPmono hpoint
    let δ := min δ₀ 1
    have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
    have hδ₁ : δ ≤ 1 := min_le_right _ _
    have hδ₀' : δ ≤ δ₀ := min_le_left _ _
    refine ⟨δ, hδ, hδ₁, ?_⟩
    intro β hβ hβi hβ0 hβsm hβM s t hs hst ht hspan x hx
    obtain ⟨y, hyN, hxy⟩ := Set.mem_iUnion₂.mp (hcov hx)
    have hyNs : y ∈ Ns := (Set.Finite.mem_toFinset hNfin).mpr hyN
    have hdist : ‖x - y‖ < ε / 16 / C := by
      rwa [Metric.mem_ball, dist_eq_norm] at hxy
    have hsmall := hP₀ y hyNs β hβi hβ0 hβsm
      (fun r => (hβM r).trans hδ₀') s t hs hst ht hspan
    let F := canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
      (⟨δ, fun r _ => hβM r⟩ : ∃ C₁ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₁)
    let V := canonicalTransportLimitFamily (a := a) (b := b) lam
    have hFop := canonicalTransportDysonFamily_unitBound_norm_le lam κ β hβi hβ0 δ hβM
      hβsm (⟨δ, fun r _ => hβM r⟩ : ∃ C₁ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₁)
      (fun r => (hβM r).trans hδ₁) s t hs hst ht
    have hFbound : ‖F.U t s‖ ≤ C := by
      calc
        ‖F.U t s‖ ≤ Real.exp (LT * (t - s)) := by simpa [F, LT] using hFop
        _ ≤ C := by
          dsimp [C]
          apply Real.exp_le_exp_of_le
          have hLT : 0 ≤ LT := by dsimp [LT]; positivity
          have hstep : LT * (t - s) ≤ LT * B := mul_le_mul_of_nonneg_left hspan hLT
          have hcoeff : LT ≤ LT + ‖canonicalTransportLimitGenerator lam‖ + 1 := by
            have hn := norm_nonneg (canonicalTransportLimitGenerator lam)
            nlinarith
          exact hstep.trans (mul_le_mul_of_nonneg_right hcoeff hB.le)
    have hVbound : ‖V.U t s‖ ≤ C := by
      have hG : ‖V.U t s‖ ≤ Real.exp (‖canonicalTransportLimitGenerator lam‖ * B) := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
        exact canonicalTransportLimitFamily_apply_norm_le lam hs hst ht hspan z
      calc
        ‖V.U t s‖ ≤ Real.exp (‖canonicalTransportLimitGenerator lam‖ * B) := hG
        _ ≤ C := by
          dsimp [C]
          apply Real.exp_le_exp_of_le
          have hGnorm : 0 ≤ ‖canonicalTransportLimitGenerator lam‖ := norm_nonneg _
          have hcoeff : ‖canonicalTransportLimitGenerator lam‖ ≤
              LT + ‖canonicalTransportLimitGenerator lam‖ + 1 := by
            have hLT : 0 ≤ LT := by dsimp [LT]; positivity
            nlinarith
          exact mul_le_mul_of_nonneg_right hcoeff hB.le
    calc
      ‖F.U t s x - V.U t s x‖ ≤
          ‖F.U t s x - F.U t s y‖ + ‖F.U t s y - V.U t s y‖ +
            ‖V.U t s y - V.U t s x‖ := by
        calc
          _ = ‖(F.U t s x - F.U t s y) + (F.U t s y - V.U t s y) +
                (V.U t s y - V.U t s x)‖ := by congr 1 <;> abel
          _ ≤ ‖(F.U t s x - F.U t s y) + (F.U t s y - V.U t s y)‖ +
                ‖V.U t s y - V.U t s x‖ := norm_add_le _ _
          _ ≤ _ := add_le_add (norm_add_le _ _) (le_rfl)
      _ < ε := by
        have hleft : ‖F.U t s x - F.U t s y‖ ≤ C * ‖x - y‖ := by
          calc
            _ = ‖F.U t s (x - y)‖ := by rw [map_sub]
            _ ≤ ‖F.U t s‖ * ‖x - y‖ := (F.U t s).le_opNorm _
            _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_right hFbound (norm_nonneg _)
        have hright : ‖V.U t s y - V.U t s x‖ ≤ C * ‖x - y‖ := by
          calc
            _ = ‖V.U t s (y - x)‖ := by rw [map_sub]
            _ ≤ ‖V.U t s‖ * ‖y - x‖ := (V.U t s).le_opNorm _
            _ ≤ C * ‖x - y‖ := by
              rw [norm_sub_rev]
              exact mul_le_mul_of_nonneg_right hVbound (norm_nonneg _)
        have hnet := hsmall
        have hdist' : C * ‖x - y‖ < ε / 16 := by
          calc
            C * ‖x - y‖ < C * (ε / 16 / C) := mul_lt_mul_of_pos_left hdist hC
            _ = ε / 16 := by field_simp
        calc
          _ ≤ C * ‖x - y‖ + ε / 2 + C * ‖x - y‖ :=
            add_le_add (add_le_add hleft hnet.le) hright
          _ < ε := by nlinarith [hdist', hε]
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro β hβ hβi hβ0 hβsm hβM s t hs hst ht hspan x hx
    exact False.elim (hKn ⟨x, hx⟩)


/-- The actual first-stage adjoints converge strongly, uniformly on bounded time windows, to the
adjoints of the inviscid transport family as the nonnegative coefficient tends to zero. The sharp
energy estimate controls the norm-square term, while the direct limit is used on the compact orbit
of the reference adjoint. -/
theorem exists_delta_canonicalTransportDysonFamily_adjoint_uniform_strong_small
    {a b B : ℝ} (hB : 0 < B) (lam κ : ℂ) (x : XG) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (β : ℝ → ℝ)
      (hβ : ContinuousOn β (Set.Icc a b))
      (hβi : ∀ u v, IntervalIntegrable β volume u v)
      (hβ0 : ∀ τ, 0 ≤ β τ)
      (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
      (hβM : ∀ r, |β r| ≤ δ) (s t : ℝ),
      a ≤ s → s ≤ t → t ≤ b → t - s ≤ B →
      ‖ContinuousLinearMap.adjoint
          ((canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
            (⟨δ, fun r _ => hβM r⟩ : ∃ C : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C)).U t s) x -
        ContinuousLinearMap.adjoint
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U t s) x‖ < ε := by
  classical
  let G := canonicalTransportLimitGenerator lam
  let V := canonicalTransportLimitFamily (a := a) (b := b) lam
  let g (u : ℝ) := NormedSpace.exp ((u : ℂ) • ContinuousLinearMap.adjoint G) x
  have hg : Continuous g :=
    UnforcedLeray.Infra.continuous_exp_smul_apply (ContinuousLinearMap.adjoint G) x
  let K : Set XG := Set.range (fun u : Set.Icc (0 : ℝ) B => g u)
  have hK : IsCompact K := by
    exact isCompact_range (hg.comp continuous_subtype_val)
  let η := ε ^ 2 / (8 * (‖x‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δd, hδd, hδd1, hdirect⟩ :=
    exists_delta_canonicalTransportDysonFamily_uniform_strong_small_on_compact
      (a := a) (b := b) hB lam κ hK hη
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
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro β hβ hβi hβ0 hβsm hβM s t hs hst ht hspan
  have hβM' : ∀ r, |β r| ≤ δd := fun r => (hβM r).trans hδd'
  have hdir : ∀ y ∈ K,
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
        (⟨δ, fun r _ => hβM r⟩ : ∃ C₁ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₁)).U t s y -
        V.U t s y‖ < η := by
    exact hdirect β hβ hβi hβ0 hβsm hβM' s t hs hst ht hspan
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
  have hBscaled : V.U t s ∘L ContinuousLinearMap.adjoint (V.U t s) =
      (ρ ^ 2 : ℂ) • (1 : XG →L[ℂ] XG) := by
    have h := canonicalTransportLimitFamily_comp_adjoint_eq_exp lam hs hst ht
    dsimp [V, ρ, Δ] at h ⊢
    have hreal : Real.exp (-2 * lam.re * (t - s)) =
        (Real.exp (-lam.re * (t - s))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [hreal] at h
    convert h using 1 <;> norm_cast
  let A := (canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
      (⟨δ, fun r _ => hβM r⟩ : ∃ C₁ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₁)).U t s
  let Bop := V.U t s
  have hVadj : ContinuousLinearMap.adjoint Bop x = g Δ := by
    dsimp [Bop, V, g, Δ]
    have hVform : (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s =
        NormedSpace.exp (((t - s : ℝ) : ℂ) • G) := by
      simp [G, canonicalTransportLimitFamily,
        UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
        UnforcedLeray.Infra.ExpSemigroup.ofExp_T]
    rw [hVform]
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
  have hβblock : ∃ C₁ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₁ :=
    ⟨δ, fun r _ => hβM r⟩
  have hAadj := canonicalTransportDysonFamily_adjoint_sharp_norm_le lam κ β hβ hβi hβ0
    δ hβM hβsm hβblock (fun r hr => le_trans (le_abs_self _) (hβM r))
    (le_of_lt hδ) hs hst ht x
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

end UnforcedLeray.Cons.G3b

end
