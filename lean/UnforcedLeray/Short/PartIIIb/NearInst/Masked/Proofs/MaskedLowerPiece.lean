import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioSup
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioTanh

/-!
# `PartIII-b:C/near/masked/27`: `maskedLowerPiece_of` (source 4011-4014, 4027-4028)

The lower end `s < s₋ = ε^b`: the masked operator has no input `t ≥ e^δ s₋` on these outputs
(`MaskedSupport`), so `1_{s<s₋} S_N = 1_{s<s₋} S_N 1_{t<e^δ s₋}`.  The gain costs at most `e^{γe^δ}`
(`g⁻¹ ≤ 1`, `g ≤ e^{γe^δ}` on the retained inputs), the free part is bounded by the free energy
(`RealStressBound`) and the far part by `ForbiddenBlockBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- `1_A 1_B = 1_B` on `L²` when the outer set `A` contains the inner set `B`. -/
theorem restrLp_outer_of_sub {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A B : Set Chart} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) (f : Lp E 2 μ) :
    restrLp μ E A (restrLp μ E B f) = restrLp μ E B f := by
  apply Lp.ext
  filter_upwards [restrLp_ae hA (restrLp μ E B f), restrLp_ae hB f] with x h1 h2
  rw [h1]
  show ind A x • (restrLp μ E B f : Chart → E) x = (restrLp μ E B f : Chart → E) x
  rw [h2]
  by_cases hx : x ∈ B
  · have hxA : x ∈ A := hBA hx
    simp [ind, Set.indicator, hx, hxA]
  · simp [ind, Set.indicator, hx]

/-- `1_A 1_B = 1_A` on `L²` when the inner set `B` contains the outer set `A`. -/
theorem restrLp_inner_of_sub {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A B : Set Chart} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (f : Lp E 2 μ) :
    restrLp μ E A (restrLp μ E B f) = restrLp μ E A f := by
  apply Lp.ext
  filter_upwards [restrLp_ae hA (restrLp μ E B f), restrLp_ae hA f, restrLp_ae hB f]
    with x h1 h2 h3
  rw [h1]
  show ind A x • (restrLp μ E B f : Chart → E) x = (restrLp μ E A f : Chart → E) x
  rw [h2, h3]
  by_cases hx : x ∈ A
  · have hxB : x ∈ B := hAB hx
    simp [ind, Set.indicator, hx, hxB]
  · simp [ind, Set.indicator, hx]

theorem outRestr_inner_of_sub (c : ℝ) {A B : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (u : Hsp c) :
    outRestr c A (outRestr c B u) = outRestr c A u :=
  restrLp_inner_of_sub hA hB hAB u

theorem outRestr_outer_of_sub (c : ℝ) {A B : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBA : B ⊆ A) (u : Hsp c) :
    outRestr c A (outRestr c B u) = outRestr c B u :=
  restrLp_outer_of_sub hA hB hBA u

theorem inRestr_outer_of_sub (c mZ ρb : ℝ) {A B : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBA : B ⊆ A) (F : Zsp c mZ ρb) :
    inRestr c mZ ρb A (inRestr c mZ ρb B F) = inRestr c mZ ρb B F := by
  apply (zEquiv c mZ ρb).injective
  simp only [zEquiv_inRestr]
  exact Prod.ext (restrLp_outer_of_sub hA hB hBA _) (restrLp_outer_of_sub hA hB hBA _)

theorem gainConjS_add' (γ : ℝ) {ν : ℝ} (hν : 0 < ν) {c mZ ρb : ℝ}
    (X Y : Zsp c mZ ρb →L[ℝ] Hsp c) :
    gainConjS γ hν (X + Y) = gainConjS γ hν X + gainConjS γ hν Y := by
  ext1 F
  simp only [ContinuousLinearMap.add_apply, gainConjS_apply, map_add]

/-- `γ s/(1+νs)` is monotone in `s ≥ 0` for `γ ≥ 0`. -/
theorem gain_mono_le {γ ν s t : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t) :
    γ * s / (1 + ν * s) ≤ γ * t / (1 + ν * t) := by
  have h1 : 0 < 1 + ν * s := by have := mul_nonneg hν.le hs; linarith
  have h2 : 0 < 1 + ν * t := by
    have := mul_nonneg hν.le (hs.trans hst); linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hst)]

theorem gainInv_block_le {γ ν l : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hl : 0 < l) (x : Chart)
    (hx : l ≤ x.1) :
    gainInvFun γ ν x ≤ Real.exp (-(γ * l / (1 + ν * l))) := by
  have hmax : max x.1 0 = x.1 := max_eq_left (le_trans hl.le hx)
  have hm := gain_mono_le hγ hν hl.le hx
  simp only [gainInvFun, gainFun, UnforcedLeray.Short.IIIa.gainG, hmax]
  rw [← Real.exp_neg]
  exact Real.exp_le_exp.2 (neg_le_neg hm)

theorem gainFun_le_of_lt {γ ν t : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (ht : 0 < t) (x : Chart)
    (hx : x.1 < t) :
    gainFun γ ν x ≤ Real.exp (γ * t / (1 + ν * t)) := by
  have hmax : max x.1 0 ≤ t := max_le hx.le ht.le
  have hm := gain_mono_le hγ hν (le_max_right _ _) hmax
  simp only [gainFun, UnforcedLeray.Short.IIIa.gainG]
  exact Real.exp_le_exp.2 hm

/-- The gain ratio on a block `[l, t]` with `t ≤ M l`: `e^{γ t/(1+νt)} e^{-γ l/(1+νl)} ≤
e^{(γ/ν) tanh(log M/4)}`. -/
theorem gain_ratio_le {γ ν l t M : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hl : 0 < l) (hlt : l ≤ t)
    (htM : t ≤ M * l) (hM : 1 ≤ M) :
    Real.exp (γ * t / (1 + ν * t)) * Real.exp (-(γ * l / (1 + ν * l))) ≤
      Real.exp (γ / ν * Real.tanh (Real.log M / 4)) := by
  have hsup := gainRatioSup ν M hν hM
  have hmem : ν * (t / (1 + ν * t) - l / (1 + ν * l)) ≤
      (Real.sqrt M - 1) / (Real.sqrt M + 1) :=
    hsup.2 ⟨l, t, hl, hlt, htM, rfl⟩
  rw [gainRatioTanh M hM] at hmem
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hνne : ν ≠ 0 := hν.ne'
  have hid : γ * t / (1 + ν * t) + -(γ * l / (1 + ν * l)) =
      γ / ν * (ν * (t / (1 + ν * t) - l / (1 + ν * l))) := by
    field_simp
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hmem (div_nonneg hγ hν.le)

/-- `g ≤ e^{γ e^δ}` on the retained inputs `t < e^δ s₋` for `s₋ ≤ 1`. -/
theorem gainFun_le_lower {γ ν δ sm : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hδ : 0 < δ) (hsm : 0 < sm)
    (hsm1 : sm ≤ 1) (x : Chart) (hx : x.1 < Real.exp δ * sm) :
    gainFun γ ν x ≤ Real.exp (γ * Real.exp δ) := by
  refine (gainFun_le_of_lt hγ hν (mul_pos (Real.exp_pos δ) hsm) x hx).trans
    (Real.exp_le_exp.2 ?_)
  have h1 : γ * (Real.exp δ * sm) / (1 + ν * (Real.exp δ * sm)) ≤ γ * (Real.exp δ * sm) := by
    apply div_le_self (mul_nonneg hγ (mul_pos (Real.exp_pos δ) hsm).le)
    have := mul_nonneg hν.le (mul_pos (Real.exp_pos δ) hsm).le
    linarith
  have h2 : γ * (Real.exp δ * sm) ≤ γ * Real.exp δ := by
    apply mul_le_mul_of_nonneg_left _ hγ
    exact mul_le_of_le_one_right (Real.exp_pos δ).le hsm1
  linarith

/-- **`maskedLowerPiece_of`** (source 4011-4014, 4027-4028): the lower end of the masked free bound. -/
theorem maskedLowerPiece_of (hE : RealStressBound) (hS : MaskedSupport)
    (hF : ForbiddenBlockBound) (hG : GainBlockBound) : MaskedLowerPiece := by
  obtain ⟨CE, hCE0, hEb⟩ := hE
  intro P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨Cf, kf, νF, hνF, hfb⟩ := hF Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  have hγ : 0 < P.eigenvalue.re := hPl.eigenpair.re_pos
  refine ⟨Real.exp (P.eigenvalue.re * Real.exp δ) * (CE + Cf), kf + 1,
    min (min νF 1) (dm ^ 3 / 12), ?_, ?_⟩
  · exact lt_min (lt_min hνF one_pos) (div_pos (pow_pos hdm 3) (by norm_num))
  intro p d hreg hν ρb hρ hρ1 μ hμ SN hSN
  have hν0 : 0 < p.ν := p.ν_pos
  have hdm' : 0 < dm := hreg.dm_pos
  have hdd : dm ≤ d := hreg.dm_le
  have hd : 0 < d := lt_of_lt_of_le hdm' hdd
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνF' : p.ν ≤ νF := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  -- the regime: `ε ≤ 1`, `P = 2εc ≤ 1`
  have hεe : p.ε = Real.exp (-d / p.ν) := hreg.eps_eq
  have hε1 : p.ε ≤ 1 := by
    rw [hεe, Real.exp_le_one_iff]
    have : 0 ≤ d / p.ν := div_nonneg hd.le hν0.le
    rw [neg_div]; linarith
  have hcc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hEexp : Real.exp (-d / p.ν) = (Real.exp (d / p.ν))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have hdmx : 0 ≤ dm / p.ν := div_nonneg hdm'.le hν0.le
  have hE2 : 2 ≤ Real.exp (d / p.ν) * p.ν ^ 2 := by
    have h1 : (dm / p.ν) ^ 3 / 6 ≤ Real.exp (dm / p.ν) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (dm / p.ν) hdmx 3
    have h2 : Real.exp (dm / p.ν) ≤ Real.exp (d / p.ν) :=
      Real.exp_le_exp.2 (by gcongr)
    have h3 : (dm / p.ν) ^ 3 / 6 * p.ν ^ 2 = dm ^ 3 / (6 * p.ν) := by
      rw [div_pow]; field_simp
    have h4 : 2 ≤ dm ^ 3 / (6 * p.ν) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hν0)]; linarith
    calc (2 : ℝ) ≤ dm ^ 3 / (6 * p.ν) := h4
      _ = (dm / p.ν) ^ 3 / 6 * p.ν ^ 2 := h3.symm
      _ ≤ Real.exp (dm / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ Real.exp (d / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hP1 : p.period ≤ 1 := by
    unfold Params.period
    rw [hεe, hcc, hEexp]
    have hEp : 0 < Real.exp (d / p.ν) := Real.exp_pos _
    rw [show 2 * (Real.exp (d / p.ν))⁻¹ * (p.ν ^ 2)⁻¹ =
        2 / (Real.exp (d / p.ν) * p.ν ^ 2) by field_simp]
    rw [div_le_one (mul_pos hEp (pow_pos hν0 2))]
    exact hE2
  haveI : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hεpos : 0 < p.ε := p.ε_pos
  -- the level `sm = ε^b ∈ (0, 1]` and `sm ≤ S = ε^{-b}`
  have hsmpos : 0 < p.ε ^ b := Real.rpow_pos_of_pos hεpos b
  have hsm1 : p.ε ^ b ≤ 1 := Real.rpow_le_one hεpos.le hε1 hb.le
  have hsmS : p.ε ^ b ≤ p.ε ^ (-b) := by
    rw [Real.rpow_neg hεpos.le]
    have hinv : 1 ≤ (p.ε ^ b)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hsm1 (inv_nonneg.2 hsmpos.le)
      rw [mul_one, inv_mul_cancel₀ hsmpos.ne'] at h
      exact h
    linarith
  have hinv1 : 1 ≤ p.ν⁻¹ := by rw [← one_div, le_div_iff₀ hν0]; linarith
  have hεsm : p.ε * Real.sqrt (p.ε ^ b) ≤ 1 := by
    have := Real.sqrt_le_one.2 hsm1
    nlinarith [Real.sqrt_nonneg (p.ε ^ b)]
  have hinvν : 1 ≤ p.ν⁻¹ := by rw [← one_div, le_div_iff₀ hν0]; linarith
  have hrp : p.ν ^ (-(1 / 2 : ℝ)) ≤ p.ν⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  -- the masked operator
  obtain ⟨Seps, Sf, hpair, hSNeq⟩ := (isMaskedNear_iff p μ δ (p.ε ^ (-b)) SN).1 hSN
  have hμpos : 0 < μ := (hKsub hμ).1
  obtain ⟨⟨Seps', hSm, hTr⟩, hF'⟩ := hpair
  subst hSNeq
  have hpairM : IsMaskedPair p μ δ (p.ε ^ (-b)) Seps Sf := ⟨⟨Seps', hSm, hTr⟩, hF'⟩
  have hmA : MeasurableSet (ageBelow (p.ε ^ b)) := measurableSet_ageBelow _
  have hmB : MeasurableSet (ageBelow (Real.exp δ * p.ε ^ b)) := measurableSet_ageBelow _
  -- the output restriction kills the masked-out inputs
  have hopL : outRestr p.c (ageBelow (p.ε ^ b)) ∘L (Seps - Sf) =
      outRestr p.c (ageBelow (p.ε ^ b)) ∘L (Seps - Sf) ∘L
        inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) := by
    ext F
    simp only [ContinuousLinearMap.comp_apply]
    have hSup := hS p mZ ρb μ δ (p.ε ^ (-b)) (p.ε ^ b) hmZ hρ hρ1 hμpos hδ hsmpos hsmS
      Seps Sf hpairM
    have h0 := congrArg (fun T : Zsp p.c mZ ρb →L[ℝ] Hsp p.c => T F) hSup
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h0
    have hsplit : (Seps - Sf) F = (Seps - Sf) (inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) F) +
        (Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * p.ε ^ b)) F) := by
      rw [← map_add, inRestr_below_add_above]
    rw [hsplit, map_add, h0, add_zero]
  have hmB : MeasurableSet (ageBelow (Real.exp δ * p.ε ^ b)) := measurableSet_ageBelow _
  have hγ0 : 0 ≤ P.eigenvalue.re := hγ.le
  have hb0 : 0 ≤ Real.exp (P.eigenvalue.re * Real.exp δ) := (Real.exp_pos _).le
  have hgI : ∀ x ∈ ageBelow (p.ε ^ b), gainInvFun P.eigenvalue.re p.ν x ≤ 1 := fun x _ =>
    inv_le_one_of_one_le₀ (one_le_gainFun hγ0 hν0 x)
  have hgF : ∀ x ∈ ageBelow (Real.exp δ * p.ε ^ b),
      gainFun P.eigenvalue.re p.ν x ≤ Real.exp (P.eigenvalue.re * Real.exp δ) := fun x hx =>
    gainFun_le_lower hγ0 hν0 hδ hsmpos hsm1 x hx
  -- the forbidden block
  have hX2 := hfb p d hreg hνF' ρb hρ hρ1 μ hμ Sf hF' (p.ε ^ b) hsmpos hsmS
  have hCf0 : 0 ≤ Cf := by
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < p.ν⁻¹ ^ kf * (p.ε * Real.sqrt (p.ε ^ b)) :=
      mul_pos (pow_pos (inv_pos.2 hν0) _) (mul_pos hεpos (Real.sqrt_pos.2 hsmpos))
    have hneg' : Cf * p.ν⁻¹ ^ kf * (p.ε * Real.sqrt (p.ε ^ b)) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
    linarith [norm_nonneg (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L
      inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)))]
  have hX2' : ‖outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L
      inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))‖ ≤ Cf * p.ν⁻¹ ^ kf :=
    hX2.trans (mul_le_of_le_one_right (mul_nonneg hCf0 (pow_nonneg (inv_nonneg.2 hν0.le) kf))
      hεsm)
  -- the idempotence of the block restriction
  have hX2idem : outRestr p.c (ageBelow (p.ε ^ b)) ∘L
      (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))) ∘L
      inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) =
      outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) := by
    ext G
    simp only [ContinuousLinearMap.comp_apply]
    rw [outRestr_idem p.c hmA, inRestr_outer_of_sub p.c mZ ρb hmB hmB (subset_refl _) G]
  -- the split of the gained restriction
  have hsub : outRestr p.c (ageBelow (p.ε ^ b)) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) =
      outRestr p.c (ageBelow (p.ε ^ b)) ∘L Seps ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) -
      outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)) :=
    ContinuousLinearMap.ext fun G => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  have hEq2 : gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))) =
      gainBlockS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (ageBelow (Real.exp δ * p.ε ^ b))
        (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))) := by
    unfold gainBlockS
    rw [hX2idem]
  have hsplitGain : gainRestrS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (Seps - Sf) =
      gainConjS P.eigenvalue.re hν0
        (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Seps ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))) -
      gainConjS P.eigenvalue.re hν0
        (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b))) := by
    unfold gainRestrS
    rw [hopL, hsub, gainConjS_sub]
  have hfinal1 : ‖gainRestrS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (Seps - Sf)‖ ≤
      ‖gainBlockS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (ageBelow (Real.exp δ * p.ε ^ b)) Seps‖ +
        ‖gainBlockS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (ageBelow (Real.exp δ * p.ε ^ b))
          (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)))‖ := by
    rw [hsplitGain, ← hEq2]
    exact norm_sub_le _ _
  have hb1 := hG p.c mZ ρb P.eigenvalue.re p.ν hν0 (ageBelow (p.ε ^ b)) (ageBelow (Real.exp δ * p.ε ^ b))
    1 (Real.exp (P.eigenvalue.re * Real.exp δ)) Seps hmA hmB zero_le_one hb0 hgI hgF
  have hb2 := hG p.c mZ ρb P.eigenvalue.re p.ν hν0 (ageBelow (p.ε ^ b)) (ageBelow (Real.exp δ * p.ε ^ b))
    1 (Real.exp (P.eigenvalue.re * Real.exp δ))
    (outRestr p.c (ageBelow (p.ε ^ b)) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ b)))
    hmA hmB zero_le_one hb0 hgI hgF
  rw [one_mul] at hb1 hb2
  have hSn : ‖Seps‖ ≤ CE * p.ν⁻¹ :=
    (hEb p.ν p.ε p.c p.period hν0 p.ε_pos p.c_pos rfl hε1 hP1 μ (hKsub hμ).1 (hKsub hμ).2
      mZ ρb hmZ hρ hρ1 Seps' Seps hSm hTr).trans (mul_le_mul_of_nonneg_left hrp hCE0)
  have hp1 : p.ν⁻¹ ≤ p.ν⁻¹ ^ (kf + 1) := by
    have := pow_le_pow_right₀ hinv1 (show 1 ≤ kf + 1 by omega)
    rwa [pow_one] at this
  have hp2 : p.ν⁻¹ ^ kf ≤ p.ν⁻¹ ^ (kf + 1) := pow_le_pow_right₀ hinv1 (Nat.le_succ kf)
  calc ‖gainRestrS P.eigenvalue.re hν0 (ageBelow (p.ε ^ b)) (Seps - Sf)‖
      ≤ _ := hfinal1
    _ ≤ Real.exp (P.eigenvalue.re * Real.exp δ) * (CE * p.ν⁻¹ ^ (kf + 1)) +
        Real.exp (P.eigenvalue.re * Real.exp δ) * (Cf * p.ν⁻¹ ^ (kf + 1)) := by
          refine add_le_add ?_ ?_
          · exact hb1.trans (mul_le_mul_of_nonneg_left (hSn.trans (mul_le_mul_of_nonneg_left hp1 hCE0)) hb0)
          · exact hb2.trans (mul_le_mul_of_nonneg_left (hX2'.trans (mul_le_mul_of_nonneg_left hp2 hCf0)) hb0)
    _ = (Real.exp (P.eigenvalue.re * Real.exp δ) * (CE + Cf)) * p.ν⁻¹ ^ (kf + 1) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
