import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioSup
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioTanh

/-!
# `PartIII-b:C/near/masked/28`: `maskedBinPiece_of` (source 3974-3990, 3996-4007, 4022-4026)

A bin `[l, r)` of the output band, `r ≤ e^{δ/2} l`, `r ≤ S`.  The input is split at `e^δ l`:
the complete block (inputs `t < e^δ l`, where `FarBlockZero` kills the far part, so the block is the
free operator) costs the gain ratio `e^{γ tanh(3δ/8)/ν}` times the free energy, and the partial
strip (inputs `e^δ l ≤ t < e^δ r`, the rest vanishes by `MaskedSupport`) costs the same ratio times
the strip bound `MaskedStripBound`.
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

/-- **`maskedBinPiece_of`** (source 3974-3990, 3996-4007, 4022-4026). -/
theorem maskedBinPiece_of (hE : RealStressBound) (hB : FarBlockZero) (hS : MaskedSupport)
    (hT : MaskedStripBound) (hG : GainBlockBound) : MaskedBinPiece := by
  obtain ⟨CE, hCE0, hEb⟩ := hE
  intro P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨Cs, ks, νs, hνs, hstrip⟩ := hT Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  have hγ : 0 < P.eigenvalue.re := hPl.eigenpair.re_pos
  refine ⟨CE + Cs, ks + 1, min (min νs 1) (dm ^ 3 / 12), ?_, ?_⟩
  · exact lt_min (lt_min hνs one_pos) (div_pos (pow_pos hdm 3) (by norm_num))
  intro p d hreg hν ρb hρ hρ1 μ hμ SN hSN l r hl hlr hrl hrS
  have hν0 : 0 < p.ν := p.ν_pos
  have hdm' : 0 < dm := hreg.dm_pos
  have hdd : dm ≤ d := hreg.dm_le
  have hd : 0 < d := lt_of_lt_of_le hdm' hdd
  have hb0 : 0 ≤ b := hb.le
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνs' : p.ν ≤ νs := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
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
  -- `ε √r ≤ 1` on the bin (since `r ≤ ε^{-b}`, `b < 1`)
  have hr0 : 0 ≤ r := by linarith
  have hεr : p.ε * Real.sqrt r ≤ 1 := by
    have hsq : p.ε ^ 2 * r ≤ 1 := by
      have h2 : p.ε ^ 2 * p.ε ^ (-b) ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hεpos]
        exact Real.rpow_le_one hεpos.le hε1 (by push_cast; linarith)
      calc p.ε ^ 2 * r ≤ p.ε ^ 2 * p.ε ^ (-b) :=
            mul_le_mul_of_nonneg_left hrS (by positivity)
        _ ≤ 1 := h2
    have hsq1 : (p.ε * Real.sqrt r) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hr0]; exact hsq
    exact (pow_le_one_iff_of_nonneg (mul_nonneg hεpos.le (Real.sqrt_nonneg r)) two_ne_zero).1
      hsq1
  -- the inverse-viscosity factor
  have hinv : 1 ≤ p.ν⁻¹ := by rw [← one_div, le_div_iff₀ hν0]; linarith
  have hrp : p.ν ^ (-(1 / 2 : ℝ)) ≤ p.ν⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  -- the masked operator
  obtain ⟨Seps, Sf, hpair, hSNeq⟩ := (isMaskedNear_iff p μ δ (p.ε ^ (-b)) SN).1 hSN
  have hμpos : 0 < μ := (hKsub hμ).1
  obtain ⟨⟨Seps', hSm, hTr⟩, hF⟩ := hpair
  subst hSNeq
  have hpairM : IsMaskedPair p μ δ (p.ε ^ (-b)) Seps Sf := ⟨⟨Seps', hSm, hTr⟩, hF⟩
  -- the bands and the input splits
  have hsplit : ∀ F : Zsp p.c mZ ρb,
      (Seps - Sf) F = (Seps - Sf) (inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) F) +
        (Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F) := fun F => by
    rw [← map_add, inRestr_below_add_above]
  have hop : outRestr p.c (ageBand l r) ∘L (Seps - Sf) =
      outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) +
        outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) := by
    ext F
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    rw [← map_add, ← map_add, inRestr_below_add_above]
  have hr0' : 0 < r := lt_trans hl hlr
  have hmB : MeasurableSet (ageBand l r) := measurableSet_ageBand l r
  have hmBl : MeasurableSet (ageBelow (Real.exp δ * l)) := measurableSet_ageBelow _
  have hmAl : MeasurableSet (ageAbove (Real.exp δ * l)) := measurableSet_ageAbove _
  have hmAr : MeasurableSet (ageAbove (Real.exp δ * r)) := measurableSet_ageAbove _
  have hmBr : MeasurableSet (ageBelow r) := measurableSet_ageBelow r
  have hBr' : MeasurableSet (ageBelow (Real.exp δ * r)) := measurableSet_ageBelow _
  have hAr_sub : ageAbove (Real.exp δ * r) ⊆ ageAbove (Real.exp δ * l) := fun x hx =>
    le_trans (mul_le_mul_of_nonneg_left hlr.le (Real.exp_pos δ).le) hx
  have hband_above : ageBand l r ⊆ ageAbove l := fun x hx => hx.1
  have hband_below : ageBand l r ⊆ ageBelow r := fun x hx => hx.2
  have hz_pos : (0 : ℝ) < Real.exp δ * l := mul_pos (Real.exp_pos δ) hl
  have hz_r : (0 : ℝ) < Real.exp δ * r := mul_pos (Real.exp_pos δ) hr0'
  -- the far part vanishes on the complete block
  have hzeroBlock : ∀ G : Zsp p.c mZ ρb,
      outRestr p.c (ageBand l r) (Sf (inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) G)) = 0 := by
    intro G
    have h0 := congrArg (fun T : Zsp p.c mZ ρb →L[ℝ] Hsp p.c => T G)
      (hB p.c mZ ρb p.R p.ν μ δ (p.ε ^ (-b)) l p.c_pos hmZ hρ hρ1 hδ hl Sf hF)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h0
    rw [← outRestr_inner_of_sub p.c hmB (measurableSet_ageAbove l) hband_above, h0, map_zero]
  have hXB : outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) =
      outRestr p.c (ageBand l r) ∘L Seps ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) := by
    ext G
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [hzeroBlock G, sub_zero]
  -- the complete block: gain ratio times the free energy
  have hBlock : ‖gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBand l r) ∘L Seps ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)))‖ ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * ‖Seps‖ := by
    have hgb := hG p.c mZ ρb P.eigenvalue.re p.ν hν0 (ageBand l r) (ageBelow (Real.exp δ * l))
      (Real.exp (-(P.eigenvalue.re * l / (1 + p.ν * l))))
      (Real.exp (P.eigenvalue.re * (Real.exp δ * l) / (1 + p.ν * (Real.exp δ * l)))) Seps
      hmB hmBl (Real.exp_pos _).le (Real.exp_pos _).le
      (fun x hx => gainInv_block_le hγ.le hν0 hl x hx.1)
      (fun x hx => gainFun_le_of_lt hγ.le hν0 hz_pos x hx)
    have hlt : l ≤ Real.exp δ * l := le_mul_of_one_le_left hl.le (Real.one_le_exp hδ.le)
    have htM : Real.exp δ * l ≤ Real.exp (3 * δ / 2) * l :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hl.le
    have hM : 1 ≤ Real.exp (3 * δ / 2) := Real.one_le_exp (by linarith)
    have hratio := gain_ratio_le (M := Real.exp (3 * δ / 2)) hγ.le hν0 hl hlt htM hM
    have hr3 : Real.log (Real.exp (3 * δ / 2)) / 4 = 3 * δ / 8 := by rw [Real.log_exp]; ring
    rw [hr3] at hratio
    have hab : Real.exp (P.eigenvalue.re * (Real.exp δ * l) / (1 + p.ν * (Real.exp δ * l))) *
        Real.exp (-(P.eigenvalue.re * l / (1 + p.ν * l))) ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by
      refine hratio.trans (Real.exp_le_exp.2 (le_of_eq ?_))
      unfold etaDelta; ring
    have hab' : Real.exp (-(P.eigenvalue.re * l / (1 + p.ν * l))) *
        Real.exp (P.eigenvalue.re * (Real.exp δ * l) / (1 + p.ν * (Real.exp δ * l))) ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by
      rw [mul_comm]; exact hab
    exact hgb.trans (mul_le_mul_of_nonneg_right hab' (norm_nonneg _))
  -- the partial strip: gain ratio times the strip bound
  have hkey : ∀ G : Zsp p.c mZ ρb,
      outRestr p.c (ageBand l r) ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) G)) =
        outRestr p.c (ageBand l r) ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))
          (inRestr p.c mZ ρb (ageBelow (Real.exp δ * r)) G))) := by
    intro G
    have hAsplit : inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) G =
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) (inRestr p.c mZ ρb (ageBelow (Real.exp δ * r)) G) +
          inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) G := by
      calc inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) G
          = inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))
              (inRestr p.c mZ ρb (ageBelow (Real.exp δ * r)) G +
                inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) G) := by
            rw [inRestr_below_add_above]
        _ = _ := by
            rw [map_add, inRestr_outer_of_sub p.c mZ ρb hmAl hmAr hAr_sub G]
    have hSr := hS p mZ ρb μ δ (p.ε ^ (-b)) r hmZ hρ hρ1 hμpos hδ hr0' hrS Seps Sf hpairM
    have hz : outRestr p.c (ageBand l r) ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) G)) = 0 := by
      have h0 := congrArg (fun T : Zsp p.c mZ ρb →L[ℝ] Hsp p.c => T G) hSr
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h0
      rw [← outRestr_inner_of_sub p.c hmB hmBr hband_below, h0, map_zero]
    have hsplitS : (Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) G) =
        (Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))
          (inRestr p.c mZ ρb (ageBelow (Real.exp δ * r)) G)) +
        (Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) G) := by
      rw [← map_add, ← hAsplit]
    rw [hsplitS, map_add, hz, add_zero]
  have hXBr : outRestr p.c (ageBand l r) ∘L (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * r)) =
      outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) := by
    ext G
    simp only [ContinuousLinearMap.comp_apply]
    rw [outRestr_idem p.c hmB, hkey G]
  have hStrip : ‖gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)))‖ ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) *
          (Cs * p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r)) := by
    have hXn := hstrip p d hreg hνs' ρb hρ hρ1 μ hμ Seps Sf hpairM l r hl hlr hrl hrS
    have hgs := hG p.c mZ ρb P.eigenvalue.re p.ν hν0 (ageBand l r) (ageBelow (Real.exp δ * r))
      (Real.exp (-(P.eigenvalue.re * l / (1 + p.ν * l))))
      (Real.exp (P.eigenvalue.re * (Real.exp δ * r) / (1 + p.ν * (Real.exp δ * r))))
      (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)))
      hmB hBr' (Real.exp_pos _).le (Real.exp_pos _).le
      (fun x hx => gainInv_block_le hγ.le hν0 hl x hx.1)
      (fun x hx => gainFun_le_of_lt hγ.le hν0 hz_r x hx)
    have hlt : l ≤ Real.exp δ * r := le_trans hlr.le (le_mul_of_one_le_left hr0'.le (Real.one_le_exp hδ.le))
    have htM : Real.exp δ * r ≤ Real.exp (3 * δ / 2) * l := by
      have hMe : Real.exp (3 * δ / 2) = Real.exp δ * Real.exp (δ / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hMe]
      calc Real.exp δ * r ≤ Real.exp δ * (Real.exp (δ / 2) * l) :=
            mul_le_mul_of_nonneg_left hrl (Real.exp_pos δ).le
        _ = Real.exp δ * Real.exp (δ / 2) * l := by ring
    have hM : 1 ≤ Real.exp (3 * δ / 2) := Real.one_le_exp (by linarith)
    have hratio := gain_ratio_le (M := Real.exp (3 * δ / 2)) hγ.le hν0 hl hlt htM hM
    have hr3 : Real.log (Real.exp (3 * δ / 2)) / 4 = 3 * δ / 8 := by rw [Real.log_exp]; ring
    rw [hr3] at hratio
    have hab' : Real.exp (-(P.eigenvalue.re * l / (1 + p.ν * l))) *
        Real.exp (P.eigenvalue.re * (Real.exp δ * r) / (1 + p.ν * (Real.exp δ * r))) ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by
      rw [mul_comm]
      refine hratio.trans (Real.exp_le_exp.2 (le_of_eq ?_))
      unfold etaDelta; ring
    have hEq : gainConjS P.eigenvalue.re hν0
        (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))) =
        gainBlockS P.eigenvalue.re hν0 (ageBand l r) (ageBelow (Real.exp δ * r))
          (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))) := by
      unfold gainBlockS
      rw [hXBr]
    have hCs : 0 ≤ Cs := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r) :=
        mul_pos (pow_pos (inv_pos.2 hν0) _) (mul_pos hεpos (Real.sqrt_pos.2 hr0'))
      have hneg' : Cs * p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r) < 0 := by
        rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
      linarith [norm_nonneg (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)))]
    rw [hEq]
    exact hgs.trans (mul_le_mul hab' hXn (norm_nonneg _) (Real.exp_pos _).le)
  have hXn0 := hstrip p d hreg hνs' ρb hρ hρ1 μ hμ Seps Sf hpairM l r hl hlr hrl hrS
  have hCs : 0 ≤ Cs := by
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r) :=
      mul_pos (pow_pos (inv_pos.2 hν0) _) (mul_pos hεpos (Real.sqrt_pos.2 hr0'))
    have hneg' : Cs * p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
    linarith [norm_nonneg (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)))]
  have hSn : ‖Seps‖ ≤ CE * p.ν⁻¹ :=
    (hEb p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl hε1 hP1 μ (hKsub hμ).1 (hKsub hμ).2
      mZ ρb hmZ hρ hρ1 Seps' Seps hSm hTr).trans (mul_le_mul_of_nonneg_left hrp hCE0)
  have hgR : gainRestrS P.eigenvalue.re p.ν_pos (ageBand l r) (Seps - Sf) =
      gainConjS P.eigenvalue.re hν0
        (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l))) +
      gainConjS P.eigenvalue.re hν0
        (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))) := by
    unfold gainRestrS
    rw [hop, gainConjS_add']
  have hfin := norm_add_le
    (gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l))))
    (gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))))
  rw [← hgR] at hfin
  have hB1 : ‖gainConjS P.eigenvalue.re hν0
      (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)))‖ ≤
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (CE * p.ν⁻¹) := by
    rw [hXB]
    exact hBlock.trans (mul_le_mul_of_nonneg_left hSn (Real.exp_pos _).le)
  have hpow1 : p.ν⁻¹ ≤ p.ν⁻¹ ^ (ks + 1) := by
    have := pow_le_pow_right₀ hinv (show 1 ≤ ks + 1 by omega)
    rwa [pow_one] at this
  have hpow2 : p.ν⁻¹ ^ ks ≤ p.ν⁻¹ ^ (ks + 1) := pow_le_pow_right₀ hinv (Nat.le_succ ks)
  have hA : p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r) ≤ p.ν⁻¹ ^ (ks + 1) :=
    (mul_le_of_le_one_right (pow_nonneg (inv_nonneg.2 hν0.le) _) hεr).trans hpow2
  have hE0 : 0 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := (Real.exp_pos _).le
  have h1 : Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (CE * p.ν⁻¹) ≤
      Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (CE * p.ν⁻¹ ^ (ks + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow1 hCE0) hE0
  have h2 : Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (Cs * p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r)) ≤
      Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (Cs * p.ν⁻¹ ^ (ks + 1)) :=
    mul_le_mul_of_nonneg_left (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hA hCs) hE0
  calc ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBand l r) (Seps - Sf)‖
      ≤ _ := hfin
    _ ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (CE * p.ν⁻¹) +
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (Cs * p.ν⁻¹ ^ ks * (p.ε * Real.sqrt r)) :=
          add_le_add hB1 hStrip
    _ ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (CE * p.ν⁻¹ ^ (ks + 1)) +
        Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (Cs * p.ν⁻¹ ^ (ks + 1)) := add_le_add h1 h2
    _ = (CE + Cs) * p.ν⁻¹ ^ (ks + 1) * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
