import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_10
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Exists

/-!
# `PartIII-b:C/near/delta/10/1`: the young masked piece (source 4011-4015)

Proves `youngMaskedPiece_of : YoungMaskedPiece` from `RealStressBound` (`near:free-energy`),
`MaskedSupport`, `ForbiddenBlockBound` and `GainBlockBound`.

Source of record `the November 2 reference manuscript`, 4011-4015.

Route: with `T = ε^a ≤ 1 ≤ ε^{-b} = S`, `g⁻¹ 1_{s<T} S_N G` is the block
`g⁻¹ 1_{s<T} S_N 1_{t<e^δT} g` (the part `1_{t≥e^δT}` vanishes by `MaskedSupport`), which is
bounded by `GainBlockBound` with `g⁻¹ ≤ 1` on `s<T` and `g ≤ e^{γe^δ}` on `t<e^δT`.  The block is
`S_ε` minus the far block; the free part is `‖S_ε‖ ≤ C ν^{-1/2}` (`RealStressBound`), the far part
`‖1_{s<T}S_far1_{t<e^δT}‖ ≤ C ν^{-k} ε√T` (`ForbiddenBlockBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## Helpers -/

/-- The norm of a `Z` element is the sum of the norms of its components. -/
theorem yme_zsp_norm_eq {c mZ ρb : ℝ} (F : Zsp c mZ ρb) :
    ‖F‖ = ‖(zEquiv c mZ ρb F).1‖ + ‖(zEquiv c mZ ρb F).2‖ := by
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp [zEquiv]

/-- The input restriction is idempotent. -/
theorem yme_inRestr_idem (c mZ ρb : ℝ) {A : Set Chart} (hA : MeasurableSet A)
    (W : Zsp c mZ ρb) :
    inRestr c mZ ρb A (inRestr c mZ ρb A W) = inRestr c mZ ρb A W := by
  apply (zEquiv c mZ ρb).injective
  rw [zEquiv_inRestr, zEquiv_inRestr]
  simp only [restrLp_idem hA]

/-- The input restriction has norm at most one. -/
theorem yme_inRestr_norm_le_one (c mZ ρb : ℝ) {A : Set Chart} (hA : MeasurableSet A) :
    ‖inRestr c mZ ρb A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun F => ?_)
  rw [one_mul, yme_zsp_norm_eq (inRestr c mZ ρb A F), zEquiv_inRestr, yme_zsp_norm_eq F]
  have e1 : ‖restrLp (z1Measure c mZ) Ten3 A (zEquiv c mZ ρb F).1‖ ≤
      ‖(zEquiv c mZ ρb F).1‖ := by
    calc _ ≤ ‖restrLp (z1Measure c mZ) Ten3 A‖ * ‖(zEquiv c mZ ρb F).1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(zEquiv c mZ ρb F).1‖ := by
          gcongr
          exact restrLp_norm_le_one hA
      _ = _ := one_mul _
  have e2 : ‖restrLp (htRhoMeasure c ρb) Ten3 A (zEquiv c mZ ρb F).2‖ ≤
      ‖(zEquiv c mZ ρb F).2‖ := by
    calc _ ≤ ‖restrLp (htRhoMeasure c ρb) Ten3 A‖ * ‖(zEquiv c mZ ρb F).2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(zEquiv c mZ ρb F).2‖ := by
          gcongr
          exact restrLp_norm_le_one hA
      _ = _ := one_mul _
  dsimp only
  linarith

/-- The block `1_A S 1_B` of a response has norm at most `‖S‖`. -/
theorem yme_outRestr_comp_le (c mZ ρb : ℝ) {A B : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (S : Zsp c mZ ρb →L[ℝ] Hsp c) :
    ‖outRestr c A ∘L S ∘L inRestr c mZ ρb B‖ ≤ ‖S‖ := by
  have h1 : ‖outRestr c A ∘L (S ∘L inRestr c mZ ρb B)‖ ≤
      ‖outRestr c A‖ * ‖S ∘L inRestr c mZ ρb B‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖S ∘L inRestr c mZ ρb B‖ ≤ ‖S‖ * ‖inRestr c mZ ρb B‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h3 : ‖outRestr c A‖ ≤ 1 := outRestr_norm_le_one c hA
  have h4 : ‖inRestr c mZ ρb B‖ ≤ 1 := yme_inRestr_norm_le_one c mZ ρb hB
  have h5 : ‖outRestr c A‖ * ‖S ∘L inRestr c mZ ρb B‖ ≤ 1 * ‖S‖ := by
    refine mul_le_mul h3 ?_ (norm_nonneg _) zero_le_one
    calc ‖S ∘L inRestr c mZ ρb B‖ ≤ ‖S‖ * ‖inRestr c mZ ρb B‖ := h2
      _ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = ‖S‖ := mul_one _
  linarith

/-- Subtracting a far block: `‖1_A(S - Sf)1_B‖ ≤ ‖S‖ + ‖1_A Sf 1_B‖`. -/
theorem yme_norm_sub (c mZ ρb : ℝ) {A B : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (S Sf : Zsp c mZ ρb →L[ℝ] Hsp c) :
    ‖outRestr c A ∘L (S - Sf) ∘L inRestr c mZ ρb B‖ ≤
      ‖S‖ + ‖outRestr c A ∘L Sf ∘L inRestr c mZ ρb B‖ := by
  have hsplit : outRestr c A ∘L (S - Sf) ∘L inRestr c mZ ρb B =
      outRestr c A ∘L S ∘L inRestr c mZ ρb B - outRestr c A ∘L Sf ∘L inRestr c mZ ρb B := by
    ext G
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    exact Filter.EventuallyEq.rfl
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have h1 := yme_outRestr_comp_le c mZ ρb hA hB S
  linarith

/-- The restriction of a response to an output region `A`, when its input part outside `B` is
killed, equals the gained block on `A × B` (`gainRestrS` is `gainBlockS` with input `B`). -/
theorem yme_block_eq (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A B C : Set Chart}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsum : ∀ F : Zsp c mZ ρb, inRestr c mZ ρb B F + inRestr c mZ ρb C F = F)
    (X : Zsp c mZ ρb →L[ℝ] Hsp c)
    (hX : outRestr c A ∘L X ∘L inRestr c mZ ρb C = 0) :
    gainRestrS γ hν A X = gainBlockS γ hν A B (outRestr c A ∘L X ∘L inRestr c mZ ρb B) := by
  have hK : outRestr c A ∘L X = outRestr c A ∘L X ∘L inRestr c mZ ρb B := by
    ext G
    simp only [ContinuousLinearMap.comp_apply]
    have key : X G = X (inRestr c mZ ρb B G) + X (inRestr c mZ ρb C G) := by
      rw [← map_add, hsum G]
    have hC : outRestr c A (X (inRestr c mZ ρb C G)) = 0 := by
      have h := DFunLike.congr_fun hX G
      simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h
    rw [key, map_add, hC, add_zero]
  have hidem : outRestr c A ∘L (outRestr c A ∘L X ∘L inRestr c mZ ρb B) ∘L
      inRestr c mZ ρb B = outRestr c A ∘L X ∘L inRestr c mZ ρb B := by
    ext G
    simp only [ContinuousLinearMap.comp_apply]
    rw [yme_inRestr_idem c mZ ρb hB G, outRestr_idem c hA]
  unfold gainRestrS gainBlockS
  rw [hidem]
  rw [hK]

/-- The gained block bound for a response whose input part outside `B` is killed. -/
theorem yme_gain_split (hG : UnforcedLeray.Short.PartIIIb.NearInst.Masked.GainBlockBound)
    (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A B C : Set Chart}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsum : ∀ F : Zsp c mZ ρb, inRestr c mZ ρb B F + inRestr c mZ ρb C F = F)
    (X : Zsp c mZ ρb →L[ℝ] Hsp c)
    (hX : outRestr c A ∘L X ∘L inRestr c mZ ρb C = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgA : ∀ x ∈ A, gainInvFun γ ν x ≤ a) (hgB : ∀ x ∈ B, gainFun γ ν x ≤ b) :
    ‖gainRestrS γ hν A X‖ ≤ a * b * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ := by
  rw [yme_block_eq c mZ ρb γ hν hA hB hsum X hX]
  exact hG c mZ ρb γ ν hν A B a b _ hA hB ha hb hgA hgB

/-! ## The young masked piece -/

/-- **`youngMaskedPiece_of`** (source 4011-4015): the young `S_N` piece from the free energy bound,
the mask support, the forbidden block bound and the gain block bound. -/
theorem youngMaskedPiece_of
    (hE : UnforcedLeray.Short.PartIIIb.NearInst.Masked.RealStressBound)
    (hS : UnforcedLeray.Short.PartIIIb.NearInst.Masked.MaskedSupport)
    (hF : UnforcedLeray.Short.PartIIIb.NearInst.Masked.ForbiddenBlockBound)
    (hG : UnforcedLeray.Short.PartIIIb.NearInst.Masked.GainBlockBound) : YoungMaskedPiece := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C0, hC0, hE'⟩ := hE
  obtain ⟨CF, kF, νF, hνF, hF'⟩ := hF Kset hK hKs mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨νP, hνP, hper⟩ :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.exists_period_le_one hdm
  have hγ0 : 0 ≤ P.eigenvalue.re := hP.eigenpair.re_pos.le
  refine ⟨Real.exp (P.eigenvalue.re * Real.exp δ) * (C0 + |CF|), kF + 1,
    min νF (min νP 1), lt_min hνF (lt_min hνP one_pos), ?_⟩
  intro p d hreg hpν ρb hρ hρ1 μ hμ SN hact
  obtain ⟨Seps, Sf, Seps', hIS, hST, hFM, rfl⟩ := hact
  have hνF' : p.ν ≤ νF := hpν.trans (min_le_left _ _)
  have hνP' : p.ν ≤ νP := hpν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hpν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν := p.ν_pos
  have hεle : p.ε ≤ 1 :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.eps_le_one_of_regime hreg
  have hεpos := p.ε_pos
  have hPer : p.period ≤ 1 := hper p d dp hreg hνP'
  have hμ0 : 0 < μ := (hKs hμ).1
  have hμ14 : μ < 1 / 4 := (hKs hμ).2
  have hi : 1 ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have ht0 : 0 ≤ p.ν⁻¹ := inv_nonneg.2 hν.le
  -- the free bound on `S_ε`
  have hSeps := hE' p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl hεle hPer μ hμ0 hμ14
    mZ ρb hmZ hρ hρ1 Seps' Seps hIS hST
  have hsq : p.ν ^ (-(1 / 2 : ℝ)) ≤ p.ν⁻¹ := by
    have e : p.ν ^ (-(1 / 2 : ℝ)) = p.ν⁻¹ ^ (1 / 2 : ℝ) := by
      rw [Real.inv_rpow hν.le, Real.rpow_neg hν.le]
    rw [e]
    calc p.ν⁻¹ ^ (1 / 2 : ℝ) ≤ p.ν⁻¹ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hi (by norm_num)
      _ = p.ν⁻¹ := Real.rpow_one _
  have hSeps' : ‖Seps‖ ≤ C0 * p.ν⁻¹ := hSeps.trans (mul_le_mul_of_nonneg_left hsq hC0)
  -- the threshold `T = ε^a ≤ 1 ≤ ε^{-b} = S`
  have hTpos : 0 < p.ε ^ a := Real.rpow_pos_of_pos hεpos a
  have hT1 : p.ε ^ a ≤ 1 := Real.rpow_le_one hεpos.le hεle ha.le
  have hTS : p.ε ^ a ≤ p.ε ^ (-b) := by
    have h1 : 1 ≤ p.ε ^ (-b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεpos hεle (by linarith)
    linarith
  have hsT : Real.sqrt (p.ε ^ a) ≤ 1 := (Real.sqrt_le_sqrt hT1).trans_eq Real.sqrt_one
  have hεsT : p.ε * Real.sqrt (p.ε ^ a) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (p.ε ^ a)]
  -- the masked support: the output part `s < T` sees no input `t ≥ e^δ T`
  have hPair : UnforcedLeray.Short.PartIIIb.NearInst.Masked.IsMaskedPair p μ δ (p.ε ^ (-b))
      Seps Sf := by
    unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.IsMaskedPair
    exact ⟨⟨Seps', hIS, hST⟩, hFM⟩
  have hzero := hS p mZ ρb μ δ (p.ε ^ (-b)) (p.ε ^ a) hmZ hρ hρ1 hμ0 hδ hTpos hTS Seps Sf hPair
  -- the gained block on `s < T`, `t < e^δ T`
  have hgA : ∀ x ∈ ageBelow (p.ε ^ a), gainInvFun P.eigenvalue.re p.ν x ≤ 1 := by
    intro x _
    unfold gainInvFun
    exact inv_le_one_of_one_le₀ (one_le_gainFun hγ0 hν x)
  have hgB : ∀ x ∈ ageBelow (Real.exp δ * p.ε ^ a),
      gainFun P.eigenvalue.re p.ν x ≤ Real.exp (P.eigenvalue.re * Real.exp δ) := by
    intro x hx
    have hx' : x.1 < Real.exp δ * p.ε ^ a := hx
    have hTe : Real.exp δ * p.ε ^ a ≤ Real.exp δ := mul_le_of_le_one_right (Real.exp_pos δ).le hT1
    have hm0 : 0 ≤ max x.1 0 := le_max_right _ _
    have hmle : max x.1 0 ≤ Real.exp δ := max_le (hx'.le.trans hTe) (Real.exp_pos δ).le
    unfold gainFun UnforcedLeray.Short.IIIa.gainG
    apply Real.exp_le_exp.2
    have hden : 1 ≤ 1 + p.ν * max x.1 0 := by
      have := mul_nonneg hν.le hm0
      linarith
    calc P.eigenvalue.re * max x.1 0 / (1 + p.ν * max x.1 0)
        ≤ P.eigenvalue.re * max x.1 0 := div_le_self (mul_nonneg hγ0 hm0) hden
      _ ≤ P.eigenvalue.re * Real.exp δ := mul_le_mul_of_nonneg_left hmle hγ0
  have hgl := yme_gain_split hG p.c mZ ρb P.eigenvalue.re hν
    (measurableSet_ageBelow (p.ε ^ a)) (measurableSet_ageBelow (Real.exp δ * p.ε ^ a))
    (inRestr_below_add_above p.c mZ ρb (Real.exp δ * p.ε ^ a)) (Seps - Sf) hzero
    1 (Real.exp (P.eigenvalue.re * Real.exp δ)) zero_le_one (Real.exp_pos _).le hgA hgB
  -- the far block
  have hQ := yme_norm_sub p.c mZ ρb (measurableSet_ageBelow (p.ε ^ a))
    (measurableSet_ageBelow (Real.exp δ * p.ε ^ a)) Seps Sf
  have hQ2 := hF' p d hreg hνF' ρb hρ hρ1 μ hμ Sf hFM (p.ε ^ a) hTpos hTS
  have hY0 : 0 ≤ p.ε * Real.sqrt (p.ε ^ a) := mul_nonneg hεpos.le (Real.sqrt_nonneg _)
  have hpow0 : 0 ≤ p.ν⁻¹ ^ kF := pow_nonneg ht0 kF
  have hQ2' : CF * p.ν⁻¹ ^ kF * (p.ε * Real.sqrt (p.ε ^ a)) ≤ |CF| * p.ν⁻¹ ^ kF := by
    calc CF * p.ν⁻¹ ^ kF * (p.ε * Real.sqrt (p.ε ^ a))
        ≤ |CF| * p.ν⁻¹ ^ kF * (p.ε * Real.sqrt (p.ε ^ a)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CF) hpow0) hY0
      _ ≤ |CF| * p.ν⁻¹ ^ kF * 1 :=
          mul_le_mul_of_nonneg_left hεsT (mul_nonneg (abs_nonneg _) hpow0)
      _ = |CF| * p.ν⁻¹ ^ kF := mul_one _
  -- powers of `ν⁻¹`
  have hK1 : p.ν⁻¹ ≤ p.ν⁻¹ ^ (kF + 1) := by
    calc p.ν⁻¹ = p.ν⁻¹ ^ 1 := (pow_one _).symm
      _ ≤ p.ν⁻¹ ^ (kF + 1) := pow_le_pow_right₀ hi (by omega)
  have hK2 : p.ν⁻¹ ^ kF ≤ p.ν⁻¹ ^ (kF + 1) := pow_le_pow_right₀ hi (Nat.le_succ kF)
  have hQle : ‖outRestr p.c (ageBelow (p.ε ^ a)) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ a))‖ ≤
      C0 * p.ν⁻¹ + |CF| * p.ν⁻¹ ^ kF := by
    linarith [hQ, hQ2, hQ2', hSeps']
  have hfin2 : C0 * p.ν⁻¹ + |CF| * p.ν⁻¹ ^ kF ≤ (C0 + |CF|) * p.ν⁻¹ ^ (kF + 1) := by
    have e1 : C0 * p.ν⁻¹ ≤ C0 * p.ν⁻¹ ^ (kF + 1) := mul_le_mul_of_nonneg_left hK1 hC0
    have e2 : |CF| * p.ν⁻¹ ^ kF ≤ |CF| * p.ν⁻¹ ^ (kF + 1) :=
      mul_le_mul_of_nonneg_left hK2 (abs_nonneg _)
    have e3 : (C0 + |CF|) * p.ν⁻¹ ^ (kF + 1) =
        C0 * p.ν⁻¹ ^ (kF + 1) + |CF| * p.ν⁻¹ ^ (kF + 1) := by ring
    linarith
  have hEpos : 0 ≤ Real.exp (P.eigenvalue.re * Real.exp δ) := (Real.exp_pos _).le
  calc _ ≤ 1 * Real.exp (P.eigenvalue.re * Real.exp δ) *
        ‖outRestr p.c (ageBelow (p.ε ^ a)) ∘L (Seps - Sf) ∘L
          inRestr p.c mZ ρb (ageBelow (Real.exp δ * p.ε ^ a))‖ := hgl
    _ ≤ 1 * Real.exp (P.eigenvalue.re * Real.exp δ) *
        (C0 * p.ν⁻¹ + |CF| * p.ν⁻¹ ^ kF) :=
          mul_le_mul_of_nonneg_left hQle (by positivity)
    _ ≤ 1 * Real.exp (P.eigenvalue.re * Real.exp δ) * ((C0 + |CF|) * p.ν⁻¹ ^ (kF + 1)) :=
          mul_le_mul_of_nonneg_left hfin2 (by positivity)
    _ = Real.exp (P.eigenvalue.re * Real.exp δ) * (C0 + |CF|) * p.ν⁻¹ ^ (kF + 1) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
