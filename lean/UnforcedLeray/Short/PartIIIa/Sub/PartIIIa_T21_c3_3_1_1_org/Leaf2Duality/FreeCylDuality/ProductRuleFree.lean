import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Test
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.Weak
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.KCont

/-!
# Cut-pairing product rule for a free cylinder flow (`IsFreeCylFlow`)

Source `the November 2 reference manuscript` (SP) lines 2937-2958, 3074-3075.

Applies the cut-pairing product-rule machinery of `Sub/T21_2_3/LinAdjDuality/ProductRule/` to
`w(τ, x) = (om(τ, x) : ℂ)` for `om` a weak free cylinder flow (`IsFreeCylFlow`) and `u = 0`
(no Biot-Savart / `∇E` interaction term, valid for every `ν > 0` and `c > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux

/-- Complexification of a real cylinder flow. -/
def freeW (om : ℝ → B0579.Plane → ℝ) (τ : ℝ) (x : ℝ × ℝ) : ℂ := ((om τ x : ℝ) : ℂ)

/-- Zero velocity placeholder (turning `ladFlowCx` into the free cylinder integrand). -/
def zeroU : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun _ _ _ => 0

lemma freeW_memX {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om) :
    ∀ τ : ℝ, s₁ ≤ τ → MemLp (freeW om τ) 2 (B0579.cellMeasure c m) :=
  fun τ hτ => (hω.memX τ hτ).ofReal

lemma freeW_strongCont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om) :
    ∀ τ : ℝ, s₁ ≤ τ →
      Tendsto (fun τ' => xNorm c m (freeW om τ' - freeW om τ)) (𝓝[Ici s₁] τ) (𝓝 0) := by
  intro τ hτ
  have heq : ∀ τ' : ℝ, xNorm c m (freeW om τ' - freeW om τ) =
      eLpNorm (om τ' - om τ) 2 (B0579.cellMeasure c m) := by
    intro τ'
    unfold xNorm
    rw [← eLpNorm_norm, ← eLpNorm_norm (f := om τ' - om τ)]
    congr 1
    funext x
    simp only [Pi.sub_apply, freeW, ← Complex.ofReal_sub, Complex.norm_real]
  exact (hω.strongCont τ hτ).congr fun τ' => (heq τ').symm

lemma flowIntegrand_freeW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om : ℝ → B0579.Plane → ℝ) (σ : ℝ) (a : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    flowIntegrand tr (freeW om σ) (zeroU σ) σ a x =
      ((UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om σ) σ a x : ℝ) : ℂ) := by
  unfold flowIntegrand freeW zeroU UnforcedLeray.Short.IIb.cylFreeIntegrand lapP
    UnforcedLeray.Short.IIb.lapP
  push_cast
  ring

private lemma intervalIntegrable_ofReal_comp {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun r => ((g r : ℝ) : ℂ)) volume a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  exact (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp hg

/-- Frozen-test weak identity between two times `s₁ ≤ a ≤ b` for `freeW om`. -/
lemma free_weak_interval {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    {Ψ : ℝ × ℝ → ℂ} (hre : B0579.IsCylTest c (fun x => (Ψ x).re))
    (him : B0579.IsCylTest c (fun x => (Ψ x).im)) {a b : ℝ} (hs₁a : s₁ ≤ a) (hab : a ≤ b) :
    (∫ x in B0579.cell c, freeW om b x * Ψ x) - (∫ x in B0579.cell c, freeW om a x * Ψ x) =
      ∫ σ in a..b, ∫ x in B0579.cell c, ladFlowCx tr (freeW om σ) (zeroU σ) σ Ψ x := by
  set ar : ℝ × ℝ → ℝ := fun x => (Ψ x).re
  set bi : ℝ × ℝ → ℝ := fun x => (Ψ x).im
  have hΨ : ∀ x : ℝ × ℝ, Ψ x = (ar x : ℂ) + (bi x : ℂ) * Complex.I :=
    fun x => (Complex.re_add_im (Ψ x)).symm
  have hΨf : Ψ = fun y => (ar y : ℂ) + (bi y : ℂ) * Complex.I := funext hΨ
  have hRealWeak : ∀ (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ → ∀ τ : ℝ, s₁ ≤ τ →
      ∫ x in B0579.cell c, freeW om τ x * (ψ x : ℂ) =
        ((∫ x in B0579.cell c, f x * ψ x : ℝ) : ℂ) +
          ∫ r in s₁..τ,
            ((∫ x in B0579.cell c,
              UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om r) r ψ x : ℝ) : ℂ) := by
    intro ψ hψ τ hτ
    have eL : (fun x => freeW om τ x * (ψ x : ℂ)) = fun x => ((om τ x * ψ x : ℝ) : ℂ) := by
      funext x; simp [freeW]
    rw [eL, integral_complex_ofReal, hω.weak ψ hψ τ hτ, Complex.ofReal_add,
      ← intervalIntegral.integral_ofReal]
  have hPairSplit : ∀ τ : ℝ, s₁ ≤ τ →
      ∫ x in B0579.cell c, freeW om τ x * Ψ x =
        (∫ x in B0579.cell c, freeW om τ x * (ar x : ℂ)) +
          (∫ x in B0579.cell c, freeW om τ x * (bi x : ℂ)) * Complex.I := by
    intro τ hτ
    have hwa := LadPRWeakAux.integ_w (freeW_memX hω τ hτ) hre
    have hwb := LadPRWeakAux.integ_w (freeW_memX hω τ hτ) him
    rw [← integral_mul_const, ← integral_add hwa (hwb.mul_const Complex.I)]
    congr 1; funext x; rw [hΨ x]; ring
  set Fa : ℝ → ℂ := fun r =>
    ((∫ x in B0579.cell c, UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om r) r ar x : ℝ) : ℂ)
  set Fb : ℝ → ℂ := fun r =>
    ((∫ x in B0579.cell c, UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om r) r bi x : ℝ) : ℂ)
  have hS : ∀ τ : ℝ, s₁ ≤ τ →
      ∫ x in B0579.cell c, freeW om τ x * Ψ x =
        (((∫ x in B0579.cell c, f x * ar x : ℝ) : ℂ) +
          ((∫ x in B0579.cell c, f x * bi x : ℝ) : ℂ) * Complex.I) +
          ∫ r in s₁..τ, (Fa r + Fb r * Complex.I) := by
    intro τ hτ
    have hIa : IntervalIntegrable Fa volume s₁ τ :=
      intervalIntegrable_ofReal_comp (hω.timeIntegrable ar hre τ hτ)
    have hIb : IntervalIntegrable Fb volume s₁ τ :=
      intervalIntegrable_ofReal_comp (hω.timeIntegrable bi him τ hτ)
    rw [hPairSplit τ hτ, hRealWeak ar hre τ hτ, hRealWeak bi him τ hτ,
      intervalIntegral.integral_add hIa (hIb.mul_const Complex.I),
      intervalIntegral.integral_mul_const]
    ring
  have hFlowEq : ∀ σ : ℝ, s₁ ≤ σ →
      ∫ x in B0579.cell c, ladFlowCx tr (freeW om σ) (zeroU σ) σ Ψ x =
        Fa σ + Fb σ * Complex.I := by
    intro σ hσ
    have hpt : ∀ x : ℝ × ℝ, ladFlowCx tr (freeW om σ) (zeroU σ) σ Ψ x =
        ((UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om σ) σ ar x : ℝ) : ℂ) +
          ((UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om σ) σ bi x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [show ladFlowCx tr (freeW om σ) (zeroU σ) σ Ψ x =
          ladFlowCx tr (freeW om σ) (zeroU σ) σ (fun y => (ar y : ℂ) + (bi y : ℂ) * Complex.I) x from
            congrArg (fun F : ℝ × ℝ → ℂ => ladFlowCx tr (freeW om σ) (zeroU σ) σ F x) hΨf]
      rw [LadPRWeakAux.ladFlow_split tr (freeW om σ) (zeroU σ) σ hre him x,
        flowIntegrand_freeW, flowIntegrand_freeW]
    have ia : IntegrableOn
        (fun x => ((UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om σ) σ ar x : ℝ) : ℂ))
        (B0579.cell c) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp (hω.integrable ar hre σ hσ)
    have ib : IntegrableOn
        (fun x => ((UnforcedLeray.Short.IIb.cylFreeIntegrand tr (om σ) σ bi x : ℝ) : ℂ))
        (B0579.cell c) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp (hω.integrable bi him σ hσ)
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_add ia (ib.mul_const Complex.I), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  have hint : ∫ σ in a..b, (∫ x in B0579.cell c, ladFlowCx tr (freeW om σ) (zeroU σ) σ Ψ x) =
      ∫ σ in a..b, (Fa σ + Fb σ * Complex.I) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le hab] at hσ
    exact hFlowEq σ (hs₁a.trans hσ.1)
  have hGb : IntervalIntegrable (fun r => Fa r + Fb r * Complex.I) volume s₁ b :=
    (intervalIntegrable_ofReal_comp (hω.timeIntegrable ar hre b (hs₁a.trans hab))).add
      ((intervalIntegrable_ofReal_comp (hω.timeIntegrable bi him b (hs₁a.trans hab))).mul_const
        Complex.I)
  have hGa : IntervalIntegrable (fun r => Fa r + Fb r * Complex.I) volume s₁ a :=
    (intervalIntegrable_ofReal_comp (hω.timeIntegrable ar hre a hs₁a)).add
      ((intervalIntegrable_ofReal_comp (hω.timeIntegrable bi him a hs₁a)).mul_const Complex.I)
  rw [hint, hS b (hs₁a.trans hab), hS a hs₁a]
  have hsub := intervalIntegral.integral_interval_sub_left hGb hGa
  linear_combination hsub

/-- Joint continuity of `ladG tr (freeW om) zeroU φ R` on `[s₁, r]²`. -/
lemma free_ladG_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ s : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hc : 0 < c) (hs₁0 : 0 ≤ s₁)
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico s₁ s ×ˢ univ))
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ico s₁ s) :
    ContinuousOn (ladG tr (freeW om) zeroU φ R) (Icc s₁ r ×ˢ Icc s₁ r) := by
  rcases eq_or_lt_of_le hr.1 with htr | htr
  · subst htr
    rw [Icc_self, Set.singleton_prod_singleton]
    exact continuousOn_singleton _ _
  have hSc : IsCompact (Icc s₁ r ×ˢ Icc s₁ r : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hzero : ∀ ρ : ℝ, ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCutPhi φ R ρ x = 0 := fun ρ x hx => by
    unfold ladCutPhi
    rw [LadPRPairAux.cut_zero hR hx]
    simp
  obtain ⟨hTf, _⟩ := GContAux.blocks_cont tr hR hφs hr.2 hs₁0 htr
  obtain ⟨hTc', hTs', M, _, hTb⟩ :=
    GContAux.clamp_facts (T := GContAux.ladTf tr φ R) hc.le hSc hTf
      (fun p _ x hx => GContAux.ladTf_zero_of tr R p.1 (ladCutPhi φ R p.2)
        (fun y hy => hzero p.2 y hy) x hx)
  have hFw_mem : ∀ p ∈ (Icc s₁ r ×ˢ Icc s₁ r : Set (ℝ × ℝ)),
      MemLp (fun x => freeW om p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) 2
        (volume.restrict (B0579.cell c)) :=
    fun p hp => GContAux.memLp_strip (L := 2 * R) (freeW_memX hω p.1 hp.1.1)
  have hFwc : ∀ p0 ∈ (Icc s₁ r ×ˢ Icc s₁ r : Set (ℝ × ℝ)),
      Tendsto (fun p : ℝ × ℝ =>
        eLpNorm ((fun x => freeW om p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) -
          (fun x => freeW om p0.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0))) 2
          (volume.restrict (B0579.cell c)))
        (𝓝[Icc s₁ r ×ˢ Icc s₁ r] p0) (𝓝 0) := by
    intro p0 hp0
    obtain ⟨κ, hκ, hκle⟩ := GCont2Aux.exists_jb_lower c (2 * R) m
    have hstrong : Tendsto (fun ρ => xNorm c m (freeW om ρ - freeW om p0.1))
        (𝓝[Ici s₁] p0.1) (𝓝 0) := freeW_strongCont hω p0.1 hp0.1.1
    have hlim : Tendsto (fun ρ => ENNReal.ofReal κ⁻¹ * xNorm c m (freeW om ρ - freeW om p0.1))
        (𝓝[Ici s₁] p0.1) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hstrong
        (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal κ⁻¹ ≠ ⊤))
      simpa using this
    have h1 : Tendsto (fun ρ =>
        eLpNorm (fun x => freeW om ρ x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0) -
          freeW om p0.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) 2
          (volume.restrict (B0579.cell c))) (𝓝[Ici s₁] p0.1) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ρ => ?_)
      have e : (fun x => freeW om ρ x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0) -
          freeW om p0.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) =
          fun x => (freeW om ρ - freeW om p0.1) x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0) := by
        funext x; simp only [Pi.sub_apply, sub_mul]
      rw [e]
      exact GCont2Aux.strip_le hκ hκle (freeW om ρ - freeW om p0.1)
    have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[Icc s₁ r ×ˢ Icc s₁ r] p0) (𝓝[Ici s₁] p0.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun p hp => hp.1.1⟩
    exact h1.comp hf
  have hIW := cell_integral_mul_continuousOn c (2 * R) M (Icc s₁ r ×ˢ Icc s₁ r)
    (fun p x => freeW om p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0))
    (fun p x => GContAux.ladTf tr φ R p (GContAux.clampQ c x)) hFw_mem hFwc hTc' hTs' hTb
  refine hIW.congr fun p _ => ?_
  unfold ladG
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
  rw [GContAux.clampQ_of_mem_cell hx, GContAux.ladFlowCx_eq]
  simp only [zeroU, zero_mul, add_zero, sub_zero]
  by_cases h2 : |x.2| ≤ 2 * R
  · simp only [h2, ↓reduceIte, mul_one]; rfl
  · have hx2 : 2 * R < |x.2| := lt_of_not_ge h2
    have hT0 : (ν : ℂ) * ladLapCx (ladCutPhi φ R p.2) x +
        ladTransport tr p.1 (ladCutPhi φ R p.2) x = 0 :=
      GContAux.ladTf_zero_of tr R p.1 (ladCutPhi φ R p.2)
        (fun y hy => hzero p.2 y hy) x hx2
    simp only [h2, ↓reduceIte]
    unfold GContAux.ladTf
    rw [hT0]
    simp

/-- Continuity of `ladK` on `(s₁, r]` and right limit at `s₁` for `freeW om`. -/
lemma free_ladK_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ s : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hs₁s : s₁ < s) (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico s₁ s ×ˢ univ))
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ico s₁ s) :
    ContinuousOn (ladK c (freeW om) φ R) (Ioc s₁ r) ∧
      ∃ L : ℂ, Tendsto (ladK c (freeW om) φ R) (𝓝[>] s₁) (𝓝 L) := by
  have hJ := LadPRKAux.ladDW_continuousOn hφs
  have hfp : ∀ {p : ℝ}, p < s → ∀ {ρ : ℝ}, ρ ∈ Icc s₁ p →
      ContinuousWithinAt
        (fun r' => ∫ x in B0579.cell c, freeW om r' x *
          ladCutPhi (LadPRKAux.ladDW s₁ s φ) R r' x) (Icc s₁ p) ρ := by
    intro p hp ρ hρ
    have hwm : ∀ r' ∈ Icc s₁ p, MemLp (freeW om r') 2 (B0579.cellMeasure c m) :=
      fun r' h => freeW_memX hω r' h.1
    have hψm : ∀ r' ∈ Icc s₁ p,
        MemLp (ladCutPhi (LadPRKAux.ladDW s₁ s φ) R r') 2 (B0579.cellMeasure c (-m)) :=
      fun r' h => LadPRKAux.memLp_cutDW hR hJ ⟨h.1, lt_of_le_of_lt h.2 hp⟩ (-m)
    have ha : Tendsto (fun r' => (eLpNorm (freeW om r' - freeW om ρ) 2
        (B0579.cellMeasure c m)).toReal) (𝓝[Icc s₁ p] ρ) (𝓝 0) := by
      have h1 : Tendsto (fun r' => xNorm c m (freeW om r' - freeW om ρ))
          (𝓝[Icc s₁ p] ρ) (𝓝 0) :=
        (freeW_strongCont hω ρ hρ.1).mono_left (nhdsWithin_mono _ fun x hx => hx.1)
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, xNorm] using this
    have hb := LadPRKAux.tendsto_cutDW (c := c) (m := -m) hR hp hJ hρ
    exact LadPRPairAux.pairCW (S := Icc s₁ p) hρ (freeW om)
      (fun r' => ladCutPhi (LadPRKAux.ladDW s₁ s φ) R r') hwm hψm ha hb
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    have hρI : ρ ∈ Ioo s₁ s := ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
    have hΦ := hfp hr.2 ⟨hρ.1.le, hρ.2⟩
    refine ContinuousWithinAt.congr (hΦ.mono Ioc_subset_Icc_self) (fun y hy => ?_) ?_
    · exact LadPRKAux.ladK_eq_pair hφs ⟨hy.1, lt_of_le_of_lt hy.2 hr.2⟩
    · exact LadPRKAux.ladK_eq_pair hφs hρI
  · have htq : s₁ < (s₁ + s) / 2 := by linarith
    have hqs : (s₁ + s) / 2 < s := by linarith
    have hΦ := hfp hqs ⟨le_rfl, htq.le⟩
    have hnhd : Icc s₁ ((s₁ + s) / 2) ∈ 𝓝[>] s₁ :=
      mem_of_superset (Ioo_mem_nhdsGT htq) fun y hy => ⟨hy.1.le, hy.2.le⟩
    have hT := hΦ.mono_left (nhdsWithin_le_of_mem hnhd)
    refine ⟨∫ x in B0579.cell c,
      freeW om s₁ x * ladCutPhi (LadPRKAux.ladDW s₁ s φ) R s₁ x, ?_⟩
    refine Tendsto.congr' ?_ hT
    filter_upwards [Ioo_mem_nhdsGT htq] with y hy
    exact (LadPRKAux.ladK_eq_pair hφs ⟨hy.1, lt_of_lt_of_le hy.2 hqs.le⟩).symm

/-- Continuity of `ladCutPair c R (freeW om) φ` on `[s₁, r]`. -/
lemma free_ladCutPair_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ s : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico s₁ s ×ˢ univ))
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ico s₁ s) :
    ContinuousOn (ladCutPair c R (freeW om) φ) (Icc s₁ r) := by
  intro ρ hρ
  have hwm : ∀ r' ∈ Icc s₁ r, MemLp (freeW om r') 2 (B0579.cellMeasure c m) :=
    fun r' h => freeW_memX hω r' h.1
  have hψm : ∀ r' ∈ Icc s₁ r, MemLp (ladCutPhi φ R r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => LadPRPairAux.memLp_cutPhi hR hφs ⟨h.1, lt_of_le_of_lt h.2 hr.2⟩ (-m)
  have ha : Tendsto (fun r' => (eLpNorm (freeW om r' - freeW om ρ) 2
      (B0579.cellMeasure c m)).toReal) (𝓝[Icc s₁ r] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (freeW om r' - freeW om ρ))
        (𝓝[Icc s₁ r] ρ) (𝓝 0) :=
      (freeW_strongCont hω ρ hρ.1).mono_left (nhdsWithin_mono _ fun x hx => hx.1)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, xNorm] using this
  have hb := LadPRPairAux.tendsto_cutDiff (c := c) (m := -m) hR hr.2 hφs hρ
  unfold ladCutPair
  exact LadPRPairAux.pairCW (S := Icc s₁ r) hρ (freeW om) (fun r' => ladCutPhi φ R r')
    hwm hψm ha hb

/-- Derivative of `ladCutPair c R (freeW om) φ` on `(s₁, r)`. -/
lemma free_ladCutPair_deriv {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ s : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico s₁ s ×ˢ univ))
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ico s₁ s)
    (hG : ContinuousOn (ladG tr (freeW om) zeroU φ R) (Icc s₁ r ×ˢ Icc s₁ r))
    (hweak : ∀ ρ ∈ Icc s₁ r, ∀ a b : ℝ, s₁ ≤ a → a ≤ b →
      (∫ x in B0579.cell c, freeW om b x * ladCutPhi φ R ρ x) -
          (∫ x in B0579.cell c, freeW om a x * ladCutPhi φ R ρ x) =
        ∫ σ in a..b, ladG tr (freeW om) zeroU φ R (σ, ρ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo s₁ r) :
    HasDerivAt (ladCutPair c R (freeW om) φ) (ladRate tr (freeW om) zeroU φ R ρ) ρ := by
  have hρI : ρ ∈ Icc s₁ r := ⟨hρ.1.le, hρ.2.le⟩
  have hρs : ρ ∈ Ioo s₁ s := ⟨hρ.1, lt_trans hρ.2 hr.2⟩
  have hwm : ∀ r' ∈ Icc s₁ r, MemLp (freeW om r') 2 (B0579.cellMeasure c m) :=
    fun r' h => freeW_memX hω r' h.1
  have hΨ : ∀ r' ∈ Icc s₁ r, MemLp (ladCutPhi φ R r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => LadPRPairAux.memLp_cutPhi hR hφs ⟨h.1, lt_of_le_of_lt h.2 hr.2⟩ (-m)
  have hwρ := hwm ρ hρI
  have hDmem : MemLp (fun x => (ladCut R x : ℂ) * ladDt φ ρ x) 2
      (B0579.cellMeasure c (-m)) := by
    refine LadPRDerivAux.memLp_of_cont_box (c := c) (n := -m) (R := R) ?_ ?_
    · exact (Complex.continuous_ofReal.comp (LadPRPairAux.cut_continuous R)).mul
        (LadPRDerivAux.ladDt_slice_cont hφs hρs)
    · intro x hx hxK
      simp only [LadPRPairAux.cut_zero hR (LadPRPairAux.not_mem_box_gt hx hxK),
        Complex.ofReal_zero, zero_mul]
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ρ + h ∈ Icc s₁ r := by
    have hopen : ∀ᶠ h in 𝓝 (0 : ℝ), ρ + h ∈ Ioo s₁ r := by
      have hc0 : Continuous (fun h : ℝ => ρ + h) := continuous_const.add continuous_id
      have hc : Tendsto (fun h : ℝ => ρ + h) (𝓝 0) (𝓝 ρ) := by simpa using hc0.tendsto 0
      exact hc.eventually (isOpen_Ioo.mem_nhds hρ)
    filter_upwards [nhdsWithin_le_nhds hopen] with h hh
    exact ⟨hh.1.le, hh.2.le⟩
  have hG1 := LadPRDerivAux.G_limit hG hρ
  have hG2 : Tendsto (fun h : ℝ => ∫ x in B0579.cell c, freeW om ρ x *
      (((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x)) (𝓝[≠] 0) (𝓝 0) := by
    have hdq := LadPRDerivAux.tendsto_dq_L2 (c := c) (n := -m) hR hφs hρs
    have ha := hdq.const_mul (eLpNorm (freeW om ρ) 2 (B0579.cellMeasure c m)).toReal
    rw [mul_zero] at ha
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [hev] with h hh
    have hQ : MemLp (fun x => ((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x) 2 (B0579.cellMeasure c (-m)) :=
      (((hΨ (ρ + h) hh).sub (hΨ ρ hρI)).const_mul _).sub hDmem
    exact (PairContAux.holder hwρ hQ).2
  have hI : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      h⁻¹ • (ladCutPair c R (freeW om) φ (ρ + h) - ladCutPair c R (freeW om) φ ρ) =
        ((h⁻¹ : ℝ) : ℂ) * (∫ σ in ρ..ρ + h, ladG tr (freeW om) zeroU φ R (σ, ρ + h)) +
          (∫ x in B0579.cell c, freeW om ρ x * (((h⁻¹ : ℝ) : ℂ) *
            (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)) +
          ∫ x in B0579.cell c, freeW om ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) := by
    filter_upwards [hev] with h hh
    have hsplit := LadPRDerivAux.incr_split (c := c) (m := m) (t := s₁) (r := r)
      (freeW om) (ladCutPhi φ R) (ladG tr (freeW om) zeroU φ R) hweak hρI hh hwρ hΨ
    have hQ : MemLp (fun x => ((h⁻¹ : ℝ) : ℂ) * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) -
        (ladCut R x : ℂ) * ladDt φ ρ x) 2 (B0579.cellMeasure c (-m)) :=
      (((hΨ (ρ + h) hh).sub (hΨ ρ hρI)).const_mul _).sub hDmem
    have iQ := (PairContAux.holder hwρ hQ).1
    have iD := (PairContAux.holder hwρ hDmem).1
    have hJ : ((h⁻¹ : ℝ) : ℂ) * (∫ x in B0579.cell c,
        freeW om ρ x * (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x)) =
        (∫ x in B0579.cell c, freeW om ρ x * (((h⁻¹ : ℝ) : ℂ) *
          (ladCutPhi φ R (ρ + h) x - ladCutPhi φ R ρ x) - (ladCut R x : ℂ) * ladDt φ ρ x)) +
        ∫ x in B0579.cell c, freeW om ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) := by
      rw [← integral_add iQ iD, ← integral_const_mul]
      congr 1; funext x; ring
    unfold ladCutPair
    rw [hsplit, Complex.real_smul, mul_add, hJ]
    ring
  have hlim := (hG1.add hG2).add
    (tendsto_const_nhds (x := ∫ x in B0579.cell c, freeW om ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)))
  rw [add_zero] at hlim
  rw [hasDerivAt_iff_tendsto_slope_zero, ladRate_eq]
  unfold ladK
  exact Tendsto.congr' (hI.mono fun h hh => hh.symm) hlim

/-- **Cut-pairing product rule for a free cylinder flow** on `[s₁, r]` (`r ∈ [s₁, s)`). -/
theorem free_productRule {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {s₁ s : ℝ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hc : 0 < c) (hs₁0 : 0 ≤ s₁) (hs₁s : s₁ < s)
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico s₁ s ×ˢ univ))
    (hper : ∀ r' ∈ Ico s₁ s, ∀ x : ℝ × ℝ, φ r' (x.1 + c, x.2) = φ r' x)
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ico s₁ s) :
    IntervalIntegrable (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) volume s₁ r ∧
      ladCutPair c R (freeW om) φ r - ladCutPair c R (freeW om) φ s₁ =
        ∫ ρ in s₁..r, ladRate tr (freeW om) zeroU φ R ρ := by
  rcases eq_or_lt_of_le hr.1 with hrt | hrt
  · subst hrt
    exact ⟨IntervalIntegrable.refl, by simp⟩
  have hG := free_ladG_cont hc hs₁0 hω hφs hR hr
  obtain ⟨hKc, L, hL⟩ := free_ladK_cont hs₁s hω hφs hR hr
  have hP := free_ladCutPair_cont hω hφs hR hr
  have hdiag : ContinuousOn (fun ρ => ladG tr (freeW om) zeroU φ R (ρ, ρ)) (Icc s₁ r) :=
    hG.comp (continuousOn_id.prodMk continuousOn_id) fun ρ hρ => ⟨hρ, hρ⟩
  have hdt : Tendsto (fun ρ => ladG tr (freeW om) zeroU φ R (ρ, ρ)) (𝓝[>] s₁)
      (𝓝 (ladG tr (freeW om) zeroU φ R (s₁, s₁))) :=
    (hdiag s₁ ⟨le_rfl, hrt.le⟩).tendsto.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hrt))
  have hRt : Tendsto (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) (𝓝[>] s₁)
      (𝓝 (ladG tr (freeW om) zeroU φ R (s₁, s₁) + L)) :=
    (hdt.add hL).congr fun ρ => (ladRate_eq tr (freeW om) zeroU φ R ρ).symm
  obtain ⟨Rate', hR'⟩ : ∃ g' : ℝ → ℂ, g' =
      Function.update (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) s₁
        (ladG tr (freeW om) zeroU φ R (s₁, s₁) + L) := ⟨_, rfl⟩
  have hEq : ∀ ρ ∈ Ioc s₁ r, Rate' ρ = ladRate tr (freeW om) zeroU φ R ρ := fun ρ hρ => by
    rw [hR']; exact Function.update_of_ne (ne_of_gt hρ.1) _ _
  have hEt : Rate' s₁ = ladG tr (freeW om) zeroU φ R (s₁, s₁) + L := by
    rw [hR']; exact Function.update_self _ _ _
  have hRateIoc : ContinuousOn (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) (Ioc s₁ r) := by
    have := (hdiag.mono Ioc_subset_Icc_self).add hKc
    exact this.congr fun ρ _ => ladRate_eq tr (freeW om) zeroU φ R ρ
  have hRate : ContinuousOn Rate' (Icc s₁ r) := by
    intro ρ hρ
    rcases eq_or_lt_of_le hρ.1 with h | h
    · rw [← h]
      refine ContinuousWithinAt.mono ?_ fun x hx => mem_Ici.2 hx.1
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto Rate' (𝓝[>] s₁) (𝓝 (Rate' s₁))
      rw [hEt]
      refine hRt.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hrt] with x hx
      exact (hEq x ⟨hx.1, hx.2.le⟩).symm
    · rw [← continuousWithinAt_inter (Ioi_mem_nhds h)]
      have e : Icc s₁ r ∩ Ioi s₁ = Ioc s₁ r := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
        exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h3, h2⟩ => ⟨⟨h3.le, h2⟩, h3⟩⟩
      rw [e]
      exact (hRateIoc.congr fun x hx => hEq x hx) ρ ⟨h, hρ.2⟩
  have hRateI : IntervalIntegrable Rate' volume s₁ r := hRate.intervalIntegrable_of_Icc hrt.le
  have hRateI' : IntervalIntegrable (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) volume s₁ r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrt.le] at hRateI ⊢
    exact hRateI.congr_fun hEq measurableSet_Ioc
  have hInt : ∫ ρ in s₁..r, Rate' ρ = ∫ ρ in s₁..r, ladRate tr (freeW om) zeroU φ R ρ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun ρ hρ => ?_)
    rw [uIoc_of_le hrt.le] at hρ
    exact hEq ρ hρ
  have hweak : ∀ ρ ∈ Icc s₁ r, ∀ a b : ℝ, s₁ ≤ a → a ≤ b →
      (∫ x in B0579.cell c, freeW om b x * ladCutPhi φ R ρ x) -
          (∫ x in B0579.cell c, freeW om a x * ladCutPhi φ R ρ x) =
        ∫ σ in a..b, ladG tr (freeW om) zeroU φ R (σ, ρ) := by
    intro ρ hρ a b hta hab
    have hρs : ρ ∈ Ico s₁ s := ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
    obtain ⟨hre, him⟩ := ladPRTest c s₁ s φ hc hφs hper R hR ρ hρs
    exact free_weak_interval hω hre him hta hab
  refine ⟨hRateI', ?_⟩
  rw [← hInt]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrt.le hP
    (fun ρ hρ => by
      rw [hEq ρ ⟨hρ.1, hρ.2.le⟩]
      exact free_ladCutPair_deriv hω hφs hR hr hG hweak hρ) hRateI

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux
