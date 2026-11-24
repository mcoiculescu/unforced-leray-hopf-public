import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# Decomposition of `partialStripBlock_of` (item `PartIII-b:C/near/delta/9`, source 3996-4009)

Source of record `the November 2 reference manuscript`.
The partial strip `g⁻¹1_{bin}(S_N - S₀)1_{t≥e^δ l}g` is assembled from

* `ZeroEntranceCausal` (3541-3545; new here): the flat free response `S₀` has no output `s < T` from
  inputs `t ≥ T` (causality of the zero-entrance solution), so `1_{bin}S₀1_{t≥e^δ l} = 0`;
* `Masked.MaskedSupport` (3905-3916): `1_{s<T}S_N1_{t≥e^δ T} = 0`, so the inputs are `t < e^δ r`;
* `Masked.MaskedStripBound` (3996-4005, kernel realization `sep:resolvent` 3611-3621, positive
  kernel majorant `sep:kernel`, Young, normalized-phase Minkowski): the ungained strip has norm
  `≤ P_ν ε√r`;
* `GainStripRatio` (4002-4007, `GainRatioSup` with `M = e^{3δ/2}`, `GainRatioTanh`): the gain costs
  at most `e^{η_δ/ν}` on a block with outputs `s ≥ l` and inputs `t < e^{3δ/2}l`;
* `√r ≤ ε^{-b/2}` (4006-4007).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **Causality of the flat free response** (source 3541-3545: "a homogeneous difference in the
energy class ... also proves causality"; 3420-3440 with `v = 0`, 3561-3571).  For a planar
reference, `K ⋐ (0, 1/4)` and `m_Z ≥ 0`: at every level of the regime with `ν ≤ ν₀`,
`0 < ρ_b ≤ 1`, `μ ∈ K` and `S₀` with the free pin `IsFreeStress` (the causal zero-entrance energy
solution), outputs of age `s < T` see no input of age `t ≥ T`:
`1_{s<T} S₀ 1_{t≥T} = 0`.  (Route: `S₀F` for `F` supported in `t ≥ T` is the zero-entrance solution
of a source vanishing on `s < T`; by uniqueness, `FreeCausalExistsUnique`, it vanishes there.) -/
def ZeroEntranceCausal : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsFreeStress S0 p.ν μ → ∀ T : ℝ, 0 < T →
          outRestr p.c (ageBelow T) ∘L S0 ∘L inRestr p.c mZ ρb (ageAbove T) = 0

/-- **The gain ratio on a partial strip** (source 4002-4007 with `GainRatioSup` for `M = e^{3δ/2}`
and `GainRatioTanh`, `η_δ = γ tanh(3δ/8)`): for `γ ≥ 0`, output region inside `{s ≥ l}` and input
region inside `{t < e^{3δ/2} l}`, `‖g⁻¹ 1_A X 1_B g‖ ≤ e^{η_δ/ν}‖1_A X 1_B‖`.  (Route: `g⁻¹ ≤ 1/g(l)`
on `A`, `g ≤ g(e^{3δ/2}l)` on `B`, `GainBlockBound`, and
`g(Ml)/g(l) = exp(γ(Ml/(1+νMl) - l/(1+νl))) ≤ exp((γ/ν)(√M-1)/(√M+1)) = exp(η_δ/ν)`.) -/
def GainStripRatio : Prop :=
  ∀ (c mZ ρb γ ν δ l : ℝ) (hν : 0 < ν), 0 ≤ γ → 0 < δ → 0 < l →
    ∀ A B : Set Chart, A ⊆ ageAbove l → B ⊆ ageBelow (Real.exp (3 * δ / 2) * l) →
      ∀ X : Zsp c mZ ρb →L[ℝ] Hsp c,
        ‖gainBlockS γ hν A B X‖ ≤
          Real.exp (etaDelta γ δ / ν) * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖

/-! ## Restriction algebra -/

theorem restrLp_nested {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A A' : Set Chart} (hA : MeasurableSet A) (hA' : MeasurableSet A') (h : A ⊆ A')
    (f : Lp E 2 μ) : restrLp μ E A (restrLp μ E A' f) = restrLp μ E A f := by
  apply Lp.ext
  filter_upwards [restrLp_ae hA (restrLp μ E A' f), restrLp_ae hA' f, restrLp_ae hA f] with
    x h1 h2 h3
  rw [h1, h3]
  change ind A x • (restrLp μ E A' f : Chart → E) x = ind A x • (f : Chart → E) x
  rw [h2]
  change ind A x • (ind A' x • (f : Chart → E) x) = ind A x • (f : Chart → E) x
  rw [smul_smul]
  by_cases hx : x ∈ A
  · have : x ∈ A' := h hx
    simp [ind, Set.indicator_of_mem hx, Set.indicator_of_mem this]
  · simp [ind, Set.indicator_of_notMem hx]

theorem restrLp_add_of {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C : Set Chart} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (h : ∀ x, ind A x + ind B x = ind C x) (f : Lp E 2 μ) :
    restrLp μ E A f + restrLp μ E B f = restrLp μ E C f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (restrLp μ E A f) (restrLp μ E B f), restrLp_ae hA f,
    restrLp_ae hB f, restrLp_ae hC f] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, h4]
  change ind A x • (f : Chart → E) x + ind B x • (f : Chart → E) x = ind C x • (f : Chart → E) x
  rw [← add_smul, h]

theorem norm_restrLp_le' {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set Chart} (hA : MeasurableSet A) (f : Lp E 2 μ) : ‖restrLp μ E A f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [restrLp_ae hA f] with x hx
  rw [hx]
  change ‖ind A x • (f : Chart → E) x‖ ≤ ‖(f : Chart → E) x‖
  rw [norm_smul]
  have := abs_ind_le A x
  rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) this

theorem inRestr_add_of (c mZ ρb : ℝ) {A B C : Set Chart} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (h : ∀ x, ind A x + ind B x = ind C x)
    (F : Zsp c mZ ρb) :
    inRestr c mZ ρb A F + inRestr c mZ ρb B F = inRestr c mZ ρb C F := by
  apply (zEquiv c mZ ρb).injective
  rw [map_add, zEquiv_inRestr, zEquiv_inRestr, zEquiv_inRestr, Prod.mk_add_mk,
    restrLp_add_of hA hB hC h, restrLp_add_of hA hB hC h]

theorem ind_split_strip {Tl Tr : ℝ} (h : Tl ≤ Tr) (x : Chart) :
    ind (ageAbove Tl ∩ ageBelow Tr) x + ind (ageAbove Tr) x = ind (ageAbove Tl) x := by
  unfold ind ageAbove ageBelow
  by_cases h1 : Tl ≤ x.1 <;> by_cases h2 : x.1 < Tr
  · have h3 : ¬ Tr ≤ x.1 := not_le.2 h2
    simp [Set.indicator, h1, h2, h3]
  · have h3 : Tr ≤ x.1 := not_lt.1 h2
    simp [Set.indicator, h1, h2, h3]
  · have h3 : ¬ Tr ≤ x.1 := fun h4 => h1 (h.trans h4)
    simp [Set.indicator, h1, h2, h3]
  · have h3 : ¬ Tr ≤ x.1 := fun h4 => h1 (h.trans h4)
    simp [Set.indicator, h1, h2, h3]

/-- The partial strip, from the four lemmas. -/
theorem partialStripBlock_of_props (hS : MaskedStripBound) (hM : MaskedSupport)
    (hZ : ZeroEntranceCausal) (hG : GainStripRatio) : PartialStripBlock := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C, k, ν₁, hν₁, hmain⟩ := hS Kset hK hKs mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨ν₂, hν₂, hcaus⟩ := hZ P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨|C|, k, min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ SN S0 hSN hS0 l r L hal hlr hr hrS
  obtain ⟨Seps, Sf, hpair, rfl⟩ := (isMaskedNear_iff p μ δ (p.ε ^ (-b)) SN).1 hSN
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hlpos : 0 < l := lt_of_lt_of_le (Real.rpow_pos_of_pos p.ε_pos a) hal
  have hrpos : 0 < r := hlpos.trans hlr
  have hμpos : 0 < μ := (hKs hμ).1
  have hγ : 0 ≤ P.eigenvalue.re := hP.eigenpair.re_pos.le
  have hexp1 : Real.exp (δ / 2) < Real.exp δ := Real.exp_lt_exp.2 (by linarith)
  have hrT : r < Real.exp δ * l := by
    calc r ≤ Real.exp (δ / 2) * l := hr
      _ < Real.exp δ * l := mul_lt_mul_of_pos_right hexp1 hlpos
  have hlr' : Real.exp δ * l ≤ Real.exp δ * r :=
    mul_le_mul_of_nonneg_left hlr.le (Real.exp_pos δ).le
  -- the sets
  have hAm := measurableSet_binSet l r L
  have hBm := measurableSet_ageAbove (Real.exp δ * l)
  have hB2m := measurableSet_ageAbove (Real.exp δ * r)
  have hB1m : MeasurableSet (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) :=
    hBm.inter (measurableSet_ageBelow _)
  have hAT : binSet l r L ⊆ ageBelow (Real.exp δ * l) := fun x hx => lt_trans hx.2.1 hrT
  have hAr : binSet l r L ⊆ ageBelow r := fun x hx => hx.2.1
  have hAband : binSet l r L ⊆ ageBand l r := fun x hx => ⟨hx.1, hx.2.1⟩
  -- the flat part vanishes
  have hE1 : ∀ F : Zsp p.c mZ ρb, outRestr p.c (binSet l r L)
      (S0 (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)) = 0 := by
    intro F
    have h0 := hcaus p d hreg hν2 ρb hρ hρ1 μ hμ S0 hS0 (Real.exp δ * l)
      (mul_pos (Real.exp_pos δ) hlpos)
    have h0F := congrArg (fun T => T F) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h0F
    have hn := restrLp_nested (μ := ageμ p.c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) hAm
      (measurableSet_ageBelow (Real.exp δ * l)) hAT
      (S0 (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))
    change restrLp _ _ (binSet l r L)
      (restrLp _ _ (ageBelow (Real.exp δ * l)) _) = _ at hn
    change restrLp _ _ (binSet l r L) _ = 0
    rw [← hn]
    change restrLp _ _ (binSet l r L) (outRestr p.c (ageBelow (Real.exp δ * l)) _) = 0
    rw [h0F]
    exact map_zero _
  -- the far input vanishes
  have hE2 : ∀ F : Zsp p.c mZ ρb, outRestr p.c (binSet l r L)
      ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) F)) = 0 := by
    intro F
    have h0 := hM p mZ ρb μ δ (p.ε ^ (-b)) r hmZ hρ hρ1 hμpos hδ hrpos hrS Seps Sf hpair
    have h0F := congrArg (fun T => T F) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h0F
    have hn := restrLp_nested (μ := ageμ p.c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) hAm
      (measurableSet_ageBelow r) hAr
      ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) F))
    change restrLp _ _ (binSet l r L)
      (restrLp _ _ (ageBelow r) _) = _ at hn
    change restrLp _ _ (binSet l r L) _ = 0
    rw [← hn]
    change restrLp _ _ (binSet l r L) (outRestr p.c (ageBelow r) _) = 0
    rw [h0F]
    exact map_zero _
  -- the strip input agrees with the full input
  have hs : ∀ F : Zsp p.c mZ ρb,
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) F +
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * r)) F =
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F :=
    fun F => inRestr_add_of p.c mZ ρb hB1m hB2m hBm (ind_split_strip hlr') F
  have e0 : ∀ F : Zsp p.c mZ ρb, outRestr p.c (binSet l r L)
      ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) F)) =
      outRestr p.c (binSet l r L) ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)) := by
    intro F
    rw [← hs F, map_add, map_add, hE2 F, add_zero]
  have e1 : ∀ F : Zsp p.c mZ ρb, outRestr p.c (binSet l r L)
      ((Seps - Sf - S0) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)) =
      outRestr p.c (binSet l r L) ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)) := by
    intro F
    rw [ContinuousLinearMap.sub_apply (Seps - Sf) S0, map_sub, hE1 F, sub_zero]
  have hgb : gainBlockS P.eigenvalue.re p.ν_pos (binSet l r L) (ageAbove (Real.exp δ * l))
        (Seps - Sf - S0) =
      gainBlockS P.eigenvalue.re p.ν_pos (binSet l r L)
        (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) (Seps - Sf) := by
    have : outRestr p.c (binSet l r L) ∘L (Seps - Sf - S0) ∘L
          inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) =
        outRestr p.c (binSet l r L) ∘L (Seps - Sf) ∘L
          inRestr p.c mZ ρb (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) := by
      ext1 F
      exact (e1 F).trans (e0 F).symm
    unfold gainBlockS
    rw [this]
  -- the gain
  have hB1T : ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r) ⊆
      ageBelow (Real.exp (3 * δ / 2) * l) := by
    intro x hx
    have h1 : x.1 < Real.exp δ * r := hx.2
    have h2 : Real.exp δ * r ≤ Real.exp (3 * δ / 2) * l := by
      calc Real.exp δ * r ≤ Real.exp δ * (Real.exp (δ / 2) * l) :=
            mul_le_mul_of_nonneg_left hr (Real.exp_pos δ).le
        _ = Real.exp (3 * δ / 2) * l := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    exact lt_of_lt_of_le h1 h2
  have hratio := hG p.c mZ ρb P.eigenvalue.re p.ν δ l p.ν_pos hγ hδ hlpos (binSet l r L)
    (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) (fun x hx => hx.1) hB1T (Seps - Sf)
  -- the strip bound
  have hband := hmain p d hreg hν1 ρb hρ hρ1 μ hμ Seps Sf hpair l r hlpos hlr hr hrS
  have hblock : ‖outRestr p.c (binSet l r L) ∘L (Seps - Sf) ∘L
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r))‖ ≤
      C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) := by
    refine le_trans ?_ hband
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro F
    simp only [ContinuousLinearMap.comp_apply]
    have hn := restrLp_nested (μ := ageμ p.c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2)) hAm
      (measurableSet_ageBand l r) hAband
      ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))
    calc ‖outRestr p.c (binSet l r L)
          ((Seps - Sf) (inRestr p.c mZ ρb
            (ageAbove (Real.exp δ * l) ∩ ageBelow (Real.exp δ * r)) F))‖
        = ‖restrLp (ageμ p.c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (binSet l r L)
            (restrLp (ageμ p.c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (ageBand l r)
              ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)))‖ := by
          rw [hn]; exact congrArg _ (e0 F)
      _ ≤ ‖restrLp (ageμ p.c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (ageBand l r)
              ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))‖ :=
          norm_restrLp_le' hAm _
      _ ≤ ‖outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
            inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))‖ * ‖F‖ :=
          ContinuousLinearMap.le_opNorm (outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
            inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))) F
  -- arithmetic
  have hsq : Real.sqrt r ≤ p.ε ^ (-b / 2) := by
    calc Real.sqrt r ≤ Real.sqrt (p.ε ^ (-b)) := Real.sqrt_le_sqrt hrS
      _ = p.ε ^ (-b / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul p.ε_pos.le]; congr 1; ring
  have hε1 : p.ε ^ (1 - b / 2) = p.ε * p.ε ^ (-b / 2) := by
    have : (1 - b / 2) = 1 + (-b / 2) := by ring
    rw [this, Real.rpow_add p.ε_pos, Real.rpow_one]
  have hεr : p.ε * Real.sqrt r ≤ p.ε ^ (1 - b / 2) := by
    rw [hε1]; exact mul_le_mul_of_nonneg_left hsq p.ε_pos.le
  have hνk : 0 ≤ p.ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 p.ν_pos.le) k
  have hexp : 0 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := (Real.exp_pos _).le
  have hCle : C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) ≤ |C| * p.ν⁻¹ ^ k * p.ε ^ (1 - b / 2) := by
    have hεs : 0 ≤ p.ε * Real.sqrt r := mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _)
    calc C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) ≤ |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hνk) hεs
      _ ≤ |C| * p.ν⁻¹ ^ k * p.ε ^ (1 - b / 2) :=
          mul_le_mul_of_nonneg_left hεr (mul_nonneg (abs_nonneg C) hνk)
  rw [hgb]
  calc _ ≤ _ := hratio
    _ ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) :=
        mul_le_mul_of_nonneg_left hblock hexp
    _ ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) * (|C| * p.ν⁻¹ ^ k * p.ε ^ (1 - b / 2)) :=
        mul_le_mul_of_nonneg_left hCle hexp
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
