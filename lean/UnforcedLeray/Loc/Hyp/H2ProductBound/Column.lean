import UnforcedLeray.Loc.L10Nonlinear
import UnforcedLeray.Loc.L01Coefficient
import UnforcedLeray.Loc.Hyp.H2ProductBound.L4

/-!
# Hypothesis H-H2Prod, helper: the `H²(ℝ³)` product bound from `H² ⊂ L^∞`

This module proves the conditional form `h2ProductBound_of : H2EmbedsC0 → H2ProductBound`
without importing the proof of `H2EmbedsC0`; `Loc/Hyp/H2ProductBound.lean` combines it with
`Loc/Hyp/H2EmbedsC0.lean` into `h2ProductBound : H2ProductBound`.

`paper/main.tex` line 504 ("The `H²` product bound and multiplication by `W^{2,∞}` fields, followed
by `loc:eq:inverse-bound`, give affine, linear and bilinear bounds"); blueprint units B1021
(`loc:eq:local-fixed-point`, the bilinear term `𝒩(z) = -𝔓 div(z ⊗ z)`) and B0721
(`unlabeled:463`, the operator `𝓝`), infrastructure INF11. The hypothesis is
`UnforcedLeray.Blueprint.L10.H2ProductBound` (`Loc/L10Nonlinear.lean`): there is `C` with
`‖g_j f‖_{H²} ≤ C ‖f‖_{H²} ‖g‖_{H²}` for the columns `g_j f` of `f ⊗ g` (line 107).

## Proof

For `f, g ∈ H²(ℝ³;ℝ³)` and `B = P_j`, `P_j(u, v) = u_j v` (`L01.prodJ`), the weak product rule
`L01.leibniz` (`Loc/L01Coefficient/Leibniz.lean`) gives

* `∂ₖ(g_j f) = (∂ₖg)_j f + g_j ∂ₖf`,
* `∂ₗ∂ₖ(g_j f) = (∂ₗ∂ₖg)_j f + (∂ₖg)_j ∂ₗf + (∂ₗg)_j ∂ₖf + g_j ∂ₗ∂ₖf`,

the second by applying the rule to `(∂ₖg)_j f` (coefficient `∂ₖg`, `H¹` factor `f`) and to
`g_j ∂ₖf` (coefficient `g`, `H¹` factor `∂ₖf`). In `L²`:

* terms with an undifferentiated factor: `‖g‖_∞‖·‖₂` or `‖·‖₂‖f‖_∞`, with `H² ⊂ L^∞`;
* the terms `(∂ₖg)_j ∂ₗf`: `‖∂ₖg‖₄‖∂ₗf‖₄` and `H¹ ⊂ L⁴` (`H2ProductBound/L4.lean`).

Summing the thirteen components gives `‖g_j f‖_{H²} ≤ 13 (A + l4Const²) ‖f‖_{H²} ‖g‖_{H²}`,
where `A` is the constant of `H² ⊂ L^∞`.

The only input not proved here is `H² ⊂ L^∞`, taken from the named hypothesis
`UnforcedLeray.Blueprint.H2EmbedsC0` (`Loc/L01Coefficient.lean`, INF11), proved in
`Loc/Hyp/H2EmbedsC0.lean`; only its sup-norm bound is used (`ae_norm_le_of_embeds`). Hence this
module's theorem is `h2ProductBound_of : H2EmbedsC0 → H2ProductBound`; the form for an
arbitrary `L^∞` constant is `exists_column_H2`.

Main declarations: `H2Prod.exists_column_H2`, `h2ProductBound_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Blueprint.L10

open SobolevGraph

namespace H2Prod

/-- The sup bound of `H2EmbedsC0`, as an a.e. bound on the `L²` representative with a
nonnegative constant. -/
theorem ae_norm_le_of_embeds (hE : H2EmbedsC0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ F : H2,
      ∀ᵐ x ∂(volume : Measure Space), ‖(F.value : SpatialField) x‖ ≤ A * ‖F‖ := by
  obtain ⟨C, hC⟩ := hE
  refine ⟨|C|, abs_nonneg C, fun F => ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC F
  filter_upwards [hv] with x hx
  rw [← hx]
  calc ‖(v : SpatialField) x‖ ≤ ‖v‖ := by
        simpa using (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := v)) ▸
          BoundedContinuousFunction.norm_coe_le_norm v.toBCF x
    _ ≤ C * ‖F‖ := hvC
    _ ≤ |C| * ‖F‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg F)

theorem norm_prodJ_le (j : Fin 3) (u v : Space) : ‖L01.prodJ j u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [L01.prodJ_apply, norm_smul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le u j) (norm_nonneg v)

/-- `l2Norm f ≤ c l2Norm g` from a pointwise a.e. bound. -/
theorem l2Norm_le_of_ae_le_mul {f g : SpatialField} {c : ℝ} (hc : 0 ≤ c)
    (hg : MemLp g 2 volume) (h : ∀ᵐ x ∂(volume : Measure Space), ‖f x‖ ≤ c * ‖g x‖) :
    l2Norm f ≤ c * l2Norm g := by
  have h2 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul h 2
  have hfin : ENNReal.ofReal c * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  unfold l2Norm
  calc (eLpNorm f 2 volume).toReal
      ≤ (ENNReal.ofReal c * eLpNorm g 2 volume).toReal := ENNReal.toReal_mono hfin h2
    _ = c * (eLpNorm g 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- `P_j(a, v)` with `a` bounded and `v ∈ L²`. -/
theorem prodJ_bdd_left (j : Fin 3) {a v : SpatialField} {M : ℝ} (hM : 0 ≤ M)
    (ha : AEStronglyMeasurable a volume) (hb : ∀ᵐ x ∂(volume : Measure Space), ‖a x‖ ≤ M)
    (hv : MemLp v 2 volume) :
    MemLp (fun x => L01.prodJ j (a x) (v x)) 2 volume ∧
      l2Norm (fun x => L01.prodJ j (a x) (v x)) ≤ M * l2Norm v := by
  have hle : ∀ᵐ x ∂(volume : Measure Space), ‖L01.prodJ j (a x) (v x)‖ ≤ M * ‖v x‖ := by
    filter_upwards [hb] with x hx
    exact (norm_prodJ_le j _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hmeas : AEStronglyMeasurable (fun x => L01.prodJ j (a x) (v x)) volume :=
    (L01.prodJ j).aestronglyMeasurable_comp₂ ha hv.1
  exact ⟨hv.of_le_mul hmeas hle, l2Norm_le_of_ae_le_mul hM hv hle⟩

/-- `P_j(a, v)` with `a ∈ L²` and `v` bounded. -/
theorem prodJ_bdd_right (j : Fin 3) {a v : SpatialField} {M : ℝ} (hM : 0 ≤ M)
    (ha : MemLp a 2 volume) (hv : AEStronglyMeasurable v volume)
    (hb : ∀ᵐ x ∂(volume : Measure Space), ‖v x‖ ≤ M) :
    MemLp (fun x => L01.prodJ j (a x) (v x)) 2 volume ∧
      l2Norm (fun x => L01.prodJ j (a x) (v x)) ≤ M * l2Norm a := by
  have hle : ∀ᵐ x ∂(volume : Measure Space), ‖L01.prodJ j (a x) (v x)‖ ≤ M * ‖a x‖ := by
    filter_upwards [hb] with x hx
    calc ‖L01.prodJ j (a x) (v x)‖ ≤ ‖a x‖ * ‖v x‖ := norm_prodJ_le j _ _
      _ ≤ ‖a x‖ * M := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = M * ‖a x‖ := mul_comm _ _
  have hmeas : AEStronglyMeasurable (fun x => L01.prodJ j (a x) (v x)) volume :=
    (L01.prodJ j).aestronglyMeasurable_comp₂ ha.1 hv
  exact ⟨ha.of_le_mul hmeas hle, l2Norm_le_of_ae_le_mul hM ha hle⟩

/-- `P_j(∂ₖg, ∂ₗf)` for `f, g ∈ H²`: Hölder `L⁴ × L⁴` and `H¹ ⊂ L⁴`. -/
theorem prodJ_partials (j : Fin 3) (f g : H2) (k l : Fin 3) :
    MemLp (fun x => L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x))
        2 volume ∧
      l2Norm (fun x =>
          L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x)) ≤
        l4Const ^ 2 * (‖f‖ * ‖g‖) := by
  refine ⟨h1_coord_smul_memLp (h2PartialH1 g k) (h2PartialH1 f l) j, ?_⟩
  have h := h1_coord_smul_l2Norm_le (h2PartialH1 g k) (h2PartialH1 f l) j
  have h1 := norm_h2PartialH1_le g k
  have h2 := norm_h2PartialH1_le f l
  have hL : 0 ≤ l4Const ^ 2 := sq_nonneg _
  calc l2Norm (fun x =>
        L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x))
      ≤ l4Const ^ 2 * ‖h2PartialH1 g k‖ * ‖h2PartialH1 f l‖ := h
    _ ≤ l4Const ^ 2 * ‖g‖ * ‖f‖ := by gcongr
    _ = l4Const ^ 2 * (‖f‖ * ‖g‖) := by ring

/-- **The column `g_j f` of `f ⊗ g` is in `H²`** (`paper/main.tex` line 504, blueprint B1021,
B0721), for `f, g ∈ H²(ℝ³;ℝ³)` with `|f|, |g| ≤ A‖·‖_{H²}` a.e.:
`‖g_j f‖_{H²} ≤ 13 (A + l4Const²) ‖f‖_{H²} ‖g‖_{H²}`. -/
theorem exists_column_H2 {A : ℝ} (hA0 : 0 ≤ A) (f g : H2) (j : Fin 3)
    (hf : ∀ᵐ x ∂(volume : Measure Space), ‖(f.value : SpatialField) x‖ ≤ A * ‖f‖)
    (hg : ∀ᵐ x ∂(volume : Measure Space), ‖(g.value : SpatialField) x‖ ≤ A * ‖g‖) :
    ∃ P : H2,
      (P.value : SpatialField) =ᵐ[volume]
        tensorColumns (f.value : SpatialField) (g.value : SpatialField) j ∧
      ‖P‖ ≤ 13 * (A + l4Const ^ 2) * ‖f‖ * ‖g‖ := by
  set D := A + l4Const ^ 2 with hD
  have hD0 : 0 ≤ D := add_nonneg hA0 (sq_nonneg _)
  set b := ‖f‖ * ‖g‖ with hb
  have hb0 : 0 ≤ b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hAf : 0 ≤ A * ‖f‖ := mul_nonneg hA0 (norm_nonneg _)
  have hAg : 0 ≤ A * ‖g‖ := mul_nonneg hA0 (norm_nonneg _)
  have hAb : A * b ≤ D * b := mul_le_mul_of_nonneg_right (by rw [hD]; linarith [sq_nonneg l4Const]) hb0
  have hLb : l4Const ^ 2 * b ≤ D * b :=
    mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hb0
  -- the three kinds of terms
  have Tg : ∀ v : L2Space, ‖v‖ ≤ ‖f‖ →
      MemLp (fun x => L01.prodJ j ((g.value : SpatialField) x) ((v : SpatialField) x)) 2 volume ∧
      l2Norm (fun x => L01.prodJ j ((g.value : SpatialField) x) ((v : SpatialField) x)) ≤
        D * b := by
    intro v hv
    obtain ⟨h1, h2⟩ := prodJ_bdd_left j hAg (Lp.aestronglyMeasurable g.value) hg (Lp.memLp v)
    refine ⟨h1, h2.trans ?_⟩
    rw [l2Norm_Lp]
    calc A * ‖g‖ * ‖v‖ ≤ A * ‖g‖ * ‖f‖ := mul_le_mul_of_nonneg_left hv hAg
      _ = A * b := by rw [hb]; ring
      _ ≤ D * b := hAb
  have Tf : ∀ u : L2Space, ‖u‖ ≤ ‖g‖ →
      MemLp (fun x => L01.prodJ j ((u : SpatialField) x) ((f.value : SpatialField) x)) 2 volume ∧
      l2Norm (fun x => L01.prodJ j ((u : SpatialField) x) ((f.value : SpatialField) x)) ≤
        D * b := by
    intro u hu
    obtain ⟨h1, h2⟩ := prodJ_bdd_right j hAf (Lp.memLp u) (Lp.aestronglyMeasurable f.value) hf
    refine ⟨h1, h2.trans ?_⟩
    rw [l2Norm_Lp]
    calc A * ‖f‖ * ‖u‖ ≤ A * ‖f‖ * ‖g‖ := mul_le_mul_of_nonneg_left hu hAf
      _ = A * b := by rw [hb]; ring
      _ ≤ D * b := hAb
  have T4 : ∀ k l : Fin 3,
      MemLp (fun x => L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x))
        2 volume ∧
      l2Norm (fun x =>
          L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x)) ≤ D * b := by
    intro k l
    obtain ⟨h1, h2⟩ := prodJ_partials j f g k l
    exact ⟨h1, h2.trans hLb⟩
  -- the fields
  let c : SpatialField := fun x =>
    L01.prodJ j ((g.value : SpatialField) x) ((f.value : SpatialField) x)
  let c1 : Fin 3 → SpatialField := fun k x =>
    L01.prodJ j ((g.first k : SpatialField) x) ((f.value : SpatialField) x) +
      L01.prodJ j ((g.value : SpatialField) x) ((f.first k : SpatialField) x)
  let c2 : Fin 3 → Fin 3 → SpatialField := fun k l x =>
    (L01.prodJ j ((g.second k l : SpatialField) x) ((f.value : SpatialField) x) +
      L01.prodJ j ((g.first k : SpatialField) x) ((f.first l : SpatialField) x)) +
    (L01.prodJ j ((g.first l : SpatialField) x) ((f.first k : SpatialField) x) +
      L01.prodJ j ((g.value : SpatialField) x) ((f.second k l : SpatialField) x))
  have hc : MemLp c 2 volume ∧ l2Norm c ≤ D * b := Tg f.value (H2.norm_value_le' f)
  have hc1 : ∀ k, MemLp (c1 k) 2 volume ∧ l2Norm (c1 k) ≤ 2 * (D * b) := by
    intro k
    have e1 := Tf (g.first k) (H2.norm_first_le g k)
    have e2 := Tg (f.first k) (H2.norm_first_le f k)
    exact ⟨e1.1.add e2.1, (l2Norm_add_le_of e1.1 e2.1 e1.2 e2.2).trans (by linarith)⟩
  have hc2 : ∀ k l, MemLp (c2 k l) 2 volume ∧ l2Norm (c2 k l) ≤ 4 * (D * b) := by
    intro k l
    have e1 := Tf (g.second k l) (H2.norm_second_le g k l)
    have e2 := T4 k l
    have e3 := T4 l k
    have e4 := Tg (f.second k l) (H2.norm_second_le f k l)
    have s1 := l2Norm_add_le_of e1.1 e2.1 e1.2 e2.2
    have s2 := l2Norm_add_le_of e3.1 e4.1 e3.2 e4.2
    exact ⟨(e1.1.add e2.1).add (e3.1.add e4.1),
      (l2Norm_add_le_of (e1.1.add e2.1) (e3.1.add e4.1) s1 s2).trans (by linarith)⟩
  -- the weak derivatives (`L01.leibniz` with `B = P_j`)
  have hd1 : ∀ k, HasWeakSpatialDerivative k c (c1 k) := fun k =>
    L01.leibniz (L01.prodJ j) k (g.hasWeakFirst k) (L01.locL2_L2 g.value)
      (L01.locL2_L2 (g.first k)) (h2AsH1 f)
  have hd2 : ∀ k l, HasWeakSpatialDerivative l (c1 k) (c2 k l) := fun k l =>
    (L01.leibniz (L01.prodJ j) l (g.hasWeakSecond k l) (L01.locL2_L2 (g.first k))
      (L01.locL2_L2 (g.second k l)) (h2AsH1 f)).add
    (L01.leibniz (L01.prodJ j) l (g.hasWeakFirst l) (L01.locL2_L2 g.value)
      (L01.locL2_L2 (g.first l)) (h2PartialH1 f k))
  refine ⟨H2.ofFields c c1 c2 hc.1 (fun k => (hc1 k).1) (fun k l => (hc2 k l).1) hd1 hd2,
    coeFn_toL2 hc.1, ?_⟩
  have hP := H2.norm_sq_ofFields c c1 c2 hc.1 (fun k => (hc1 k).1) (fun k l => (hc2 k l).1)
    hd1 hd2
  have s0 : l2Norm c ^ 2 ≤ (D * b) ^ 2 := pow_le_pow_left₀ (l2Norm_nonneg' _) hc.2 2
  have s1 : ∑ k : Fin 3, l2Norm (c1 k) ^ 2 ≤ ∑ _k : Fin 3, (2 * (D * b)) ^ 2 :=
    Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (l2Norm_nonneg' _) (hc1 k).2 2
  have s2 : ∑ k : Fin 3, ∑ l : Fin 3, l2Norm (c2 k l) ^ 2 ≤
      ∑ _k : Fin 3, ∑ _l : Fin 3, (4 * (D * b)) ^ 2 :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
      pow_le_pow_left₀ (l2Norm_nonneg' _) (hc2 k l).2 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at s1 s2
  have hDb : 0 ≤ D * b := mul_nonneg hD0 hb0
  have hsq : ‖H2.ofFields c c1 c2 hc.1 (fun k => (hc1 k).1) (fun k l => (hc2 k l).1) hd1 hd2‖ ^ 2
      ≤ (13 * (D * b)) ^ 2 := by
    rw [hP]
    nlinarith [sq_nonneg (D * b)]
  have hfin := (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp hsq
  calc _ ≤ 13 * (D * b) := hfin
    _ = 13 * D * ‖f‖ * ‖g‖ := by rw [hb]; ring

end H2Prod

/-- **Hypothesis H-H2Prod from `H² ⊂ L^∞`** (`paper/main.tex` line 504, "the `H²` product bound";
blueprint B1021, B0721, INF11). Given the Sobolev embedding `H2EmbedsC0` (B0711, proved
elsewhere), the columns of `f ⊗ g` satisfy `‖g_j f‖_{H²} ≤ C ‖f‖_{H²} ‖g‖_{H²}` with
`C = 13 (A + l4Const²)`, `A` the embedding constant. -/
theorem h2ProductBound_of (hE : H2EmbedsC0) : H2ProductBound := by
  obtain ⟨A, hA0, hA⟩ := H2Prod.ae_norm_le_of_embeds hE
  exact ⟨13 * (A + H2Prod.l4Const ^ 2), fun f g j =>
    H2Prod.exists_column_H2 hA0 f g j (hA f) (hA g)⟩

end UnforcedLeray.Blueprint.L10
