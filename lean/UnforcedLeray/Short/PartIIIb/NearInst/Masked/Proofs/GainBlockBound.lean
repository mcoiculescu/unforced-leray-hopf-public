import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `PartIII-b:C/near/masked/26`: `GainBlockBound` (source 3978-3981)

`gainBlockS γ hν A B X = gainConjS γ hν (outRestr c A ∘L X ∘L inRestr c mZ ρb B)`.  The gain
`g⁻¹` on the output region `A` and `g` on the input region `B` cost at most `a` and `b`
(`gainInvFun ≤ a` on `A`, `gainFun ≤ b` on `B`), so `‖g⁻¹ 1_A X 1_B g‖ ≤ a b ‖X‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- An `L²` element `g` with `g = φ • f` a.e. and `|φ| ≤ a` has `‖g‖ ≤ a‖f‖`. -/
theorem norm_le_of_ae_smul_bound {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : Lp E 2 μ) (φ : α → ℝ) (a : ℝ) (ha : 0 ≤ a) (hbd : ∀ x, |φ x| ≤ a)
    (hg : (g : α → E) =ᵐ[μ] φ • (f : α → E)) : ‖g‖ ≤ a * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hg]
  have h1 : eLpNorm (φ • (f : α → E)) 2 μ ≤ eLpNorm (a • (f : α → E)) 2 μ := by
    apply eLpNorm_mono_ae
    filter_upwards with x
    show ‖φ x • (f : α → E) x‖ ≤ ‖a • (f : α → E) x‖
    rw [norm_smul, norm_smul, Real.norm_eq_abs (φ x), Real.norm_eq_abs a, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)
  have h2 : eLpNorm (a • (f : α → E)) 2 μ = ENNReal.ofReal a * eLpNorm (f : α → E) 2 μ := by
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg ha]
  have hfin : eLpNorm (f : α → E) 2 μ ≠ ⊤ := (Lp.memLp f).2.ne
  calc (eLpNorm (φ • (f : α → E)) 2 μ).toReal
      ≤ (ENNReal.ofReal a * eLpNorm (f : α → E) 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (h1.trans h2.le)
    _ = a * (eLpNorm (f : α → E) 2 μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]

/-- Restriction after the gain: `‖1_B g f‖ ≤ b‖f‖` when `g ≤ b` on `B`. -/
theorem norm_restrLp_gainLp_le {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : Set Chart} (hB : MeasurableSet B) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (b : ℝ) (hb : 0 ≤ b) (hgB : ∀ x ∈ B, gainFun γ ν x ≤ b) (f : Lp E 2 μ) :
    ‖restrLp μ E B (gainLp μ γ hν f)‖ ≤ b * ‖f‖ := by
  apply norm_le_of_ae_smul_bound f _ (fun x => ind B x * gainFun γ ν x) b hb
  · intro x
    unfold ind
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx, one_mul]
      rw [abs_of_pos (gainFun_pos γ ν x)]
      exact hgB x hx
    · simp [Set.indicator_of_notMem hx, hb]
  · have h1 : ((gainLp μ γ hν f : Lp E 2 μ) : Chart → E) =ᵐ[μ] gainFun γ ν • (f : Chart → E) :=
      mulBdd_apply_ae (gainFun γ ν) (gainFun_measurable γ ν) (Real.exp (|γ| / ν))
        (gainFun_le hν) f
    filter_upwards [restrLp_ae hB (gainLp μ γ hν f), h1] with x hx1 hx2
    rw [hx1]
    show ind B x • ((gainLp μ γ hν f : Lp E 2 μ) : Chart → E) x =
      (ind B x * gainFun γ ν x) • (f : Chart → E) x
    rw [hx2]
    show ind B x • (gainFun γ ν x • (f : Chart → E) x) = (ind B x * gainFun γ ν x) • (f : Chart → E) x
    rw [smul_smul]

/-- The output restriction after the inverse gain: `‖g⁻¹ 1_A u‖ ≤ a‖u‖` when `g⁻¹ ≤ a` on `A`. -/
theorem norm_gainH_symm_outRestr_le {c : ℝ} (γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A : Set Chart}
    (hA : MeasurableSet A) (a : ℝ) (ha : 0 ≤ a) (hgA : ∀ x ∈ A, gainInvFun γ ν x ≤ a)
    (u : Hsp c) :
    ‖(gainH c γ hν).symm (outRestr c A u)‖ ≤ a * ‖u‖ := by
  apply norm_le_of_ae_smul_bound u _ (fun x => gainInvFun γ ν x * ind A x) a ha
  · intro x
    unfold ind
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, mul_one]
      have hpos : 0 < gainInvFun γ ν x := inv_pos.2 (gainFun_pos γ ν x)
      rw [abs_of_pos hpos]
      exact hgA x hx
    · simp [Set.indicator_of_notMem hx, ha]
  · have h1 : (((gainH c γ hν).symm (outRestr c A u) : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2))
        =ᵐ[ageμ c (-3 / 2)] gainInvFun γ ν • ((outRestr c A u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) :=
      mulBdd_apply_ae (gainInvFun γ ν) (gainFun_measurable γ ν).inv (Real.exp (|γ| / ν))
        (gainInvFun_le hν) _
    have h2 : ((outRestr c A u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2))
        =ᵐ[ageμ c (-3 / 2)] ind A • ((u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) :=
      restrLp_ae hA u
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1]
    show gainInvFun γ ν x • ((outRestr c A u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x =
      (gainInvFun γ ν x * ind A x) • ((u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x
    rw [hx2]
    show gainInvFun γ ν x • (ind A x • ((u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x) =
      (gainInvFun γ ν x * ind A x) • ((u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x
    rw [smul_smul, mul_comm]

/-- The `Z`-norm of the restricted gained input (`zEquiv` of the gain). -/
theorem zsp_norm_eq {c mZ ρb : ℝ} (F : Zsp c mZ ρb) :
    ‖F‖ = ‖(zEquiv c mZ ρb F).1‖ + ‖(zEquiv c mZ ρb F).2‖ := by
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp [zEquiv]

theorem zEquiv_gainEquiv {c mZ ρb γ : ℝ} {ν : ℝ} (hν : 0 < ν) (F : Zsp c mZ ρb) :
    zEquiv c mZ ρb (gainEquiv c mZ ρb γ hν F) =
      (gainLp (z1Measure c mZ) γ hν (zEquiv c mZ ρb F).1,
        gainLp (htRhoMeasure c ρb) γ hν (zEquiv c mZ ρb F).2) := rfl

/-- The input restriction after the gain on `Z`. -/
theorem norm_inRestr_gainEquiv_le {c mZ ρb γ : ℝ} {ν : ℝ} (hν : 0 < ν) {B : Set Chart}
    (hB : MeasurableSet B) (b : ℝ) (hb : 0 ≤ b) (hgB : ∀ x ∈ B, gainFun γ ν x ≤ b)
    (F : Zsp c mZ ρb) :
    ‖inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)‖ ≤ b * ‖F‖ := by
  rw [zsp_norm_eq (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)), zEquiv_inRestr,
    zEquiv_gainEquiv hν, zsp_norm_eq F]
  have e1 := norm_restrLp_gainLp_le (μ := z1Measure c mZ) (E := Ten3) hB γ hν b hb hgB
    (zEquiv c mZ ρb F).1
  have e2 := norm_restrLp_gainLp_le (μ := htRhoMeasure c ρb) (E := Ten3) hB γ hν b hb hgB
    (zEquiv c mZ ρb F).2
  calc _ ≤ b * ‖(zEquiv c mZ ρb F).1‖ + b * ‖(zEquiv c mZ ρb F).2‖ := add_le_add e1 e2
    _ = b * (‖(zEquiv c mZ ρb F).1‖ + ‖(zEquiv c mZ ρb F).2‖) := by ring

/-- **The cost of the gain on a block** (source 3978-3981). -/
theorem gainBlockBound : GainBlockBound := by
  intro c mZ ρb γ ν hν A B a b X hA hB ha hb hgA hgB
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg ha hb) (norm_nonneg _))
  intro F
  have hZ := norm_inRestr_gainEquiv_le (c := c) (mZ := mZ) (ρb := ρb) (γ := γ) hν hB b hb hgB F
  have hX : ‖X (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F))‖ ≤ ‖X‖ * (b * ‖F‖) :=
    (X.le_opNorm _).trans (mul_le_mul_of_nonneg_left hZ (norm_nonneg _))
  have hout := norm_gainH_symm_outRestr_le (c := c) γ hν hA a ha hgA
    (X (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)))
  change ‖(gainH c γ hν).symm (outRestr c A (X (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F))))‖
    ≤ a * b * ‖X‖ * ‖F‖
  calc _ ≤ a * ‖X (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F))‖ := hout
    _ ≤ a * (‖X‖ * (b * ‖F‖)) := mul_le_mul_of_nonneg_left hX ha
    _ = a * b * ‖X‖ * ‖F‖ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
