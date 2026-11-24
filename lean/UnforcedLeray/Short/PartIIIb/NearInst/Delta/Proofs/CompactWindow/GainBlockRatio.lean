import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioSup
import UnforcedLeray.Short.PartIIIb.Proofs.GainRatioTanh
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# Proof of `GainBlockRatio` (source `the November 2 reference manuscript`,
lines 3978-3990, 4002-4007).

For `γ ≥ 0`, output region `A ⊆ {s ≥ l}`, input region `B ⊆ {t < e^δ l}`:
`g⁻¹ 1_A X 1_B g = G⁻¹ Y G` with `Y = 1_A X 1_B`.  Bound `‖G⁻¹ Y G‖ ≤ a b ‖Y‖` where
`a = (g(l))⁻¹ ≥ sup_A g⁻¹` and `b = g(e^δ l) ≥ sup_B g`, and
`a b = exp(γ (f(e^δ l) - f(l)))` with `f(s) = s/(1+νs)`; the gain-ratio supremum
(`GainRatioSup` with `M = e^{3δ/2}`, `GainRatioTanh`) gives `ν(f(e^δ l)-f(l)) ≤ tanh(3δ/8)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

theorem gbr_lp_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Measure Chart} {a : ℝ} (ha : 0 ≤ a) {φ ψ : Lp E 2 m}
    (h : ∀ᵐ p ∂m, ‖(φ : Chart → E) p‖ ≤ a * ‖(ψ : Chart → E) p‖) : ‖φ‖ ≤ a * ‖ψ‖ := by
  have h2 : ‖φ‖ ≤ ‖a • ψ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, Lp.coeFn_smul a ψ] with p hp hs
    rw [hs, Pi.smul_apply, norm_smul, Real.norm_of_nonneg ha]
    exact hp
  rwa [norm_smul, Real.norm_of_nonneg ha] at h2

theorem gbr_restrLp_zero_of_not {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : Set Chart} (hA : ¬MeasurableSet A) : restrLp μ E A = 0 := by
  unfold restrLp
  simp [hA]

theorem gbr_outRestr_zero_of_not (c : ℝ) {A : Set Chart} (hA : ¬MeasurableSet A) :
    outRestr c A = 0 := by
  unfold outRestr
  exact gbr_restrLp_zero_of_not hA

theorem gbr_inRestr_fst (c mZ ρb : ℝ) (A : Set Chart) (W : Zsp c mZ ρb) :
    (inRestr c mZ ρb A W).fst = restrLp (z1Measure c mZ) Ten3 A W.fst :=
  congrArg Prod.fst (zEquiv_inRestr c mZ ρb A W)

theorem gbr_inRestr_snd (c mZ ρb : ℝ) (A : Set Chart) (W : Zsp c mZ ρb) :
    (inRestr c mZ ρb A W).snd = restrLp (htRhoMeasure c ρb) Ten3 A W.snd :=
  congrArg Prod.snd (zEquiv_inRestr c mZ ρb A W)

theorem gbr_inRestr_idem (c mZ ρb : ℝ) {A : Set Chart} (hA : MeasurableSet A)
    (W : Zsp c mZ ρb) :
    inRestr c mZ ρb A (inRestr c mZ ρb A W) = inRestr c mZ ρb A W := by
  apply (zEquiv c mZ ρb).injective
  rw [zEquiv_inRestr, zEquiv_inRestr]
  simp only [restrLp_idem hA]

theorem gbr_inRestr_zero_of_not (c mZ ρb : ℝ) {A : Set Chart} (hA : ¬MeasurableSet A) :
    inRestr c mZ ρb A = 0 := by
  ext W
  rw [zero_apply]
  apply (zEquiv c mZ ρb).injective
  rw [zEquiv_inRestr, gbr_restrLp_zero_of_not (μ := z1Measure c mZ) (E := Ten3) hA,
    gbr_restrLp_zero_of_not (μ := htRhoMeasure c ρb) (E := Ten3) hA]
  simp

theorem gbr_gainG_pos (γ ν s : ℝ) : 0 < UnforcedLeray.Short.IIIa.gainG γ ν s := by
  unfold UnforcedLeray.Short.IIIa.gainG
  exact Real.exp_pos _

theorem gbr_gainG_mono {γ ν s t : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t) :
    UnforcedLeray.Short.IIIa.gainG γ ν s ≤ UnforcedLeray.Short.IIIa.gainG γ ν t := by
  unfold UnforcedLeray.Short.IIIa.gainG
  apply Real.exp_le_exp.2
  have h1 : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have h2 : 0 < 1 + ν * t := by nlinarith [mul_nonneg hν.le (hs.trans hst)]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hst)]

/-- Multiplication by the gain on the output side. -/
theorem gbr_out_norm (c : ℝ) {γ ν a : ℝ} (hν : 0 < ν) {A : Set Chart} (hA : MeasurableSet A)
    (ha : 0 ≤ a) (haA : ∀ p ∈ A, gainInvFun γ ν p ≤ a) (v : Hsp c) :
    ‖(gainH c γ hν).symm (outRestr c A v)‖ ≤ a * ‖outRestr c A v‖ := by
  apply gbr_lp_norm_le ha
  have hO : (outRestr c A v : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      fun p => ind A p • (v : Chart → EuclideanSpace ℝ (Fin 2)) p :=
    restrLp_ae hA v
  filter_upwards [coeFn_gainH_symm γ hν (outRestr c A v), hO] with p h1 h2
  simp only [h1, h2]
  by_cases hp : p ∈ A
  · have hind : ind A p = 1 := by simp [ind, hp]
    have hpos : 0 ≤ gainInvFun γ ν p := by
      unfold gainInvFun
      exact (inv_pos.2 (gainFun_pos γ ν p)).le
    simp only [hind, one_smul]
    rw [norm_smul, Real.norm_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_right (haA p hp) (norm_nonneg _)
  · have hind : ind A p = 0 := by simp [ind, hp]
    simp [hind]

/-- Multiplication by the gain on the input side, restricted to `B`. -/
theorem gbr_restr_gain_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Measure Chart) {γ ν b : ℝ} (hν : 0 < ν) {B : Set Chart} (hB : MeasurableSet B)
    (hb : 0 ≤ b) (hbB : ∀ p ∈ B, gainFun γ ν p ≤ b) (f : Lp E 2 m) :
    ‖restrLp m E B (gainLp m γ hν f)‖ ≤ b * ‖f‖ := by
  apply gbr_lp_norm_le hb
  filter_upwards [restrLp_ae hB (gainLp m γ hν f), coeFn_gainLp m γ hν f] with p h1 h2
  rw [h1]
  change ‖ind B p • ((gainLp m γ hν f : Chart → E) p)‖ ≤ b * ‖(f : Chart → E) p‖
  rw [h2]
  by_cases hp : p ∈ B
  · have hind : ind B p = 1 := by simp [ind, hp]
    have hg : ‖gainFun γ ν p‖ = gainFun γ ν p :=
      Real.norm_of_nonneg (gainFun_pos γ ν p).le
    rw [hind, one_smul, norm_smul, hg]
    exact mul_le_mul_of_nonneg_right (hbB p hp) (norm_nonneg _)
  · have hind : ind B p = 0 := by simp [ind, hp]
    rw [hind, zero_smul, norm_zero]
    exact mul_nonneg hb (norm_nonneg _)

theorem gbr_in_norm {c mZ ρb γ ν b : ℝ} (hν : 0 < ν) {B : Set Chart} (hB : MeasurableSet B)
    (hb : 0 ≤ b) (hbB : ∀ p ∈ B, gainFun γ ν p ≤ b) (F : Zsp c mZ ρb) :
    ‖inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)‖ ≤ b * ‖F‖ := by
  rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1, gbr_inRestr_fst, gbr_inRestr_snd,
    gainEquiv_fst, gainEquiv_snd]
  have e1 := gbr_restr_gain_norm (z1Measure c mZ) hν hB hb hbB F.fst
  have e2 := gbr_restr_gain_norm (htRhoMeasure c ρb) hν hB hb hbB F.snd
  rw [mul_add]
  linarith

/-- The block bound with output bound `a` and input bound `b`. -/
theorem gbr_core (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A B : Set Chart}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haA : ∀ p ∈ A, gainInvFun γ ν p ≤ a) (hbB : ∀ p ∈ B, gainFun γ ν p ≤ b)
    (X : Zsp c mZ ρb →L[ℝ] Hsp c) :
    ‖gainConjS γ hν (outRestr c A ∘L X ∘L inRestr c mZ ρb B)‖ ≤
      a * b * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg ha hb) (norm_nonneg _))
  intro F
  rw [gainConjS_apply]
  have h1 : ‖(gainH c γ hν).symm ((outRestr c A ∘L X ∘L inRestr c mZ ρb B)
      (gainEquiv c mZ ρb γ hν F))‖ ≤
      a * ‖(outRestr c A ∘L X ∘L inRestr c mZ ρb B) (gainEquiv c mZ ρb γ hν F)‖ :=
    gbr_out_norm c hν hAm ha haA _
  have h3 : (outRestr c A ∘L X ∘L inRestr c mZ ρb B) (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F))
      = (outRestr c A ∘L X ∘L inRestr c mZ ρb B) (gainEquiv c mZ ρb γ hν F) := by
    show outRestr c A (X (inRestr c mZ ρb B (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)))) =
      outRestr c A (X (inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)))
    rw [gbr_inRestr_idem c mZ ρb hBm]
  have h5 := gbr_in_norm (c := c) (mZ := mZ) (ρb := ρb) (γ := γ) hν hBm hb hbB F
  calc _ ≤ a * ‖(outRestr c A ∘L X ∘L inRestr c mZ ρb B) (gainEquiv c mZ ρb γ hν F)‖ := h1
    _ ≤ a * (‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ *
          ‖inRestr c mZ ρb B (gainEquiv c mZ ρb γ hν F)‖) := by
        apply mul_le_mul_of_nonneg_left _ ha
        rw [← h3]
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ a * (‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ * (b * ‖F‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (norm_nonneg _)) ha
    _ = a * b * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ * ‖F‖ := by ring

theorem gainBlockRatio : GainBlockRatio := by
  intro c mZ ρb γ ν δ l hν hγ hδ hl A B hA hB X
  show ‖gainConjS γ hν (outRestr c A ∘L X ∘L inRestr c mZ ρb B)‖ ≤
    Real.exp (etaDelta γ δ / ν) * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖
  by_cases hAm : MeasurableSet A
  · by_cases hBm : MeasurableSet B
    · -- the constants
      have haA : ∀ p ∈ A, gainInvFun γ ν p ≤
          (UnforcedLeray.Short.IIIa.gainG γ ν l)⁻¹ := by
        intro p hp
        have hlp : l ≤ p.1 := hA hp
        have hmono : UnforcedLeray.Short.IIIa.gainG γ ν l ≤ gainFun γ ν p :=
          gbr_gainG_mono hγ hν hl.le (le_max_of_le_left hlp)
        unfold gainInvFun
        exact inv_anti₀ (gbr_gainG_pos γ ν l) hmono
      have hbB : ∀ p ∈ B, gainFun γ ν p ≤
          UnforcedLeray.Short.IIIa.gainG γ ν (Real.exp δ * l) := by
        intro p hp
        have hpl : p.1 < Real.exp δ * l := hB hp
        exact gbr_gainG_mono hγ hν (le_max_right _ _)
          (max_le hpl.le (mul_pos (Real.exp_pos δ) hl).le)
      have hcore := gbr_core c mZ ρb γ hν hAm hBm
        (inv_nonneg.2 (gbr_gainG_pos γ ν l).le)
        (gbr_gainG_pos γ ν _).le haA hbB X
      -- the arithmetic: a b ≤ exp(η_δ/ν)
      have hab : (UnforcedLeray.Short.IIIa.gainG γ ν l)⁻¹ *
          UnforcedLeray.Short.IIIa.gainG γ ν (Real.exp δ * l) ≤
          Real.exp (etaDelta γ δ / ν) := by
        unfold UnforcedLeray.Short.IIIa.gainG
        have hx : (Real.exp (γ * l / (1 + ν * l)))⁻¹ *
            Real.exp (γ * (Real.exp δ * l) / (1 + ν * (Real.exp δ * l))) =
            Real.exp (γ * (Real.exp δ * l) / (1 + ν * (Real.exp δ * l)) - γ * l / (1 + ν * l)) := by
          rw [Real.exp_sub]
          ring
        rw [hx]
        apply Real.exp_le_exp.2
        have hM3 : (1 : ℝ) ≤ Real.exp (3 * δ / 2) := Real.one_le_exp (by linarith)
        have hsl : l ≤ Real.exp δ * l :=
          le_mul_of_one_le_left hl.le (Real.one_le_exp hδ.le)
        have htM : Real.exp δ * l ≤ Real.exp (3 * δ / 2) * l :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hl.le
        have hS := (gainRatioSup ν (Real.exp (3 * δ / 2)) hν hM3).2
          ⟨l, Real.exp δ * l, hl, hsl, htM, rfl⟩
        have hT := gainRatioTanh (Real.exp (3 * δ / 2)) hM3
        rw [Real.log_exp] at hT
        have hT' : (Real.sqrt (Real.exp (3 * δ / 2)) - 1) / (Real.sqrt (Real.exp (3 * δ / 2)) + 1)
            = Real.tanh (3 * δ / 8) := by
          rw [hT]
          congr 1
          ring
        rw [hT'] at hS
        unfold etaDelta
        rw [le_div_iff₀ hν]
        have key : (γ * (Real.exp δ * l) / (1 + ν * (Real.exp δ * l)) - γ * l / (1 + ν * l)) * ν
            = γ * (ν * (Real.exp δ * l / (1 + ν * (Real.exp δ * l)) - l / (1 + ν * l))) := by
          ring
        rw [key]
        exact mul_le_mul_of_nonneg_left hS hγ
      calc _ ≤ (UnforcedLeray.Short.IIIa.gainG γ ν l)⁻¹ *
            UnforcedLeray.Short.IIIa.gainG γ ν (Real.exp δ * l) *
            ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ := hcore
        _ ≤ Real.exp (etaDelta γ δ / ν) * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖ :=
          mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    · have hI0 : inRestr c mZ ρb B = 0 := gbr_inRestr_zero_of_not c mZ ρb hBm
      have hY0 : outRestr c A ∘L X ∘L inRestr c mZ ρb B = 0 := by
        rw [hI0]; simp
      rw [hY0]
      have hG0 : gainConjS γ hν (0 : Zsp c mZ ρb →L[ℝ] Hsp c) = 0 := by
        ext F
        simp [gainConjS_apply]
      rw [hG0]
      simp
  · have hO0 : outRestr c A = 0 := gbr_outRestr_zero_of_not c hAm
    have hY0 : outRestr c A ∘L X ∘L inRestr c mZ ρb B = 0 := by
      rw [hO0]; simp
    rw [hY0]
    have hG0 : gainConjS γ hν (0 : Zsp c mZ ρb →L[ℝ] Hsp c) = 0 := by
      ext F
      simp [gainConjS_apply]
    rw [hG0]
    simp

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
