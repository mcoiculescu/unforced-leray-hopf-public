import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.WeakDuhamelGrid

/-- Grid points `min t (k/(n+1))`. -/
def gq (t : ℝ) (n k : ℕ) : ℝ := min t ((k : ℝ) / (n + 1))

/-- Grid index of `r`. -/
def gk (n : ℕ) (r : ℝ) : ℕ := ⌈r * (n + 1)⌉₊

theorem measurable_gk (n : ℕ) : Measurable (gk n) :=
  (Nat.measurable_ceil (R := ℝ)).comp (measurable_id.mul_const _)

theorem gq_ge {t r : ℝ} (hr : r ≤ t) (n : ℕ) : r ≤ gq t n (gk n r) := by
  unfold gq gk
  refine le_min hr ?_
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem gq_le {t r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) : gq t n (gk n r) ≤ r + 1 / (n + 1) := by
  unfold gq gk
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have h := Nat.ceil_lt_add_one (mul_nonneg hr0 (by positivity : (0:ℝ) ≤ n + 1))
  have : (r + 1 / ((n:ℝ) + 1)) * (n + 1) = r * (n + 1) + 1 := by
    field_simp
  rw [this]; exact h.le

theorem tendsto_gq {t r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ t) :
    Tendsto (fun n : ℕ => gq t n (gk n r)) atTop (𝓝[Icc r t] r) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun n => ⟨gq_ge hr n, (min_le_left _ _)⟩⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => gq_ge hr n) (fun n => gq_le hr0 n)
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using this.const_add r

/-- Measurable representatives for `H q`. -/
@[irreducible] def rep (s t : ℝ) (H : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) μ) (q : ℝ) : ℝ → ℝ :=
  if hq : q ∈ Icc s t then (hmeas q hq).mk (H q) else fun _ => 0

theorem rep_measurable (s t : ℝ) (H : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) μ) (q : ℝ) :
    Measurable (rep s t H μ hmeas q) := by
  unfold rep
  split_ifs with hq
  · exact (hmeas q hq).stronglyMeasurable_mk.measurable
  · exact measurable_const

theorem measurable_rep_prod (s t : ℝ) (H : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) μ) (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => rep s t H μ hmeas (gq t n (gk n z.2)) z.1) := by
  have h1 : Measurable (fun z : ℕ × ℝ => rep s t H μ hmeas (gq t n z.1) z.2) :=
    measurable_from_prod_countable_right (α := ℕ) (β := ℝ)
      (f := fun z : ℕ × ℝ => rep s t H μ hmeas (gq t n z.1) z.2)
      (fun k => rep_measurable s t H μ hmeas (gq t n k))
  have h2 : Measurable (fun z : ℝ × ℝ => (gk n z.2, z.1)) :=
    ((measurable_gk n).comp measurable_snd).prodMk measurable_fst
  exact h1.comp h2

theorem measurable_rep_diag (s t : ℝ) (H : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) μ) (n : ℕ) :
    Measurable (fun τ : ℝ => rep s t H μ hmeas (gq t n (gk n τ)) τ) := by
  have h1 : Measurable (fun z : ℕ × ℝ => rep s t H μ hmeas (gq t n z.1) z.2) :=
    measurable_from_prod_countable_right (α := ℕ) (β := ℝ)
      (f := fun z : ℕ × ℝ => rep s t H μ hmeas (gq t n z.1) z.2)
      (fun k => rep_measurable s t H μ hmeas (gq t n k))
  have h2 : Measurable (fun τ : ℝ => (gk n τ, τ)) := (measurable_gk n).prodMk measurable_id
  exact h1.comp h2

theorem ae_rep (s t : ℝ) (H : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) μ) :
    ∀ᵐ τ ∂μ, ∀ (n k : ℕ), gq t n k ∈ Icc s t →
      H (gq t n k) τ = rep s t H μ hmeas (gq t n k) τ := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro k
  by_cases hq : gq t n k ∈ Icc s t
  · filter_upwards [(hmeas _ hq).ae_eq_mk] with τ hτ _
    simp only [rep, hq, dif_pos]
    exact hτ
  · exact Eventually.of_forall fun τ h => absurd h hq

/-- One-variable grid measurability. -/
theorem aesm_diag {s t : ℝ} (hs : 0 ≤ s) (_hst : s ≤ t) (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) (volume.restrict (Ioc s t)))
    (hlim : ∀ τ ∈ Ioc s t, Tendsto (fun q => H q τ) (𝓝[Icc τ t] τ) (𝓝 (G τ))) :
    AEStronglyMeasurable G (volume.restrict (Ioc s t)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun τ => rep s t H (volume.restrict (Ioc s t)) hmeas (gq t n (gk n τ)) τ)
    (fun n => (measurable_rep_diag s t H _ hmeas n).aestronglyMeasurable) ?_
  filter_upwards [ae_rep s t H _ hmeas, ae_restrict_mem measurableSet_Ioc] with τ h1 hτ
  have hτ0 : 0 ≤ τ := hs.trans hτ.1.le
  have hτt : τ ≤ t := hτ.2
  have heq : ∀ n : ℕ, rep s t H _ hmeas (gq t n (gk n τ)) τ = H (gq t n (gk n τ)) τ := by
    intro n
    have hmem : gq t n (gk n τ) ∈ Icc s t :=
      ⟨hτ.1.le.trans (gq_ge hτt n), min_le_left _ _⟩
    exact (h1 n _ hmem).symm
  simp only [heq]
  exact (hlim τ hτ).comp (tendsto_gq hτ0 hτt)

/-- Two-variable grid measurability on the triangle `τ ≤ r`. -/
theorem aesm_tri {s t : ℝ} (hs : 0 ≤ s) (_hst : s ≤ t) (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (hmeas : ∀ q ∈ Icc s t, AEStronglyMeasurable (H q) (volume.restrict (Ioc s t)))
    (hlim : ∀ τ ∈ Ioc s t, ∀ r, τ ≤ r → r ≤ t →
      Tendsto (fun q => H q τ) (𝓝[Icc r t] r) (𝓝 (G τ r))) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => G z.1 z.2)
      (((volume.restrict (Ioc s t)).prod (volume.restrict (Ioc s t))).restrict
        {z : ℝ × ℝ | z.1 ≤ z.2}) := by
  set μ : Measure ℝ := volume.restrict (Ioc s t)
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun z : ℝ × ℝ => rep s t H μ hmeas (gq t n (gk n z.2)) z.1)
    (fun n => (measurable_rep_prod s t H _ hmeas n).aestronglyMeasurable) ?_
  have hae1 : ∀ᵐ z ∂(μ.prod μ), ∀ (n k : ℕ), gq t n k ∈ Icc s t →
      H (gq t n k) z.1 = rep s t H μ hmeas (gq t n k) z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (ae_rep s t H μ hmeas)
  have hae2 : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ Ioc s t :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (ae_restrict_mem measurableSet_Ioc)
  have hae3 : ∀ᵐ z ∂(μ.prod μ), z.2 ∈ Ioc s t :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (ae_restrict_mem measurableSet_Ioc)
  have hT : MeasurableSet {z : ℝ × ℝ | z.1 ≤ z.2} :=
    measurableSet_le measurable_fst measurable_snd
  filter_upwards [ae_restrict_of_ae hae1, ae_restrict_of_ae hae2, ae_restrict_of_ae hae3,
    ae_restrict_mem hT] with z h1 h2 h3 hz
  have hτ0 : 0 ≤ z.1 := hs.trans h2.1.le
  have hrt : z.2 ≤ t := h3.2
  have heq : ∀ n : ℕ, rep s t H μ hmeas (gq t n (gk n z.2)) z.1 =
      H (gq t n (gk n z.2)) z.1 := by
    intro n
    have hmem : gq t n (gk n z.2) ∈ Icc s t :=
      ⟨h3.1.le.trans (gq_ge hrt n), min_le_left _ _⟩
    exact (h1 n _ hmem).symm
  simp only [heq]
  exact (hlim z.1 h2 z.2 hz hrt).comp (tendsto_gq (hτ0.trans hz) hrt)

end UnforcedLeray.Short.IIb.WeakDuhamelGrid

end
