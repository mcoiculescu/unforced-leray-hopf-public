import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniInner.Coef
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniInner.Step

/-!
# `VtvFubiniInner` (source 4610)

For a.e. `r > 0` the functional `R(r,·)` is the `r^μ`-multiple of the sum of five cell integrals
`∫ a_i · (∂^{α_i} φ)` with coefficients `a_i` (Coef.lean) that are integrable against every
cylinder test.  With `G(s,x) = η(s,x)` and `H_i ∈ {G, ∂_qG, ∂_ηG, ∂_q²G, ∂_η²G}` the jets of
`∂_sη(s)` are `∂_s H_i(s,·)` (symmetry of mixed partials, Jet.lean), and each term is handled by
`Tstep` (Fubini in `(s,x)` plus the fundamental theorem of calculus in `s`, `η(s_2) = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open FubiniInner

theorem Rform_jets {ν c μ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om g : ℝ → ℝ × ℝ → ℂ) (b : Chart → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, MemLp (fun x => f (r, x) i) 2 (volume.restrict (B0579.cell c)))
    (hu : ∀ j, MemLp (fun x => b (r, x) j) 2 (volume.restrict (B0579.cell c)))
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => om r x * (ψ x : ℂ)) (B0579.cell c))
    (hcurl : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, g r x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, (f (r, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          f (r, x) 1 * (B0579.pd 0 ψ x : ℂ)))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) {j0 j1 j2 j3 j4 : ℝ × ℝ → ℝ}
    (h0 : φ = j0) (h1 : B0579.pd 0 φ = j1) (h2 : B0579.pd 1 φ = j2)
    (h3 : B0579.pd 0 (B0579.pd 0 φ) = j3) (h4 : B0579.pd 1 (B0579.pd 1 φ) = j4) :
    vtvR μ tr om g b r φ = ((r : ℂ) ^ (μ : ℂ)) *
      (((((∫ x in B0579.cell c, cA0 tr (fun x => b (r, x)) r x * (j0 x : ℂ)) +
        ∫ x in B0579.cell c, cA1 tr (om r) (fun x => f (r, x)) r x * (j1 x : ℂ)) +
        ∫ x in B0579.cell c, cA2 tr (om r) (fun x => f (r, x)) r x * (j2 x : ℂ)) +
        ∫ x in B0579.cell c, cA3 ν (om r) x * (j3 x : ℂ)) +
        ∫ x in B0579.cell c, cA3 ν (om r) x * (j4 x : ℂ)) := by
  rw [← h0, ← h1, ← h2, ← h3, ← h4]
  exact Rform tr om g b f hr hF hu hom hcurl hφ

theorem pdfun {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (j : Fin 2) (s : ℝ) :
    B0579.pd j (fun y => H (s, y)) = fun y => Pj j H (s, y) :=
  funext (pd_eq hH j s)

theorem inner_at {ν c μ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (om g : ℝ → ℝ × ℝ → ℂ) (b : Chart → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, MemLp (fun x => f (r, x) i) 2 (volume.restrict (B0579.cell c)))
    (hu : ∀ j, MemLp (fun x => b (r, x) j) 2 (volume.restrict (B0579.cell c)))
    (hom : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => om r x * (ψ x : ℂ)) (B0579.cell c))
    (hcurl : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, g r x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, (f (r, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          f (r, x) 1 * (B0579.pd 0 ψ x : ℂ)))
    (η : ℝ → ℝ × ℝ → ℝ) (hη : IsStreamTest c η) :
    ∫ s in Ioi (0 : ℝ), (if r ≤ s then
        vtvR μ tr om g b r (fun x => deriv (fun s' => η s' x) s) else 0) =
      - vtvR μ tr om g b r (η r) := by
  have hDC := vtvDerivCyl c η hη
  obtain ⟨hGs, hcyl, s1, s2, R, hs1, hband⟩ := hη
  set G : ℝ × (ℝ × ℝ) → ℝ := fun p => η p.1 p.2 with hGdef
  have hG : ContDiff ℝ ∞ G := hGs
  have hU : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|} := by
    refine (isOpen_lt continuous_fst continuous_const).union ?_
    exact (isOpen_lt continuous_const continuous_fst).union
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd)))
  have z0 : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → G p = 0 :=
    fun p hp => hband p.1 p.2 hp
  have s1' : ContDiff ℝ ∞ (Pj 0 G) := smooth_Pj 0 hG
  have s2' : ContDiff ℝ ∞ (Pj 1 G) := smooth_Pj 1 hG
  have s3' : ContDiff ℝ ∞ (Pj 0 (Pj 0 G)) := smooth_Pj 0 s1'
  have s4' : ContDiff ℝ ∞ (Pj 1 (Pj 1 G)) := smooth_Pj 1 s2'
  have z1 : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → Pj 0 G p = 0 :=
    fun p hp => zero_Pj hU z0 0 p hp
  have z2 : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → Pj 1 G p = 0 :=
    fun p hp => zero_Pj hU z0 1 p hp
  have z3 : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → Pj 0 (Pj 0 G) p = 0 :=
    fun p hp => zero_Pj hU z1 0 p hp
  have z4 : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → Pj 1 (Pj 1 G) p = 0 :=
    fun p hp => zero_Pj hU z2 1 p hp
  -- the five exchange steps
  obtain ⟨I0, E0⟩ := Tstep (fun ψ hψ => int_a0 tr hr.le hu hψ) hG z0 hr
  obtain ⟨I1, E1⟩ := Tstep (fun ψ hψ => int_a1 tr hr.le hom hF hψ) s1' z1 hr
  obtain ⟨I2, E2⟩ := Tstep (fun ψ hψ => int_a2 tr hr.le hom hF hψ) s2' z2 hr
  obtain ⟨I3, E3⟩ := Tstep (fun ψ hψ => int_a3 ν hom hψ) s3' z3 hr
  obtain ⟨I4, E4⟩ := Tstep (fun ψ hψ => int_a3 ν hom hψ) s4' z4 hr
  -- jets of `∂_s η(s)`
  have jets_s : ∀ s : ℝ,
      (fun x => deriv (fun s' => η s' x) s) = (fun y => Ds G (s, y)) ∧
      B0579.pd 0 (fun x => deriv (fun s' => η s' x) s) = (fun y => Ds (Pj 0 G) (s, y)) ∧
      B0579.pd 1 (fun x => deriv (fun s' => η s' x) s) = (fun y => Ds (Pj 1 G) (s, y)) ∧
      B0579.pd 0 (B0579.pd 0 (fun x => deriv (fun s' => η s' x) s)) =
        (fun y => Ds (Pj 0 (Pj 0 G)) (s, y)) ∧
      B0579.pd 1 (B0579.pd 1 (fun x => deriv (fun s' => η s' x) s)) =
        (fun y => Ds (Pj 1 (Pj 1 G)) (s, y)) := by
    intro s
    have e0 : (fun x => deriv (fun s' => η s' x) s) = (fun y => Ds G (s, y)) :=
      funext fun y => deriv_s hG s y
    have e1 : ∀ j : Fin 2, B0579.pd j (fun x => deriv (fun s' => η s' x) s) =
        (fun y => Ds (Pj j G) (s, y)) := by
      intro j
      rw [e0, pdfun (smooth_Ds hG) j s, ← Ds_Pj hG j]
    have e2 : ∀ j : Fin 2, B0579.pd j (B0579.pd j (fun x => deriv (fun s' => η s' x) s)) =
        (fun y => Ds (Pj j (Pj j G)) (s, y)) := by
      intro j
      rw [e1 j, pdfun (smooth_Ds (smooth_Pj j hG)) j s, ← Ds_Pj (smooth_Pj j hG) j]
    exact ⟨e0, e1 0, e1 1, e2 0, e2 1⟩
  have jets_r : (η r) = (fun y => G (r, y)) ∧
      B0579.pd 0 (η r) = (fun y => Pj 0 G (r, y)) ∧
      B0579.pd 1 (η r) = (fun y => Pj 1 G (r, y)) ∧
      B0579.pd 0 (B0579.pd 0 (η r)) = (fun y => Pj 0 (Pj 0 G) (r, y)) ∧
      B0579.pd 1 (B0579.pd 1 (η r)) = (fun y => Pj 1 (Pj 1 G) (r, y)) := by
    have e1 : ∀ j : Fin 2, B0579.pd j (η r) = (fun y => Pj j G (r, y)) := fun j =>
      pdfun hG j r
    have e2 : ∀ j : Fin 2, B0579.pd j (B0579.pd j (η r)) = (fun y => Pj j (Pj j G) (r, y)) := by
      intro j
      rw [e1 j]
      exact pdfun (smooth_Pj j hG) j r
    exact ⟨rfl, e1 0, e1 1, e2 0, e2 1⟩
  -- pointwise decomposition in `s`
  have hpt : ∀ s : ℝ, (if r ≤ s then
        vtvR μ tr om g b r (fun x => deriv (fun s' => η s' x) s) else 0) =
      ((r : ℂ) ^ (μ : ℂ)) *
        ((((fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c,
              cA0 tr (fun x => b (r, x)) r x * (Ds G (s, x) : ℂ) else 0) s +
          (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c,
              cA1 tr (om r) (fun x => f (r, x)) r x * (Ds (Pj 0 G) (s, x) : ℂ) else 0) s) +
          (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c,
              cA2 tr (om r) (fun x => f (r, x)) r x * (Ds (Pj 1 G) (s, x) : ℂ) else 0) s) +
          (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c,
              cA3 ν (om r) x * (Ds (Pj 0 (Pj 0 G)) (s, x) : ℂ) else 0) s +
          (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c,
              cA3 ν (om r) x * (Ds (Pj 1 (Pj 1 G)) (s, x) : ℂ) else 0) s) := by
    intro s
    by_cases h : r ≤ s
    · obtain ⟨a0, a1, a2, a3, a4⟩ := jets_s s
      have := Rform_jets (μ := μ) tr om g b f hr hF hu hom hcurl (hDC s) a0 a1 a2 a3 a4
      simp only [if_pos h]
      rw [this]
    · simp [h]
  simp only [hpt]
  have hR := Rform_jets (μ := μ) tr om g b f hr hF hu hom hcurl (hcyl r) jets_r.1 jets_r.2.1
    jets_r.2.2.1 jets_r.2.2.2.1 jets_r.2.2.2.2
  rw [hR, integral_const_mul]
  rw [integral_add, integral_add, integral_add, integral_add]
  · rw [E0, E1, E2, E3, E4]
    beta_reduce
    ring
  all_goals first
    | exact I0 | exact I1 | exact I2 | exact I3 | exact I4
    | exact I0.add I1 | exact (I0.add I1).add I2 | exact ((I0.add I1).add I2).add I3

theorem vtvFubiniInner : VtvFubiniInner := by
  intro ν c μ tr om g b G f H η hη
  obtain ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, hOm⟩ := H
  filter_upwards [slice_ae (c := c) hf, ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))]
    with r hr hr0
  have hr0' : (0 : ℝ) < r := hr0
  exact inner_at tr om g b f hr0' hr (fun j => (hBS r hr0').1 j) (hOm r hr0')
    (hcurl r hr0') η hη

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
