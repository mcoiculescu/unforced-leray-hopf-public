import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPeriodic

/-!
# Periodicity of the glued window Hessian, Hessian version

Task `PartIII-b:C/ward/12/3/1/2/2/9`.  Proves `WindowHessPeriodic` from the uniqueness
`WindowHessUnique` (Hessian analogue of `windowLapPeriodic_of`).  Source of record:
`the November 2 reference manuscript`, lines 1437-1441.

Strategy.  `H' (p) = H (p.1 + P, p.2)` is a window Hessian of `W` at every centre `s`, by the
translation of test functions and the a.e. `P`-periodicity of `W`.  On the windows
`I_s = (s - 1/4, s + 1/4) × ℝ³` both `H` and `H'` are locally integrable (each lies in one integer
window), so `hUn` gives `H = H'` a.e. on each `I_s`.  Countably many rational `s` cover `ℝ × ℝ³`
up to a null set, and `Measure.ae_prod_iff_ae_ae` gives the slice statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Manifold

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)
open UnforcedLeray.Short.PartIIa (sub_neg_shift dy_comp_add locallyIntegrableOn_shift interval_sub_winSet)

/-- Translation commutes with `ν∂_j∂_k` (the Hessian analogue of `lapT_comp_add`). -/
private theorem hsPer_nuHessT_comp_add (ν : ℝ) (j k : Fin 3) (Ψ : ℝ × Space → CVec3)
    (a : ℝ × Space) :
    nuHessT ν j k (fun q => Ψ (q + a)) = fun p => nuHessT ν j k Ψ (p + a) := by
  funext p
  show ν • dy j (dy k (fun q => Ψ (q + a))) p = ν • dy j (dy k Ψ) (p + a)
  rw [dy_comp_add Ψ a k, dy_comp_add (dy k Ψ) a j]

/-- Translation in the window: a window Hessian of `W` at centre `c + P`, translated by `P` in
`τ`, is a window Hessian of `W` at centre `c`, when `W` is a.e. `P`-periodic. -/
theorem isWindowHess_shift (ν P c : ℝ) (j k : Fin 3) {W H : ℝ × Space → CVec3}
    (hW : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), W (p.1 + P, p.2) = W p)
    (hH : IsWindowHess ν (c + P) j k W H) :
    IsWindowHess ν c j k W (fun p => H (p.1 + P, p.2)) := by
  unfold IsWindowHess at hH ⊢
  intro ψ hψ hψc hψs
  have hφ : ContDiff ℝ ∞ (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) :=
    hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) :=
    hψc.comp_homeomorph (Homeomorph.addRight (-P, (0 : Space)))
  have hφs : tsupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) ⊆ winSet (c + P) := by
    have h1 : tsupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) ⊆
        (fun q : ℝ × Space => q + (-P, (0 : Space))) ⁻¹' tsupport ψ :=
      closure_minimal
        (fun q hq => subset_tsupport ψ (show q + (-P, (0 : Space)) ∈ Function.support ψ from hq))
        ((isClosed_tsupport ψ).preimage (continuous_id.add continuous_const))
    intro q hq
    obtain ⟨⟨h3, h4⟩, -⟩ := hψs (h1 hq)
    have h3' : c - 1 < q.1 + -P := h3
    have h4' : q.1 + -P < c + 1 := h4
    exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  obtain ⟨H1, H2, H3⟩ := hH (fun q => ψ (q + (-P, (0 : Space)))) hφ hφc hφs
  have hLφ := hsPer_nuHessT_comp_add ν j k ψ (-P, (0 : Space))
  have hadd : ∀ p : ℝ × Space, (p.1 + P, p.2) + (-P, (0 : Space)) = p :=
    fun p => Prod.ext (by simp) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · have h := H1.comp_sub_right (-P, (0 : Space))
    refine h.congr (by
      filter_upwards [hW] with p hp
      simp only [hLφ, sub_neg_shift, hadd, hp])
  · have h := H2.comp_sub_right (-P, (0 : Space))
    refine h.congr (ae_of_all _ (fun p => ?_))
    show dotL (H (p - (-P, (0 : Space)))) (ψ (p - (-P, (0 : Space)) + (-P, (0 : Space)))) =
      dotL (H (p.1 + P, p.2)) (ψ p)
    rw [sub_add_cancel, sub_neg_shift]
  · have e1 : ∫ p, dotL (W p) (nuHessT ν j k ψ p) = ∫ p, dotL (W (p - (-P, (0 : Space))))
        (nuHessT ν j k ψ p) := by
      refine integral_congr_ae ?_
      filter_upwards [hW] with p hp
      rw [sub_neg_shift, hp]
    have e2 : ∫ p, dotL (W (p - (-P, (0 : Space)))) (nuHessT ν j k ψ p) =
        ∫ q, dotL (W q) (nuHessT ν j k (fun q => ψ (q + (-P, (0 : Space)))) q) := by
      rw [← integral_sub_right_eq_self
        (fun q => dotL (W q) (nuHessT ν j k (fun q => ψ (q + (-P, (0 : Space)))) q))
        (-P, (0 : Space))]
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      simp only [hLφ, sub_add_cancel]
    have e4 : ∫ q, dotL (H q) (ψ (q + (-P, (0 : Space)))) =
        ∫ p, dotL (H (p.1 + P, p.2)) (ψ p) := by
      rw [← integral_sub_right_eq_self (fun q => dotL (H q) (ψ (q + (-P, (0 : Space)))))
        (-P, (0 : Space))]
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      show dotL (H (p - (-P, (0 : Space)))) (ψ (p - (-P, (0 : Space)) + (-P, (0 : Space)))) =
        dotL (H (p.1 + P, p.2)) (ψ p)
      rw [sub_add_cancel, sub_neg_shift]
    exact e1.trans (e2.trans (H3.trans e4))

/-- **Periodicity of the glued window Hessian** (source 1437-1441; Hessian analogue of
`windowLapPeriodic_of`). -/
theorem windowHessPeriodic_of (hUn : WindowHessUnique) : WindowHessPeriodic := by
  unfold WindowHessPeriodic
  intro P ν _ j k W H hWm hHm hper hwin hloc
  have hm1 : Measurable (fun p : ℝ × Space => W (p.1 + P, p.2)) :=
    hWm.measurable.comp ((measurable_fst.add_const P).prodMk measurable_snd)
  have hmeasW : MeasurableSet {p : ℝ × Space | W (p.1 + P, p.2) = W p} :=
    measurableSet_eq_fun hm1 hWm.measurable
  have hWp : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), W (p.1 + P, p.2) = W p := by
    rw [Measure.volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hmeasW).2 (by
      filter_upwards [hper] with τ hτ
      exact hτ)
  have hH' : ∀ s : ℝ, IsWindowHess ν s j k W (fun p => H (p.1 + P, p.2)) := fun s =>
    isWindowHess_shift ν P s j k hWp (hwin (s + P))
  have hwin_ae : ∀ s : ℝ, ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      p ∈ Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space) → H p = H (p.1 + P, p.2) := by
    intro s
    have hLoc1 : LocallyIntegrableOn H (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space))
        (volume : Measure (ℝ × Space)) :=
      (hloc ⌊s + 1 / 2⌋).mono_set (fun p hp => ⟨interval_sub_winSet s hp.1, hp.2⟩)
    have hST : (fun p : ℝ × Space => (p.1 + P, p.2)) ''
        (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space)) ⊆
        winSet ((⌊s + P + 1 / 2⌋ : ℤ) : ℝ) := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, -⟩ := hp
      exact ⟨interval_sub_winSet (s + P)
        (show p.1 + P ∈ Ioo (s + P - 1 / 4) (s + P + 1 / 4) from ⟨by linarith, by linarith⟩),
        mem_univ _⟩
    have hLoc2 : LocallyIntegrableOn (fun p : ℝ × Space => H (p.1 + P, p.2))
        (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space)) (volume : Measure (ℝ × Space)) :=
      locallyIntegrableOn_shift P (isOpen_Ioo.prod isOpen_univ) hST (hloc (⌊s + P + 1 / 2⌋))
    have hUs := hUn ν s s (s - 1 / 4) (s + 1 / 4) j k W H (fun p => H (p.1 + P, p.2))
      (by linarith) (by linarith) (by linarith) (by linarith) (hwin s) (hH' s) hLoc1 hLoc2
    exact (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).1 hUs
  have hall : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), ∀ q : ℚ,
      p ∈ Ioo ((q : ℝ) - 1 / 4) ((q : ℝ) + 1 / 4) ×ˢ (univ : Set Space) →
        H p = H (p.1 + P, p.2) := by
    rw [ae_all_iff]
    intro q
    exact hwin_ae (q : ℝ)
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), H (p.1 + P, p.2) = H p := by
    filter_upwards [hall] with p hp
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p.1 - 1 / 8 < p.1 + 1 / 8 by linarith)
    have hmem : p ∈ Ioo ((q : ℝ) - 1 / 4) ((q : ℝ) + 1 / 4) ×ˢ (univ : Set Space) :=
      ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
    exact (hp q hmem).symm
  have hmeasH : MeasurableSet {p : ℝ × Space | H (p.1 + P, p.2) = H p} :=
    measurableSet_eq_fun
      (hHm.measurable.comp ((measurable_fst.add_const P).prodMk measurable_snd)) hHm.measurable
  rw [Measure.volume_eq_prod] at hae
  filter_upwards [(Measure.ae_prod_iff_ae_ae hmeasH).1 hae] with τ hτ
  exact hτ

end UnforcedLeray.Short.PartIIIb.Concrete
