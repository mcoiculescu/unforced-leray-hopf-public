import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.PsiSProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.LogSubst
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/3`: Minkowski's integral inequality over the stream atoms

Source `the November 2 reference manuscript` 5590 ("Minkowski"), 4178-4186, 5592.
Analogue of `Sub/PartIII-b_C_rep_5_1_2_4_1_3/PsiAtomsMinkowski.lean` with the stream kernel
`ϱ(y)^{-2}(ϱ(y)² + (y₂ - λz₂)²)^{-1}` in place of `|y - λz|^{-4}`.  Proves `PsiSAtomsMinkowski`:
the atom representation `Ψ_s ≤ ∫ phKerS · srcW` (log substitution, set restriction to
`Iio τ ×ˢ S`), joint measurability of `phKerS · srcW`, and Minkowski's integral inequality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore (srcW omega2 ybin)

/-- Measurability of the stream kernel in the output variable, for a fixed atom. -/
theorem atoms_phKerS_measurable_output (θ σ : ℝ) (z : Space) :
    Measurable (fun x : ℝ × Space => phKerS θ x.1 x.2 σ z) := by
  unfold phKerS
  have hc : MeasurableSet {x : ℝ × Space | σ < x.1 ∧ ϱ z < θ * ϱ x.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const (measurable_const.mul (measurable_ϱ.comp measurable_snd)))
  have m1 : Measurable (fun x : ℝ × Space => ENNReal.ofReal (Real.exp ((σ - x.1) / 2) / 2)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have ha : Measurable (fun x : ℝ × Space => ϱ x.2) := measurable_ϱ.comp measurable_snd
  have hb : Measurable (fun x : ℝ × Space => x.2 2) := (measurable_coord 2).comp measurable_snd
  have hc2 : Measurable (fun x : ℝ × Space => Real.exp ((σ - x.1) / 2) * z 2) := by
    fun_prop
  have m2 : Measurable (fun x : ℝ × Space =>
      ENNReal.ofReal ((ϱ x.2 ^ 2 * (ϱ x.2 ^ 2 + (x.2 2 - Real.exp ((σ - x.1) / 2) * z 2) ^ 2))⁻¹)) :=
    psiS_kernel_gen _ _ _ ha hb hc2
  exact Measurable.ite hc (m1.mul m2) measurable_const

/-- Joint measurability of `phKerS · srcW` in output and atom. -/
theorem atoms_phKerS_srcW_measurable (R c θ : ℝ) (G : Chart → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      phKerS θ q.1.1 q.1.2 q.2.1 q.2.2 * srcW R c G q.2.1 q.2.2) := by
  have hsrc : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => srcW R c G q.2.1 q.2.2) :=
    (WYCore.measurable_srcW R c hG).comp measurable_snd
  have hcond : MeasurableSet {q : (ℝ × Space) × (ℝ × Space) |
      q.2.1 < q.1.1 ∧ ϱ q.2.2 < θ * ϱ q.1.2} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (measurable_fst.comp measurable_snd)
        (measurable_fst.comp measurable_fst)
    · exact measurableSet_lt (measurable_ϱ.comp (measurable_snd.comp measurable_snd))
        ((measurable_const.mul (measurable_ϱ.comp (measurable_snd.comp measurable_fst))))
  have h1 : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      ENNReal.ofReal (Real.exp ((q.2.1 - q.1.1) / 2) / 2)) := by
    have : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => Real.exp ((q.2.1 - q.1.1) / 2) / 2) := by
      fun_prop
    exact ENNReal.measurable_ofReal.comp this
  have ha : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => ϱ q.1.2) :=
    measurable_ϱ.comp (measurable_snd.comp measurable_fst)
  have hb : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => q.1.2 2) :=
    (measurable_coord 2).comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      Real.exp ((q.2.1 - q.1.1) / 2) * q.2.2 2) := by
    have h3 : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => q.2.2 2) :=
      (measurable_coord 2).comp (measurable_snd.comp measurable_snd)
    have h4 : Measurable (fun q : (ℝ × Space) × (ℝ × Space) => Real.exp ((q.2.1 - q.1.1) / 2)) := by
      fun_prop
    exact h4.mul h3
  have hk := psiS_kernel_gen _ _ _ ha hb hc
  have hf : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      ENNReal.ofReal (Real.exp ((q.2.1 - q.1.1) / 2) / 2) *
        ENNReal.ofReal ((ϱ q.1.2 ^ 2 * (ϱ q.1.2 ^ 2 + (q.1.2 2 - Real.exp ((q.2.1 - q.1.1) / 2) * q.2.2 2) ^ 2))⁻¹)) :=
    h1.mul hk
  have hker : Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      phKerS θ q.1.1 q.1.2 q.2.1 q.2.2) := by
    unfold phKerS
    exact Measurable.ite (p := fun q : (ℝ × Space) × (ℝ × Space) =>
        q.2.1 < q.1.1 ∧ ϱ q.2.2 < θ * ϱ q.1.2) hcond hf measurable_const
  exact hker.mul hsrc

/-- The atom representation `Ψ_s(τ, y) ≤ ∫ phKerS(τ, y; σ, z) srcW(σ, z) d(σ, z)`
(log substitution `λ = e^{(σ-τ)/2}`, restriction to `Iio τ ×ˢ S`). -/
theorem psiS_atom_rep (R c θ : ℝ) (G : Chart → ℝ≥0∞) (hG : Measurable G) (τ : ℝ) (y : Space) :
    psiMajS R c θ G τ y ≤
      ∫⁻ a : ℝ × Space, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 := by
  set S : Set Space := {z : Space | ϱ z < θ * ϱ y} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_ϱ measurable_const
  set Φ : ℝ × Space → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - p.1 * p.2 2) ^ 2))⁻¹) *
      srcW R c G (τ + 2 * Real.log p.1) p.2 with hΦ
  have hΦm : Measurable Φ := by
    have ha : Measurable (fun _ : ℝ × Space => ϱ y) := measurable_const
    have hb : Measurable (fun _ : ℝ × Space => y 2) := measurable_const
    have hc : Measurable (fun p : ℝ × Space => p.1 * p.2 2) :=
      measurable_fst.mul ((measurable_coord 2).comp measurable_snd)
    have h1 := psiS_kernel_gen _ _ _ ha hb hc
    have h2 : Measurable (fun p : ℝ × Space => srcW R c G (τ + 2 * Real.log p.1) p.2) :=
      (WYCore.measurable_srcW R c hG).comp
        ((measurable_const.add (measurable_const.mul (Real.measurable_log.comp measurable_fst))).prodMk
          measurable_snd)
    exact h1.mul h2
  have hΨm : Measurable ((Prod.snd ⁻¹' S).indicator Φ) :=
    hΦm.indicator (hSm.preimage measurable_snd)
  have hpsi : ∀ l : ℝ, ∫⁻ z in S, Φ (l, z) = ∫⁻ z, (Prod.snd ⁻¹' S).indicator Φ (l, z) := by
    intro l
    rw [← lintegral_indicator hSm]
    congr 1
  have hFm : Measurable (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) := by
    have hfun : (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) =
        fun l : ℝ => ∫⁻ z, (Prod.snd ⁻¹' S).indicator Φ (l, z) := funext hpsi
    rw [hfun]
    exact hΨm.lintegral_prod_right'
  have hL : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in S, Φ (l, z) =
      ∫⁻ σ in Iio τ, ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) *
        ∫⁻ z in S, Φ (Real.exp ((σ - τ) / 2), z) :=
    WYCore.logSubst τ (fun l : ℝ => ∫⁻ z in S, Φ (l, z)) hFm
  set K : ℝ × Space → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp ((a.1 - τ) / 2) / 2) *
      (ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - Real.exp ((a.1 - τ) / 2) * a.2 2) ^ 2))⁻¹) *
        srcW R c G a.1 a.2)
    with hK
  have hKm : Measurable K := by
    have h1 : Measurable (fun a : ℝ × Space => ENNReal.ofReal (Real.exp ((a.1 - τ) / 2) / 2)) := by
      have : Measurable (fun a : ℝ × Space => Real.exp ((a.1 - τ) / 2) / 2) := by fun_prop
      exact ENNReal.measurable_ofReal.comp this
    have hc : Measurable (fun a : ℝ × Space => Real.exp ((a.1 - τ) / 2) * a.2 2) := by
      have h3 : Measurable (fun a : ℝ × Space => a.2 2) := (measurable_coord 2).comp measurable_snd
      have h4 : Measurable (fun a : ℝ × Space => Real.exp ((a.1 - τ) / 2)) := by fun_prop
      exact h4.mul h3
    have hk := psiS_kernel_gen (fun _ : ℝ × Space => ϱ y) (fun _ : ℝ × Space => y 2)
      (fun a : ℝ × Space => Real.exp ((a.1 - τ) / 2) * a.2 2) measurable_const measurable_const hc
    have hs : Measurable (fun a : ℝ × Space => srcW R c G a.1 a.2) :=
      WYCore.measurable_srcW R c hG
    exact h1.mul (hk.mul hs)
  have hinner : ∀ σ : ℝ, ∫⁻ z in S, K (σ, z) =
      ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) * ∫⁻ z in S, Φ (Real.exp ((σ - τ) / 2), z) := by
    intro σ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    have hlog : τ + 2 * Real.log (Real.exp ((σ - τ) / 2)) = σ := by
      rw [Real.log_exp]; ring
    simp only [hK, hΦ]
    rw [hlog]
  have hA : MeasurableSet (Iio τ ×ˢ S) := measurableSet_Iio.prod hSm
  have hAK : ∫⁻ a in Iio τ ×ˢ S, K a = ∫⁻ σ in Iio τ, ∫⁻ z in S, K (σ, z) := by
    rw [Measure.volume_eq_prod]
    exact setLIntegral_prod K hKm.aemeasurable
  have hPhKer : ∀ a ∈ Iio τ ×ˢ S, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 = K a := by
    rintro ⟨σ, z⟩ ⟨hσ, hz⟩
    have hσ' : σ < τ := hσ
    have hz' : ϱ z < θ * ϱ y := hz
    simp only [hK, phKerS]
    rw [if_pos ⟨hσ', hz'⟩, mul_assoc]
  have hRHS : ∫⁻ a in Iio τ ×ˢ S, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 =
      ∫⁻ a in Iio τ ×ˢ S, K a :=
    setLIntegral_congr_fun hA hPhKer
  have hle : ∫⁻ a in Iio τ ×ˢ S, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 ≤
      ∫⁻ a : ℝ × Space, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 :=
    setLIntegral_le_lintegral _ _
  calc psiMajS R c θ G τ y
      = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in S, Φ (l, z) := rfl
    _ = ∫⁻ σ in Iio τ, ∫⁻ z in S, K (σ, z) :=
        hL.trans (lintegral_congr fun σ => (hinner σ).symm)
    _ = ∫⁻ a in Iio τ ×ˢ S, K a := hAK.symm
    _ = ∫⁻ a in Iio τ ×ˢ S, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 := hRHS.symm
    _ ≤ ∫⁻ a : ℝ × Space, phKerS θ τ y a.1 a.2 * srcW R c G a.1 a.2 := hle

/-- **`PsiSAtomsMinkowski`**: Minkowski's integral inequality over the source atoms for `Ψ_s`. -/
theorem psiSAtomsMinkowski : PsiSAtomsMinkowski := by
  intro R c θ G hG X
  have hW : ∀ W : ℝ≥0∞, (W ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = W := fun W => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have key : ∀ a : ℝ × Space,
      (∫⁻ x in X, (phKerS θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        srcW R c G a.1 a.2 * (∫⁻ x in X, phKerS θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro a
    have h1 : ∀ x : ℝ × Space, (phKerS θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ) =
        phKerS θ x.1 x.2 a.1 a.2 ^ (2 : ℝ) * srcW R c G a.1 a.2 ^ (2 : ℝ) :=
      fun x => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    simp only [h1]
    rw [lintegral_mul_const _ ((atoms_phKerS_measurable_output θ a.1 a.2).pow_const (2 : ℝ)),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hW, mul_comm]
  have hM := UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict X) (ν := (volume : Measure (ℝ × Space)))
    (F := fun x a => phKerS θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2)
    (atoms_phKerS_srcW_measurable R c θ G hG).aemeasurable (p := 2) (by norm_num)
  calc (∫⁻ x in X, psiMajS R c θ G x.1 x.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x in X, (∫⁻ a : ℝ × Space, phKerS θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow
          (lintegral_mono fun x => ENNReal.rpow_le_rpow (psiS_atom_rep R c θ G hG x.1 x.2) (by norm_num))
          (by norm_num)
    _ ≤ ∫⁻ a : ℝ × Space, (∫⁻ x in X, (phKerS θ x.1 x.2 a.1 a.2 * srcW R c G a.1 a.2) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) := hM
    _ = ∫⁻ a : ℝ × Space, srcW R c G a.1 a.2 *
          (∫⁻ x in X, phKerS θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        lintegral_congr key

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
