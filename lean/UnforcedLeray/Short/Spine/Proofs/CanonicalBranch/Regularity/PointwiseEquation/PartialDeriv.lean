import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5

/-!
# Spine: `PartialDerivAe` (leaf 1 of `Spine:SP-CAN/4/5`)

Proves `PartialDerivAe` (`Short/Spine/Sub/SP_CAN4_5.lean`, line 52) with the statement unchanged.

Source of record: `the November 2 reference manuscript` line 1086.

Route. Put `h_m = 1/(m+1)`, which tends to `0` inside `𝓝[≠] 0`.

1. The `X_G` difference quotients `Q_m = h_m⁻¹ • (V (θ + h_m) - V θ)` converge to `deriv V θ` in
   `X_G` (`hasDerivAt_iff_tendsto_slope_zero`), hence in measure (`tendstoInMeasure_of_tendsto_Lp`).
2. An a.e.-convergent subsequence `Q_{ns i}` is extracted (`TendstoInMeasure.exists_seq_tendsto_ae`).
3. For `r > 0`, `t ↦ W t r` is differentiable at `θ` (joint smoothness of `W` on `(0, ∞)²`), so the
   quotients `h_m⁻¹ • (W (θ + h_m) r - W θ r)` converge to `deriv (fun t => W t r) θ`.
4. Off a null set, `Q_m r` equals these quotients for all `m` (`Lp.coeFn_smul`, `Lp.coeFn_sub`,
   `W θ' =ᵐ V θ'`, countably many null sets via `ae_all_iff`); `ae_xG_pos` gives `r > 0`.
   Uniqueness of limits gives the identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 1, the `X_G`-derivative is the pointwise `θ`-derivative** (a.e. in `r`); proved with the
statement of `PartialDerivAe` unchanged. -/
theorem partialDerivAe_proof : UnforcedLeray.Short.Spine.PartialDerivAe := by
  intro V hs W hWV hWsm θ hθ
  obtain ⟨_, hVd⟩ := hs θ hθ
  have hVd' : HasDerivAt V (deriv V θ) θ := hVd.differentiableAt.hasDerivAt
  -- the step sequence `h_m = 1/(m+1)` tends to `0` inside the punctured filter
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => Set.mem_compl_singleton_iff.mpr (hpos m).ne'⟩
  -- Step 1: the `X_G` difference quotients converge in `L²`, hence in measure
  have hQ : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1))⁻¹ : ℝ) •
      (V (θ + 1 / ((m : ℝ) + 1)) - V θ)) atTop (𝓝 (deriv V θ)) :=
    (hasDerivAt_iff_tendsto_slope_zero.mp hVd').comp hseq
  have hmeas := tendstoInMeasure_of_tendsto_Lp hQ
  -- Step 2: an a.e.-convergent subsequence
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- Step 3: for each `m`, the quotient of `V` is a.e. the quotient of `W`
  have hQae : ∀ m : ℕ, ∀ᵐ r ∂xGMeasure,
      (((1 / ((m : ℝ) + 1))⁻¹ : ℝ) • (V (θ + 1 / ((m : ℝ) + 1)) - V θ) : XG) r =
        ((1 / ((m : ℝ) + 1))⁻¹ : ℝ) • (W (θ + 1 / ((m : ℝ) + 1)) r - W θ r) := by
    intro m
    have hp := hpos m
    filter_upwards [Lp.coeFn_smul ((1 / ((m : ℝ) + 1))⁻¹ : ℝ) (V (θ + 1 / ((m : ℝ) + 1)) - V θ),
      Lp.coeFn_sub (V (θ + 1 / ((m : ℝ) + 1))) (V θ),
      hWV (θ + 1 / ((m : ℝ) + 1)) (by linarith), hWV θ hθ] with r e1 e2 e3 e4
    simp only [Pi.smul_apply, Pi.sub_apply] at e1 e2
    rw [e1, e2, e3, e4]
  have hall : ∀ᵐ r ∂xGMeasure, ∀ m : ℕ,
      (((1 / ((m : ℝ) + 1))⁻¹ : ℝ) • (V (θ + 1 / ((m : ℝ) + 1)) - V θ) : XG) r =
        ((1 / ((m : ℝ) + 1))⁻¹ : ℝ) • (W (θ + 1 / ((m : ℝ) + 1)) r - W θ r) :=
    ae_all_iff.2 hQae
  -- Step 4: for `r > 0` the quotients of `W` converge pointwise to `∂_θ W(θ, r)`
  have hWr : ∀ r : ℝ, 0 < r → Tendsto (fun m : ℕ =>
      ((1 / ((m : ℝ) + 1))⁻¹ : ℝ) • (W (θ + 1 / ((m : ℝ) + 1)) r - W θ r)) atTop
      (𝓝 (deriv (fun t => W t r) θ)) := by
    intro r hr
    have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).prod isOpen_Ioi
    have hmem : (θ, r) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
      mk_mem_prod (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr hr)
    have hg : DifferentiableAt ℝ (fun z : ℝ × ℝ => W z.1 z.2) (θ, r) :=
      (hWsm.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
    have hφ : DifferentiableAt ℝ (fun t : ℝ => (t, r)) θ := by fun_prop
    have hcomp : DifferentiableAt ℝ ((fun z : ℝ × ℝ => W z.1 z.2) ∘ fun t : ℝ => (t, r)) θ :=
      DifferentiableAt.comp θ hg hφ
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => W t r) θ := hcomp
    exact (hasDerivAt_iff_tendsto_slope_zero.mp hdiff.hasDerivAt).comp hseq
  -- Step 5: off a null set, the a.e. limits agree; uniqueness of limits gives the identity
  filter_upwards [hae, hall, UnforcedLeray.B0012.ae_xG_pos] with r hr1 hr2 hr3
  have hlim : Tendsto (fun i : ℕ =>
      ((1 / ((ns i : ℝ) + 1))⁻¹ : ℝ) • (W (θ + 1 / ((ns i : ℝ) + 1)) r - W θ r)) atTop
      (𝓝 (⇑(deriv V θ) r)) :=
    Tendsto.congr (fun i => hr2 (ns i)) hr1
  have hW : Tendsto (fun i : ℕ =>
      ((1 / ((ns i : ℝ) + 1))⁻¹ : ℝ) • (W (θ + 1 / ((ns i : ℝ) + 1)) r - W θ r)) atTop
      (𝓝 (deriv (fun t => W t r) θ)) :=
    (hWr r hr3).comp hns.tendsto_atTop
  exact tendsto_nhds_unique hW hlim

end UnforcedLeray.Short.Spine
