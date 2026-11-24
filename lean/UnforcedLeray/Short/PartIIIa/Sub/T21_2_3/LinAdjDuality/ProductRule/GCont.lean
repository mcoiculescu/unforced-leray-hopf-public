import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.GCont_4

/-!
# Continuity of the cut Lagrangian `G` (`PartIII-a:T21/2/3/1/5/3`, SP 3074-3075)

`ladG tr w u φ R (σ, ρ) = ∫_{C_c} ladFlowCx (w σ) (u σ) σ (χ_R φ(ρ))` is split, pointwise on the
cell, as `w σ · ζ_R · T - Σ_j u_j(σ) · D_j` where `T = ν Δ Ψ + v(σ)·∇Ψ`, `D_j = ∂_j E(σ) Ψ`,
`Ψ = χ_R φ(ρ)`, and `ζ_R` is the indicator of the strip `|η| ≤ 2R`. The three integrals are
continuous on `[t, r]²` by the parametric cell-integral lemma `cell_integral_mul_continuousOn`
(`GCont_1`) applied to the strip-cut weighted flow and the velocity (`ladPR_w_u_L2_cont`,
`GCont_2`) and to the joint continuous factors `T`, `D_j`. The factors are clamped in the cell
variable (`clampQ`) so that they are bounded on all of `ℝ²`; on the cell the clamp is the identity.
The joint continuity of the spatial derivatives of `χ_R φ` uses the within-set derivative on
`[t, r] × ℝ²` (`pdCx_slice`, as in `GCont_3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GContAux

/-- The fixed-time slice derivative of `Φ(ρ, ·)` equals the within-`A ×ˢ univ` derivative of `Φ`
in the direction `(0, e)`. -/
lemma slice_fderiv_eq {A : Set ℝ} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : DifferentiableOn ℝ Φ (A ×ˢ univ)) {ρ : ℝ} (hρ : ρ ∈ A) (z e : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => Φ (ρ, y)) z e = fderivWithin ℝ Φ (A ×ˢ univ) (ρ, z) (0, e) := by
  have hdiff : DifferentiableWithinAt ℝ Φ (A ×ˢ univ) (ρ, z) := hΦ (ρ, z) ⟨hρ, mem_univ z⟩
  have hline : HasFDerivAt (fun w : ℝ × ℝ => ((ρ, w) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hasFDerivAt_const ρ z).prodMk (hasFDerivAt_id z)
  have hmaps : MapsTo (fun w : ℝ × ℝ => ((ρ, w) : ℝ × (ℝ × ℝ))) univ (A ×ˢ univ) :=
    fun w _ => ⟨hρ, mem_univ w⟩
  have hc := hdiff.hasFDerivWithinAt.comp z hline.hasFDerivWithinAt hmaps
  have hF : HasFDerivAt (fun y : ℝ × ℝ => Φ (ρ, y))
      ((fderivWithin ℝ Φ (A ×ˢ univ) (ρ, z)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z :=
    hc.hasFDerivAt univ_mem
  rw [hF.fderiv]
  simp

lemma pdCx_slice {A : Set ℝ} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : DifferentiableOn ℝ Φ (A ×ˢ univ)) {ρ : ℝ} (hρ : ρ ∈ A) (k : Fin 2) (z : ℝ × ℝ) :
    pdCx k (fun y => Φ (ρ, y)) z = fderivWithin ℝ Φ (A ×ˢ univ) (ρ, z) (0, B0579.dir k) :=
  slice_fderiv_eq hΦ hρ z (B0579.dir k)

/-- Joint continuity of the first spatial derivative. -/
lemma cont_pdCx {A : Set ℝ} (hA : UniqueDiffOn ℝ (A ×ˢ (univ : Set (ℝ × ℝ))))
    {Φ : ℝ × (ℝ × ℝ) → ℂ} (hΦ : ContDiffOn ℝ 1 Φ (A ×ˢ univ)) (k : Fin 2) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => pdCx k (fun y => Φ (q.1, y)) q.2) (A ×ˢ univ) := by
  have h1 : ContinuousOn (fderivWithin ℝ Φ (A ×ˢ univ)) (A ×ˢ univ) :=
    hΦ.continuousOn_fderivWithin hA (by norm_num)
  have h2 := (ContinuousLinearMap.apply ℝ ℂ (0, B0579.dir k)).continuous.comp_continuousOn h1
  refine h2.congr ?_
  intro q hq
  exact pdCx_slice (hΦ.differentiableOn (by norm_num)) hq.1 k q.2

/-- Joint continuity of the second spatial derivative `∂_k ∂_j Φ`. -/
lemma cont_pdCx_pdCx {A : Set ℝ} (hA : UniqueDiffOn ℝ (A ×ˢ (univ : Set (ℝ × ℝ))))
    {Φ : ℝ × (ℝ × ℝ) → ℂ} (hΦ : ContDiffOn ℝ 2 Φ (A ×ˢ univ)) (j k : Fin 2) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => pdCx k (fun y => pdCx j (fun x => Φ (q.1, x)) y) q.2)
      (A ×ˢ univ) := by
  have hfd : ContDiffOn ℝ 1 (fderivWithin ℝ Φ (A ×ˢ univ)) (A ×ˢ univ) :=
    hΦ.fderivWithin hA (by norm_num)
  have hap : ContDiffOn ℝ 1
      (fun q : ℝ × (ℝ × ℝ) => fderivWithin ℝ Φ (A ×ˢ univ) q (0, B0579.dir j)) (A ×ˢ univ) :=
    hfd.clm_apply contDiffOn_const
  have hΨ : ContDiffOn ℝ 1 (fun q : ℝ × (ℝ × ℝ) => pdCx j (fun x => Φ (q.1, x)) q.2) (A ×ˢ univ) :=
    hap.congr (fun q hq => pdCx_slice (hΦ.differentiableOn (by norm_num)) hq.1 j q.2)
  exact (cont_pdCx hA hΨ k).congr (fun q _ => rfl)

lemma isOpen_outside (R : ℝ) : IsOpen {y : ℝ × ℝ | 2 * R < |y.2|} :=
  isOpen_lt continuous_const (continuous_abs.comp continuous_snd)

lemma pdCx_zero_of_open {U : Set (ℝ × ℝ)} (hU : IsOpen U) {Ψ : ℝ × ℝ → ℂ}
    (h0 : ∀ y ∈ U, Ψ y = 0) (k : Fin 2) {x : ℝ × ℝ} (hx : x ∈ U) : pdCx k Ψ x = 0 := by
  have hev : Ψ =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := Filter.eventually_of_mem (hU.mem_nhds hx) h0
  unfold pdCx
  rw [hev.fderiv_eq]
  simp

lemma pdCx_zero_on_open {R : ℝ} {Ψ : ℝ × ℝ → ℂ} (hΨ : ∀ y : ℝ × ℝ, 2 * R < |y.2| → Ψ y = 0)
    (k : Fin 2) (x : ℝ × ℝ) (hx : 2 * R < |x.2|) : pdCx k Ψ x = 0 :=
  pdCx_zero_of_open (isOpen_outside R) (fun y hy => hΨ y hy) k hx

/-- The support of the spatial second derivative: `ν Δ Ψ + v·∇Ψ` vanishes off the strip. -/
lemma ladTf_zero_of {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (R σ : ℝ)
    (Ψ : ℝ × ℝ → ℂ) (hΨ : ∀ y : ℝ × ℝ, 2 * R < |y.2| → Ψ y = 0) (x : ℝ × ℝ)
    (hx : 2 * R < |x.2|) :
    (ν : ℂ) * ladLapCx Ψ x + ladTransport tr σ Ψ x = 0 := by
  have hk : ∀ j k : Fin 2, pdCx k (pdCx j Ψ) x = 0 := fun j k =>
    pdCx_zero_of_open (isOpen_outside R) (fun y hy => pdCx_zero_on_open hΨ j y hy) k hx
  unfold ladLapCx ladTransport
  rw [hk 0 0, hk 1 1, pdCx_zero_on_open hΨ 0 x hx, pdCx_zero_on_open hΨ 1 x hx]
  simp

/-- The joint factor `T(σ, ρ, x) = ν Δ Ψ_ρ + v(σ)·∇Ψ_ρ`, `Ψ_ρ = χ_R φ(ρ)`. -/
def ladTf {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ → ℝ × ℝ → ℂ) (R : ℝ)
    (p : ℝ × ℝ) (x : ℝ × ℝ) : ℂ :=
  (ν : ℂ) * ladLapCx (ladCutPhi φ R p.2) x + ladTransport tr p.1 (ladCutPhi φ R p.2) x

/-- The joint factor `D_j(σ, ρ, x) = ∂_j E(σ)(x) · Ψ_ρ(x)`. -/
def ladDf {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ → ℝ × ℝ → ℂ) (R : ℝ)
    (j : Fin 2) (p : ℝ × ℝ) (x : ℝ × ℝ) : ℂ :=
  ((B0579.pd j (UnforcedLeray.B0238.Ec tr p.1) x : ℝ) : ℂ) * ladCutPhi φ R p.2 x

lemma ladFlowCx_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ)
    (uu : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ) (Ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ladFlowCx tr om uu ρ Ψ x = om x * ((ν : ℂ) * ladLapCx Ψ x + ladTransport tr ρ Ψ x) -
      (uu x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) * Ψ x) +
        uu x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) * Ψ x)) := by
  unfold ladFlowCx ladForce
  ring

/-- Clamp of the cell variable: the first coordinate is clamped to `[-c/2, c/2]`. -/
def clampQ (c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (max (-(c / 2)) (min (c / 2) x.1), x.2)

lemma clampQ_cont (c : ℝ) : Continuous (clampQ c) :=
  (continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd

lemma clampQ_of_mem_cell {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) : clampQ c x = x := by
  have h1 : min (c / 2) x.1 = x.1 := min_eq_right hx.1.2.le
  have h2 : max (-(c / 2)) x.1 = x.1 := max_eq_right hx.1.1
  simp [clampQ, h1, h2]

/-- Clamping keeps the factor continuous, strip-supported and bounded on all of `ℝ²`. -/
lemma clamp_facts {c R : ℝ} (hc : 0 ≤ c) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    {T : ℝ × ℝ → ℝ × ℝ → ℂ}
    (hT : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 z.2) (S ×ˢ univ))
    (hsupp : ∀ p ∈ S, ∀ x : ℝ × ℝ, 2 * R < |x.2| → T p x = 0) :
    ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => T z.1 (clampQ c z.2)) (S ×ˢ univ) ∧
    (∀ p ∈ S, ∀ x : ℝ × ℝ, 2 * R < |x.2| → T p (clampQ c x) = 0) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S, ∀ x : ℝ × ℝ, ‖T p (clampQ c x)‖ ≤ M := by
  refine ⟨?_, ?_, ?_⟩
  · have hmap : ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1, clampQ c z.2)) (S ×ˢ univ) :=
      (continuous_fst.prodMk ((clampQ_cont c).comp continuous_snd)).continuousOn
    exact hT.comp hmap (fun z hz => Set.mk_mem_prod hz.1 (mem_univ _))
  · intro p hp x hx
    exact hsupp p hp (clampQ c x) hx
  · obtain ⟨C, hC⟩ := (hS.prod (B0579.isCompact_box c (2 * R))).exists_bound_of_continuousOn
      (hT.mono (prod_mono subset_rfl (subset_univ _)))
    refine ⟨max C 0, le_max_right _ _, fun p hp x => ?_⟩
    by_cases hx : 2 * R < |x.2|
    · rw [hsupp p hp (clampQ c x) hx]
      simp
    · have hm : clampQ c x ∈ B0579.box c (2 * R) := by
        simp only [B0579.box, clampQ, Set.mem_prod, Set.mem_Icc]
        refine ⟨⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩, ?_⟩
        exact abs_le.1 (not_lt.1 hx)
      exact (hC (p, clampQ c x) (Set.mk_mem_prod hp hm)).trans (le_max_left _ _)

/-- Strip cut-off of a weighted `L²` function is `L²` on the cell. -/
lemma memLp_strip {c m L : ℝ} {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => g x * (if |x.2| ≤ L then (1 : ℂ) else 0)) 2
      (volume.restrict (B0579.cell c)) := by
  obtain ⟨κ, hκ, hκle⟩ := GCont2Aux.exists_jb_lower c L m
  have hA := PairContAux.memLp_scaled hg
  have hmeas : Measurable (fun x : ℝ × ℝ => (if |x.2| ≤ L then (1 : ℂ) else 0)) :=
    Measurable.ite (measurableSet_le (continuous_abs.comp continuous_snd).measurable
      measurable_const) measurable_const measurable_const
  have hinv : Continuous (fun x : ℝ × ℝ => (((B0579.jb x ^ (m / 2) : ℝ) : ℂ))⁻¹) :=
    (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow (m / 2))).inv₀ (fun x => by
      show ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (B0579.jb_pos x) _).ne')
  refine ⟨?_, ?_⟩
  · refine AEStronglyMeasurable.congr
      (((hinv.aestronglyMeasurable).mul hmeas.aestronglyMeasurable).mul hA.1)
      (ae_of_all _ fun x => ?_)
    have hne : (((B0579.jb x ^ (m / 2) : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (B0579.jb_pos x) _).ne'
    show (((B0579.jb x ^ (m / 2) : ℝ) : ℂ))⁻¹ * (if |x.2| ≤ L then (1 : ℂ) else 0) *
        (((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x) = g x * (if |x.2| ≤ L then (1 : ℂ) else 0)
    rw [show (((B0579.jb x ^ (m / 2) : ℝ) : ℂ))⁻¹ * (if |x.2| ≤ L then (1 : ℂ) else 0) *
        (((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x) =
        ((((B0579.jb x ^ (m / 2) : ℝ) : ℂ))⁻¹ * ((B0579.jb x ^ (m / 2) : ℝ) : ℂ)) *
          (g x * (if |x.2| ≤ L then (1 : ℂ) else 0)) by ring, inv_mul_cancel₀ hne, one_mul]
  · have hfin := GCont2Aux.strip_le hκ hκle g
    exact lt_of_le_of_lt hfin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2)

/-- Joint continuity of the factors `T` and `D_j` on `[t, r]² × ℝ²`. -/
lemma blocks_cont {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {φ : ℝ → ℝ × ℝ → ℂ}
    {R t r s : ℝ} (hR : 0 < R)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hrs : r < s) (ht0 : 0 ≤ t) (htr : t < r) :
    ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ladTf tr φ R z.1 z.2)
        ((Icc t r ×ˢ Icc t r) ×ˢ univ) ∧
      ∀ j : Fin 2, ContinuousOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ladDf tr φ R j z.1 z.2)
        ((Icc t r ×ˢ Icc t r) ×ˢ univ) := by
  have hQu : UniqueDiffOn ℝ (Icc t r ×ˢ (univ : Set (ℝ × ℝ))) :=
    (uniqueDiffOn_Icc htr).prod uniqueDiffOn_univ
  have hΦ2 : ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => ladCutPhi φ R q.1 q.2)
      (Icc t r ×ˢ univ) :=
    (ladCutPhi_jointC2 (c := c) hR hφs hrs).1
  have hΦ1 : ContDiffOn ℝ 1 (fun q : ℝ × (ℝ × ℝ) => ladCutPhi φ R q.1 q.2)
      (Icc t r ×ˢ univ) :=
    hΦ2.of_le (by norm_num)
  have hMc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((z.1.2, z.2) : ℝ × (ℝ × ℝ))) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hMmap : MapsTo (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((z.1.2, z.2) : ℝ × (ℝ × ℝ)))
      ((Icc t r ×ˢ Icc t r) ×ˢ univ) (Icc t r ×ˢ univ) :=
    fun z hz => Set.mk_mem_prod hz.1.2 (mem_univ _)
  have hVc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((z.1.1, z.2) : ℝ × (ℝ × ℝ))) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hVmap : MapsTo (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((z.1.1, z.2) : ℝ × (ℝ × ℝ)))
      ((Icc t r ×ˢ Icc t r) ×ˢ univ) (Ici 0 ×ˢ univ) :=
    fun z hz => Set.mk_mem_prod (show (0 : ℝ) ≤ z.1.1 from ht0.trans hz.1.1.1) (mem_univ _)
  have hLap := ((cont_pdCx_pdCx hQu hΦ2 0 0).add (cont_pdCx_pdCx hQu hΦ2 1 1)).comp
    hMc.continuousOn hMmap
  have hPD : ∀ k : Fin 2, ContinuousOn
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => pdCx k (ladCutPhi φ R z.1.2) z.2)
      ((Icc t r ×ˢ Icc t r) ×ˢ univ) := fun k =>
    (cont_pdCx hQu hΦ1 k).comp hMc.continuousOn hMmap
  have hV : ∀ k : Fin 2, ContinuousOn
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((tr.v z.1.1 z.2 k : ℝ) : ℂ))
      ((Icc t r ×ˢ Icc t r) ×ˢ univ) := fun k =>
    Complex.continuous_ofReal.comp_continuousOn
      (((continuous_apply k).comp (PiLp.continuous_ofLp _ _)).comp_continuousOn
        ((train_joint_cont tr).1.comp hVc.continuousOn hVmap))
  have hTf0 := ((continuousOn_const (c := (ν : ℂ))).mul hLap).add
    (((hV 0).mul (hPD 0)).add ((hV 1).mul (hPD 1)))
  have hD0 := fun j : Fin 2 => (Complex.continuous_ofReal.comp_continuousOn
        (((train_joint_cont tr).2 j).comp hVc.continuousOn hVmap)).mul
        (hΦ2.continuousOn.comp hMc.continuousOn hMmap)
  refine ⟨hTf0.congr (fun z _ => rfl), fun j => (hD0 j).congr (fun z _ => rfl)⟩

end GContAux

set_option maxHeartbeats 1000000 in
open GContAux in
/-- **Assembly** (`PartIII-a:T21/2/3/1/5/3`): joint continuity of `G` on `[t, r]²`. -/
theorem ladPRG : LadPRG := by
  intro ν c m tr t s f w u φ hS R hR r hr
  rcases eq_or_lt_of_le hr.1 with htr | htr
  · subst htr
    rw [Icc_self, Set.singleton_prod_singleton]
    exact continuousOn_singleton _ _
  have hrs : r < s := hr.2
  have hφs := hS.smooth
  have ht0 : (0 : ℝ) ≤ t := hS.ht
  have hc0 : (0 : ℝ) ≤ c := hS.hc.le
  have hSc : IsCompact (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hzero : ∀ ρ : ℝ, ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCutPhi φ R ρ x = 0 := fun ρ x hx => by
    unfold ladCutPhi
    rw [LadPRPairAux.cut_zero hR hx]
    simp
  obtain ⟨hTf, hDc⟩ := blocks_cont tr hR hφs hrs ht0 htr
  -- clamping in the cell variable
  obtain ⟨hTc', hTs', M, hM0, hTb⟩ :=
    clamp_facts (T := ladTf tr φ R) hc0 hSc hTf
      (fun p _ x hx => ladTf_zero_of tr R p.1 (ladCutPhi φ R p.2) (fun y hy => hzero p.2 y hy) x hx)
  obtain ⟨hD0c, hD0s, M0, hM00, hD0b⟩ :=
    clamp_facts (T := ladDf tr φ R 0) hc0 hSc (hDc 0)
      (fun p _ x hx => by unfold ladDf; rw [hzero p.2 x hx, mul_zero])
  obtain ⟨hD1c, hD1s, M1, hM10, hD1b⟩ :=
    clamp_facts (T := ladDf tr φ R 1) hc0 hSc (hDc 1)
      (fun p _ x hx => by unfold ladDf; rw [hzero p.2 x hx, mul_zero])
  -- integrability and `L²` data
  have hFw_mem : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) 2
        (volume.restrict (B0579.cell c)) :=
    fun p hp => memLp_strip (L := 2 * R) (hS.flow.memX p.1 hp.1.1)
  have hU_mem : ∀ j : Fin 2, ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => u p.1 x j) 2 (volume.restrict (B0579.cell c)) := by
    intro j p hp
    have hbs := hS.flow.biotSavart p.1 hp.1.1
    unfold IsBiotSavart at hbs
    exact hbs.1 j
  have hFw0 : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) 2
        (B0579.cellMeasure c 0) := fun p hp => by
    rw [GCont1Aux.cellMeasure_zero]
    exact hFw_mem p hp
  have hU0 : ∀ j : Fin 2, ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => u p.1 x j) 2 (B0579.cellMeasure c 0) := fun j p hp => by
    rw [GCont1Aux.cellMeasure_zero]
    exact hU_mem j p hp
  have hT_mem : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => ladTf tr φ R p (clampQ c x)) 2 (B0579.cellMeasure c 0) := fun p hp =>
    GCont1Aux.memLp_T (c := c) (T := fun p x => ladTf tr φ R p (clampQ c x)) hTs' hTb hTc' hp hM0
  have hD0_mem : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => ladDf tr φ R 0 p (clampQ c x)) 2 (B0579.cellMeasure c 0) := fun p hp =>
    GCont1Aux.memLp_T (c := c) (T := fun p x => ladDf tr φ R 0 p (clampQ c x)) hD0s hD0b hD0c
      hp hM00
  have hD1_mem : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      MemLp (fun x => ladDf tr φ R 1 p (clampQ c x)) 2 (B0579.cellMeasure c 0) := fun p hp =>
    GCont1Aux.memLp_T (c := c) (T := fun p x => ladDf tr φ R 1 p (clampQ c x)) hD1s hD1b hD1c
      hp hM10
  -- pointwise splitting on the cell
  have hpt : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)), ∀ x ∈ B0579.cell c,
      ladFlowCx tr (w p.1) (u p.1) p.1 (ladCutPhi φ R p.2) x =
        (w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) * ladTf tr φ R p (clampQ c x) -
          (u p.1 x 0 * ladDf tr φ R 0 p (clampQ c x) +
            u p.1 x 1 * ladDf tr φ R 1 p (clampQ c x)) := by
    intro p _ x hx
    rw [clampQ_of_mem_cell hx, ladFlowCx_eq]
    by_cases h2 : |x.2| ≤ 2 * R
    · rw [if_pos h2, mul_one]
      unfold ladTf ladDf
      ring
    · have hx2 : 2 * R < |x.2| := lt_of_not_ge h2
      have h0 : ladCutPhi φ R p.2 x = 0 := hzero p.2 x hx2
      have hT0 : (ν : ℂ) * ladLapCx (ladCutPhi φ R p.2) x +
          ladTransport tr p.1 (ladCutPhi φ R p.2) x = 0 :=
        ladTf_zero_of tr R p.1 (ladCutPhi φ R p.2) (fun y hy => hzero p.2 y hy) x hx2
      rw [if_neg h2]
      unfold ladTf ladDf
      rw [hT0, h0]
      simp
  have hdec : ∀ p ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      ladG tr w u φ R p =
        (∫ x in B0579.cell c, (w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) *
            ladTf tr φ R p (clampQ c x)) -
          (∫ x in B0579.cell c, u p.1 x 0 * ladDf tr φ R 0 p (clampQ c x)) -
          (∫ x in B0579.cell c, u p.1 x 1 * ladDf tr φ R 1 p (clampQ c x)) := by
    intro p hp
    have hIA : IntegrableOn (fun x => (w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) *
        ladTf tr φ R p (clampQ c x)) (B0579.cell c) :=
      (GCont1Aux.holder0 (hFw0 p hp) (hT_mem p hp)).1
    have hI0 : IntegrableOn (fun x => u p.1 x 0 * ladDf tr φ R 0 p (clampQ c x))
        (B0579.cell c) :=
      (GCont1Aux.holder0 (hU0 0 p hp) (hD0_mem p hp)).1
    have hI1 : IntegrableOn (fun x => u p.1 x 1 * ladDf tr φ R 1 p (clampQ c x))
        (B0579.cell c) :=
      (GCont1Aux.holder0 (hU0 1 p hp) (hD1_mem p hp)).1
    unfold ladG
    have hsum : IntegrableOn (fun x => u p.1 x 0 * ladDf tr φ R 0 p (clampQ c x) +
        u p.1 x 1 * ladDf tr φ R 1 p (clampQ c x)) (B0579.cell c) := hI0.add hI1
    rw [setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => hpt p hp x hx),
      integral_sub hIA hsum, integral_add hI0 hI1]
    ring
  -- continuity of the three cell integrals
  have hFwc : ∀ p0 ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      Tendsto (fun p : ℝ × ℝ => eLpNorm ((fun x => w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0)) -
        (fun x => w p0.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0))) 2
          (volume.restrict (B0579.cell c)))
        (𝓝[Icc t r ×ˢ Icc t r] p0) (𝓝 0) := by
    intro p0 hp0
    have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[Icc t r ×ˢ Icc t r] p0) (𝓝[Ici t] p0.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun p hp => hp.1.1⟩
    exact ((ladPR_w_u_L2_cont hS (2 * R) p0.1 hp0.1.1).1).comp hf
  have hUc : ∀ j : Fin 2, ∀ p0 ∈ (Icc t r ×ˢ Icc t r : Set (ℝ × ℝ)),
      Tendsto (fun p : ℝ × ℝ => eLpNorm ((fun x => u p.1 x j) - (fun x => u p0.1 x j)) 2
          (volume.restrict (B0579.cell c)))
        (𝓝[Icc t r ×ˢ Icc t r] p0) (𝓝 0) := by
    intro j p0 hp0
    have hf : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[Icc t r ×ˢ Icc t r] p0) (𝓝[Ici t] p0.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun p hp => hp.1.1⟩
    exact ((ladPR_w_u_L2_cont hS (2 * R) p0.1 hp0.1.1).2 j).comp hf
  have hIW := cell_integral_mul_continuousOn c (2 * R) M (Icc t r ×ˢ Icc t r)
    (fun p x => w p.1 x * (if |x.2| ≤ 2 * R then (1 : ℂ) else 0))
    (fun p x => ladTf tr φ R p (clampQ c x)) hFw_mem hFwc hTc' hTs' hTb
  have hI0 := cell_integral_mul_continuousOn c (2 * R) M0 (Icc t r ×ˢ Icc t r)
    (fun p x => u p.1 x 0) (fun p x => ladDf tr φ R 0 p (clampQ c x))
    (fun p hp => hU_mem 0 p hp) (hUc 0) hD0c hD0s hD0b
  have hI1 := cell_integral_mul_continuousOn c (2 * R) M1 (Icc t r ×ˢ Icc t r)
    (fun p x => u p.1 x 1) (fun p x => ladDf tr φ R 1 p (clampQ c x))
    (fun p hp => hU_mem 1 p hp) (hUc 1) hD1c hD1s hD1b
  exact ((hIW.sub hI0).sub hI1).congr (fun p hp => hdec p hp)

end UnforcedLeray.Short.IIIa
