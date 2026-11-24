import UnforcedLeray.Short.PartI.Sub.PartI_T21_2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# `PartI:T21/2/2` (`Sub/PartI_T21_2/FluctJetWSupNorm.lean`): `wSupNorm` stability of horizontal fluctuations

Source of record: `the November 2 reference manuscript`, lines 499-526 (old 493-515).

Proves `trainFluctJetWSupNormLe_proof : TrainFluctJetWSupNormLe`: for a BUC train `tr` at age `s > 0`,
`tr.ψ` and `tr.v` are jointly `C^∞` on `(0, ∞) × Plane`; differentiating `hmean c` under the compact
horizontal integral over `Ioc (-c/2) (c/2)` shows that `ageJet ℓ j` of `(r, z) ↦ hmean c (f r) z.2`
has weighted sup-norm bounded by `wSupNorm m (ageJet ℓ j f s)`, so the triangle inequality gives
`wSupNorm m (ageJet ℓ j (f - hmean c f) s) ≤ ENNReal.ofReal (2 * B)` for scalar fields and
`≤ ENNReal.ofReal (4 * B)` for `Vec`-valued fields via coordinate decomposition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet jap)

namespace PartI_T21_2

/-- Expresses the `n`-th age derivative of a jointly `C^∞` family `K : ℝ × V → E` at `s > 0`
as the `n`-th Fréchet derivative applied to `(1, 0)`. -/
private theorem slice_iteratedDeriv_eq {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℝ × V → E) (hK : ContDiffOn ℝ ∞ K (Ioi 0 ×ˢ univ)) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (w : V) :
    iteratedDeriv n (fun r => K (r, w)) s = iteratedFDeriv ℝ n K (s, w) (fun _ => (1, 0)) := by
  have hopen : IsOpen {p : ℝ × V | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hmaps : MapsTo (fun p : ℝ × V => p + ((0 : ℝ), w)) {p : ℝ × V | 0 < p.1}
      (Ioi 0 ×ˢ (univ : Set V)) :=
    fun p hp => ⟨by simpa using hp, Set.mem_univ _⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × V => K (p + ((0 : ℝ), w))) {p : ℝ × V | 0 < p.1} :=
    hK.comp (contDiff_id.add contDiff_const).contDiffOn hmaps
  have hfun : (fun r : ℝ => K (r, w)) =
      (fun p : ℝ × V => K (p + ((0 : ℝ), w))) ∘ (ContinuousLinearMap.inl ℝ ℝ V) := by
    funext r
    simp
  have hL : ContinuousLinearMap.inl ℝ ℝ V s ∈ {p : ℝ × V | 0 < p.1} := by simpa using hs
  have hpre : IsOpen ((ContinuousLinearMap.inl ℝ ℝ V) ⁻¹' {p : ℝ × V | 0 < p.1}) :=
    hopen.preimage (ContinuousLinearMap.continuous _)
  have hs_pre : s ∈ (ContinuousLinearMap.inl ℝ ℝ V) ⁻¹' {p : ℝ × V | 0 < p.1} := hL
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inl ℝ ℝ V) hsmooth hopen.uniqueDiffOn hpre.uniqueDiffOn hL
    (i := n) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hopen hL,
    iteratedFDerivWithin_of_isOpen n hpre hs_pre] at hcomp
  have hA : iteratedFDeriv ℝ n (fun p : ℝ × V => K (p + ((0 : ℝ), w)))
      (ContinuousLinearMap.inl ℝ ℝ V s) = iteratedFDeriv ℝ n K (s, w) := by
    simp [iteratedFDeriv_comp_add_right]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, hcomp, hA]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1

/-- Joint `C^∞` smoothness of `(s, w) ↦ iteratedDeriv n (fun r => F r w) s` on `(0, ∞) × Plane`. -/
private theorem contDiffOn_iteratedDeriv_age {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => iteratedDeriv n (fun r => F r x.2) x.1)
      (Ioi 0 ×ˢ univ) := by
  refine contDiffOn_infty.2 fun m x hx => ?_
  have hKa : ContDiffAt ℝ ∞ (fun y : ℝ × Plane => F y.1 y.2) x :=
    hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hx)
  have h1 : ContDiffAt ℝ m (iteratedFDeriv ℝ n (fun y : ℝ × Plane => F y.1 y.2)) x :=
    hKa.iteratedFDeriv_right (m := (m : WithTop ℕ∞)) (i := n) (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ m
      (fun y : ℝ × Plane =>
        iteratedFDeriv ℝ n (fun p : ℝ × Plane => F p.1 p.2) y (fun _ => (1, 0))) x :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × Plane) E
      (fun _ => (1, 0))).contDiff.contDiffAt).comp x h1
  refine h2.contDiffWithinAt.congr (fun y hy => ?_) ?_
  · exact slice_iteratedDeriv_eq (fun p : ℝ × Plane => F p.1 p.2) hF n hy.1 y.2
  · exact slice_iteratedDeriv_eq (fun p : ℝ × Plane => F p.1 p.2) hF n hx.1 x.2

/-- Spatial `C^∞` smoothness of `w ↦ iteratedDeriv n (fun r => F r w) s` at fixed `s > 0`. -/
private theorem contDiff_iteratedDeriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ)) (n : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv n (fun r => F r w) s) :=
  (contDiffOn_iteratedDeriv_age hF n).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun w => ⟨hs, mem_univ w⟩)

/-- Age `C^m` smoothness of `r ↦ F r w` at `s > 0`. -/
private theorem contDiffAt_age_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (w : Plane) (m : ℕ) :
    ContDiffAt ℝ m (fun r => F r w) s := by
  have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (s, w) :=
    hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  exact ContDiffAt.of_le (m := (m : WithTop ℕ∞))
    (h0.comp s (contDiffAt_id.prodMk contDiffAt_const)) (mod_cast le_top)

/-- Linearity of `ageJet ℓ j` over a difference of jointly smooth families at `s > 0`. -/
private theorem ageJet_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j (fun r w => F r w - G r w) s z =
      ageJet ℓ j F s z - ageJet ℓ j G s z := by
  have hsub : (fun w : Plane => iteratedDeriv ℓ (fun r => F r w - G r w) s) =
      (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) -
        (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) := by
    funext w
    exact iteratedDeriv_sub (contDiffAt_age_slice hF hs w ℓ) (contDiffAt_age_slice hG hs w ℓ)
  have hA : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) z :=
    ((contDiff_iteratedDeriv_slice hF ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  have hB : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) z :=
    ((contDiff_iteratedDeriv_slice hG ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w - G r w) s) z = _
  rw [hsub, iteratedFDeriv_sub_apply hA hB]

/-- Linearity of `ageJet ℓ j` over a sum of jointly smooth families at `s > 0`. -/
private theorem ageJet_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → Plane → E)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j (fun r w => F r w + G r w) s z =
      ageJet ℓ j F s z + ageJet ℓ j G s z := by
  have hadd : (fun w : Plane => iteratedDeriv ℓ (fun r => F r w + G r w) s) =
      (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) +
        (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) := by
    funext w
    exact iteratedDeriv_add (contDiffAt_age_slice hF hs w ℓ) (contDiffAt_age_slice hG hs w ℓ)
  have hA : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w) s) z :=
    ((contDiff_iteratedDeriv_slice hF ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  have hB : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => G r w) s) z :=
    ((contDiff_iteratedDeriv_slice hG ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => F r w + G r w) s) z = _
  rw [hadd, iteratedFDeriv_add_apply hA hB]

/-- Iterated age derivative commutes with a continuous linear map on jointly smooth families. -/
private theorem clm_ageJet_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {H : ℝ → Plane → E}
    (hH : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => H x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (z : Plane) :
    ageJet ℓ j (fun r w => L (H r w)) s z =
      L.compContinuousMultilinearMap (ageJet ℓ j H s z) := by
  have hLH : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => L (H x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    L.contDiff.comp_contDiffOn hH
  have hslice_eq : (fun w : Plane => iteratedDeriv ℓ (fun r => L (H r w)) s) =
      L ∘ (fun w : Plane => iteratedDeriv ℓ (fun r => H r w) s) := by
    funext w
    rw [Function.comp_apply, slice_iteratedDeriv_eq (fun x : ℝ × Plane => L (H x.1 x.2)) hLH ℓ hs w,
      slice_iteratedDeriv_eq (fun x : ℝ × Plane => H x.1 x.2) hH ℓ hs w]
    have hK : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => H x.1 x.2) (s, w) :=
      hH.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
    have hcomp := L.iteratedFDeriv_comp_left hK (i := ℓ) (by exact_mod_cast le_top)
    change iteratedFDeriv ℝ ℓ (L ∘ fun x : ℝ × Plane => H x.1 x.2) (s, w) (fun _ => (1, 0)) = _
    rw [hcomp]
    rfl
  have hG_sm : ContDiffAt ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => H r w) s) z :=
    ((contDiff_iteratedDeriv_slice hH ℓ hs).contDiffAt).of_le (by exact_mod_cast le_top)
  unfold ageJet jet
  change iteratedFDeriv ℝ j (fun w : Plane => iteratedDeriv ℓ (fun r => L (H r w)) s) z = _
  rw [hslice_eq, L.iteratedFDeriv_comp_left hG_sm le_rfl]

/-- Iterated age derivative commutes with `hmean c` for jointly `C^∞` scalar families. -/
private theorem iteratedDeriv_hmean_scalar {c : ℝ} (hc : 0 < c) {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ (ℓ : ℕ) {s : ℝ}, 0 < s → ∀ η : ℝ,
      iteratedDeriv ℓ (fun r => hmean c (f r) η) s =
        hmean c (fun w => iteratedDeriv ℓ (fun r => f r w) s) η
  | 0, _, _, _ => rfl
  | ℓ + 1, s, hs, η => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => hmean c (f r) η) =ᶠ[𝓝 s]
        fun r => hmean c (fun w => iteratedDeriv ℓ (fun r' => f r' w) r) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using iteratedDeriv_hmean_scalar hc hf ℓ hr η
    rw [hev.deriv_eq, hmeanDerivS c hc (fun r w => iteratedDeriv ℓ (fun r' => f r' w) r)
      (contDiffOn_iteratedDeriv_age hf ℓ) s hs η]
    simp only [iteratedDeriv_succ]

/-- The projection `(x, y) ↦ (0, y)` on `Plane` as a continuous linear map of norm `≤ 1`. -/
private def sndPlane : Plane →L[ℝ] Plane :=
  (0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem sndPlane_apply (w : Plane) : sndPlane w = (0, w.2) := rfl

private theorem norm_sndPlane_le_one : ‖sndPlane‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, sndPlane_apply, Prod.norm_def, Prod.norm_def, norm_zero]
  exact max_le ((norm_nonneg w.1).trans (le_max_left _ _)) (le_max_right _ _)

/-- Slice formula for `w' ↦ G (q, w'.2)`: the `n`-th derivative is `(D^n G (q, w.2))` composed
with `sndPlane`. -/
private theorem slice_snd_iteratedFDeriv {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w =
      (iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap
        (fun _ : Fin n => sndPlane) := by
  have hsmooth : ContDiff ℝ ∞ (fun z : Plane => G (z + (q, 0))) :=
    hG.comp (contDiff_id.add contDiff_const)
  have hfun : (fun w' : Plane => G (q, w'.2)) =
      (fun z : Plane => G (z + (q, 0))) ∘ sndPlane := by
    funext w'
    simp [sndPlane_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    sndPlane hsmooth w (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hw : sndPlane w + (q, 0) = (q, w.2) := by ext <;> simp [sndPlane_apply]
  rw [hw]

/-- Norm bound `‖iteratedFDeriv ℝ n (fun w' => G (q, w'.2)) w‖ ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖`. -/
private theorem norm_slice_snd_iteratedFDeriv_le {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ) (n : ℕ) (w : Plane) :
    ‖iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w‖ ≤
      ‖iteratedFDeriv ℝ n G (q, w.2)‖ := by
  rw [slice_snd_iteratedFDeriv hG q n w]
  have hprod : ∏ _i : Fin n, ‖sndPlane‖ ≤ 1 := by
    calc ∏ _i : Fin n, ‖sndPlane‖
        ≤ ∏ _i : Fin n, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_sndPlane_le_one)
      _ = 1 := Finset.prod_const_one
  calc ‖(iteratedFDeriv ℝ n G (q, w.2)).compContinuousLinearMap (fun _ => sndPlane)‖
      ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * ∏ _i : Fin n, ‖sndPlane‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n G (q, w.2)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n G (q, w.2)‖ := mul_one _

/-- Continuity in `q` of `iteratedFDeriv ℝ n (fun w' => G (q, w'.2)) w`. -/
private theorem slice_snd_continuous {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (w : Plane) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n G (q, w.2)) :=
    (hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => sndPlane)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => sndPlane)).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (slice_snd_iteratedFDeriv hG q n w).symm

/-- Local domination of `(q, w) ↦ G (q, w.2)` on `Plane` for `q ∈ Ioc (-c/2) (c/2)`. -/
private theorem slice_snd_locDominated {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G) (c : ℝ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (w : Plane) => G (q, w.2)) univ := by
  intro n x _
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (fun p : ℝ × Plane => iteratedFDeriv ℝ n G (p.1, p.2.2))
      (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    ((hG.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C, integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  exact (norm_slice_snd_iteratedFDeriv_le hG q n y).trans (hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩)

/-- For smooth `G : Plane → ℝ` and `c > 0`, `‖jet j (fun w => hmean c G w.2) z‖` is bounded by
`c⁻¹ * ∫ q in Ioc (-c/2) (c/2), ‖jet j (fun w => G (q, w.2)) z‖`. -/
private theorem norm_jet_hmean_scalar_le {c : ℝ} (hc : 0 < c) {G : Plane → ℝ}
    (hG : ContDiff ℝ ∞ G) (j : ℕ) (z : Plane) :
    ‖jet j (fun w : Plane => hmean c G w.2) z‖ ≤
      c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2),
        ‖iteratedFDeriv ℝ j (fun w : Plane => G (q, w.2)) z‖ := by
  let μ : Measure ℝ := volume.restrict (Ioc (-c / 2) (c / 2))
  let S : ℝ →L[ℝ] ℝ := c⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let I : Plane → ℝ := fun w => ∫ q, G (q, w.2) ∂μ
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun w : Plane => G (q, w.2)) :=
    fun _ => hG.comp (contDiff_const.prodMk contDiff_snd)
  have hmeas : ∀ (n : ℕ) (w : Plane),
      AEStronglyMeasurable (fun q => iteratedFDeriv ℝ n (fun w' : Plane => G (q, w'.2)) w) μ :=
    fun n w => (slice_snd_continuous hG n w).aestronglyMeasurable
  have hdom := slice_snd_locDominated hG c
  have hI_cd : ContDiffOn ℝ ∞ I univ :=
    UnforcedLeray.Kernels.contDiffOn_integral isOpen_univ (ae_of_all _ hsmooth) hmeas hdom
  have hI_at : ContDiffAt ℝ j I z :=
    (hI_cd.contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).of_le (by exact_mod_cast le_top)
  have hfun : (fun w : Plane => hmean c G w.2) = S ∘ I := rfl
  unfold jet
  rw [hfun, S.iteratedFDeriv_comp_left hI_at le_rfl]
  have hS_norm : ‖S‖ ≤ c⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) fun x => ?_
    simp [S, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  have hint_le := UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le isOpen_univ
    (ae_of_all _ hsmooth) hmeas hdom j (mem_univ z)
  calc ‖S.compContinuousMultilinearMap (iteratedFDeriv ℝ j I z)‖
      ≤ ‖S‖ * ‖iteratedFDeriv ℝ j I z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ c⁻¹ * (∫ q, ‖iteratedFDeriv ℝ j (fun w : Plane => G (q, w.2)) z‖ ∂μ) :=
        mul_le_mul hS_norm hint_le (norm_nonneg _) (inv_nonneg.2 hc.le)

/-- **Scalar horizontal fluctuation bound**: for a jointly `C^∞` scalar family `f : ℝ → Plane → ℝ`,
if `wSupNorm m (ageJet ℓ j f s) ≤ ENNReal.ofReal B` at `s > 0`, then
`wSupNorm m (ageJet ℓ j (fun r z => f r z - hmean c (f r) z.2) s) ≤ ENNReal.ofReal (2 * B)`. -/
private theorem wSupNorm_ageJet_scalar_fluct_le {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (m ℓ j : ℕ) {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s)
    (hSup : wSupNorm m (ageJet ℓ j f s) ≤ ENNReal.ofReal B) :
    wSupNorm m (ageJet ℓ j (fun r z => f r z - hmean c (f r) z.2) s) ≤
      ENNReal.ofReal (2 * B) := by
  let G : Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => f r w) s
  have hG : ContDiff ℝ ∞ G := contDiff_iteratedDeriv_slice hf ℓ hs
  have hhm_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (f x.1) x.2.2) (Ioi 0 ×ˢ univ) := by
    have hm := hmeanContDiff c hc f hf
    have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
    exact hm.comp hproj.contDiffOn (fun x hx => ⟨hx.1, mem_univ _⟩)
  have hpt : ∀ w : Plane, Real.sqrt (jap m w) * ‖jet j G w‖ ≤ B := by
    intro w
    have hw : ENNReal.ofReal (Real.sqrt (jap m w)) * ‖ageJet ℓ j f s w‖ₑ ≤ ENNReal.ofReal B :=
      (le_iSup (fun z' : Plane => ENNReal.ofReal (Real.sqrt (jap m z')) *
        ‖ageJet ℓ j f s z'‖ₑ) w).trans hSup
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hw
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hw
  unfold wSupNorm
  refine iSup_le fun z => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [ageJet_sub f (fun r w => hmean c (f r) w.2) hf hhm_sm hs ℓ j z]
  have hhm_eq : ageJet ℓ j (fun r w => hmean c (f r) w.2) s z =
      jet j (fun w : Plane => hmean c G w.2) z := by
    unfold ageJet jet
    congr 1
    funext w
    exact iteratedDeriv_hmean_scalar hc hf ℓ hs w.2
  rw [hhm_eq]
  have hjap_pos : 0 < Real.sqrt (jap m z) := by
    apply Real.sqrt_pos.2
    unfold jap
    positivity
  have hslice_le : ∀ q ∈ Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ j (fun w : Plane => G (q, w.2)) z‖ ≤ B / Real.sqrt (jap m z) := by
    intro q _
    have h1 := norm_slice_snd_iteratedFDeriv_le hG q j z
    have h2 : ‖iteratedFDeriv ℝ j G (q, z.2)‖ ≤ B / Real.sqrt (jap m z) := by
      rw [le_div_iff₀ hjap_pos, mul_comm]
      have hjap_eq : jap m (q, z.2) = jap m z := rfl
      rw [← hjap_eq]
      exact hpt (q, z.2)
    exact h1.trans h2
  have hint_bound : ∫ q in Ioc (-c / 2) (c / 2),
      ‖iteratedFDeriv ℝ j (fun w : Plane => G (q, w.2)) z‖ ≤
        (B / Real.sqrt (jap m z)) * c := by
    have h0 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => ‖iteratedFDeriv ℝ j (fun w : Plane => G (q, w.2)) z‖)
      measure_Ioc_lt_top (fun q hq => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hslice_le q hq)
    rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring,
      Real.norm_eq_abs] at h0
    exact (le_abs_self _).trans h0
  have hmean_le : Real.sqrt (jap m z) * ‖jet j (fun w : Plane => hmean c G w.2) z‖ ≤ B := by
    have h1 := (norm_jet_hmean_scalar_le hc hG j z).trans
      (mul_le_mul_of_nonneg_left hint_bound (inv_nonneg.2 hc.le))
    have h2 : c⁻¹ * ((B / Real.sqrt (jap m z)) * c) = B / Real.sqrt (jap m z) := by
      have hc_ne : c ≠ 0 := hc.ne'
      field_simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hjap_pos.le
    rwa [mul_div_cancel₀ _ hjap_pos.ne'] at h3
  have htri : ‖ageJet ℓ j f s z - jet j (fun w : Plane => hmean c G w.2) z‖ ≤
      ‖ageJet ℓ j f s z‖ + ‖jet j (fun w : Plane => hmean c G w.2) z‖ :=
    norm_sub_le _ _
  calc Real.sqrt (jap m z) * ‖ageJet ℓ j f s z - jet j (fun w : Plane => hmean c G w.2) z‖
      ≤ Real.sqrt (jap m z) * (‖ageJet ℓ j f s z‖ + ‖jet j (fun w : Plane => hmean c G w.2) z‖) :=
        mul_le_mul_of_nonneg_left htri hjap_pos.le
    _ = Real.sqrt (jap m z) * ‖jet j G z‖ +
          Real.sqrt (jap m z) * ‖jet j (fun w : Plane => hmean c G w.2) z‖ :=
        mul_add _ _ _
    _ ≤ B + B := add_le_add (hpt z) hmean_le
    _ = 2 * B := by ring

/-- Coordinatewise `hmean c` for continuous vector fields `a : Plane → Vec`. -/
private theorem hmean_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (k : Fin 2) :
    (hmean c a η) k = hmean c (fun z => a z k) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- Embedding of the `k`-th coordinate into `Vec` via `Train.toVecL`, with operator norm `≤ 1`. -/
private def liftCoord (k : Fin 2) : ℝ →L[ℝ] Vec :=
  if k = 0 then (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
  else (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)

private theorem norm_liftCoord_le_one (k : Fin 2) : ‖liftCoord k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
  rw [one_mul, Real.norm_eq_abs]
  fin_cases k
  · change ‖Train.toVec (t, 0)‖ ≤ |t|
    rw [Train.norm_toVec]
    simp [Real.sqrt_sq_eq_abs]
  · change ‖Train.toVec (0, t)‖ ≤ |t|
    rw [Train.norm_toVec]
    simp [Real.sqrt_sq_eq_abs]

private theorem vec_eq_liftCoord_add (v : Vec) :
    v = liftCoord 0 (v 0) + liftCoord 1 (v 1) := by
  ext i
  fin_cases i
  · change v 0 = (Train.toVec (v 0, 0) + Train.toVec (0, v 1)) 0
    rw [PiLp.add_apply, Train.toVec_zero, Train.toVec_zero, add_zero]
  · change v 1 = (Train.toVec (v 0, 0) + Train.toVec (0, v 1)) 1
    rw [PiLp.add_apply, Train.toVec_one, Train.toVec_one, zero_add]

end PartI_T21_2

open PartI_T21_2 in
/-- **Proof of `TrainFluctJetWSupNormLe` (`PartI:T21/2/2`)**:
for any BUC train `tr` at age `s > 0`, subtracting the horizontal average `hmean c` increases
`wSupNorm m (ageJet ℓ j · s)` by at most a factor of `4` for both `tr.ψ` and `tr.v`. -/
theorem trainFluctJetWSupNormLe_proof : TrainFluctJetWSupNormLe := by
  intro ν c hν hc tr htr m ℓ j s B hs hB
  refine ⟨fun hSupΨ => ?_, fun hSupV => ?_⟩
  · have hψ_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
      trainStreamSmooth ν c hν hc tr htr
    have h2B := wSupNorm_ageJet_scalar_fluct_le hc hB m ℓ j hψ_sm hs hSupΨ
    exact h2B.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hv_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
    let fk : Fin 2 → ℝ → Plane → ℝ := fun k r w => tr.v r w k
    let gk : Fin 2 → ℝ → Plane → ℝ := fun k r w => fk k r w - hmean c (fk k r) w.2
    have hfk_sm : ∀ k : Fin 2,
        ContDiffOn ℝ ∞ (fun x : ℝ × Plane => fk k x.1 x.2) (Ioi 0 ×ˢ univ) :=
      fun k => (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv_sm
    have hgk_sm : ∀ k : Fin 2,
        ContDiffOn ℝ ∞ (fun x : ℝ × Plane => gk k x.1 x.2) (Ioi 0 ×ˢ univ) := by
      intro k
      have hm := hmeanContDiff c hc (fk k) (hfk_sm k)
      have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
      exact (hfk_sm k).sub (hm.comp hproj.contDiffOn (fun x hx => ⟨hx.1, mem_univ _⟩))
    have hSup_fk : ∀ k : Fin 2, wSupNorm m (ageJet ℓ j (fk k) s) ≤ ENNReal.ofReal B := by
      intro k
      unfold wSupNorm
      refine iSup_le fun z => ?_
      have hz : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖ageJet ℓ j tr.v s z‖ₑ ≤ ENNReal.ofReal B :=
        (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) *
          ‖ageJet ℓ j tr.v s w‖ₑ) z).trans hSupV
      refine (mul_le_mul_of_nonneg_left ?_ (by positivity)).trans hz
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have hcomp := clm_ageJet_comp (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) hv_sm hs ℓ j z
      change ‖ageJet ℓ j (fun r w => (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) (tr.v r w)) s z‖ ≤ _
      rw [hcomp]
      have hproj_norm : ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
        rw [one_mul]
        exact PiLp.norm_apply_le v k
      calc ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ).compContinuousMultilinearMap
              (ageJet ℓ j tr.v s z)‖
          ≤ ‖(EuclideanSpace.proj k : Vec →L[ℝ] ℝ)‖ * ‖ageJet ℓ j tr.v s z‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ‖ageJet ℓ j tr.v s z‖ :=
            mul_le_mul_of_nonneg_right hproj_norm (norm_nonneg _)
        _ = ‖ageJet ℓ j tr.v s z‖ := one_mul _
    have hgk_bound : ∀ (k : Fin 2) (z : Plane),
        Real.sqrt (jap m z) * ‖ageJet ℓ j (gk k) s z‖ ≤ 2 * B := by
      intro k z
      have h2B := wSupNorm_ageJet_scalar_fluct_le hc hB m ℓ j (hfk_sm k) hs (hSup_fk k)
      have hz : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖ageJet ℓ j (gk k) s z‖ₑ ≤
          ENNReal.ofReal (2 * B) :=
        (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) *
          ‖ageJet ℓ j (gk k) s w‖ₑ) z).trans h2B
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hz
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hz
    unfold wSupNorm
    refine iSup_le fun z => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hev_fluct : ∀ w : Plane,
        (fun r => hfluct c (tr.v r) w) =ᶠ[𝓝 s]
          fun r => liftCoord 0 (gk 0 r w) + liftCoord 1 (gk 1 r w) := by
      intro w
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hv_cont : Continuous (tr.v r) :=
        hv_sm.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
          (fun w' => ⟨hr, mem_univ w'⟩)
      have hdec := vec_eq_liftCoord_add (hfluct c (tr.v r) w)
      have h0 : hfluct c (tr.v r) w 0 = gk 0 r w := by
        unfold hfluct
        rw [PiLp.sub_apply, hmean_apply_vec hv_cont w.2 0]
      have h1 : hfluct c (tr.v r) w 1 = gk 1 r w := by
        unfold hfluct
        rw [PiLp.sub_apply, hmean_apply_vec hv_cont w.2 1]
      rw [h0, h1] at hdec
      exact hdec
    have hjet_eq : ageJet ℓ j (fun r => hfluct c (tr.v r)) s z =
        ageJet ℓ j (fun r w => liftCoord 0 (gk 0 r w) + liftCoord 1 (gk 1 r w)) s z := by
      unfold ageJet jet
      congr 1
      funext w
      exact (hev_fluct w).iteratedDeriv_eq ℓ
    have hL0_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => liftCoord 0 (gk 0 x.1 x.2)) (Ioi 0 ×ˢ univ) :=
      (liftCoord 0).contDiff.comp_contDiffOn (hgk_sm 0)
    have hL1_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => liftCoord 1 (gk 1 x.1 x.2)) (Ioi 0 ×ˢ univ) :=
      (liftCoord 1).contDiff.comp_contDiffOn (hgk_sm 1)
    rw [hjet_eq, ageJet_add _ _ hL0_sm hL1_sm hs ℓ j z,
      clm_ageJet_comp (liftCoord 0) (hgk_sm 0) hs ℓ j z,
      clm_ageJet_comp (liftCoord 1) (hgk_sm 1) hs ℓ j z]
    have hnorm0 : ‖(liftCoord 0).compContinuousMultilinearMap (ageJet ℓ j (gk 0) s z)‖ ≤
        ‖ageJet ℓ j (gk 0) s z‖ := by
      calc ‖(liftCoord 0).compContinuousMultilinearMap (ageJet ℓ j (gk 0) s z)‖
          ≤ ‖liftCoord 0‖ * ‖ageJet ℓ j (gk 0) s z‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ‖ageJet ℓ j (gk 0) s z‖ :=
            mul_le_mul_of_nonneg_right (norm_liftCoord_le_one 0) (norm_nonneg _)
        _ = ‖ageJet ℓ j (gk 0) s z‖ := one_mul _
    have hnorm1 : ‖(liftCoord 1).compContinuousMultilinearMap (ageJet ℓ j (gk 1) s z)‖ ≤
        ‖ageJet ℓ j (gk 1) s z‖ := by
      calc ‖(liftCoord 1).compContinuousMultilinearMap (ageJet ℓ j (gk 1) s z)‖
          ≤ ‖liftCoord 1‖ * ‖ageJet ℓ j (gk 1) s z‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ‖ageJet ℓ j (gk 1) s z‖ :=
            mul_le_mul_of_nonneg_right (norm_liftCoord_le_one 1) (norm_nonneg _)
        _ = ‖ageJet ℓ j (gk 1) s z‖ := one_mul _
    have htri : ‖(liftCoord 0).compContinuousMultilinearMap (ageJet ℓ j (gk 0) s z) +
          (liftCoord 1).compContinuousMultilinearMap (ageJet ℓ j (gk 1) s z)‖ ≤
        ‖ageJet ℓ j (gk 0) s z‖ + ‖ageJet ℓ j (gk 1) s z‖ :=
      (norm_add_le _ _).trans (add_le_add hnorm0 hnorm1)
    calc Real.sqrt (jap m z) *
          ‖(liftCoord 0).compContinuousMultilinearMap (ageJet ℓ j (gk 0) s z) +
            (liftCoord 1).compContinuousMultilinearMap (ageJet ℓ j (gk 1) s z)‖
        ≤ Real.sqrt (jap m z) * (‖ageJet ℓ j (gk 0) s z‖ + ‖ageJet ℓ j (gk 1) s z‖) :=
          mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg _)
      _ = Real.sqrt (jap m z) * ‖ageJet ℓ j (gk 0) s z‖ +
            Real.sqrt (jap m z) * ‖ageJet ℓ j (gk 1) s z‖ :=
          mul_add _ _ _
      _ ≤ 2 * B + 2 * B := add_le_add (hgk_bound 0 z) (hgk_bound 1 z)
      _ = 4 * B := by ring

end UnforcedLeray.Short.PartI
