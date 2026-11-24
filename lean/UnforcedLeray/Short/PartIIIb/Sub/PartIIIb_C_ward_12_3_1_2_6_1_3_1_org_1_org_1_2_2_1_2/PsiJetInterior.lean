import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1_2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSegment
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# `PsiJetInterior`: jets of the train stream on the transverse band

Source: `the November 2 reference manuscript`,
SP 261-288 (the train is smooth on `[0,∞) × ℝ²`, `v = ∇^⊥ψ`, periodic in `q`), SP 468-478.

* `theta_exists`: the age/space jets of a family smooth on the closed half space are the values of a
  function continuous up to `s = 0`.
* `velAgeJet_band_bound`: compactness (periodicity in `q`) bounds the jets of `v` on the band.
* `psi_ageJet_succ`: `‖∂_s^ℓ D^{m+1} ψ‖ ≤ 2 ‖∂_s^ℓ D^m v‖` (`Dψ·h = h₁ v₁ - h₂ v₀`).
* `j = 0`: the mean value theorem in `η` (`psiEtaSegment_proof`) from the band edge.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.PsiJetInteriorAux

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.PartI

/-- Slice formula in the plane variable at fixed `s > 0`. -/
theorem slice_plane_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × Plane → E) (hH : ContDiffOn ℝ ∞ H (Ioi 0 ×ˢ univ)) (m : ℕ) {s : ℝ} (hs : 0 < s)
    (z : Plane) :
    iteratedFDeriv ℝ m (fun z' : Plane => H (s, z')) z =
      (iteratedFDeriv ℝ m H (s, z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane) := by
  have hopen : IsOpen {p : ℝ × Plane | 0 < s + p.1} :=
    isOpen_lt continuous_const (continuous_const.add continuous_fst)
  have hmaps : MapsTo (fun p : ℝ × Plane => p + (s, (0 : Plane))) {p : ℝ × Plane | 0 < s + p.1}
      (Ioi 0 ×ˢ (univ : Set Plane)) :=
    fun p hp => ⟨by simpa [add_comm] using hp, mem_univ _⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => H (p + (s, (0 : Plane))))
      {p : ℝ × Plane | 0 < s + p.1} :=
    hH.comp (contDiff_id.add contDiff_const).contDiffOn hmaps
  have hfun : (fun z' : Plane => H (s, z')) =
      (fun p : ℝ × Plane => H (p + (s, (0 : Plane)))) ∘ (ContinuousLinearMap.inr ℝ ℝ Plane) := by
    funext z'
    simp [add_comm]
  have hL : ContinuousLinearMap.inr ℝ ℝ Plane z ∈ {p : ℝ × Plane | 0 < s + p.1} := by
    simpa using hs
  have hpre : (ContinuousLinearMap.inr ℝ ℝ Plane) ⁻¹' {p : ℝ × Plane | 0 < s + p.1} = univ := by
    ext z'
    simp [hs]
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inr ℝ ℝ Plane) hsmooth hopen.uniqueDiffOn
    (by rw [hpre]; exact uniqueDiffOn_univ) hL (i := m) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m hopen hL, hpre, iteratedFDerivWithin_univ] at hcomp
  have hA : iteratedFDeriv ℝ m (fun p : ℝ × Plane => H (p + (s, (0 : Plane))))
      (ContinuousLinearMap.inr ℝ ℝ Plane z) = iteratedFDeriv ℝ m H (s, z) := by
    rw [iteratedFDeriv_comp_add_right]
    simp [add_comm]
  rw [hfun, hcomp, hA]

/-- Within the closed half space, at an interior point, the within-derivative is the derivative. -/
theorem within_eq_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Plane → E) (n : ℕ) {x : ℝ × Plane} (hx : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :
    iteratedFDerivWithin ℝ n f (Ici 0 ×ˢ univ) x = iteratedFDeriv ℝ n f x := by
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hUD : (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) ⊆ Ici 0 ×ˢ univ :=
    prod_mono Ioi_subset_Ici_self (subset_refl _)
  rw [← iteratedFDerivWithin_inter_open hUo hx, inter_eq_right.mpr hUD,
    iteratedFDerivWithin_of_isOpen n hUo hx]

/-- The age/space jets of a family smooth on `[0,∞) × ℝ²` extend continuously to `s = 0`. -/
theorem theta_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℝ × Plane → E) (hV : ContDiffOn ℝ ∞ V (Ici 0 ×ˢ univ)) (ℓ m : ℕ) :
    ∃ Θ : ℝ × Plane → ContinuousMultilinearMap ℝ (fun _ : Fin m => Plane) E,
      ContinuousOn Θ (Ici 0 ×ˢ univ) ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
        iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv ℓ (fun r => V (r, z')) s) z =
          Θ (s, z) := by
  have hDU : UniqueDiffOn ℝ (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hUD : (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) ⊆ Ici 0 ×ˢ univ :=
    prod_mono Ioi_subset_Ici_self (subset_refl _)
  have hVU : ContDiffOn ℝ ∞ V (Ioi 0 ×ˢ univ) := hV.mono hUD
  have hPs : ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ ℓ V (Ici 0 ×ˢ univ)) (Ici 0 ×ˢ univ) := by
    intro x hx
    exact (hV x hx).iteratedFDerivWithin_right hDU (by simp) hx
  have hHs : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => iteratedFDerivWithin ℝ ℓ V (Ici 0 ×ˢ univ) x (fun _ => (1, 0)))
      (Ici 0 ×ˢ univ) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin ℓ => ℝ × Plane) E
      (fun _ => (1, 0))).contDiff.comp_contDiffOn hPs
  have hQ := hHs.continuousOn_iteratedFDerivWithin (m := m) (mod_cast le_top) hDU
  refine ⟨fun x => (iteratedFDerivWithin ℝ m
      (fun x : ℝ × Plane => iteratedFDerivWithin ℝ ℓ V (Ici 0 ×ˢ univ) x (fun _ => (1, 0)))
      (Ici 0 ×ˢ univ) x).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane),
    ?_, ?_⟩
  · exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ Plane)).continuous.comp_continuousOn hQ
  · intro s hs z
    have hmem : ∀ w : Plane, (s, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) :=
      fun w => ⟨hs, mem_univ _⟩
    have hstep : (fun z' : Plane => iteratedDeriv ℓ (fun r => V (r, z')) s) =
        fun z' : Plane => (fun x : ℝ × Plane =>
          iteratedFDerivWithin ℝ ℓ V (Ici 0 ×ˢ univ) x (fun _ => (1, 0))) (s, z') := by
      funext z'
      rw [vb_slice_iteratedDeriv_eq V hVU ℓ hs z']
      show _ = iteratedFDerivWithin ℝ ℓ V (Ici 0 ×ˢ univ) (s, z') (fun _ => (1, 0))
      rw [within_eq_open V ℓ (hmem z')]
    rw [hstep, slice_plane_iteratedFDeriv _ (hHs.mono hUD) m hs z,
      ← within_eq_open _ m (hmem z)]

/-- The age/space jets of `v` are periodic in `q` for `s > 0`. -/
theorem ageJet_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) (ℓ m : ℕ) {s : ℝ} (hs : 0 < s)
    (z : Plane) : ageJet ℓ m tr.v s (z.1 + c, z.2) = ageJet ℓ m tr.v s z := by
  set W : Plane → UnforcedLeray.Train.Vec := fun z' => iteratedDeriv ℓ (fun r => tr.v r z') s
    with hWdef
  have hW : ∀ z' : Plane, W (z'.1 + c, z'.2) = W z' := by
    intro z'
    have : (fun r => tr.v r (z'.1 + c, z'.2)) =ᶠ[𝓝 s] (fun r => tr.v r z') := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      exact tr.isTrain.periodic_v r (le_of_lt hr) z'
    exact this.iteratedDeriv_eq ℓ
  have hfun : (fun z' : Plane => W (z' + (c, 0))) = W := by
    funext z'
    have e : z' + (c, 0) = (z'.1 + c, z'.2) := by ext <;> simp
    rw [e]
    exact hW z'
  have h1 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := W) m (c, (0 : ℝ)) z
  rw [hfun] at h1
  show iteratedFDeriv ℝ m W (z.1 + c, z.2) = iteratedFDeriv ℝ m W z
  have : ((z.1 + c, z.2) : Plane) = z + (c, 0) := by ext <;> simp
  rw [this, ← h1]

/-- **Band bound for the velocity jets** (SP 261-288, 468-478): at fixed `c`, every age/space jet
of `v` is bounded on `0 < s ≤ S`, `|η| ≤ R` (continuity up to `s = 0` and `c`-periodicity in `q`). -/
theorem velAgeJet_band_bound {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c) (S R : ℝ)
    (ℓ m : ℕ) :
    ∃ M : ℝ, ∀ s : ℝ, 0 < s → s ≤ S → ∀ z : Plane, |z.2| ≤ R →
      ‖ageJet ℓ m tr.v s z‖ ≤ M := by
  obtain ⟨Θ, hΘ, hΘeq⟩ := theta_exists (fun x : ℝ × Plane => tr.v x.1 x.2)
    tr.isTrain.smooth_v ℓ m
  have hKc : IsCompact (Icc (0 : ℝ) S ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKD : (Icc (0 : ℝ) S ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-R) R)) ⊆ Ici 0 ×ˢ univ :=
    fun x hx => ⟨hx.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΘ.mono hKD)
  refine ⟨M, fun s hs hsS z hz => ?_⟩
  have hper : Function.Periodic (fun q : ℝ => ageJet ℓ m tr.v s (q, z.2)) c := by
    intro q
    exact ageJet_periodic tr ℓ m hs (q, z.2)
  obtain ⟨q', hq', hqq⟩ := hper.exists_mem_Ico₀ hc z.1
  have e1 : ageJet ℓ m tr.v s z = Θ (s, (q', z.2)) := by
    have h : ageJet ℓ m tr.v s z = ageJet ℓ m tr.v s (q', z.2) := hqq
    rw [h]
    exact hΘeq s hs (q', z.2)
  rw [e1]
  exact hM (s, (q', z.2)) ⟨⟨hs.le, hsS⟩, ⟨hq'.1, hq'.2.le⟩, abs_le.1 hz⟩

/-- Directional derivative of a differentiable function on the plane along the first axis. -/
theorem hasDerivAt_fst_line {G : Plane → ℝ} {z : Plane} (hG : DifferentiableAt ℝ G z) :
    HasDerivAt (fun x : ℝ => G (x, z.2)) (fderiv ℝ G z (1, 0)) z.1 :=
  hG.hasFDerivAt.comp_hasDerivAt z.1 ((hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2))

/-- Directional derivative of a differentiable function on the plane along the second axis. -/
theorem hasDerivAt_snd_line {G : Plane → ℝ} {z : Plane} (hG : DifferentiableAt ℝ G z) :
    HasDerivAt (fun y : ℝ => G (z.1, y)) (fderiv ℝ G z (0, 1)) z.2 :=
  hG.hasFDerivAt.comp_hasDerivAt z.2 ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2))

/-- The linear map `w ↦ (h ↦ h₁ w₁ - h₂ w₀)`. -/
def Lam : UnforcedLeray.Train.Vec →L[ℝ] (Plane →L[ℝ] ℝ) :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    (EuclideanSpace.proj (0 : Fin 2)).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem Lam_apply (w : UnforcedLeray.Train.Vec) (h : Plane) :
    Lam w h = h.1 * w 1 - h.2 * w 0 := by
  simp [Lam]
  ring

theorem Lam_norm_le : ‖Lam‖ ≤ 2 := by
  refine Lam.opNorm_le_bound (by norm_num) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [Lam_apply, Real.norm_eq_abs]
  have hw0 : |w 0| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le w 0
  have hw1 : |w 1| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le w 1
  have h1 : |h.1| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le h
  have h2 : |h.2| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le h
  calc |h.1 * w 1 - h.2 * w 0| ≤ |h.1 * w 1| + |h.2 * w 0| := abs_sub _ _
    _ = |h.1| * |w 1| + |h.2| * |w 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖h‖ * ‖w‖ + ‖h‖ * ‖w‖ :=
        add_le_add (mul_le_mul h1 hw1 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h2 hw0 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖h‖ := by ring

/-- **Jets of the stream from jets of the velocity** (`Dψ·h = h₁ v₁ - h₂ v₀`, SP 261-291):
`‖∂_s^ℓ D^{m+1} ψ‖ ≤ 2 ‖∂_s^ℓ D^m v‖` for `s > 0`. -/
theorem psi_ageJet_succ (ψ : ℝ → Plane → ℝ) (v : ℝ → Plane → UnforcedLeray.Train.Vec)
    (hsp : IsStreamPair ψ v) (ℓ m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ (m + 1) ψ s z‖ ≤ 2 * ‖ageJet ℓ m v s z‖ := by
  obtain ⟨hΨ, hV, _⟩ := id hsp
  set g : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => ψ r z') s with hg
  set W : Plane → UnforcedLeray.Train.Vec := fun z' => iteratedDeriv ℓ (fun r => v r z') s
    with hW
  have hgc : ∀ w : Plane, ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g w := fun w =>
    vb_slice_contDiffAt (fun x : ℝ × Plane => ψ x.1 x.2) hΨ ℓ (m + 1) hs w
  have hWc : ContDiffAt ℝ (m : WithTop ℕ∞) W z :=
    vb_slice_contDiffAt (fun x : ℝ × Plane => v x.1 x.2) hV ℓ m hs z
  have hgd : ∀ w : Plane, DifferentiableAt ℝ g w := fun w =>
    (hgc w).differentiableAt (by norm_cast)
  have h10 : ∀ w : Plane, fderiv ℝ g w (1, 0) = W w 1 := fun w =>
    (hasDerivAt_fst_line (hgd w)).unique (psiQSwap_proof ψ v hsp ℓ s hs w.1 w.2)
  have h01 : ∀ w : Plane, fderiv ℝ g w (0, 1) = -(W w 0) := fun w =>
    (hasDerivAt_snd_line (hgd w)).unique (psiEtaSwap_proof ψ v hsp ℓ s hs w.1 w.2)
  have hLin : ∀ w h : Plane, fderiv ℝ g w h = h.1 * W w 1 - h.2 * W w 0 := by
    intro w h
    have hsplit : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h10, h01]
    ring
  have hfd : fderiv ℝ g = Lam ∘ W := by
    funext w
    refine ContinuousLinearMap.ext fun h => ?_
    rw [hLin, Function.comp_apply, Lam_apply]
  calc ‖ageJet ℓ (m + 1) ψ s z‖ = ‖iteratedFDeriv ℝ (m + 1) g z‖ := rfl
    _ = ‖iteratedFDeriv ℝ m (fderiv ℝ g) z‖ := norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ m (Lam ∘ W) z‖ := by rw [hfd]
    _ ≤ ‖Lam‖ * ‖iteratedFDeriv ℝ m W z‖ := Lam.norm_iteratedFDeriv_comp_left hWc le_rfl
    _ ≤ 2 * ‖ageJet ℓ m v s z‖ :=
        mul_le_mul Lam_norm_le (le_of_eq rfl) (norm_nonneg _) (by norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete.PsiJetInteriorAux

open UnforcedLeray.Short.PartIIIb.Concrete.PsiJetInteriorAux in
/-- **Jets of the train stream on the transverse band, bounded ages** (SP 261-288, 468-478). -/
theorem psiJetInterior : UnforcedLeray.Short.PartIIIb.Concrete.PsiJetInterior := by
  intro ν c hν hc tr htr ℓ j S R K hedge
  have hsp : UnforcedLeray.Short.IIb.IsStreamPair tr.ψ tr.v :=
    ⟨UnforcedLeray.Short.PartI.trainStreamSmooth ν c hν hc tr htr,
      tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self (subset_rfl)),
      fun s hs z => tr.isTrain.stream s hs.le z⟩
  cases j with
  | zero =>
    obtain ⟨M, hM⟩ := velAgeJet_band_bound hc tr S R ℓ 0
    refine ⟨K + max M 0 * (2 * R), fun s hs hsS z hz => ?_⟩
    have hz' := abs_le.1 hz
    have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hz
    have hseg : ∀ t ∈ Set.uIcc z.2 R, ‖UnforcedLeray.Short.PartI.ageJet ℓ 0 tr.v s (z.1, t)‖ ≤
        max M 0 := by
      intro t ht
      have ht' : |t| ≤ R := by
        rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact abs_le.2 ⟨by linarith, by linarith⟩
        · exact abs_le.2 ⟨by linarith, by linarith⟩
      exact (hM s hs hsS (z.1, t) ht').trans (le_max_left _ _)
    have h1 := psiEtaSegment_proof tr.ψ tr.v hsp ℓ s hs z.1 z.2 R
      (max M 0) hseg
    have h2 := hedge s hs hsS z.1
    have h3 : |z.2 - R| ≤ 2 * R := by
      rw [abs_le]; constructor <;> linarith
    have h4 : max M 0 * |z.2 - R| ≤ max M 0 * (2 * R) :=
      mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    simp only [Prod.mk.eta] at h1
    linarith
  | succ m =>
    obtain ⟨M, hM⟩ := velAgeJet_band_bound hc tr S R ℓ m
    refine ⟨2 * M, fun s hs hsS z hz => ?_⟩
    calc _ ≤ 2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ :=
          psi_ageJet_succ tr.ψ tr.v hsp ℓ m hs z
      _ ≤ 2 * M := by linarith [hM s hs hsS z hz]
