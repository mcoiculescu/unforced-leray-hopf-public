import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.TrainBandSub

/-!
# `TBChartRaised` (`PartIII-b:C/asrc/ra/9/2/2/11/2`)

Source of record: `the November 2 reference manuscript`, 2419-2423, 2075-2077, 4371.

`trH p s x = raisedStream ψ s x.1 x.2 = raisedProf p (s, x)` by definition.  For `s > 0` the stream
`ψ` is jointly `C^∞` (`BgRegime.train_stream_smooth`), so `raisedProf p` agrees near `(s, x)` with the
jointly smooth function `tbrR p = ψ - (η ∂_η ψ + 2 s ∂_s ψ)` written with joint Fréchet derivatives.
Slice derivatives of `tbrR p` are the partials of its joint derivative, which gives the bound with
the factor `2` as slack.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The smooth representative of `raisedProf p` on `s > 0`:
`ψ - (η ∂_η ψ + 2 s ∂_s ψ)` with joint Fréchet derivatives of `ψ`. -/
private def tbrR (p : Params) : ℝ × (ℝ × ℝ) → ℝ := fun y =>
  p.train.ψ y.1 y.2 - (y.2.2 * fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) y (0, (0, 1)) +
    2 * y.1 * fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) y (1, 0))

/-- Derivative of a slice in the first argument. -/
private lemma tbr_slice_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × (ℝ × ℝ) → E} {s : ℝ} {z : ℝ × ℝ} (hG : DifferentiableAt ℝ G (s, z)) :
    HasDerivAt (fun t : ℝ => G (t, z)) (fderiv ℝ G (s, z) (1, 0)) s := by
  have hc : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
  exact hG.hasFDerivAt.comp_hasDerivAt s hc

/-- Derivative of a slice in the `η`-coordinate. -/
private lemma tbr_slice_deriv_eta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × (ℝ × ℝ) → E} {s q η : ℝ} (hG : DifferentiableAt ℝ G (s, (q, η))) :
    HasDerivAt (fun t : ℝ => G (s, (q, t))) (fderiv ℝ G (s, (q, η)) (0, (0, 1))) η := by
  have hc : HasDerivAt (fun t : ℝ => ((s, (q, t)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
    (hasDerivAt_const η s).prodMk ((hasDerivAt_const η q).prodMk (hasDerivAt_id' η))
  exact hG.hasFDerivAt.comp_hasDerivAt η hc

/-- Fréchet derivative of a spatial slice. -/
private lemma tbr_slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × (ℝ × ℝ) → E} {s : ℝ} {z : ℝ × ℝ} (hG : DifferentiableAt ℝ G (s, z)) :
    HasFDerivAt (fun y : ℝ × ℝ => G (s, y))
      ((fderiv ℝ G (s, z)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z := by
  have hc : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  exact hG.hasFDerivAt.comp z hc

/-- Operator norm of a real-valued functional on `ℝ × ℝ` is at most the sum of its basis values. -/
private lemma tbr_opNorm_le (N : (ℝ × ℝ) →L[ℝ] ℝ) : ‖N‖ ≤ |N (1, 0)| + |N (0, 1)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hw : N w = w.1 * N (1, 0) + w.2 * N (0, 1) := by
    conv_lhs => rw [show w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) by ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h1 : |w.1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_fst_le w
  have h2 : |w.2| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_snd_le w
  have habs := abs_add_le (w.1 * N (1, 0)) (w.2 * N (0, 1))
  rw [abs_mul, abs_mul] at habs
  have e1 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (N (1, 0)))
  have e2 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (N (0, 1)))
  rw [Real.norm_eq_abs, hw]
  linarith [habs, e1, e2]

/-- Joint `C^∞` regularity of the derivative of `ψ` in a fixed direction on `(0,∞) × ℝ²`. -/
private lemma tbr_fderiv_dir_contDiffOn {Ψ : ℝ × (ℝ × ℝ) → ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)))) (e : ℝ × (ℝ × ℝ)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ y e)
      (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hD : ContDiffOn ℝ ∞ (fun y => fderiv ℝ Ψ y) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) :=
    hΨ.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (by simp)
  exact hD.clm_apply contDiffOn_const

theorem tbChartRaised : TBChartRaised := by
  intro p d dm dp hBG s hs x
  have hΨ : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) :=
    hBG.train_stream_smooth
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  -- pointwise identity `raisedProf p = tbrR p` on `s > 0`
  have hR1 : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      UnforcedLeray.Short.IIb.raisedProf p y = tbrR p y := by
    intro y hy
    have hdiff : DifferentiableAt ℝ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2)
        (y.1, (y.2.1, y.2.2)) :=
      (hΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ⟨hy, trivial⟩)
    have d1 : deriv (fun t => p.train.ψ y.1 (y.2.1, t)) y.2.2 =
        fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) y (0, (0, 1)) :=
      (tbr_slice_deriv_eta hdiff).deriv
    have d2 : deriv (fun t => p.train.ψ t (y.2.1, y.2.2)) y.1 =
        fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => p.train.ψ z.1 z.2) y (1, 0) :=
      (tbr_slice_deriv hdiff).deriv
    unfold UnforcedLeray.Short.IIb.raisedProf UnforcedLeray.Cons.C03.raisedStream tbrR
    rw [d1, d2]
  -- `tbrR p` is jointly `C^∞` on `(0,∞) × ℝ²`
  have hRC : ContDiffOn ℝ ∞ (tbrR p) (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) := by
    have hD1 := tbr_fderiv_dir_contDiffOn hΨ (0, (0, 1))
    have hD2 := tbr_fderiv_dir_contDiffOn hΨ (1, 0)
    exact hΨ.sub (((contDiff_snd.comp contDiff_snd).contDiffOn.mul hD1).add
      (((contDiff_const.mul contDiff_fst).contDiffOn).mul hD2))
  have hdiffR : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → DifferentiableAt ℝ (tbrR p) y := fun y hy =>
    (hRC.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ⟨hy, trivial⟩)
  have hEv : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → UnforcedLeray.Short.IIb.raisedProf p =ᶠ[𝓝 y] tbrR p :=
    fun y hy => Filter.eventually_of_mem (hU.mem_nhds ⟨hy, trivial⟩) (fun z hz => hR1 z hz.1)
  have hEvS := hEv (s, x) hs
  have hfdEq : fderiv ℝ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) =
      fderiv ℝ (tbrR p) (s, x) := hEvS.fderiv_eq
  -- the planar `x`-derivative of `trH p s`
  have hTH : (fun y => trH p s y) = fun y => tbrR p (s, y) :=
    funext (fun y => hR1 (s, y) hs)
  have hNfd : fderiv ℝ (trH p s) x =
      (fderiv ℝ (tbrR p) (s, x)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (ℝ × ℝ))) := by
    show fderiv ℝ (fun y => trH p s y) x = _
    rw [hTH]
    exact (tbr_slice_fderiv (hdiffR (s, x) hs)).fderiv
  have hNorm : ‖fderiv ℝ (trH p s) x‖ ≤
      |fderiv ℝ (tbrR p) (s, x) (0, (1, 0))| + |fderiv ℝ (tbrR p) (s, x) (0, (0, 1))| := by
    rw [hNfd]
    exact tbr_opNorm_le _
  -- chart quantities of the statement in terms of `tbrR p`
  have hdQ : UnforcedLeray.Axi.dQ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) =
      fderiv ℝ (tbrR p) (s, x) (0, (1, 0)) := by
    show fderiv ℝ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) (0, (1, 0)) = _
    rw [hfdEq]
  have hdE : UnforcedLeray.Axi.dEta (UnforcedLeray.Short.IIb.raisedProf p) (s, x) =
      fderiv ℝ (tbrR p) (s, x) (0, (0, 1)) := by
    show fderiv ℝ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) (0, (0, 1)) = _
    rw [hfdEq]
  have hkAge : UnforcedLeray.Short.IIb.kAge (UnforcedLeray.Short.IIb.raisedProf p) (s, x) =
      (2 * s) • fderiv ℝ (tbrR p) (s, x) (1, 0) + x.2 • fderiv ℝ (tbrR p) (s, x) (0, (0, 1)) := by
    show (2 * s) • fderiv ℝ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) (1, 0) +
      x.2 • fderiv ℝ (UnforcedLeray.Short.IIb.raisedProf p) (s, x) (0, (0, 1)) = _
    rw [hfdEq]
  -- the derivative of `s ↦ H(s, x)` and the operator `𝒦 H`
  have hdsl : deriv (fun s' => trH p s' x) s = fderiv ℝ (tbrR p) (s, x) (1, 0) := by
    have hev : (fun s' => trH p s' x) =ᶠ[𝓝 s] (fun s' => tbrR p (s', x)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) (fun s' hs' => hR1 (s', x) hs')
    rw [hev.deriv_eq]
    exact (tbr_slice_deriv (hdiffR (s, x) hs)).deriv
  have hKop : Kop (trH p) s x =
      (2 * s) • fderiv ℝ (tbrR p) (s, x) (1, 0) + x.2 • fderiv ℝ (tbrR p) (s, x) (0, (0, 1)) := by
    show x.2 * fderiv ℝ (trH p s) x (ei 1) + 2 * s * deriv (fun s' => trH p s' x) s = _
    rw [hdsl, hNfd]
    show x.2 * fderiv ℝ (tbrR p) (s, x) (0, (0, 1)) + 2 * s * fderiv ℝ (tbrR p) (s, x) (1, 0) = _
    simp only [smul_eq_mul]
    ring
  -- assembly
  rw [show |trH p s x| = |UnforcedLeray.Short.IIb.raisedProf p (s, x)| from rfl]
  rw [hKop, hkAge, hdQ, hdE]
  have hA := abs_nonneg (UnforcedLeray.Short.IIb.raisedProf p (s, x))
  have hB := abs_nonneg (fderiv ℝ (tbrR p) (s, x) (0, (1, 0)))
  have hC := abs_nonneg (fderiv ℝ (tbrR p) (s, x) (0, (0, 1)))
  have hE := abs_nonneg ((2 * s) • fderiv ℝ (tbrR p) (s, x) (1, 0) +
    x.2 • fderiv ℝ (tbrR p) (s, x) (0, (0, 1)))
  linarith [hNorm, hA, hB, hC, hE]

end UnforcedLeray.Short.PartIIIb.Concrete
